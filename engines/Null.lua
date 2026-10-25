--!native
--!optimize 2
--[[
    FABLE  -  chess engine for Luau / Roblox
    ------------------------------------------------------------------
    Drop-in API compatible with Aether Prime:
        local Fable = require(thisModule)
        local move, score, reaction = Fable:GetBestMoveFromFEN(fen, thinkSeconds, options)

    Extra:
        Fable:Perft(fen, depth)                 -- move-generator self test
        Fable:Duel(opponentEngine, {Games=10, ThinkTime=0.5})   -- built-in match harness
        Fable:Configure({HashBits=18, NodeLimit=..., MaxQDepth=..., UseBook=true})
        Fable:SetStyle("Balanced" | "Aggressive" | "Solid" | "Tactical" | "Endgame")

    Main upgrades over a plain PVS engine:
      * zero per-node table allocation (preallocated move/score/quiet buffers per ply)
      * 2-way bucket transposition table with aging, TT-aware static eval, TT in qsearch
      * PVS + aspiration windows, check extension, singular extensions + multi-cut
      * null move (with verification), reverse futility, razoring, futility, late-move pruning,
        SEE pruning (quiets + captures), internal iterative deepening
      * LMR driven by history / continuation history / improving / PV / check
      * butterfly history (persistent, aged) + 1-ply continuation history + killers + countermoves
      * richer eval: tapered PST, bishop pair, mobility on safe squares, outposts, bad bishop,
        passed pawns (king distance, blockers, supported, unstoppable), isolated/doubled/phalanx,
        rook files + 7th, pawn threats, king shield + king-zone attack danger,
        opposite-bishop / drawish scaling, KXK mop-up
      * partial-iteration result acceptance and soft/hard time management
]]

local G = _G.__FABLE_V1 or {}
_G.__FABLE_V1 = G

local bit = bit32
local band, bxor, rshift = bit.band, bit.bxor, bit.rshift
local floor, abs, mmin, mmax, mlog = math.floor, math.abs, math.min, math.max, math.log
local clock = os.clock
local yield = (task and task.wait) or function() end
local tcreate = table.create or function(n, v)
    local t = {}
    for i = 1, n do t[i] = v end
    return t
end
local function clamp(x, lo, hi)
    if x < lo then return lo elseif x > hi then return hi end
    return x
end

local INF, MATE, MAX_PLY = 1000000000, 100000, 100
local WHITE, BLACK = 1, -1
local PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 1, 2, 3, 4, 5, 6

local VAL = {100, 320, 330, 500, 900, 20000}
local PHASE_W = {0, 1, 1, 2, 4, 0}
local KNIGHT_D = {33, 31, 18, 14, -14, -18, -31, -33}
local BISHOP_D = {15, 17, -15, -17}
local ROOK_D = {1, -1, 16, -16}
local KING_D = {1, -1, 16, -16, 15, 17, -15, -17}
local PROMOS = {QUEEN, ROOK, BISHOP, KNIGHT}

local FLAG_CAPTURE, FLAG_EP, FLAG_CASTLE, FLAG_DOUBLE = 1, 2, 4, 8
local START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

-- ON[s + 64] is true when 0x88 square s is on the board
local ON = {}
for i = 0, 255 do
    local s = i - 64
    ON[i] = (s >= 0 and s < 128 and band(s, 8) == 0)
end

local SQ64 = {}
for r = 0, 7 do for f = 0, 7 do SQ64[#SQ64 + 1] = r * 16 + f end end

local CM = {}
for i = 0, 127 do CM[i] = 15 end
CM[0] = 13; CM[7] = 14; CM[4] = 12
CM[112] = 7; CM[119] = 11; CM[116] = 3

------------------------------------------------------------------------
-- Zobrist (two independent 32-bit keys -> effectively 64-bit)
------------------------------------------------------------------------
G.Seed = G.Seed or 0x9E3779B1
local function rand32()
    local x = G.Seed
    x = bxor(x, bit.lshift(x, 13))
    x = bxor(x, rshift(x, 17))
    x = bxor(x, bit.lshift(x, 5))
    G.Seed = x
    return x
end

if not G.ZInit then
    G.ZP1, G.ZP2 = {}, {}
    for p = 1, 13 do
        G.ZP1[p], G.ZP2[p] = {}, {}
        for s = 0, 127 do
            G.ZP1[p][s + 1] = rand32()
            G.ZP2[p][s + 1] = rand32()
        end
    end
    G.ZC1, G.ZC2, G.ZE1, G.ZE2 = {}, {}, {}, {}
    for i = 1, 16 do G.ZC1[i] = rand32(); G.ZC2[i] = rand32() end
    for i = 1, 8 do G.ZE1[i] = rand32(); G.ZE2[i] = rand32() end
    G.ZS1, G.ZS2 = rand32(), rand32()
    G.ZInit = true
end
local ZP1, ZP2, ZC1, ZC2, ZE1, ZE2 = G.ZP1, G.ZP2, G.ZC1, G.ZC2, G.ZE1, G.ZE2
local ZS1, ZS2 = G.ZS1, G.ZS2

------------------------------------------------------------------------
-- Piece-square tables (rank 8 first, white's point of view)
------------------------------------------------------------------------
local MAT_MG = {82, 337, 365, 477, 1025, 0}
local MAT_EG = {94, 281, 297, 512, 936, 0}

local PST_MG = {
    { 0, 0, 0, 0, 0, 0, 0, 0,
      60, 60, 60, 60, 60, 60, 60, 60,
      25, 25, 28, 35, 35, 28, 25, 25,
      10, 10, 16, 28, 28, 16, 10, 10,
      2, 4, 10, 24, 24, 10, 4, 2,
      2, 0, 4, 10, 10, 4, 0, 2,
      4, 6, 6, -22, -22, 6, 6, 4,
      0, 0, 0, 0, 0, 0, 0, 0 },
    { -50, -40, -30, -30, -30, -30, -40, -50,
      -40, -20, 0, 5, 5, 0, -20, -40,
      -30, 0, 12, 18, 18, 12, 0, -30,
      -30, 5, 18, 24, 24, 18, 5, -30,
      -30, 0, 18, 24, 24, 18, 0, -30,
      -30, 5, 12, 18, 18, 12, 5, -30,
      -40, -20, 0, 5, 5, 0, -20, -40,
      -50, -35, -30, -30, -30, -30, -35, -50 },
    { -20, -10, -10, -10, -10, -10, -10, -20,
      -10, 5, 0, 0, 0, 0, 5, -10,
      -10, 10, 10, 12, 12, 10, 10, -10,
      -10, 0, 12, 14, 14, 12, 0, -10,
      -10, 4, 10, 14, 14, 10, 4, -10,
      -10, 8, 10, 10, 10, 10, 8, -10,
      -10, 12, 4, 4, 4, 4, 12, -10,
      -20, -10, -10, -10, -10, -10, -10, -20 },
    { 0, 0, 0, 0, 0, 0, 0, 0,
      10, 14, 14, 14, 14, 14, 14, 10,
      -6, 0, 0, 0, 0, 0, 0, -6,
      -6, 0, 0, 0, 0, 0, 0, -6,
      -6, 0, 0, 0, 0, 0, 0, -6,
      -6, 0, 0, 0, 0, 0, 0, -6,
      -6, 0, 0, 0, 0, 0, 0, -6,
      -2, 0, 4, 8, 8, 4, 0, -2 },
    { -20, -10, -10, -5, -5, -10, -10, -20,
      -10, 0, 0, 0, 0, 0, 0, -10,
      -10, 0, 6, 6, 6, 6, 0, -10,
      -5, 0, 6, 8, 8, 6, 0, -5,
      -5, 0, 6, 8, 8, 6, 0, -5,
      -10, 0, 6, 6, 6, 6, 0, -10,
      -10, 0, 2, 0, 0, 0, 0, -10,
      -20, -10, -10, -5, -5, -10, -10, -20 },
    { -65, -75, -80, -90, -90, -80, -75, -65,
      -60, -70, -75, -85, -85, -75, -70, -60,
      -55, -65, -70, -80, -80, -70, -65, -55,
      -50, -60, -65, -75, -75, -65, -60, -50,
      -40, -50, -55, -65, -65, -55, -50, -40,
      -25, -35, -40, -45, -45, -40, -35, -25,
      10, 5, -15, -30, -30, -15, 5, 10,
      25, 40, 15, -10, -10, 10, 40, 25 },
}

local PST_EG = {}
for t = 2, 5 do PST_EG[t] = PST_MG[t] end
PST_EG[KING] = {
    -50, -35, -25, -20, -20, -25, -35, -50,
    -35, -15, -5, 0, 0, -5, -15, -35,
    -25, -5, 15, 25, 25, 15, -5, -25,
    -20, 0, 25, 35, 35, 25, 0, -20,
    -20, 0, 25, 35, 35, 25, 0, -20,
    -25, -5, 15, 25, 25, 15, -5, -25,
    -35, -15, -5, 0, 0, -5, -15, -35,
    -50, -35, -25, -20, -20, -25, -35, -50 }
do
    local adv = {0, 0, 4, 12, 28, 55, 95, 0}
    local t = {}
    for i = 1, 64 do
        local row = floor((i - 1) / 8) -- 0 = rank 8
        t[i] = adv[8 - row]
    end
    PST_EG[PAWN] = t
end

local MGT, EGT = {}, {}
for i = 1, 13 do MGT[i], EGT[i] = {}, {} end
for t = 1, 6 do
    for s = 0, 127 do
        if band(s, 8) == 0 then
            local r, f = rshift(s, 4), band(s, 15)
            local iw = (7 - r) * 8 + f + 1
            local ib = r * 8 + f + 1
            MGT[t + 7][s] = MAT_MG[t] + PST_MG[t][iw]
            EGT[t + 7][s] = MAT_EG[t] + PST_EG[t][iw]
            MGT[7 - t][s] = -(MAT_MG[t] + PST_MG[t][ib])
            EGT[7 - t][s] = -(MAT_EG[t] + PST_EG[t][ib])
        end
    end
end

------------------------------------------------------------------------
-- Styles
------------------------------------------------------------------------
local STYLE = {
    Balanced   = {Att = 1.0, Safe = 1.0, Mob = 1.0, Pwn = 1.0, Contempt = 10, Center = 4, LMR = 1.0},
    Aggressive = {Att = 1.35, Safe = 0.85, Mob = 1.1, Pwn = 0.95, Contempt = 22, Center = 6, LMR = 1.0},
    Solid      = {Att = 0.85, Safe = 1.25, Mob = 0.95, Pwn = 1.1, Contempt = 0, Center = 3, LMR = 1.0},
    Tactical   = {Att = 1.25, Safe = 0.95, Mob = 1.15, Pwn = 0.95, Contempt = 14, Center = 6, LMR = 0.9},
    Endgame    = {Att = 0.8, Safe = 0.9, Mob = 1.0, Pwn = 1.3, Contempt = 5, Center = 4, LMR = 1.0},
}

------------------------------------------------------------------------
-- Moves
------------------------------------------------------------------------
local function moveName(m)
    local from, to, promo = band(m, 127), band(rshift(m, 7), 127), band(rshift(m, 14), 7)
    local s = string.char(97 + band(from, 15)) .. tostring(rshift(from, 4) + 1)
        .. string.char(97 + band(to, 15)) .. tostring(rshift(to, 4) + 1)
    if promo == KNIGHT then s = s .. "n" elseif promo == BISHOP then s = s .. "b"
    elseif promo == ROOK then s = s .. "r" elseif promo == QUEEN then s = s .. "q" end
    return s
end
local function squareName(s)
    return string.char(97 + band(s, 15)) .. tostring(rshift(s, 4) + 1)
end

------------------------------------------------------------------------
-- Attacks
------------------------------------------------------------------------
local function isAttacked(E, s, by)
    local B = E.board
    if by == WHITE then
        local a = s - 15
        if ON[a + 64] and B[a] == PAWN then return true end
        a = s - 17
        if ON[a + 64] and B[a] == PAWN then return true end
    else
        local a = s + 15
        if ON[a + 64] and B[a] == -PAWN then return true end
        a = s + 17
        if ON[a + 64] and B[a] == -PAWN then return true end
    end
    local kn = by * KNIGHT
    for i = 1, 8 do
        local t = s + KNIGHT_D[i]
        if ON[t + 64] and B[t] == kn then return true end
    end
    local bi, qu, ro, ki = by * BISHOP, by * QUEEN, by * ROOK, by * KING
    for i = 1, 4 do
        local d = BISHOP_D[i]
        local t = s + d
        while ON[t + 64] do
            local p = B[t]
            if p ~= 0 then
                if p == bi or p == qu then return true end
                break
            end
            t = t + d
        end
    end
    for i = 1, 4 do
        local d = ROOK_D[i]
        local t = s + d
        while ON[t + 64] do
            local p = B[t]
            if p ~= 0 then
                if p == ro or p == qu then return true end
                break
            end
            t = t + d
        end
    end
    for i = 1, 8 do
        local t = s + KING_D[i]
        if ON[t + 64] and B[t] == ki then return true end
    end
    return false
end

local function inCheck(E, side)
    local k = (side == WHITE) and E.kingW or E.kingB
    return isAttacked(E, k, -side)
end

------------------------------------------------------------------------
-- Move generation (pseudo-legal) into a caller-supplied buffer
------------------------------------------------------------------------
local function generate(E, moves, capsOnly)
    local B = E.board
    local n = 0
    local side = E.side
    local enemy = -side
    local ep = E.ep
    local step = side * 16
    local startRank = (side == WHITE) and 1 or 6
    local promoRank = (side == WHITE) and 7 or 0

    for idx = 1, 64 do
        local s = SQ64[idx]
        local p = B[s]
        if p * side > 0 then
            local t = (p > 0) and p or -p
            if t == PAWN then
                local one = s + step
                if B[one] == 0 then
                    if rshift(one, 4) == promoRank then
                        if capsOnly then
                            n = n + 1; moves[n] = s + one * 128 + QUEEN * 16384
                        else
                            for i = 1, 4 do n = n + 1; moves[n] = s + one * 128 + PROMOS[i] * 16384 end
                        end
                    elseif not capsOnly then
                        n = n + 1; moves[n] = s + one * 128
                        if rshift(s, 4) == startRank then
                            local two = one + step
                            if B[two] == 0 then n = n + 1; moves[n] = s + two * 128 + FLAG_DOUBLE * 131072 end
                        end
                    end
                end
                for k = -1, 1, 2 do
                    local c = one + k
                    if ON[c + 64] then
                        local q = B[c]
                        if q * side < 0 then
                            if rshift(c, 4) == promoRank then
                                if capsOnly then
                                    n = n + 1; moves[n] = s + c * 128 + QUEEN * 16384 + FLAG_CAPTURE * 131072
                                else
                                    for i = 1, 4 do
                                        n = n + 1; moves[n] = s + c * 128 + PROMOS[i] * 16384 + FLAG_CAPTURE * 131072
                                    end
                                end
                            else
                                n = n + 1; moves[n] = s + c * 128 + FLAG_CAPTURE * 131072
                            end
                        elseif q == 0 and c == ep then
                            n = n + 1; moves[n] = s + c * 128 + (FLAG_CAPTURE + FLAG_EP) * 131072
                        end
                    end
                end
            elseif t == KNIGHT then
                for i = 1, 8 do
                    local to = s + KNIGHT_D[i]
                    if ON[to + 64] then
                        local q = B[to]
                        if q == 0 then
                            if not capsOnly then n = n + 1; moves[n] = s + to * 128 end
                        elseif q * side < 0 then
                            n = n + 1; moves[n] = s + to * 128 + FLAG_CAPTURE * 131072
                        end
                    end
                end
            elseif t == KING then
                for i = 1, 8 do
                    local to = s + KING_D[i]
                    if ON[to + 64] then
                        local q = B[to]
                        if q == 0 then
                            if not capsOnly then n = n + 1; moves[n] = s + to * 128 end
                        elseif q * side < 0 then
                            n = n + 1; moves[n] = s + to * 128 + FLAG_CAPTURE * 131072
                        end
                    end
                end
                local cr = E.castle
                if not capsOnly and cr ~= 0 then
                    if side == WHITE and s == 4 then
                        if band(cr, 1) ~= 0 and B[5] == 0 and B[6] == 0 and B[7] == ROOK
                            and not isAttacked(E, 4, enemy) and not isAttacked(E, 5, enemy) and not isAttacked(E, 6, enemy) then
                            n = n + 1; moves[n] = 4 + 6 * 128 + FLAG_CASTLE * 131072
                        end
                        if band(cr, 2) ~= 0 and B[3] == 0 and B[2] == 0 and B[1] == 0 and B[0] == ROOK
                            and not isAttacked(E, 4, enemy) and not isAttacked(E, 3, enemy) and not isAttacked(E, 2, enemy) then
                            n = n + 1; moves[n] = 4 + 2 * 128 + FLAG_CASTLE * 131072
                        end
                    elseif side == BLACK and s == 116 then
                        if band(cr, 4) ~= 0 and B[117] == 0 and B[118] == 0 and B[119] == -ROOK
                            and not isAttacked(E, 116, enemy) and not isAttacked(E, 117, enemy) and not isAttacked(E, 118, enemy) then
                            n = n + 1; moves[n] = 116 + 118 * 128 + FLAG_CASTLE * 131072
                        end
                        if band(cr, 8) ~= 0 and B[115] == 0 and B[114] == 0 and B[113] == 0 and B[112] == -ROOK
                            and not isAttacked(E, 116, enemy) and not isAttacked(E, 115, enemy) and not isAttacked(E, 114, enemy) then
                            n = n + 1; moves[n] = 116 + 114 * 128 + FLAG_CASTLE * 131072
                        end
                    end
                end
            else
                local deltas = (t == BISHOP) and BISHOP_D or ((t == ROOK) and ROOK_D or KING_D)
                local stop = (t == QUEEN) and 8 or 4
                for i = 1, stop do
                    local d = deltas[i]
                    local to = s + d
                    while ON[to + 64] do
                        local q = B[to]
                        if q == 0 then
                            if not capsOnly then n = n + 1; moves[n] = s + to * 128 end
                        else
                            if q * side < 0 then n = n + 1; moves[n] = s + to * 128 + FLAG_CAPTURE * 131072 end
                            break
                        end
                        to = to + d
                    end
                end
            end
        end
    end
    return n
end

------------------------------------------------------------------------
-- Make / unmake (incremental hash, mg/eg, phase, non-pawn material)
------------------------------------------------------------------------
local function restore(E, S)
    local B = E.board
    local rf = S.rookFrom
    if rf then
        B[rf] = B[S.rookTo]
        B[S.rookTo] = 0
    end
    B[S.to] = 0
    B[S.capSq] = S.captured
    B[S.from] = S.piece
    E.castle = S.castle
    E.ep = S.ep
    E.half = S.half
    E.h1 = S.h1
    E.h2 = S.h2
    E.mg = S.mg
    E.eg = S.eg
    E.phase = S.phase
    E.npmW = S.npmW
    E.npmB = S.npmB
    E.kingW = S.kingW
    E.kingB = S.kingB
    E.side = S.side
end

local function makeMove(E, m, ply)
    local B = E.board
    local from = band(m, 127)
    local to = band(rshift(m, 7), 127)
    local promo = band(rshift(m, 14), 7)
    local flags = band(rshift(m, 17), 15)
    local piece = B[from]
    if piece == 0 then return false end
    local mover = E.side
    local capSq = to
    if band(flags, FLAG_EP) ~= 0 then capSq = to - mover * 16 end
    local captured = B[capSq]

    local S = E.stack[ply]
    if not S then S = {}; E.stack[ply] = S end
    S.from, S.to, S.piece, S.captured, S.capSq = from, to, piece, captured, capSq
    S.castle, S.ep, S.half, S.h1, S.h2 = E.castle, E.ep, E.half, E.h1, E.h2
    S.mg, S.eg, S.phase, S.npmW, S.npmB = E.mg, E.eg, E.phase, E.npmW, E.npmB
    S.kingW, S.kingB, S.side = E.kingW, E.kingB, E.side
    S.rookFrom, S.rookTo = nil, nil

    local h1, h2 = E.h1, E.h2
    local ep = E.ep
    if ep >= 0 then
        local fi = band(ep, 15) + 1
        h1 = bxor(h1, ZE1[fi]); h2 = bxor(h2, ZE2[fi])
    end
    local c = E.castle
    h1 = bxor(h1, ZC1[c + 1]); h2 = bxor(h2, ZC2[c + 1])

    local mg, eg = E.mg, E.eg
    local pi = piece + 7
    h1 = bxor(h1, ZP1[pi][from + 1]); h2 = bxor(h2, ZP2[pi][from + 1])
    mg = mg - MGT[pi][from]; eg = eg - EGT[pi][from]

    if captured ~= 0 then
        local ci = captured + 7
        h1 = bxor(h1, ZP1[ci][capSq + 1]); h2 = bxor(h2, ZP2[ci][capSq + 1])
        mg = mg - MGT[ci][capSq]; eg = eg - EGT[ci][capSq]
        local ac = (captured > 0) and captured or -captured
        E.phase = E.phase - PHASE_W[ac]
        if ac ~= PAWN then
            if captured > 0 then E.npmW = E.npmW - VAL[ac] else E.npmB = E.npmB - VAL[ac] end
        end
        B[capSq] = 0
    end
    B[from] = 0

    local placed = piece
    if promo ~= 0 then
        placed = mover * promo
        E.phase = E.phase + PHASE_W[promo]
        if mover == WHITE then E.npmW = E.npmW + VAL[promo] else E.npmB = E.npmB + VAL[promo] end
    end
    B[to] = placed
    local pli = placed + 7
    h1 = bxor(h1, ZP1[pli][to + 1]); h2 = bxor(h2, ZP2[pli][to + 1])
    mg = mg + MGT[pli][to]; eg = eg + EGT[pli][to]

    if piece == KING then E.kingW = to elseif piece == -KING then E.kingB = to end

    if band(flags, FLAG_CASTLE) ~= 0 then
        local rf, rt
        if to == 6 then rf, rt = 7, 5
        elseif to == 2 then rf, rt = 0, 3
        elseif to == 118 then rf, rt = 119, 117
        else rf, rt = 112, 115 end
        local rook = B[rf]
        B[rf] = 0
        B[rt] = rook
        S.rookFrom, S.rookTo = rf, rt
        local ri = rook + 7
        h1 = bxor(h1, ZP1[ri][rf + 1], ZP1[ri][rt + 1])
        h2 = bxor(h2, ZP2[ri][rf + 1], ZP2[ri][rt + 1])
        mg = mg - MGT[ri][rf] + MGT[ri][rt]
        eg = eg - EGT[ri][rf] + EGT[ri][rt]
    end

    c = band(c, CM[from], CM[to])
    E.castle = c
    h1 = bxor(h1, ZC1[c + 1]); h2 = bxor(h2, ZC2[c + 1])

    if band(flags, FLAG_DOUBLE) ~= 0 then
        ep = rshift(from + to, 1)
        local fi = band(ep, 15) + 1
        h1 = bxor(h1, ZE1[fi]); h2 = bxor(h2, ZE2[fi])
    else
        ep = -1
    end
    E.ep = ep
    h1 = bxor(h1, ZS1); h2 = bxor(h2, ZS2)

    if piece == PAWN or piece == -PAWN or captured ~= 0 then E.half = 0 else E.half = E.half + 1 end
    E.mg, E.eg = mg, eg
    E.h1, E.h2 = h1, h2
    E.side = -mover

    local ks = (mover == WHITE) and E.kingW or E.kingB
    if isAttacked(E, ks, -mover) then
        restore(E, S)
        return false
    end
    local n = E.repN + 1
    E.repN = n
    E.rep1[n], E.rep2[n] = h1, h2
    return true
end

local function unmakeMove(E, m, ply)
    restore(E, E.stack[ply])
    E.repN = E.repN - 1
end

------------------------------------------------------------------------
-- Static Exchange Evaluation
------------------------------------------------------------------------
local function leastAttacker(B, s, side)
    if side == WHITE then
        local a = s - 15
        if ON[a + 64] and B[a] == PAWN then return a end
        a = s - 17
        if ON[a + 64] and B[a] == PAWN then return a end
    else
        local a = s + 15
        if ON[a + 64] and B[a] == -PAWN then return a end
        a = s + 17
        if ON[a + 64] and B[a] == -PAWN then return a end
    end
    local kn = side * KNIGHT
    for i = 1, 8 do
        local t = s + KNIGHT_D[i]
        if ON[t + 64] and B[t] == kn then return t end
    end
    local bi = side * BISHOP
    for i = 1, 4 do
        local d = BISHOP_D[i]
        local t = s + d
        while ON[t + 64] do
            local p = B[t]
            if p ~= 0 then
                if p == bi then return t end
                break
            end
            t = t + d
        end
    end
    local ro = side * ROOK
    for i = 1, 4 do
        local d = ROOK_D[i]
        local t = s + d
        while ON[t + 64] do
            local p = B[t]
            if p ~= 0 then
                if p == ro then return t end
                break
            end
            t = t + d
        end
    end
    local qu = side * QUEEN
    for i = 1, 8 do
        local d = KING_D[i]
        local t = s + d
        while ON[t + 64] do
            local p = B[t]
            if p ~= 0 then
                if p == qu then return t end
                break
            end
            t = t + d
        end
    end
    local ki = side * KING
    for i = 1, 8 do
        local t = s + KING_D[i]
        if ON[t + 64] and B[t] == ki then return t end
    end
    return -1
end

local seeGain, seeSq, seeOld = {}, {}, {}
local function see(E, m)
    local B = E.board
    local from, to = band(m, 127), band(rshift(m, 7), 127)
    local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
    local piece = B[from]
    local side = (piece > 0) and WHITE or BLACK
    local target = B[to]
    local g0
    if band(flags, FLAG_EP) ~= 0 then g0 = VAL[PAWN]
    elseif target ~= 0 then g0 = VAL[abs(target)]
    else g0 = 0 end
    local attVal = VAL[abs(piece)]
    if promo ~= 0 then g0 = g0 + VAL[promo] - VAL[PAWN]; attVal = VAL[promo] end
    seeGain[1] = g0
    local oldFrom, oldTo = B[from], B[to]
    B[from] = 0
    B[to] = piece
    local d, n = 1, 0
    side = -side
    while true do
        local sq = leastAttacker(B, to, side)
        if sq < 0 then break end
        d = d + 1
        seeGain[d] = attVal - seeGain[d - 1]
        if mmax(-seeGain[d - 1], seeGain[d]) < 0 then
            d = d - 1
            break
        end
        local p = B[sq]
        attVal = VAL[abs(p)]
        n = n + 1
        seeSq[n], seeOld[n] = sq, p
        B[sq] = 0
        B[to] = p
        side = -side
    end
    for i = n, 1, -1 do B[seeSq[i]] = seeOld[i] end
    B[from] = oldFrom
    B[to] = oldTo
    while d > 1 do
        seeGain[d - 1] = -mmax(-seeGain[d - 1], seeGain[d])
        d = d - 1
    end
    return seeGain[1]
end

------------------------------------------------------------------------
-- Evaluation
------------------------------------------------------------------------
local PASS_MG = {0, 5, 10, 20, 35, 60, 100, 0}
local PASS_EG = {0, 10, 20, 40, 70, 120, 190, 0}
local THREAT = {0, 25, 25, 45, 60, 0}
local ATK_MULT = {0, 0, 50, 75, 88, 94, 97, 99, 100}
local TEMPO = 10
local LAZY = 320

local fileW, fileB, maxRB, minRW = {}, {}, {}, {}
local LW = {{}, {}, {}, {}, {}, {}}
local LB = {{}, {}, {}, {}, {}, {}}
local CW = {0, 0, 0, 0, 0, 0}
local CB = {0, 0, 0, 0, 0, 0}
local pAtkW, pAtkB, zoneW, zoneB = {}, {}, {}, {}
local evalStamp = 0

local function kdist(a, b)
    local dr = abs(rshift(a, 4) - rshift(b, 4))
    local df = abs(band(a, 15) - band(b, 15))
    return dr > df and dr or df
end

local function slideScan(B, s, D, nd, side, pAtkEn, zoneEn, stamp)
    local cnt, zc = 0, 0
    for k = 1, nd do
        local d = D[k]
        local t = s + d
        while ON[t + 64] do
            local q = B[t]
            if zoneEn[t] == stamp then zc = zc + 1 end
            if q == 0 then
                if pAtkEn[t] ~= stamp then cnt = cnt + 1 end
            else
                if q * side < 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                break
            end
            t = t + d
        end
    end
    return cnt, zc
end

local function evalSide(B, side, L, C, ownFile, enFile, enFar, pAtkEn, pAtkOwn, zoneEn, stamp, ownK, enK, st, npmEn, stmIsSide)
    local mg, eg, aw, an = 0, 0, 0, 0
    local mob, pw, safe = st.Mob, st.Pwn, st.Safe
    local pawn = side * PAWN
    local fwd = side * 16
    local pc0, pc1 = 0, 0

    -- pawns
    local PL = L[1]
    for i = 1, C[1] do
        local s = PL[i]
        local f, r = band(s, 15), rshift(s, 4)
        if band(f + r, 1) == 0 then pc0 = pc0 + 1 else pc1 = pc1 + 1 end
        local fi = f + 2
        local rr = (side == WHITE) and r or 7 - r
        if ownFile[fi - 1] == 0 and ownFile[fi + 1] == 0 then
            mg = mg - 10 * pw; eg = eg - 16 * pw
        end
        local passed
        if side == WHITE then
            passed = enFar[fi - 1] <= r and enFar[fi] <= r and enFar[fi + 1] <= r
        else
            passed = enFar[fi - 1] >= r and enFar[fi] >= r and enFar[fi + 1] >= r
        end
        local supported = (pAtkOwn[s] == stamp)
        if passed then
            local bm, be = PASS_MG[rr + 1], PASS_EG[rr + 1]
            local stop = s + fwd
            if B[stop] ~= 0 then bm = bm * 0.5; be = be * 0.5 end
            if supported then bm = bm + rr * 2; be = be + rr * 4 end
            if rr >= 2 then
                be = be + (kdist(enK, stop) * 4 - kdist(ownK, stop) * 2) * rr * 0.5
            end
            if npmEn == 0 and rr >= 1 then
                local clear = true
                local t = s + fwd
                while ON[t + 64] do
                    if B[t] ~= 0 then clear = false; break end
                    t = t + fwd
                end
                if clear then
                    local pd = 7 - rr
                    if rr == 1 then pd = pd - 1 end
                    local promoSq = ((side == WHITE) and 112 or 0) + f
                    local tempo = stmIsSide and 0 or 1
                    if pd + tempo < kdist(enK, promoSq) then be = be + 350 end
                end
            end
            mg = mg + bm * pw; eg = eg + be * pw
        end
        if supported then
            mg = mg + (3 + rr * 2) * pw; eg = eg + (4 + rr * 3) * pw
        elseif B[s - 1] == pawn or B[s + 1] == pawn then
            mg = mg + (2 + rr) * pw; eg = eg + (3 + rr * 2) * pw
        end
        for k = -1, 1, 2 do
            local t = s + fwd + k
            if ON[t + 64] then
                local q = B[t]
                if q * side < 0 then
                    local a = (q > 0) and q or -q
                    if a > 1 and a < 6 then mg = mg + THREAT[a]; eg = eg + THREAT[a] end
                end
            end
        end
    end
    for fi = 2, 9 do
        local c = ownFile[fi]
        if c > 1 then
            mg = mg - (c - 1) * 10 * pw
            eg = eg - (c - 1) * 22 * pw
        end
    end

    -- knights
    local KL = L[2]
    for i = 1, C[2] do
        local s = KL[i]
        local f, r = band(s, 15), rshift(s, 4)
        local cnt, zc = 0, 0
        for k = 1, 8 do
            local t = s + KNIGHT_D[k]
            if ON[t + 64] then
                if B[t] * side <= 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                if zoneEn[t] == stamp then zc = zc + 1 end
            end
        end
        mg = mg + (cnt - 4) * 4 * mob
        eg = eg + (cnt - 4) * 4 * mob
        if zc > 0 then aw = aw + 20 + zc * 2; an = an + 1 end
        local rr = (side == WHITE) and r or 7 - r
        if rr >= 3 and rr <= 5 and f >= 2 and f <= 5 and pAtkOwn[s] == stamp then
            local fi = f + 2
            local out
            if side == WHITE then out = enFar[fi - 1] <= r and enFar[fi + 1] <= r
            else out = enFar[fi - 1] >= r and enFar[fi + 1] >= r end
            if out then mg = mg + 24; eg = eg + 14 end
        end
    end

    -- bishops
    local BL = L[3]
    for i = 1, C[3] do
        local s = BL[i]
        local f, r = band(s, 15), rshift(s, 4)
        local cnt, zc = slideScan(B, s, BISHOP_D, 4, side, pAtkEn, zoneEn, stamp)
        mg = mg + (cnt - 5) * 4 * mob
        eg = eg + (cnt - 5) * 5 * mob
        if zc > 0 then aw = aw + 20 + zc * 2; an = an + 1 end
        local same = (band(f + r, 1) == 0) and pc0 or pc1
        if same > 3 then mg = mg - (same - 3) * 3; eg = eg - (same - 3) * 5 end
        local rr = (side == WHITE) and r or 7 - r
        if rr >= 3 and rr <= 5 and f >= 2 and f <= 5 and pAtkOwn[s] == stamp then
            local fi = f + 2
            local out
            if side == WHITE then out = enFar[fi - 1] <= r and enFar[fi + 1] <= r
            else out = enFar[fi - 1] >= r and enFar[fi + 1] >= r end
            if out then mg = mg + 12; eg = eg + 8 end
        end
    end
    if C[3] >= 2 then mg = mg + 30; eg = eg + 50 end

    -- rooks
    local RL = L[4]
    for i = 1, C[4] do
        local s = RL[i]
        local f, r = band(s, 15), rshift(s, 4)
        local cnt, zc = slideScan(B, s, ROOK_D, 4, side, pAtkEn, zoneEn, stamp)
        mg = mg + (cnt - 5) * 2 * mob
        eg = eg + (cnt - 5) * 4 * mob
        if zc > 0 then aw = aw + 40 + zc * 2; an = an + 1 end
        local fi = f + 2
        if ownFile[fi] == 0 then
            if enFile[fi] == 0 then mg = mg + 22; eg = eg + 12 else mg = mg + 10; eg = eg + 8 end
        end
        local rr = (side == WHITE) and r or 7 - r
        if rr == 6 then mg = mg + 10; eg = eg + 20 end
    end

    -- queens
    local QL = L[5]
    for i = 1, C[5] do
        local s = QL[i]
        local cnt, zc = slideScan(B, s, KING_D, 8, side, pAtkEn, zoneEn, stamp)
        mg = mg + (cnt - 10) * mob
        eg = eg + (cnt - 10) * 2 * mob
        if zc > 0 then aw = aw + 80 + zc * 2; an = an + 1 end
    end

    -- king pawn shield
    local kr = rshift(ownK, 4)
    local krr = (side == WHITE) and kr or 7 - kr
    if krr <= 2 then
        local kf = band(ownK, 15)
        local sh = 0
        for df = -1, 1 do
            local f = kf + df
            if f >= 0 and f <= 7 then
                local sq1 = ownK + fwd + df
                if B[sq1] == pawn then
                    sh = sh + 12
                elseif B[sq1 + fwd] == pawn then
                    sh = sh + 6
                else
                    sh = sh - 14
                    if ownFile[f + 2] == 0 then sh = sh - 12 end
                end
            end
        end
        mg = mg + sh * safe
    end
    return mg, eg, aw, an
end

local function dangerOf(aw, an, attackerQueens, att)
    if an < 2 then return 0 end
    local d = aw * ATK_MULT[mmin(an, 8) + 1] / 100
    if attackerQueens == 0 then d = d * 0.5 end
    return d * att
end

local function evaluate(E)
    local B = E.board
    evalStamp = evalStamp + 1
    local stamp = evalStamp
    for i = 1, 10 do
        fileW[i], fileB[i] = 0, 0
        maxRB[i], minRW[i] = -1, 8
    end
    for t = 1, 6 do CW[t] = 0; CB[t] = 0 end

    for idx = 1, 64 do
        local s = SQ64[idx]
        local p = B[s]
        if p > 0 then
            local n = CW[p] + 1
            CW[p] = n
            LW[p][n] = s
            if p == PAWN then
                local f, r = band(s, 15), rshift(s, 4)
                local fi = f + 2
                fileW[fi] = fileW[fi] + 1
                if r < minRW[fi] then minRW[fi] = r end
                pAtkW[s + 15] = stamp; pAtkW[s + 17] = stamp
            end
        elseif p < 0 then
            local t = -p
            local n = CB[t] + 1
            CB[t] = n
            LB[t][n] = s
            if t == PAWN then
                local f, r = band(s, 15), rshift(s, 4)
                local fi = f + 2
                fileB[fi] = fileB[fi] + 1
                if r > maxRB[fi] then maxRB[fi] = r end
                pAtkB[s - 15] = stamp; pAtkB[s - 17] = stamp
            end
        end
    end

    local npmW, npmB = E.npmW, E.npmB
    if CW[1] + CB[1] == 0 then
        if npmW <= 340 and npmB <= 340 then return 0 end
        if (npmW == 640 and npmB == 0 and CW[2] == 2) or (npmB == 640 and npmW == 0 and CB[2] == 2) then return 0 end
    end

    local wk, bk = E.kingW, E.kingB
    zoneW[wk] = stamp
    zoneB[bk] = stamp
    for i = 1, 8 do
        zoneW[wk + KING_D[i]] = stamp
        zoneB[bk + KING_D[i]] = stamp
    end
    for d = -1, 1 do
        zoneW[wk + 32 + d] = stamp
        zoneB[bk - 32 + d] = stamp
    end

    local st = E.style
    local stm = E.side
    local wmg, weg, waw, wan = evalSide(B, WHITE, LW, CW, fileW, fileB, maxRB, pAtkB, pAtkW, zoneB, stamp, wk, bk, st, npmB, stm == WHITE)
    local bmg, beg, baw, ban = evalSide(B, BLACK, LB, CB, fileB, fileW, minRW, pAtkW, pAtkB, zoneW, stamp, bk, wk, st, npmW, stm == BLACK)

    local mg = E.mg + wmg - bmg
    local eg = E.eg + weg - beg
    local att = st.Att
    local dW = dangerOf(baw, ban, CB[5], att) -- black attacking white king
    local dB = dangerOf(waw, wan, CW[5], att) -- white attacking black king
    mg = mg - dW + dB
    eg = eg - dW * 0.25 + dB * 0.25

    local ph = E.phase
    if ph > 24 then ph = 24 end
    local score = floor((mg * ph + eg * (24 - ph)) / 24)
    score = score + stm * TEMPO

    -- opposite-coloured bishops
    if CW[3] == 1 and CB[3] == 1 and CW[2] + CB[2] + CW[4] + CB[4] + CW[5] + CB[5] == 0 then
        local ws, bs = LW[3][1], LB[3][1]
        if band(band(ws, 15) + rshift(ws, 4), 1) ~= band(band(bs, 15) + rshift(bs, 4), 1) then
            score = floor(score * 0.62)
        end
    end

    if npmW - npmB >= 450 and npmB == 0 and CB[1] == 0 then
        local f, r = band(bk, 15), rshift(bk, 4)
        local cd = mmax(3 - f, f - 4) + mmax(3 - r, r - 4)
        score = score + cd * 10 + (14 - kdist(wk, bk)) * 4
    elseif npmB - npmW >= 450 and npmW == 0 and CW[1] == 0 then
        local f, r = band(wk, 15), rshift(wk, 4)
        local cd = mmax(3 - f, f - 4) + mmax(3 - r, r - 4)
        score = score - (cd * 10 + (14 - kdist(wk, bk)) * 4)
    elseif score > 0 and CW[1] == 0 and npmW - npmB <= 350 then
        score = floor(score / 3)
    elseif score < 0 and CB[1] == 0 and npmB - npmW <= 350 then
        score = -floor(-score / 3)
    end
    return stm * score
end

local function staticEval(E, alpha, beta)
    local ph = E.phase
    if ph > 24 then ph = 24 end
    local quick = E.side * floor((E.mg * ph + E.eg * (24 - ph)) / 24)
    if quick + LAZY <= alpha or quick - LAZY >= beta then return quick end
    return evaluate(E)
end

------------------------------------------------------------------------
-- Transposition table: 2-way buckets, aging
------------------------------------------------------------------------
local function newTT(bits)
    local size = bit.lshift(1, bits)
    return {
        k1 = tcreate(size, -1), k2 = tcreate(size, -1),
        mv = tcreate(size, 0), dp = tcreate(size, 0),
        bd = tcreate(size, 0), sc = tcreate(size, 0),
        gn = tcreate(size, -1),
        mask = size - 1, bits = bits,
    }
end
G.SearchId = G.SearchId or 0
G.TT = (G.TT and G.TT.k1) and G.TT or newTT(G.HashBits or 18)

local function ttProbe(tt, h1, h2)
    local base = band(h1, tt.mask)
    local i = base + 1
    if tt.k1[i] == h1 and tt.k2[i] == h2 then return i end
    local j = bxor(base, 1) + 1
    if tt.k1[j] == h1 and tt.k2[j] == h2 then return j end
    return 0
end

local function ttStore(E, depth, score, bound, move, ply)
    local tt = E.tt
    local h1, h2 = E.h1, E.h2
    local gen = G.SearchId
    local idx = ttProbe(tt, h1, h2)
    local replace
    if idx ~= 0 then
        replace = depth >= tt.dp[idx] - 3 or bound == 0 or tt.gn[idx] ~= gen
    else
        local base = band(h1, tt.mask)
        local i = base + 1
        local j = bxor(base, 1) + 1
        local pi = tt.dp[i] + ((tt.gn[i] == gen) and 64 or 0)
        local pj = tt.dp[j] + ((tt.gn[j] == gen) and 64 or 0)
        idx = (pi <= pj) and i or j
        replace = true
        tt.k1[idx] = -1; tt.k2[idx] = -1; tt.mv[idx] = 0
    end
    if replace then
        if score > MATE - 1000 then score = score + ply
        elseif score < -MATE + 1000 then score = score - ply end
        local old = tt.mv[idx]
        if move == 0 and tt.k1[idx] == h1 and tt.k2[idx] == h2 then move = old end
        tt.k1[idx], tt.k2[idx] = h1, h2
        tt.mv[idx], tt.dp[idx], tt.bd[idx], tt.sc[idx], tt.gn[idx] = move, depth, bound, score, gen
    elseif move ~= 0 and tt.mv[idx] == 0 then
        tt.mv[idx] = move
    end
end

------------------------------------------------------------------------
-- Search helpers
------------------------------------------------------------------------
local LMRT = {}
for d = 1, 64 do
    LMRT[d] = {}
    for i = 1, 64 do
        LMRT[d][i] = floor(0.6 + mlog(d) * mlog(i) / 2.1)
    end
end

local function touch(E)
    if E.abort then return false end
    local n = E.nodes + 1
    E.nodes = n
    if n >= E.nodeLimit then E.abort = true; return false end
    if band(n, 255) == 0 then
        local now = clock()
        if now >= E.deadline then E.abort = true; return false end
        if E.cancel and E.cancel() then E.abort = true; return false end
        if now - E.lastYield >= E.slice then
            yield()
            E.lastYield = clock()
        end
    end
    return true
end

local function drawScore(E, ply)
    local c = E.style.Contempt
    if ply % 2 == 0 then return -c end
    return c
end

local function isRepetition(E)
    local n = E.repN
    local lim = E.half
    if lim > n - 1 then lim = n - 1 end
    local stop = n - lim
    local h1, h2 = E.h1, E.h2
    local r1, r2 = E.rep1, E.rep2
    local i = n - 2
    while i >= stop and i >= 1 do
        if r1[i] == h1 and r2[i] == h2 then return true end
        i = i - 2
    end
    return false
end

local function addHist(tbl, k, b)
    local h = tbl[k] or 0
    tbl[k] = h + b - floor(h * abs(b) / 16384)
end

local function pick(moves, scores, i, n)
    local best, bs = i, scores[i]
    for j = i + 1, n do
        if scores[j] > bs then best = j; bs = scores[j] end
    end
    if best ~= i then
        moves[i], moves[best] = moves[best], moves[i]
        scores[i], scores[best] = scores[best], scores[i]
    end
end

local function moveScore(E, m, ply, ttMove)
    if m == ttMove and m ~= 0 then return 9000000 end
    local B = E.board
    local from, to = band(m, 127), band(rshift(m, 7), 127)
    local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
    local piece = B[from]
    local pt = (piece > 0) and piece or -piece
    if band(flags, FLAG_CAPTURE) ~= 0 then
        local victim = (band(flags, FLAG_EP) ~= 0) and PAWN or abs(B[to])
        local vv, av = VAL[victim], VAL[pt]
        local mvv = vv * 10 - pt
        local score
        if vv >= av then
            score = 2000000 + mvv
        else
            local s = see(E, m)
            if s >= 0 then score = 2000000 + mvv else score = -1000000 + s end
        end
        if promo == QUEEN then score = score + 800 end
        return score
    end
    if promo ~= 0 then
        return (promo == QUEEN) and 1950000 or -900000
    end
    local k = E.killers[ply]
    if k then
        if m == k[1] then return 900000 end
        if m == k[2] then return 800000 end
    end
    local score = E.history[((piece > 0) and 0 or 16384) + from * 128 + to] or 0
    if ply > 0 then
        local prev = E.stack[ply - 1]
        if prev and prev.piece ~= 0 then
            local pkey = (prev.piece + 7) * 128 + prev.to
            if E.counter[pkey] == m then return 700000 end
            score = score + (E.chist[pkey * 2048 + (piece + 7) * 128 + to] or 0)
        end
    end
    local fl = band(to, 15)
    if fl == 3 or fl == 4 then score = score + E.style.Center end
    return score
end

local function getBuf(E, bi)
    local mv = E.mvs[bi]
    if not mv then
        mv = {}; E.mvs[bi] = mv
        E.scs[bi] = {}
        E.qts[bi] = {}
    end
    return mv, E.scs[bi], E.qts[bi]
end

local function qsearch(E, alpha, beta, ply, qd)
    if not touch(E) then return 0 end
    E.qnodes = E.qnodes + 1
    if ply >= MAX_PLY - 1 then return evaluate(E) end
    if E.half >= 100 then return 0 end
    local isPV = beta - alpha > 1
    local alpha0 = alpha

    local tt = E.tt
    local ttMove = 0
    local hi = ttProbe(tt, E.h1, E.h2)
    if hi ~= 0 then
        ttMove = tt.mv[hi]
        local ttScore, ttBound = tt.sc[hi], tt.bd[hi]
        if ttScore > MATE - 1000 then ttScore = ttScore - ply
        elseif ttScore < -MATE + 1000 then ttScore = ttScore + ply end
        if not isPV and (ttBound == 0 or (ttBound == 2 and ttScore >= beta) or (ttBound == 1 and ttScore <= alpha)) then
            return ttScore
        end
    end

    local checked = inCheck(E, E.side)
    local stand, best
    if checked then
        if qd > E.maxQDepth + 6 then return evaluate(E) end
        best = -INF
    else
        stand = staticEval(E, alpha, beta)
        if stand >= beta then return stand end
        if stand > alpha then alpha = stand end
        if qd >= E.maxQDepth then return stand end
        best = stand
    end

    local moves, scores = getBuf(E, ply)
    local n = generate(E, moves, not checked)
    local B = E.board
    for i = 1, n do
        local m = moves[i]
        local flags = band(rshift(m, 17), 15)
        local sc = 0
        if m == ttMove and m ~= 0 then
            sc = 3000000
        elseif band(flags, FLAG_CAPTURE) ~= 0 then
            local victim = (band(flags, FLAG_EP) ~= 0) and PAWN or abs(B[band(rshift(m, 7), 127)])
            local pt = abs(B[band(m, 127)])
            sc = 1000000 + VAL[victim] * 10 - pt
        elseif band(rshift(m, 14), 7) ~= 0 then
            sc = 900000
        end
        scores[i] = sc
    end

    local legal, bestMove = 0, 0
    for i = 1, n do
        pick(moves, scores, i, n)
        local m = moves[i]
        local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
        local skip = false
        if not checked and band(flags, FLAG_CAPTURE) ~= 0 then
            local victim = (band(flags, FLAG_EP) ~= 0) and PAWN or abs(B[band(rshift(m, 7), 127)])
            if promo == 0 and stand + VAL[victim] + 200 < alpha then
                skip = true
            elseif VAL[victim] < VAL[abs(B[band(m, 127)])] and see(E, m) < 0 then
                skip = true
            end
        end
        if not skip and makeMove(E, m, ply) then
            legal = legal + 1
            local score = -qsearch(E, -beta, -alpha, ply + 1, qd + 1)
            unmakeMove(E, m, ply)
            if E.abort then return 0 end
            if score > best then
                best = score
                bestMove = m
                if score > alpha then
                    alpha = score
                    if score >= beta then
                        ttStore(E, 0, score, 2, m, ply)
                        return score
                    end
                end
            end
        end
    end
    if checked and legal == 0 then return -MATE + ply end
    ttStore(E, 0, best, (best > alpha0) and 0 or 1, bestMove, ply)
    return best
end

local function negamax(E, depth, alpha, beta, ply, allowNull, excluded)
    if not touch(E) then return 0 end
    local isPV = beta - alpha > 1

    if ply > 0 then
        if E.half >= 100 then return drawScore(E, ply) end
        if isRepetition(E) then return drawScore(E, ply) end
        local a2 = mmax(alpha, -MATE + ply)
        local b2 = mmin(beta, MATE - ply - 1)
        if a2 >= b2 then return a2 end
        alpha, beta = a2, b2
    end
    if ply >= MAX_PLY - 1 then return evaluate(E) end

    local checked = inCheck(E, E.side)
    if depth <= 0 then return qsearch(E, alpha, beta, ply, 0) end
    if checked then depth = depth + 1 end

    local alpha0 = alpha
    local bi = ply + ((excluded ~= 0) and 128 or 0)

    -- TT probe
    local tt = E.tt
    local ttMove, ttScore, ttDepth, ttBound = 0, 0, -1, 0
    local hi = ttProbe(tt, E.h1, E.h2)
    if hi ~= 0 then
        ttMove, ttDepth, ttBound, ttScore = tt.mv[hi], tt.dp[hi], tt.bd[hi], tt.sc[hi]
        if ttScore > MATE - 1000 then ttScore = ttScore - ply
        elseif ttScore < -MATE + 1000 then ttScore = ttScore + ply end
        if excluded == 0 and not isPV and ttDepth >= depth then
            if ttBound == 0 or (ttBound == 2 and ttScore >= beta) or (ttBound == 1 and ttScore <= alpha) then
                return ttScore
            end
        end
    end

    local static = -INF
    if not checked then
        static = staticEval(E, alpha, beta)
        if hi ~= 0 and ttDepth >= 0 and abs(ttScore) < MATE - 1000 then
            if ttBound == 0 or (ttBound == 2 and ttScore > static) or (ttBound == 1 and ttScore < static) then
                static = ttScore
            end
        end
    end
    E.evalStack[ply] = static
    local improving = false
    if not checked and ply >= 2 then
        local e2 = E.evalStack[ply - 2]
        improving = e2 ~= nil and e2 > -INF and static > e2
    end

    local side = E.side
    if not isPV and not checked and abs(beta) < MATE - 1000 then
        -- reverse futility
        if depth <= 7 and static - 80 * depth + (improving and 0 or 30) >= beta then
            return static
        end
        -- razoring
        if depth <= 2 and static + 250 * depth <= alpha then
            local q = qsearch(E, alpha, beta, ply, 0)
            if E.abort then return 0 end
            if q <= alpha then return q end
        end
        -- null move
        local npm = (side == WHITE) and E.npmW or E.npmB
        if allowNull and depth >= 3 and static >= beta and npm > 0
            and not (hi ~= 0 and ttBound == 1 and ttScore < beta) then
            local R = 3 + floor(depth / 4) + mmin(2, floor((static - beta) / 200))
            local oldEp, oh1, oh2, ohalf = E.ep, E.h1, E.h2, E.half
            local sN = E.stack[ply]
            if not sN then sN = {}; E.stack[ply] = sN end
            sN.piece, sN.to = 0, 0
            if oldEp >= 0 then
                local fi = band(oldEp, 15) + 1
                E.h1 = bxor(E.h1, ZE1[fi]); E.h2 = bxor(E.h2, ZE2[fi])
            end
            E.ep = -1
            E.h1 = bxor(E.h1, ZS1); E.h2 = bxor(E.h2, ZS2)
            E.side = -side
            E.half = 0
            local nr = E.repN + 1
            E.repN = nr
            E.rep1[nr], E.rep2[nr] = E.h1, E.h2
            local score = -negamax(E, depth - 1 - R, -beta, -beta + 1, ply + 1, false, 0)
            E.repN = nr - 1
            E.side = side
            E.ep = oldEp
            E.h1, E.h2, E.half = oh1, oh2, ohalf
            if E.abort then return 0 end
            if score >= beta then
                if score > MATE - 1000 then score = beta end
                if depth < 9 then return score end
                local v = negamax(E, depth - R, beta - 1, beta, ply, false, 0)
                if E.abort then return 0 end
                if v >= beta then return score end
            end
        end
    end

    -- internal iterative deepening
    if isPV and ttMove == 0 and depth >= 5 and excluded == 0 then
        negamax(E, depth - 2, alpha, beta, ply, false, 0)
        if E.abort then return 0 end
        hi = ttProbe(tt, E.h1, E.h2)
        if hi ~= 0 then
            ttMove, ttDepth, ttBound, ttScore = tt.mv[hi], tt.dp[hi], tt.bd[hi], tt.sc[hi]
            if ttScore > MATE - 1000 then ttScore = ttScore - ply
            elseif ttScore < -MATE + 1000 then ttScore = ttScore + ply end
        end
    end

    local moves, scores, quiets = getBuf(E, bi)
    local n = generate(E, moves, false)
    for i = 1, n do scores[i] = moveScore(E, moves[i], ply, ttMove) end

    local best, bestMove, legal = -INF, 0, 0
    local nq = 0
    local B = E.board
    local style = E.style
    local hist = E.history

    for i = 1, n do
        pick(moves, scores, i, n)
        local m, sc = moves[i], scores[i]
        if m ~= excluded then
            local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
            local isCap = band(flags, FLAG_CAPTURE) ~= 0
            local quiet = (not isCap) and promo == 0

            local prune = false
            if not isPV and not checked and best > -MATE + 1000 then
                if quiet then
                    if depth <= 8 and nq >= (3 + depth * depth) / (improving and 1 or 2) then
                        prune = true
                    elseif depth <= 5 and sc < 700000 and see(E, m) < -35 * depth * depth then
                        prune = true
                    end
                elseif isCap and sc < -500000 and depth <= 5 and (sc + 1000000) < -90 * depth then
                    prune = true
                end
            end

            if not prune then
                -- singular extension (done before the move is made)
                local ext = 0
                if m == ttMove and excluded == 0 and ply > 0 and depth >= 7 and ttDepth >= depth - 3
                    and (ttBound == 0 or ttBound == 2) and abs(ttScore) < MATE - 1000 then
                    local sBeta = ttScore - 2 * depth
                    local v = negamax(E, floor((depth - 1) / 2), sBeta - 1, sBeta, ply, false, m)
                    if E.abort then return 0 end
                    if v < sBeta then
                        ext = 1
                    elseif sBeta >= beta then
                        return sBeta
                    elseif ttScore >= beta then
                        ext = -1
                    end
                end

                if makeMove(E, m, ply) then
                    legal = legal + 1
                    local skip = false
                    if quiet and not isPV and not checked and depth <= 6 and legal > 1 and best > -MATE + 1000
                        and static + 100 + 120 * depth <= alpha then
                        if not inCheck(E, E.side) then skip = true end
                    end
                    if skip then
                        unmakeMove(E, m, ply)
                    else
                        local newDepth = depth - 1 + ext
                        local score
                        if legal == 1 then
                            score = -negamax(E, newDepth, -beta, -alpha, ply + 1, true, 0)
                        else
                            local r = 0
                            if depth >= 3 and not checked then
                                if quiet then
                                    r = LMRT[mmin(depth, 64)][mmin(legal, 64)]
                                    r = floor(r * style.LMR + 0.5)
                                    if isPV then r = r - 1 end
                                    if not improving then r = r + 1 end
                                    if sc >= 700000 then
                                        r = r - 1
                                    else
                                        local adj = floor(sc / 6000)
                                        if adj > 2 then adj = 2 elseif adj < -2 then adj = -2 end
                                        r = r - adj
                                    end
                                elseif isCap and sc < -500000 then
                                    r = 1
                                end
                                if r > 0 and inCheck(E, E.side) then r = r - 1 end
                                if r < 0 then r = 0 end
                                if r > newDepth - 1 then r = mmax(0, newDepth - 1) end
                            end
                            score = -negamax(E, newDepth - r, -alpha - 1, -alpha, ply + 1, true, 0)
                            if score > alpha and r > 0 then
                                score = -negamax(E, newDepth, -alpha - 1, -alpha, ply + 1, true, 0)
                            end
                            if score > alpha and score < beta then
                                score = -negamax(E, newDepth, -beta, -alpha, ply + 1, true, 0)
                            end
                        end
                        unmakeMove(E, m, ply)
                        if E.abort then return 0 end

                        if score > best then
                            best = score
                            bestMove = m
                            if score > alpha then
                                alpha = score
                                if alpha >= beta then
                                    if quiet then
                                        local k = E.killers[ply]
                                        if not k then k = {0, 0}; E.killers[ply] = k end
                                        if k[1] ~= m then k[2] = k[1]; k[1] = m end
                                        local bonus = mmin(2000, depth * depth * 32)
                                        local sidx = (side == WHITE) and 0 or 16384
                                        local prev = (ply > 0) and E.stack[ply - 1] or nil
                                        local pkey = (prev and prev.piece ~= 0) and ((prev.piece + 7) * 128 + prev.to) or nil
                                        addHist(hist, sidx + band(m, 127) * 128 + band(rshift(m, 7), 127), bonus)
                                        if pkey then
                                            E.counter[pkey] = m
                                            addHist(E.chist, pkey * 2048 + (B[band(m, 127)] + 7) * 128 + band(rshift(m, 7), 127), bonus)
                                        end
                                        for q = 1, nq do
                                            local qm = quiets[q]
                                            local qf, qt = band(qm, 127), band(rshift(qm, 7), 127)
                                            addHist(hist, sidx + qf * 128 + qt, -bonus)
                                            if pkey then
                                                addHist(E.chist, pkey * 2048 + (B[qf] + 7) * 128 + qt, -bonus)
                                            end
                                        end
                                    end
                                    break
                                end
                            end
                        end
                        if quiet then nq = nq + 1; quiets[nq] = m end
                    end
                end
            end
        end
    end

    if legal == 0 then
        if excluded ~= 0 then return alpha end
        if checked then return -MATE + ply end
        return 0
    end

    if excluded == 0 then
        local bound = (best >= beta) and 2 or ((best > alpha0) and 0 or 1)
        ttStore(E, depth, best, bound, bestMove, ply)
    end
    return best
end

local function rootSearch(E, depth, alpha, beta)
    local list = E.root
    local best, bestMove = -INF, 0
    local checkedRoot = inCheck(E, E.side)
    for i = 1, #list do
        local ent = list[i]
        local m = ent.m
        if makeMove(E, m, 0) then
            local newDepth = depth - 1
            local score
            if i == 1 then
                score = -negamax(E, newDepth, -beta, -alpha, 1, true, 0)
            else
                local r = 0
                if depth >= 3 and i >= 3 and not checkedRoot
                    and band(rshift(m, 17), FLAG_CAPTURE) == 0 and band(rshift(m, 14), 7) == 0 then
                    r = LMRT[mmin(depth, 64)][mmin(i, 64)] - 1
                    if r < 0 then r = 0 end
                    if r > newDepth - 1 then r = mmax(0, newDepth - 1) end
                    if r > 0 and inCheck(E, E.side) then r = 0 end
                end
                score = -negamax(E, newDepth - r, -alpha - 1, -alpha, 1, true, 0)
                if score > alpha and r > 0 then
                    score = -negamax(E, newDepth, -alpha - 1, -alpha, 1, true, 0)
                end
                if score > alpha and score < beta then
                    score = -negamax(E, newDepth, -beta, -alpha, 1, true, 0)
                end
            end
            unmakeMove(E, m, 0)
            if E.abort then return bestMove, best, false end
            ent.score = score
            if score > best then best = score; bestMove = m end
            if score > alpha then alpha = score end
            if alpha >= beta then break end
        end
    end
    return bestMove, best, true
end

------------------------------------------------------------------------
-- FEN
------------------------------------------------------------------------
local FENP = {P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6, p = -1, n = -2, b = -3, r = -4, q = -5, k = -6}
local PCH = {"P", "N", "B", "R", "Q", "K"}

local function parseFEN(fen)
    local fields = {}
    for part in string.gmatch(fen, "%S+") do fields[#fields + 1] = part end
    local placement = fields[1] or "8/8/8/8/8/8/8/8"
    local side = (fields[2] == "b") and BLACK or WHITE
    local castleText = fields[3] or "-"
    local epText = fields[4] or "-"
    local half = tonumber(fields[5] or "0") or 0

    local B = {}
    for i = 0, 127 do B[i] = 0 end
    local kingW, kingB = -1, -1
    local mg, eg, phase, npmW, npmB = 0, 0, 0, 0, 0
    local rank = 7
    for row in string.gmatch(placement, "[^/]+") do
        local file = 0
        for ch in string.gmatch(row, ".") do
            local num = tonumber(ch)
            if num then
                file = file + num
            else
                local piece = FENP[ch]
                if piece and file < 8 and rank >= 0 then
                    local s = rank * 16 + file
                    B[s] = piece
                    mg = mg + MGT[piece + 7][s]
                    eg = eg + EGT[piece + 7][s]
                    local pt = (piece > 0) and piece or -piece
                    phase = phase + PHASE_W[pt]
                    if pt ~= PAWN and pt ~= KING then
                        if piece > 0 then npmW = npmW + VAL[pt] else npmB = npmB + VAL[pt] end
                    end
                    if piece == KING then kingW = s end
                    if piece == -KING then kingB = s end
                    file = file + 1
                end
            end
        end
        rank = rank - 1
    end

    local castle = 0
    if string.find(castleText, "K", 1, true) then castle = castle + 1 end
    if string.find(castleText, "Q", 1, true) then castle = castle + 2 end
    if string.find(castleText, "k", 1, true) then castle = castle + 4 end
    if string.find(castleText, "q", 1, true) then castle = castle + 8 end
    local ep = -1
    if epText ~= "-" and #epText >= 2 then
        local f = string.byte(epText, 1) - 97
        local r = tonumber(epText:sub(2, 2))
        if f >= 0 and f < 8 and r and r >= 1 and r <= 8 then ep = (r - 1) * 16 + f end
    end

    local E = {
        board = B, side = side, castle = castle, ep = ep, half = half,
        mg = mg, eg = eg, phase = phase, npmW = npmW, npmB = npmB,
        kingW = kingW, kingB = kingB, h1 = 0, h2 = 0,
        stack = {}, tt = G.TT, killers = {}, history = {}, counter = {}, chist = {}, evalStack = {},
        mvs = {}, scs = {}, qts = {},
        nodes = 0, qnodes = 0, abort = false, maxQDepth = 8, deadline = math.huge,
        nodeLimit = 50000000, lastYield = clock(), slice = 0.03, cancel = nil,
        style = STYLE.Balanced, root = {},
    }
    local h1, h2 = 0, 0
    for i = 0, 127 do
        local p = B[i]
        if p ~= 0 then
            h1 = bxor(h1, ZP1[p + 7][i + 1]); h2 = bxor(h2, ZP2[p + 7][i + 1])
        end
    end
    h1 = bxor(h1, ZC1[castle + 1]); h2 = bxor(h2, ZC2[castle + 1])
    if ep >= 0 then
        local fi = band(ep, 15) + 1
        h1 = bxor(h1, ZE1[fi]); h2 = bxor(h2, ZE2[fi])
    end
    if side == BLACK then h1 = bxor(h1, ZS1); h2 = bxor(h2, ZS2) end
    E.h1, E.h2 = h1, h2
    E.rep1, E.rep2, E.repN = {h1}, {h2}, 1
    return E
end

local function toFEN(E, fullmove)
    local rows = {}
    for r = 7, 0, -1 do
        local row, empty = "", 0
        for f = 0, 7 do
            local p = E.board[r * 16 + f]
            if p == 0 then
                empty = empty + 1
            else
                if empty > 0 then row = row .. tostring(empty); empty = 0 end
                local ch = PCH[abs(p)]
                if p < 0 then ch = ch:lower() end
                row = row .. ch
            end
        end
        if empty > 0 then row = row .. tostring(empty) end
        rows[#rows + 1] = row
    end
    local c = ""
    if band(E.castle, 1) ~= 0 then c = c .. "K" end
    if band(E.castle, 2) ~= 0 then c = c .. "Q" end
    if band(E.castle, 4) ~= 0 then c = c .. "k" end
    if band(E.castle, 8) ~= 0 then c = c .. "q" end
    if c == "" then c = "-" end
    local ep = (E.ep >= 0) and squareName(E.ep) or "-"
    return table.concat(rows, "/") .. " " .. ((E.side == WHITE) and "w" or "b") .. " " .. c .. " " .. ep
        .. " " .. tostring(E.half) .. " " .. tostring(fullmove or 1)
end

------------------------------------------------------------------------
-- Opening book
------------------------------------------------------------------------
local BOOK_LINES = {
    "e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6 c2c3 e8g8 h2h3",
    "e2e4 e7e5 g1f3 b8c6 f1b5 g8f6 e1g1 f6e4 d2d4 e4d6 b5c6 d7c6 d4e5 d6f5 d1d8 e8d8",
    "e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 c2c3 g8f6 d2d3 d7d6 e1g1 e8g8",
    "e2e4 e7e5 g1f3 b8c6 f1c4 g8f6 d2d3 f8c5 c2c3 d7d6 e1g1 e8g8",
    "e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 g8f6 b1c3 f8b4 d4c6 b7c6 f1d3 d7d5 e4d5 c6d5 e1g1 e8g8",
    "e2e4 e7e5 g1f3 g8f6 f3e5 d7d6 e5f3 f6e4 d2d4 d6d5 f1d3 f8e7 e1g1 b8c6",
    "e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6 c1e3 e7e5 d4b3 c8e6 f2f3 f8e7 d1d2 e8g8",
    "e2e4 c7c5 g1f3 b8c6 d2d4 c5d4 f3d4 g8f6 b1c3 d7d6 c1g5 e7e6 d1d2 a7a6 e1c1 c8d7",
    "e2e4 c7c5 g1f3 b8c6 d2d4 c5d4 f3d4 g8f6 b1c3 e7e5 d4b5 d7d6 c1g5 a7a6 b5a3 b7b5 c3d5 f8e7",
    "e2e4 e7e6 d2d4 d7d5 b1c3 g8f6 c1g5 f8e7 e4e5 f6d7 g5e7 d8e7 f2f4 e8g8 g1f3 c7c5",
    "e2e4 e7e6 d2d4 d7d5 b1d2 g8f6 e4e5 f6d7 f1d3 c7c5 c2c3 b8c6 g1e2 c5d4 c3d4 f7f6",
    "e2e4 c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5 e4g3 f5g6 h2h4 h7h6 g1f3 b8d7 h4h5 g6h7 f1d3 h7d3 d1d3 e7e6",
    "e2e4 c7c6 d2d4 d7d5 e4e5 c8f5 g1f3 e7e6 f1e2 c6c5 e1g1 b8c6",
    "e2e4 d7d5 e4d5 d8d5 b1c3 d5a5 d2d4 g8f6 g1f3 c7c6 f1c4 c8f5",
    "e2e4 d7d6 d2d4 g8f6 b1c3 g7g6 g1f3 f8g7 f1e2 e8g8 e1g1 c7c6",
    "d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8 g1f3 h7h6 g5h4 b7b6 c4d5 e6d5",
    "d2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 d5c4 a2a4 c8f5 e2e3 e7e6 f1c4 f8b4 e1g1 e8g8",
    "d2d4 g8f6 c2c4 e7e6 g2g3 d7d5 f1g2 f8e7 g1f3 e8g8 e1g1 d5c4 d1c2 a7a6 c2c4 b7b5 c4c2 c8b7",
    "d2d4 g8f6 c2c4 e7e6 b1c3 f8b4 e2e3 e8g8 f1d3 d7d5 g1f3 c7c5 e1g1 b8c6 a2a3 b4c3 b2c3 d5c4 d3c4 d8c7",
    "d2d4 g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8 f1e2 e7e5 e1g1 b8c6 d4d5 c6e7",
    "d2d4 g8f6 c2c4 g7g6 b1c3 d7d5 c4d5 f6d5 e2e4 d5c3 b2c3 f8g7 g1f3 c7c5 f1e2 e8g8 e1g1 b8c6",
    "d2d4 g8f6 c2c4 e7e6 g1f3 b7b6 g2g3 c8b7 f1g2 f8e7 e1g1 e8g8 b1c3 f6e4 d1c2 e4c3 c2c3 c7c5",
    "d2d4 d7d5 g1f3 g8f6 c1f4 e7e6 e2e3 c7c5 c2c3 b8c6 b1d2 f8d6 f4g3 e8g8 f1d3 d8c7",
    "d2d4 f7f5 g2g3 g8f6 f1g2 e7e6 g1f3 f8e7 e1g1 e8g8 c2c4 d7d6",
    "c2c4 e7e5 b1c3 g8f6 g1f3 b8c6 g2g3 d7d5 c4d5 f6d5 f1g2 d5b6 e1g1 f8e7 d2d3 e8g8",
    "c2c4 c7c5 g1f3 g8f6 b1c3 b8c6 g2g3 g7g6 f1g2 f8g7 e1g1 e8g8 d2d4 c5d4 f3d4 c6d4 d1d4 d7d6",
    "g1f3 d7d5 g2g3 g8f6 f1g2 e7e6 e1g1 f8e7 d2d4 e8g8 c2c4 d5c4 d1c2 b7b5 a2a4 c7c6",
}

local function buildBook()
    local book = {}
    local buf = {}
    for _, line in ipairs(BOOK_LINES) do
        local pos = parseFEN(START_FEN)
        local ply = 0
        for token in string.gmatch(line, "%S+") do
            local n = generate(pos, buf, false)
            local found
            for j = 1, n do
                if moveName(buf[j]) == token then found = buf[j]; break end
            end
            if not found then break end
            local key = tostring(pos.h1) .. ":" .. tostring(pos.h2)
            local entry = book[key]
            if not entry then entry = {}; book[key] = entry end
            entry[token] = (entry[token] or 0) + 1
            if not makeMove(pos, found, ply) then break end
            ply = ply + 1
        end
    end
    return book
end

------------------------------------------------------------------------
-- Engine API
------------------------------------------------------------------------
local Engine = {Name = "Fable", Version = "1.0"}

if not G.History then
    G.History = {}
    for i = 0, 32767 do G.History[i] = 0 end
end

function Engine:SetStyle(style)
    style = tostring(style or "Balanced")
    self.Style = STYLE[style] and style or "Balanced"
    G.Style = self.Style
    return self.Style
end

function Engine:Configure(options)
    if type(options) ~= "table" then return end
    if options.SliceTime then G.Slice = clamp(tonumber(options.SliceTime) or 0.03, 0.005, 0.2) end
    if options.NodeLimit then G.NodeLimit = mmax(100000, floor(tonumber(options.NodeLimit) or 50000000)) end
    if options.MaxQDepth then G.MaxQDepth = clamp(floor(tonumber(options.MaxQDepth) or 8), 4, 12) end
    if options.UseBook ~= nil then G.UseBook = options.UseBook and true or false end
    if options.HashBits then
        local b = clamp(floor(tonumber(options.HashBits) or 18), 14, 22)
        G.HashBits = b
        G.TT = newTT(b)
    end
end

function Engine:GetStats() return G.LastStats or {} end

function Engine:ClearCache()
    G.TT = newTT(G.HashBits or 18)
    for i = 0, 32767 do G.History[i] = 0 end
end

function Engine:Perft(fen, depth)
    local E = parseFEN(fen or START_FEN)
    local function perft(d, ply)
        if d == 0 then return 1 end
        local buf = E.mvs[ply]
        if not buf then buf = {}; E.mvs[ply] = buf end
        local n = generate(E, buf, false)
        local total = 0
        for i = 1, n do
            local m = buf[i]
            if makeMove(E, m, ply) then
                total = total + perft(d - 1, ply + 1)
                unmakeMove(E, m, ply)
            end
        end
        return total
    end
    return perft(depth or 3, 0)
end

function Engine:GetPV(fen, maxPly)
    local E = parseFEN(fen)
    maxPly = mmax(1, floor(tonumber(maxPly) or 12))
    local out, seen = {}, {}
    local tt = G.TT
    local buf = {}
    for i = 1, maxPly do
        local hi = ttProbe(tt, E.h1, E.h2)
        if hi == 0 or tt.mv[hi] == 0 then break end
        local m = tt.mv[hi]
        local key = tostring(E.h1) .. ":" .. tostring(m)
        if seen[key] then break end
        seen[key] = true
        local ok = false
        local n = generate(E, buf, false)
        for j = 1, n do
            if buf[j] == m then ok = makeMove(E, m, i); break end
        end
        if not ok then break end
        out[#out + 1] = moveName(m)
    end
    return table.concat(out, " ")
end

function Engine:GetBestMoveFromFEN(fen, thinkTime, options)
    if type(fen) ~= "string" or fen == "" then return nil end
    options = type(options) == "table" and options or {}
    local requested = clamp(tonumber(thinkTime) or 1.25, 0.05, 60)

    G.SearchId = (G.SearchId + 1) % 1000000
    local E = parseFEN(fen)
    if E.kingW < 0 or E.kingB < 0 then return nil end
    E.style = STYLE[self.Style or G.Style or "Balanced"] or STYLE.Balanced
    local start = clock()
    E.deadline = start + requested * 0.94
    E.nodeLimit = floor(tonumber(options.NodeLimit) or G.NodeLimit or 50000000)
    E.maxQDepth = clamp(floor(tonumber(options.MaxQDepth) or G.MaxQDepth or 8), 4, 12)
    E.slice = G.Slice or 0.03
    E.cancel = type(options.Cancel) == "function" and options.Cancel or nil
    E.tt = G.TT
    E.lastYield = start

    local H = G.History
    for i = 0, 32767 do
        local v = H[i]
        if v ~= 0 then H[i] = floor(v / 2) end
    end
    E.history = H

    if type(options.History) == "table" and #options.History > 0 then
        local r1, r2 = {}, {}
        for _, hf in ipairs(options.History) do
            if type(hf) == "string" then
                local P = parseFEN(hf)
                r1[#r1 + 1], r2[#r2 + 1] = P.h1, P.h2
            end
        end
        r1[#r1 + 1], r2[#r2 + 1] = E.h1, E.h2
        E.rep1, E.rep2, E.repN = r1, r2, #r1
    end

    -- legal root moves, ordered
    local pseudo = {}
    local np = generate(E, pseudo, false)
    local rootTT = 0
    do
        local hi = ttProbe(E.tt, E.h1, E.h2)
        if hi ~= 0 then rootTT = E.tt.mv[hi] end
    end
    local rscores = {}
    for i = 1, np do rscores[i] = moveScore(E, pseudo[i], 0, rootTT) end
    for i = 1, np do pick(pseudo, rscores, i, np) end
    local list = {}
    for i = 1, np do
        if makeMove(E, pseudo[i], 0) then
            unmakeMove(E, pseudo[i], 0)
            list[#list + 1] = {m = pseudo[i], score = 0}
        end
    end
    E.root = list

    local rootChecked = inCheck(E, E.side)
    if #list == 0 then
        return nil, rootChecked and -MATE or 0, nil
    end

    local function finish(move, score, depth, pv, reaction)
        local el = clock() - start
        G.LastStats = {
            Name = self.Name, Version = self.Version, Depth = depth, Nodes = E.nodes, QNodes = E.qnodes,
            Time = el, NPS = floor(E.nodes / mmax(el, 1e-3)), Score = score,
            Move = move and moveName(move) or nil, PV = pv or "",
        }
        return moveName(move), score, reaction
    end

    -- opening book
    if options.UseBook ~= false and G.UseBook ~= false and #list > 1 and E.half < 50 then
        G.Book = G.Book or buildBook()
        local entry = G.Book[tostring(E.h1) .. ":" .. tostring(E.h2)]
        if entry then
            local total, choices = 0, {}
            for tok, w in pairs(entry) do
                for i = 1, #list do
                    if moveName(list[i].m) == tok then
                        choices[#choices + 1] = {m = list[i].m, w = w}
                        total = total + w
                        break
                    end
                end
            end
            if total > 0 then
                local roll = math.random() * total
                for i = 1, #choices do
                    roll = roll - choices[i].w
                    if roll <= 0 or i == #choices then
                        return finish(choices[i].m, 0, 0, moveName(choices[i].m),
                            {notify = false, tag = "BOOK", message = "Opening book move.", icon = "book-open"})
                    end
                end
            end
        end
    end

    if #list == 1 then
        return finish(list[1].m, evaluate(E), 0, moveName(list[1].m), nil)
    end

    local bestMove = list[1].m
    local bestScore, previousScore, completedDepth = 0, 0, 0
    local maxDepth = mmin(floor(tonumber(options.MaxDepth) or 64), MAX_PLY - 10)
    local softFrac = 0.45
    local stable, lastBest = 0, 0
    local depth = 1

    while depth <= maxDepth do
        if depth > 1 and clock() - start >= requested * softFrac then break end
        E.abort = false
        local alpha, beta = -INF, INF
        local delta = 22
        if depth >= 5 and abs(previousScore) < MATE - 1000 then
            alpha, beta = previousScore - delta, previousScore + delta
        end
        local m, score, complete
        local done = false
        local winLo, winHi = alpha, beta
        while true do
            winLo, winHi = alpha, beta
            m, score, complete = rootSearch(E, depth, alpha, beta)
            if not complete then break end
            if score <= alpha and alpha > -INF then
                if delta >= 300 or abs(score) > MATE - 1000 then alpha = -INF else alpha = score - delta end
                delta = delta * 2
            elseif score >= beta and beta < INF then
                if delta >= 300 or abs(score) > MATE - 1000 then beta = INF else beta = score + delta end
                delta = delta * 2
            else
                done = true
                break
            end
        end

        if done then
            bestMove, bestScore = m, score
            if m == lastBest then stable = stable + 1 else stable = 0 end
            lastBest = m
            if completedDepth > 0 and previousScore - score > 25 then
                softFrac = mmin(0.8, softFrac * 1.5)
            elseif stable >= 3 then
                softFrac = mmax(0.28, softFrac * 0.92)
            end
            previousScore = score
            completedDepth = depth
            table.sort(list, function(a, b) return a.score > b.score end)
            for i = 1, #list do
                if list[i].m == m then
                    local ent = table.remove(list, i)
                    table.insert(list, 1, ent)
                    break
                end
            end
            ttStore(E, depth, score, 0, m, 0)
            local elapsed = clock() - start
            if score > MATE - 1000 and (MATE - score) <= depth then break end
            if stable >= 5 and elapsed > requested * 0.2 and depth >= 9 then break end
        else
            -- aborted: accept a move only if it was fully searched inside the window
            if m ~= 0 and score > winLo and score < winHi then
                bestMove, bestScore = m, score
            end
            break
        end
        depth = depth + 1
        yield()
    end

    local pv = self:GetPV(fen, mmin(12, mmax(1, completedDepth)))
    local reaction
    if bestScore >= MATE - 2000 then
        reaction = {notify = true, tag = "MATE", message = "A mating line was found.", icon = "swords"}
    elseif bestScore <= -MATE + 2000 then
        reaction = {notify = true, tag = "DANGER", message = "The position contains a forced tactical threat.", icon = "triangle-alert"}
    elseif E.nodes > 50000 and completedDepth >= 6 then
        reaction = {notify = false, tag = "DEEP", message = "Deep search completed.", icon = "scan-search"}
    end
    return finish(bestMove, bestScore, completedDepth, pv, reaction)
end

function Engine:Analyze(fen, thinkTime, options)
    local move, score, reaction = self:GetBestMoveFromFEN(fen, thinkTime, options)
    return {Move = move, Score = score, Reaction = reaction, Stats = G.LastStats}
end

------------------------------------------------------------------------
-- Duel harness: plays Fable against any engine exposing
-- opponent:GetBestMoveFromFEN(fen, seconds, {History=..., UseBook=false})
------------------------------------------------------------------------
local function insufficient(E)
    local minors = 0
    for idx = 1, 64 do
        local p = abs(E.board[SQ64[idx]])
        if p == PAWN or p == ROOK or p == QUEEN then return false end
        if p == KNIGHT or p == BISHOP then minors = minors + 1 end
    end
    return minors <= 1
end

function Engine:Duel(opponent, options)
    options = options or {}
    local games = floor(options.Games or 10)
    local think = options.ThinkTime or 0.5
    local randPlies = options.RandomPlies or 4
    local maxPlies = options.MaxPlies or 300
    local fableVsName = (opponent and opponent.Name) or "Opponent"
    local wins, draws, losses = 0, 0, 0
    local buf = {}

    local function legalMoves(E)
        local n = generate(E, buf, false)
        local out = {}
        for i = 1, n do
            local m = buf[i]
            if makeMove(E, m, 0) then unmakeMove(E, m, 0); out[#out + 1] = m end
        end
        return out
    end

    local function playGame(fableWhite, opening)
        local E = parseFEN(START_FEN)
        local prevFens = {}
        local counts = {}
        local function note()
            local k = tostring(E.h1) .. ":" .. tostring(E.h2)
            counts[k] = (counts[k] or 0) + 1
            return counts[k]
        end
        note()
        local plyCount = 0
        for _, tok in ipairs(opening) do
            local legal = legalMoves(E)
            local found
            for _, m in ipairs(legal) do if moveName(m) == tok then found = m; break end end
            if not found then break end
            prevFens[#prevFens + 1] = toFEN(E, 1 + floor(plyCount / 2))
            makeMove(E, found, 0)
            plyCount = plyCount + 1
            note()
        end
        while plyCount < maxPlies do
            local legal = legalMoves(E)
            if #legal == 0 then
                if inCheck(E, E.side) then
                    local fableToMove = ((E.side == WHITE) == fableWhite)
                    return fableToMove and 0 or 1, "checkmate"
                end
                return 0.5, "stalemate"
            end
            if E.half >= 100 then return 0.5, "50-move" end
            if insufficient(E) then return 0.5, "insufficient material" end
            local fen = toFEN(E, 1 + floor(plyCount / 2))
            local fableToMove = ((E.side == WHITE) == fableWhite)
            local mover = fableToMove and self or opponent
            local name = mover:GetBestMoveFromFEN(fen, think, {History = prevFens, UseBook = false})
            local found
            if name then
                for _, m in ipairs(legal) do if moveName(m) == name then found = m; break end end
            end
            if not found then return fableToMove and 0 or 1, "illegal/no move" end
            prevFens[#prevFens + 1] = fen
            makeMove(E, found, 0)
            plyCount = plyCount + 1
            if note() >= 3 then return 0.5, "repetition" end
        end
        return 0.5, "move limit"
    end

    local played = 0
    local pairIdx = 0
    while played < games do
        pairIdx = pairIdx + 1
        local P = parseFEN(START_FEN)
        local opening = {}
        for _ = 1, randPlies do
            local legal = legalMoves(P)
            if #legal == 0 then break end
            local m = legal[math.random(1, #legal)]
            opening[#opening + 1] = moveName(m)
            makeMove(P, m, 0)
        end
        for colorIdx = 1, 2 do
            if played >= games then break end
            local fableWhite = (colorIdx == 1)
            local res, why = playGame(fableWhite, opening)
            played = played + 1
            if res == 1 then wins = wins + 1 elseif res == 0 then losses = losses + 1 else draws = draws + 1 end
            print(string.format("Game %d (%s as %s): %s  [%s]  | Fable +%d =%d -%d",
                played, self.Name, fableWhite and "White" or "Black",
                res == 1 and "Fable wins" or (res == 0 and (fableVsName .. " wins") or "draw"),
                why or "", wins, draws, losses))
        end
    end
    local score = (wins + draws * 0.5) / mmax(1, played)
    print(string.format("Match finished: Fable %d - %d - %d vs %s  (score %.1f%%)",
        wins, draws, losses, fableVsName, score * 100))
    return {Wins = wins, Draws = draws, Losses = losses, Score = score}
end

Engine:SetStyle(G.Style or "Balanced")
_G.__FABLE_API = Engine

return Engine

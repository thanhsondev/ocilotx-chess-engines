local G = _G.__AETHER_PRIME_V3 or {}
_G.__AETHER_PRIME_V3 = G

local bit = bit32
local band, bxor, rshift = bit.band, bit.bxor, bit.rshift
local floor, abs, mmin, mmax, mlog = math.floor, math.abs, math.min, math.max, math.log
local clock = os.clock
local yield = (task and task.wait) or function() end

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

local ON = {}
for i = 0, 255 do
    local s = i - 64
    ON[i] = (s >= 0 and s < 128 and band(s, 8) == 0)
end

local CM = {}
for i = 0, 127 do CM[i] = 15 end
CM[0] = 13; CM[7] = 14; CM[4] = 12
CM[112] = 7; CM[119] = 11; CM[116] = 3

G.Seed = G.Seed or 0xA37F19D1
G.Z1 = G.Z1 or {}
G.Z2 = G.Z2 or {}
G.ZCastle1 = G.ZCastle1 or {}
G.ZCastle2 = G.ZCastle2 or {}
G.ZEp1 = G.ZEp1 or {}
G.ZEp2 = G.ZEp2 or {}
G.SearchId = G.SearchId or 0
G.Style = G.Style or "Balanced"
G.History = G.History or {}

local function rand32()
    local x = G.Seed
    x = bxor(x, bit.lshift(x, 13))
    x = bxor(x, rshift(x, 17))
    x = bxor(x, bit.lshift(x, 5))
    G.Seed = x
    return x
end

if not G.ZInitialized then
    for p = 1, 12 do
        G.Z1[p], G.Z2[p] = {}, {}
        for s = 0, 127 do
            G.Z1[p][s + 1] = rand32()
            G.Z2[p][s + 1] = rand32()
        end
    end
    for i = 0, 15 do G.ZCastle1[i + 1] = rand32(); G.ZCastle2[i + 1] = rand32() end
    for i = 0, 7 do G.ZEp1[i + 1] = rand32(); G.ZEp2[i + 1] = rand32() end
    G.ZSide1 = rand32()
    G.ZSide2 = rand32()
    G.ZInitialized = true
end

local ZP1, ZP2 = {}, {}
for p = -6, 6 do
    if p ~= 0 then
        local i = p > 0 and p or 6 - p
        ZP1[p + 7] = G.Z1[i]
        ZP2[p + 7] = G.Z2[i]
    end
end
local ZE1, ZE2, ZC1, ZC2 = G.ZEp1, G.ZEp2, G.ZCastle1, G.ZCastle2
local ZS1, ZS2 = G.ZSide1, G.ZSide2

------------------------------------------------------------------------
-- Piece-square tables (rank 8 first, white's point of view)
------------------------------------------------------------------------
local MAT_MG = {100, 330, 345, 500, 975, 0}
local MAT_EG = {115, 305, 325, 540, 960, 0}

local PST_MG = {
    { 0, 0, 0, 0, 0, 0, 0, 0,
      50, 50, 50, 50, 50, 50, 50, 50,
      10, 10, 20, 30, 30, 20, 10, 10,
      5, 5, 10, 25, 25, 10, 5, 5,
      0, 0, 0, 20, 20, 0, 0, 0,
      5, -5, -10, 0, 0, -10, -5, 5,
      5, 10, 10, -20, -20, 10, 10, 5,
      0, 0, 0, 0, 0, 0, 0, 0 },
    { -50, -40, -30, -30, -30, -30, -40, -50,
      -40, -20, 0, 0, 0, 0, -20, -40,
      -30, 0, 10, 15, 15, 10, 0, -30,
      -30, 5, 15, 20, 20, 15, 5, -30,
      -30, 0, 15, 20, 20, 15, 0, -30,
      -30, 5, 10, 15, 15, 10, 5, -30,
      -40, -20, 0, 5, 5, 0, -20, -40,
      -50, -40, -30, -30, -30, -30, -40, -50 },
    { -20, -10, -10, -10, -10, -10, -10, -20,
      -10, 0, 0, 0, 0, 0, 0, -10,
      -10, 0, 5, 10, 10, 5, 0, -10,
      -10, 5, 5, 10, 10, 5, 5, -10,
      -10, 0, 10, 10, 10, 10, 0, -10,
      -10, 10, 10, 10, 10, 10, 10, -10,
      -10, 5, 0, 0, 0, 0, 5, -10,
      -20, -10, -10, -10, -10, -10, -10, -20 },
    { 0, 0, 0, 0, 0, 0, 0, 0,
      5, 10, 10, 10, 10, 10, 10, 5,
      -5, 0, 0, 0, 0, 0, 0, -5,
      -5, 0, 0, 0, 0, 0, 0, -5,
      -5, 0, 0, 0, 0, 0, 0, -5,
      -5, 0, 0, 0, 0, 0, 0, -5,
      -5, 0, 0, 0, 0, 0, 0, -5,
      0, 0, 0, 5, 5, 0, 0, 0 },
    { -20, -10, -10, -5, -5, -10, -10, -20,
      -10, 0, 0, 0, 0, 0, 0, -10,
      -10, 0, 5, 5, 5, 5, 0, -10,
      -5, 0, 5, 5, 5, 5, 0, -5,
      0, 0, 5, 5, 5, 5, 0, -5,
      -10, 5, 5, 5, 5, 5, 0, -10,
      -10, 0, 5, 0, 0, 0, 0, -10,
      -20, -10, -10, -5, -5, -10, -10, -20 },
    { -30, -40, -40, -50, -50, -40, -40, -30,
      -30, -40, -40, -50, -50, -40, -40, -30,
      -30, -40, -40, -50, -50, -40, -40, -30,
      -30, -40, -40, -50, -50, -40, -40, -30,
      -20, -30, -30, -40, -40, -30, -30, -20,
      -10, -20, -20, -20, -20, -20, -20, -10,
      20, 20, 0, 0, 0, 0, 20, 20,
      20, 30, 10, 0, 0, 10, 30, 20 },
}

local PST_EG = {}
for t = 1, 5 do PST_EG[t] = PST_MG[t] end
PST_EG[KING] = {
    -50, -40, -30, -20, -20, -30, -40, -50,
    -30, -20, -10, 0, 0, -10, -20, -30,
    -30, -10, 20, 30, 30, 20, -10, -30,
    -30, -10, 30, 40, 40, 30, -10, -30,
    -30, -10, 30, 40, 40, 30, -10, -30,
    -30, -10, 20, 30, 30, 20, -10, -30,
    -30, -30, 0, 0, 0, 0, -30, -30,
    -50, -30, -30, -30, -30, -30, -30, -50 }
do -- endgame pawns: pure advancement
    local adv = {0, 0, 5, 15, 30, 55, 90, 0}
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
-- Styles (tune evaluation weights; Balanced is the strongest all-rounder)
------------------------------------------------------------------------
local STYLE = {
    Balanced = {Att = 1.0, Safe = 1.0, Mob = 1.0, Pwn = 1.0, Contempt = 8, Center = 6, LMR = 1.0},
    Aggressive = {Att = 1.4, Safe = 0.85, Mob = 1.1, Pwn = 0.9, Contempt = 20, Center = 8, LMR = 1.0},
    Calm = {Att = 0.8, Safe = 1.1, Mob = 1.0, Pwn = 1.1, Contempt = 0, Center = 5, LMR = 1.0},
    Defensive = {Att = 0.7, Safe = 1.4, Mob = 0.9, Pwn = 1.1, Contempt = 0, Center = 3, LMR = 1.0},
    Tactical = {Att = 1.3, Safe = 0.9, Mob = 1.2, Pwn = 0.9, Contempt = 12, Center = 10, LMR = 0.85},
    Trickery = {Att = 1.2, Safe = 0.9, Mob = 1.1, Pwn = 0.9, Contempt = 25, Center = 9, LMR = 0.9},
    Positional = {Att = 0.8, Safe = 1.1, Mob = 1.25, Pwn = 1.4, Contempt = 5, Center = 10, LMR = 1.0},
    Endgame = {Att = 0.8, Safe = 0.9, Mob = 1.0, Pwn = 1.3, Contempt = 5, Center = 6, LMR = 1.0},
    ["Alien Gambit"] = {Att = 1.6, Safe = 0.7, Mob = 1.2, Pwn = 0.9, Contempt = 40, Center = 10, LMR = 0.5},
    ["Willy Alien"] = {Att = 1.8, Safe = 0.6, Mob = 1.3, Pwn = 0.8, Contempt = 60, Center = 12, LMR = 0.4},
}

------------------------------------------------------------------------
-- Moves
------------------------------------------------------------------------
local function enc(from, to, promo, flags)
    return from + to * 128 + promo * 16384 + flags * 131072
end
local function moveFrom(m) return band(m, 127) end
local function moveTo(m) return band(rshift(m, 7), 127) end
local function movePromo(m) return band(rshift(m, 14), 7) end
local function moveFlags(m) return band(rshift(m, 17), 15) end

local function squareName(s)
    return string.char(97 + band(s, 15)) .. tostring(rshift(s, 4) + 1)
end

local PROMO_CH = {[KNIGHT] = "n", [BISHOP] = "b", [ROOK] = "r", [QUEEN] = "q"}
local function moveName(m)
    return squareName(moveFrom(m)) .. squareName(moveTo(m)) .. (PROMO_CH[movePromo(m)] or "")
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
    local k = side == WHITE and E.kingW or E.kingB
    return isAttacked(E, k, -side)
end

------------------------------------------------------------------------
-- Move generation (pseudo-legal)
------------------------------------------------------------------------
local function generate(E, capsOnly)
    local B = E.board
    local moves, n = {}, 0
    local side = E.side
    local enemy = -side
    local ep = E.ep
    local step = side * 16
    local startRank = side == WHITE and 1 or 6
    local promoRank = side == WHITE and 7 or 0

    for r = 0, 7 do
        local base = r * 16
        for f = 0, 7 do
            local s = base + f
            local p = B[s]
            if p * side > 0 then
                local t = p > 0 and p or -p
                if t == PAWN then
                    local one = s + step
                    if B[one] == 0 then
                        if rshift(one, 4) == promoRank then
                            if capsOnly then
                                n = n + 1; moves[n] = enc(s, one, QUEEN, 0)
                            else
                                for i = 1, 4 do n = n + 1; moves[n] = enc(s, one, PROMOS[i], 0) end
                            end
                        elseif not capsOnly then
                            n = n + 1; moves[n] = enc(s, one, 0, 0)
                            if r == startRank then
                                local two = one + step
                                if B[two] == 0 then n = n + 1; moves[n] = enc(s, two, 0, FLAG_DOUBLE) end
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
                                        n = n + 1; moves[n] = enc(s, c, QUEEN, FLAG_CAPTURE)
                                    else
                                        for i = 1, 4 do n = n + 1; moves[n] = enc(s, c, PROMOS[i], FLAG_CAPTURE) end
                                    end
                                else
                                    n = n + 1; moves[n] = enc(s, c, 0, FLAG_CAPTURE)
                                end
                            elseif q == 0 and c == ep then
                                n = n + 1; moves[n] = enc(s, c, 0, FLAG_CAPTURE + FLAG_EP)
                            end
                        end
                    end
                elseif t == KNIGHT then
                    for i = 1, 8 do
                        local to = s + KNIGHT_D[i]
                        if ON[to + 64] then
                            local q = B[to]
                            if q == 0 then
                                if not capsOnly then n = n + 1; moves[n] = enc(s, to, 0, 0) end
                            elseif q * side < 0 then
                                n = n + 1; moves[n] = enc(s, to, 0, FLAG_CAPTURE)
                            end
                        end
                    end
                elseif t == KING then
                    for i = 1, 8 do
                        local to = s + KING_D[i]
                        if ON[to + 64] then
                            local q = B[to]
                            if q == 0 then
                                if not capsOnly then n = n + 1; moves[n] = enc(s, to, 0, 0) end
                            elseif q * side < 0 then
                                n = n + 1; moves[n] = enc(s, to, 0, FLAG_CAPTURE)
                            end
                        end
                    end
                    local cr = E.castle
                    if not capsOnly and cr ~= 0 then
                        if side == WHITE and s == 4 then
                            if band(cr, 1) ~= 0 and B[5] == 0 and B[6] == 0 and B[7] == ROOK
                                and not isAttacked(E, 4, enemy) and not isAttacked(E, 5, enemy) and not isAttacked(E, 6, enemy) then
                                n = n + 1; moves[n] = enc(4, 6, 0, FLAG_CASTLE)
                            end
                            if band(cr, 2) ~= 0 and B[3] == 0 and B[2] == 0 and B[1] == 0 and B[0] == ROOK
                                and not isAttacked(E, 4, enemy) and not isAttacked(E, 3, enemy) and not isAttacked(E, 2, enemy) then
                                n = n + 1; moves[n] = enc(4, 2, 0, FLAG_CASTLE)
                            end
                        elseif side == BLACK and s == 116 then
                            if band(cr, 4) ~= 0 and B[117] == 0 and B[118] == 0 and B[119] == -ROOK
                                and not isAttacked(E, 116, enemy) and not isAttacked(E, 117, enemy) and not isAttacked(E, 118, enemy) then
                                n = n + 1; moves[n] = enc(116, 118, 0, FLAG_CASTLE)
                            end
                            if band(cr, 8) ~= 0 and B[115] == 0 and B[114] == 0 and B[113] == 0 and B[112] == -ROOK
                                and not isAttacked(E, 116, enemy) and not isAttacked(E, 115, enemy) and not isAttacked(E, 114, enemy) then
                                n = n + 1; moves[n] = enc(116, 114, 0, FLAG_CASTLE)
                            end
                        end
                    end
                else
                    local deltas = (t == BISHOP) and BISHOP_D or (t == ROOK) and ROOK_D or KING_D
                    local stop = (t == QUEEN) and 8 or 4
                    for i = 1, stop do
                        local d = deltas[i]
                        local to = s + d
                        while ON[to + 64] do
                            local q = B[to]
                            if q == 0 then
                                if not capsOnly then n = n + 1; moves[n] = enc(s, to, 0, 0) end
                            else
                                if q * side < 0 then n = n + 1; moves[n] = enc(s, to, 0, FLAG_CAPTURE) end
                                break
                            end
                            to = to + d
                        end
                    end
                end
            end
        end
    end
    return moves
end

------------------------------------------------------------------------
-- Make / unmake  (incremental hash, mg/eg score, phase, non-pawn material)
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
        local ac = captured > 0 and captured or -captured
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
    local side = piece > 0 and WHITE or BLACK
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
-- Evaluation (tapered, incremental PST + dynamic terms, lazy cutoff)
------------------------------------------------------------------------
local PASS_MG = {0, 5, 10, 20, 35, 60, 100, 0}
local PASS_EG = {0, 10, 20, 40, 70, 120, 190, 0}
local THREAT = {0, 25, 25, 45, 60, 0}
local ATK_MULT = {0, 0, 50, 75, 88, 94, 97, 99, 100}
local TEMPO = 10
local LAZY = 350

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

local function evalSide(B, side, L, C, ownFile, enExt, pAtkEn, zoneEn, stamp, ownK, enK, st)
    local mg, eg, aw, an = 0, 0, 0, 0
    local mob, pw, safe = st.Mob, st.Pwn, st.Safe
    local pawn = side * PAWN
    local fwd = side * 16

    -- pawns
    for i = 1, C[1] do
        local s = L[1][i]
        local f, r = band(s, 15), rshift(s, 4)
        local fi = f + 2
        local rr = (side == WHITE) and r or 7 - r
        if ownFile[fi - 1] == 0 and ownFile[fi + 1] == 0 then
            mg = mg - 10 * pw; eg = eg - 16 * pw
        end
        local passed
        if side == WHITE then
            passed = enExt[fi - 1] <= r and enExt[fi] <= r and enExt[fi + 1] <= r
        else
            passed = enExt[fi - 1] >= r and enExt[fi] >= r and enExt[fi + 1] >= r
        end
        if passed then
            local bm, be = PASS_MG[rr + 1], PASS_EG[rr + 1]
            local stop = s + fwd
            if (B[stop] or 0) ~= 0 then bm = bm * 0.5; be = be * 0.5 end
            if rr >= 2 then
                be = be + (kdist(enK, stop) * 4 - kdist(ownK, stop) * 2) * rr * 0.5
            end
            mg = mg + bm * pw; eg = eg + be * pw
        end
        if B[s - fwd - 1] == pawn or B[s - fwd + 1] == pawn or B[s - 1] == pawn or B[s + 1] == pawn then
            mg = mg + (3 + rr * 2) * pw
            eg = eg + (5 + rr * 3) * pw
        end
        for k = -1, 1, 2 do
            local t = s + fwd + k
            if ON[t + 64] then
                local q = B[t]
                if q * side < 0 then
                    local a = q > 0 and q or -q
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
    for i = 1, C[2] do
        local s = L[2][i]
        local cnt, hit = 0, false
        for k = 1, 8 do
            local t = s + KNIGHT_D[k]
            if ON[t + 64] then
                if B[t] * side <= 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                if zoneEn[t] == stamp then hit = true end
            end
        end
        mg = mg + (cnt - 4) * 4 * mob
        eg = eg + (cnt - 4) * 4 * mob
        if hit then aw = aw + 20; an = an + 1 end
    end
    -- bishops
    for i = 1, C[3] do
        local s = L[3][i]
        local cnt, hit = 0, false
        for k = 1, 4 do
            local d = BISHOP_D[k]
            local t = s + d
            while ON[t + 64] do
                local q = B[t]
                if zoneEn[t] == stamp then hit = true end
                if q == 0 then
                    if pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                else
                    if q * side < 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                    break
                end
                t = t + d
            end
        end
        mg = mg + (cnt - 5) * 5 * mob
        eg = eg + (cnt - 5) * 5 * mob
        if hit then aw = aw + 20; an = an + 1 end
    end
    if C[3] >= 2 then mg = mg + 30; eg = eg + 50 end
    -- rooks
    for i = 1, C[4] do
        local s = L[4][i]
        local f, r = band(s, 15), rshift(s, 4)
        local cnt, hit = 0, false
        for k = 1, 4 do
            local d = ROOK_D[k]
            local t = s + d
            while ON[t + 64] do
                local q = B[t]
                if zoneEn[t] == stamp then hit = true end
                if q == 0 then
                    if pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                else
                    if q * side < 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                    break
                end
                t = t + d
            end
        end
        mg = mg + (cnt - 5) * 2 * mob
        eg = eg + (cnt - 5) * 4 * mob
        if hit then aw = aw + 40; an = an + 1 end
        if ownFile[f + 2] == 0 then
            if enExt == maxRB then
                -- we are white: enemy pawns tracked by maxRB; open if none on file
                if maxRB[f + 2] < 0 then mg = mg + 22; eg = eg + 12 else mg = mg + 10; eg = eg + 8 end
            else
                if minRW[f + 2] > 7 then mg = mg + 22; eg = eg + 12 else mg = mg + 10; eg = eg + 8 end
            end
        end
        local rr = (side == WHITE) and r or 7 - r
        if rr == 6 then mg = mg + 10; eg = eg + 20 end
    end
    -- queens
    for i = 1, C[5] do
        local s = L[5][i]
        local cnt, hit = 0, false
        for k = 1, 8 do
            local d = KING_D[k]
            local t = s + d
            while ON[t + 64] do
                local q = B[t]
                if zoneEn[t] == stamp then hit = true end
                if q == 0 then
                    if pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                else
                    if q * side < 0 and pAtkEn[t] ~= stamp then cnt = cnt + 1 end
                    break
                end
                t = t + d
            end
        end
        mg = mg + (cnt - 10) * 1 * mob
        eg = eg + (cnt - 10) * 2 * mob
        if hit then aw = aw + 80; an = an + 1 end
    end

    -- pawn shield in front of own king
    local kf = band(ownK, 15)
    local sh = 0
    for df = -1, 1 do
        local f = kf + df
        if f >= 0 and f <= 7 then
            local sq1 = ownK + fwd + df
            if B[sq1] == pawn then
                sh = sh + 10
            elseif B[sq1 + fwd] == pawn then
                sh = sh + 5
            else
                sh = sh - 12
                if ownFile[f + 2] == 0 then sh = sh - 10 end
            end
        end
    end
    mg = mg + sh * safe
    return mg, eg, aw, an
end

local function dangerOf(aw, an, enemyQueens, att)
    if an < 2 then return 0 end
    local d = aw * ATK_MULT[mmin(an, 8) + 1] / 100
    if enemyQueens == 0 then d = d * 0.5 end
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

    for r = 0, 7 do
        local base = r * 16
        for f = 0, 7 do
            local s = base + f
            local p = B[s]
            if p > 0 then
                local n = CW[p] + 1
                CW[p] = n
                LW[p][n] = s
                if p == PAWN then
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
                    local fi = f + 2
                    fileB[fi] = fileB[fi] + 1
                    if r > maxRB[fi] then maxRB[fi] = r end
                    pAtkB[s - 15] = stamp; pAtkB[s - 17] = stamp
                end
            end
        end
    end

    local npmW, npmB = E.npmW, E.npmB
    if CW[1] + CB[1] == 0 and npmW <= 340 and npmB <= 340 then return 0 end

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
    local wmg, weg, waw, wan = evalSide(B, WHITE, LW, CW, fileW, maxRB, pAtkB, zoneB, stamp, wk, bk, st)
    local bmg, beg, baw, ban = evalSide(B, BLACK, LB, CB, fileB, minRW, pAtkW, zoneW, stamp, bk, wk, st)

    local mg = E.mg + wmg - bmg
    local eg = E.eg + weg - beg
    local att = st.Att
    local dW = dangerOf(baw, ban, CB[5], att) -- black attacking white king
    local dB = dangerOf(waw, wan, CW[5], att)
    mg = mg - dW + dB
    eg = eg - dW * 0.25 + dB * 0.25

    local ph = E.phase
    if ph > 24 then ph = 24 end
    local score = floor((mg * ph + eg * (24 - ph)) / 24)
    score = score + E.side * TEMPO

    -- mop-up: drive a bare king to the edge
    if npmW - npmB >= 450 and npmB == 0 and CB[1] == 0 then
        local f, r = band(bk, 15), rshift(bk, 4)
        local cd = mmax(3 - f, f - 4) + mmax(3 - r, r - 4)
        score = score + cd * 10 + (14 - kdist(wk, bk)) * 4
    elseif npmB - npmW >= 450 and npmW == 0 and CW[1] == 0 then
        local f, r = band(wk, 15), rshift(wk, 4)
        local cd = mmax(3 - f, f - 4) + mmax(3 - r, r - 4)
        score = score - (cd * 10 + (14 - kdist(wk, bk)) * 4)
    elseif score > 0 and CW[1] == 0 and npmW - npmB <= 350 then
        score = floor(score / 2)
    elseif score < 0 and CB[1] == 0 and npmB - npmW <= 350 then
        score = -floor(-score / 2)
    end
    return E.side * score
end

local function staticEval(E, alpha, beta)
    local ph = E.phase
    if ph > 24 then ph = 24 end
    local quick = E.side * floor((E.mg * ph + E.eg * (24 - ph)) / 24)
    if quick + LAZY <= alpha or quick - LAZY >= beta then return quick end
    return evaluate(E)
end

------------------------------------------------------------------------
-- Transposition table (parallel arrays)
------------------------------------------------------------------------
local function newTT(bits)
    local size = bit.lshift(1, bits)
    return {
        k1 = table.create(size, -1), k2 = table.create(size, -1),
        mv = table.create(size, 0), dp = table.create(size, 0),
        bd = table.create(size, 0), sc = table.create(size, 0),
        gn = table.create(size, 0),
        mask = size - 1, bits = bits,
    }
end
G.TT = G.TT and G.TT.k1 and G.TT or newTT(G.HashBits or 17)

local function ttStore(E, depth, score, bound, move, ply)
    local tt = E.tt
    local idx = band(E.h1, tt.mask) + 1
    local same = tt.k1[idx] == E.h1 and tt.k2[idx] == E.h2
    local old = tt.dp[idx]
    local replace
    if same then
        replace = depth >= old - 2 or bound == 0
    else
        replace = tt.gn[idx] ~= G.SearchId or depth >= old
    end
    if replace then
        if score > MATE - 1000 then score = score + ply
        elseif score < -MATE + 1000 then score = score - ply end
        if move == 0 and same then move = tt.mv[idx] end
        tt.k1[idx], tt.k2[idx] = E.h1, E.h2
        tt.mv[idx], tt.dp[idx], tt.bd[idx], tt.sc[idx], tt.gn[idx] = move, depth, bound, score, G.SearchId
    elseif same and move ~= 0 and tt.mv[idx] == 0 then
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
        LMRT[d][i] = floor(0.7 + mlog(d) * mlog(i) / 2.2)
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

local function addHist(E, k, b)
    local h = E.history[k] or 0
    E.history[k] = h + b - floor(h * abs(b) / 16384)
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
    local pt = piece > 0 and piece or -piece
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
        return promo == QUEEN and 1950000 or -900000
    end
    local k = E.killers[ply]
    if k then
        if m == k[1] then return 900000 end
        if m == k[2] then return 800000 end
    end
    if ply > 0 then
        local prev = E.stack[ply - 1]
        if prev and prev.piece ~= 0 and E.counter[(prev.piece + 7) * 128 + prev.to] == m then
            return 700000
        end
    end
    local score = E.history[(piece + 7) * 128 + to] or 0
    local fl = band(to, 15)
    if fl == 3 or fl == 4 then score = score + E.style.Center end
    return score
end

local function qsearch(E, alpha, beta, ply, qd)
    if not touch(E) then return 0 end
    E.qnodes = E.qnodes + 1
    if ply >= MAX_PLY - 1 then return evaluate(E) end
    if E.half >= 100 then return 0 end
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

    local moves = generate(E, not checked)
    local n = #moves
    local scores = {}
    local B = E.board
    for i = 1, n do
        local m = moves[i]
        local flags = band(rshift(m, 17), 15)
        local sc = 0
        if band(flags, FLAG_CAPTURE) ~= 0 then
            local victim = (band(flags, FLAG_EP) ~= 0) and PAWN or abs(B[band(rshift(m, 7), 127)])
            local pt = abs(B[band(m, 127)])
            sc = 1000000 + VAL[victim] * 10 - pt
        elseif band(rshift(m, 14), 7) ~= 0 then
            sc = 900000
        end
        scores[i] = sc
    end

    local legal = 0
    for i = 1, n do
        pick(moves, scores, i, n)
        local m = moves[i]
        local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
        local skip = false
        if not checked then
            if band(flags, FLAG_CAPTURE) ~= 0 then
                local victim = (band(flags, FLAG_EP) ~= 0) and PAWN or abs(B[band(rshift(m, 7), 127)])
                if promo == 0 and stand + VAL[victim] + 200 < alpha then
                    skip = true
                elseif VAL[victim] < VAL[abs(B[band(m, 127)])] and see(E, m) < 0 then
                    skip = true
                end
            end
        end
        if not skip and makeMove(E, m, ply) then
            legal = legal + 1
            local score = -qsearch(E, -beta, -alpha, ply + 1, qd + 1)
            unmakeMove(E, m, ply)
            if E.abort then return 0 end
            if score > best then
                best = score
                if score > alpha then
                    alpha = score
                    if score >= beta then return score end
                end
            end
        end
    end
    if checked and legal == 0 then return -MATE + ply end
    return best
end

local function negamax(E, depth, alpha, beta, ply, allowNull)
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

    -- TT probe
    local tt = E.tt
    local idx = band(E.h1, tt.mask) + 1
    local ttMove, ttScore, ttDepth, ttBound = 0, 0, -1, 0
    if tt.k1[idx] == E.h1 and tt.k2[idx] == E.h2 then
        ttMove, ttDepth, ttBound, ttScore = tt.mv[idx], tt.dp[idx], tt.bd[idx], tt.sc[idx]
        if ttScore > MATE - 1000 then ttScore = ttScore - ply
        elseif ttScore < -MATE + 1000 then ttScore = ttScore + ply end
        if not isPV and ttDepth >= depth then
            if ttBound == 0 or (ttBound == 2 and ttScore >= beta) or (ttBound == 1 and ttScore <= alpha) then
                return ttScore
            end
        end
    end

    local static = -INF
    if not checked then static = staticEval(E, alpha, beta) end
    E.evalStack[ply] = static
    local improving = false
    if not checked and ply >= 2 then
        local e2 = E.evalStack[ply - 2]
        improving = e2 ~= nil and e2 > -INF and static > e2
    end

    local side = E.side
    if not isPV and not checked and abs(beta) < MATE - 1000 then
        -- reverse futility
        if depth <= 6 and static - 85 * depth + (improving and 0 or 25) >= beta then
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
        if allowNull and depth >= 3 and static >= beta and npm > 0 then
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
            local score = -negamax(E, depth - 1 - R, -beta, -beta + 1, ply + 1, false)
            E.repN = nr - 1
            E.side = side
            E.ep = oldEp
            E.h1, E.h2, E.half = oh1, oh2, ohalf
            if E.abort then return 0 end
            if score >= beta then
                if score > MATE - 1000 then score = beta end
                if depth < 9 then return score end
                local v = negamax(E, depth - R, beta - 1, beta, ply, false)
                if E.abort then return 0 end
                if v >= beta then return score end
            end
        end
    end

    -- internal iterative deepening
    if isPV and ttMove == 0 and depth >= 5 then
        negamax(E, depth - 2, alpha, beta, ply, false)
        if E.abort then return 0 end
        if tt.k1[idx] == E.h1 and tt.k2[idx] == E.h2 then ttMove = tt.mv[idx] end
    end

    local moves = generate(E, false)
    local n = #moves
    local scores = {}
    for i = 1, n do scores[i] = moveScore(E, moves[i], ply, ttMove) end

    local best, bestMove, legal = -INF, 0, 0
    local quiets, nq = {}, 0
    local B = E.board
    local style = E.style

    for i = 1, n do
        pick(moves, scores, i, n)
        local m, sc = moves[i], scores[i]
        local flags, promo = band(rshift(m, 17), 15), band(rshift(m, 14), 7)
        local isCap = band(flags, FLAG_CAPTURE) ~= 0
        local quiet = (not isCap) and promo == 0

        local prune = false
        if not isPV and not checked and best > -MATE + 1000 then
            if quiet then
                if depth <= 3 and nq >= 3 + depth * depth then prune = true end
            elseif isCap and sc < -500000 and depth <= 5 and (sc + 1000000) < -90 * depth then
                prune = true
            end
        end

        if not prune and makeMove(E, m, ply) then
            legal = legal + 1
            local skip = false
            if quiet and not isPV and not checked and depth <= 4 and legal > 1 and best > -MATE + 1000
                and static + 90 + 110 * depth <= alpha then
                if not inCheck(E, E.side) then skip = true end
            end
            if skip then
                unmakeMove(E, m, ply)
            else
                local newDepth = depth - 1
                local score
                if legal == 1 then
                    score = -negamax(E, newDepth, -beta, -alpha, ply + 1, true)
                else
                    local r = 0
                    if depth >= 3 and not checked then
                        if quiet then
                            r = LMRT[mmin(depth, 64)][mmin(legal, 64)]
                            r = floor(r * style.LMR + 0.5)
                            if isPV then r = r - 1 end
                            if not improving then r = r + 1 end
                            if sc >= 700000 then r = r - 1
                            elseif sc > -20000 and sc < 20000 then r = r - floor(sc / 5000) end
                        elseif isCap and sc < -500000 then
                            r = 1
                        end
                        if r < 0 then r = 0 end
                        if r > newDepth - 1 then r = mmax(0, newDepth - 1) end
                    end
                    score = -negamax(E, newDepth - r, -alpha - 1, -alpha, ply + 1, true)
                    if score > alpha and r > 0 then
                        score = -negamax(E, newDepth, -alpha - 1, -alpha, ply + 1, true)
                    end
                    if score > alpha and score < beta then
                        score = -negamax(E, newDepth, -beta, -alpha, ply + 1, true)
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
                                local pk = (B[band(m, 127)] + 7) * 128 + band(rshift(m, 7), 127)
                                addHist(E, pk, bonus)
                                for q = 1, nq do
                                    local qm = quiets[q]
                                    addHist(E, (B[band(qm, 127)] + 7) * 128 + band(rshift(qm, 7), 127), -bonus)
                                end
                                if ply > 0 then
                                    local prev = E.stack[ply - 1]
                                    if prev and prev.piece ~= 0 then
                                        E.counter[(prev.piece + 7) * 128 + prev.to] = m
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

    if legal == 0 then
        if checked then return -MATE + ply end
        return 0
    end

    local bound = (best >= beta) and 2 or ((best > alpha0) and 0 or 1)
    ttStore(E, depth, best, bound, bestMove, ply)
    return best
end

local function rootSearch(E, depth, alpha, beta)
    local list = E.root
    local best, bestMove = -INF, 0
    local quietRoot = not inCheck(E, E.side)
    for i = 1, #list do
        local ent = list[i]
        local m = ent.m
        if makeMove(E, m, 0) then
            local newDepth = depth - 1
            local score
            if i == 1 then
                score = -negamax(E, newDepth, -beta, -alpha, 1, true)
            else
                local r = 0
                if depth >= 3 and i >= 4 and quietRoot and band(rshift(m, 17), 15) == 0 and band(rshift(m, 14), 7) == 0 then
                    r = (i > 10) and 2 or 1
                    if r > newDepth - 1 then r = mmax(0, newDepth - 1) end
                end
                score = -negamax(E, newDepth - r, -alpha - 1, -alpha, 1, true)
                if score > alpha and r > 0 then
                    score = -negamax(E, newDepth, -alpha - 1, -alpha, 1, true)
                end
                if score > alpha and score < beta then
                    score = -negamax(E, newDepth, -beta, -alpha, 1, true)
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
                    local pt = piece > 0 and piece or -piece
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
        stack = {}, tt = G.TT, killers = {}, history = {}, counter = {}, evalStack = {},
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

------------------------------------------------------------------------
-- Opening book (built by replaying lines; validated for legality)
------------------------------------------------------------------------
local BOOK_LINES = {
    "e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6 c2c3 e8g8",
    "e2e4 e7e5 g1f3 b8c6 f1c4 f8c5 c2c3 g8f6 d2d3 d7d6",
    "e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 g8f6 b1c3 f8b4",
    "e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6",
    "e2e4 c7c5 g1f3 b8c6 d2d4 c5d4 f3d4 g8f6 b1c3 e7e5",
    "e2e4 e7e6 d2d4 d7d5 b1c3 g8f6 c1g5 f8e7 e4e5 f6d7",
    "e2e4 c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5 e4g3 f5g6",
    "d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8 g1f3",
    "d2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 d5c4 a2a4 c8f5",
    "d2d4 g8f6 c2c4 e7e6 b1c3 f8b4 e2e3 e8g8 f1d3 d7d5 g1f3 c7c5",
    "d2d4 g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8 f1e2 e7e5",
    "c2c4 e7e5 b1c3 g8f6 g1f3 b8c6 g2g3 d7d5 c4d5 f6d5",
    "g1f3 d7d5 g2g3 g8f6 f1g2 e7e6 e1g1 f8e7 d2d4 e8g8",
}

local function buildBook()
    local book = {}
    for _, line in ipairs(BOOK_LINES) do
        local pos = parseFEN(START_FEN)
        local ply = 0
        for token in string.gmatch(line, "%S+") do
            local moves = generate(pos, false)
            local found
            for j = 1, #moves do
                if moveName(moves[j]) == token then found = moves[j]; break end
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
local Engine = {Name = "Aether Prime", Version = "3.0"}

function Engine:SetStyle(style)
    style = tostring(style or "Balanced")
    self.Style = STYLE[style] and style or "Balanced"
    G.Style = self.Style
    return self.Style
end

function Engine:Configure(options)
    if type(options) ~= "table" then return end
    if options.YieldEvery then G.Slice = nil end
    if options.SliceTime then G.Slice = math.clamp(tonumber(options.SliceTime) or 0.03, 0.005, 0.2) end
    if options.NodeLimit then G.NodeLimit = math.max(100000, floor(tonumber(options.NodeLimit) or 50000000)) end
    if options.MaxQDepth then G.MaxQDepth = math.clamp(floor(tonumber(options.MaxQDepth) or 8), 4, 12) end
    if options.UseBook ~= nil then G.UseBook = options.UseBook and true or false end
    if options.HashBits then
        local b = math.clamp(floor(tonumber(options.HashBits) or 17), 14, 22)
        G.HashBits = b
        G.TT = newTT(b)
    end
end

function Engine:GetStats() return G.LastStats or {} end

function Engine:ClearCache()
    G.TT = newTT(G.HashBits or 17)
    G.History = {}
end

function Engine:Perft(fen, depth)
    local E = parseFEN(fen or START_FEN)
    local function perft(d, ply)
        if d == 0 then return 1 end
        local moves = generate(E, false)
        local total = 0
        for i = 1, #moves do
            if makeMove(E, moves[i], ply) then
                total = total + perft(d - 1, ply + 1)
                unmakeMove(E, moves[i], ply)
            end
        end
        return total
    end
    return perft(depth or 3, 0)
end

function Engine:GetPV(fen, maxPly)
    local E = parseFEN(fen)
    maxPly = mmax(1, floor(tonumber(maxPly) or 12))
    local out = {}
    local seen = {}
    local tt = G.TT
    for i = 1, maxPly do
        local idx = band(E.h1, tt.mask) + 1
        if tt.k1[idx] ~= E.h1 or tt.k2[idx] ~= E.h2 or tt.mv[idx] == 0 then break end
        local m = tt.mv[idx]
        local key = tostring(E.h1) .. ":" .. tostring(m)
        if seen[key] then break end
        seen[key] = true
        local ok = false
        local list = generate(E, false)
        for j = 1, #list do
            if list[j] == m then ok = makeMove(E, m, i); break end
        end
        if not ok then break end
        out[#out + 1] = moveName(m)
    end
    return table.concat(out, " ")
end

function Engine:GetBestMoveFromFEN(fen, thinkTime, options)
    if type(fen) ~= "string" or fen == "" then return nil end
    options = type(options) == "table" and options or {}
    local requested = math.clamp(tonumber(thinkTime) or 1.25, 0.1, 30)

    G.SearchId = G.SearchId + 1
    local E = parseFEN(fen)
    E.style = STYLE[self.Style] or STYLE.Balanced
    local start = clock()
    E.deadline = start + requested
    E.nodeLimit = floor(tonumber(options.NodeLimit) or G.NodeLimit or 50000000)
    E.maxQDepth = math.clamp(floor(tonumber(options.MaxQDepth) or G.MaxQDepth or 8), 4, 12)
    E.slice = G.Slice or 0.03
    E.cancel = type(options.Cancel) == "function" and options.Cancel or nil
    E.tt = G.TT
    E.lastYield = start

    -- persistent, aged history
    for k, v in pairs(G.History) do G.History[k] = floor(v / 2) end
    E.history = G.History

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

    -- legal root moves
    local pseudo = generate(E, false)
    local rscores = {}
    for i = 1, #pseudo do rscores[i] = moveScore(E, pseudo[i], 0, 0) end
    for i = 1, #pseudo do pick(pseudo, rscores, i, #pseudo) end
    local list = {}
    for i = 1, #pseudo do
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
        G.LastStats = {
            Name = self.Name, Version = self.Version, Depth = depth, Nodes = E.nodes, QNodes = E.qnodes,
            Time = clock() - start, NPS = floor(E.nodes / mmax(clock() - start, 1e-3)), Score = score,
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

    -- single legal move: no need to think
    if #list == 1 then
        local s = evaluate(E)
        return finish(list[1].m, s, 0, moveName(list[1].m), nil)
    end

    local bestMove = list[1].m
    local bestScore, previousScore, completedDepth = 0, 0, 0
    local maxDepth = mmin(floor(tonumber(options.MaxDepth) or 64), MAX_PLY - 8)
    local softLimit = start + requested * 0.55
    local stable, lastBest = 0, 0
    local depth = 1

    while depth <= maxDepth do
        if depth > 1 and clock() >= softLimit then break end
        E.abort = false
        local alpha, beta = -INF, INF
        local delta = 30
        if depth >= 5 and abs(previousScore) < MATE - 1000 then
            alpha, beta = previousScore - delta, previousScore + delta
        end
        local m, score, complete
        local done = false
        while true do
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
            if completedDepth > 0 and previousScore - score > 30 then
                softLimit = start + requested * 0.8
            end
            previousScore = score
            completedDepth = depth
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
            if stable >= 4 and elapsed > requested * 0.25 and depth >= 8 then break end
        else
            -- aborted: keep a move only if it beat the window cleanly
            if m ~= 0 and score > alpha and score < beta then
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

Engine:SetStyle(G.Style)
_G.__AETHER_PRIME_API = Engine

return Engine

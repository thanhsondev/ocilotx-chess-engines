--!optimize 2
--!native
--[[
    OcilotX  -  chess engine for Luau / Roblox (OcilotX Chess)
    ------------------------------------------------------------------
    API (compatible with the other OcilotX engine modules):
        local Engine = <this module>
        local moveUCI, score, reaction = Engine:GetBestMoveFromFEN(fen, seconds, options)
        Engine:SetStyle(name) -> true | false
        Engine:Perft(fen, depth), Engine:GetPV(fen, maxPly), Engine:Analyze(fen, seconds, options)
        Engine:MakeMoveFEN(fen, uci), Engine:Configure({HashBits=, SliceTime=, Yield=}), Engine:NewGame()
        Engine.LastSearch = {elapsed, computeTime, depth, nodes, nps, score, move, pv, style}

    Score convention: centipawns from the point of view of the side to move in `fen`
    (positive = good for the side to move). Forced mates are reported as
    +-(30000 - pliesToMate); any |score| >= 29904 is a mate score.
    `options` is optional. Supported fields: History = {previous FENs} (for repetition
    detection; a bare array of FEN strings is accepted too), MaxDepth, NodeLimit,
    Cancel = function() -> bool, UseBook (ignored: this engine has no book).
    One engine instance must be called sequentially (no concurrent searches).

    Provenance / credits:
      * Written in 2026 for the OcilotX Chess project as a new engine. Architecture
        ideas were taken from the readable engines shipped with the project
        (Nova, Auralith Sovereign "Lith", FABLE "Null", Aether Prime "Muse" - authors
        unknown, published via github.com/jalokol/Grav) and re-implemented here:
        16x16 mailbox with upvalue state (Lith), bucketed TT with aging, gravity
        history / continuation history, singular extensions (FABLE).
      * Piece values and piece-square tables: PeSTO's evaluation function by
        Ronald Friederich (RofChade / PeSTO), published on the Chess Programming Wiki
        under CC BY-SA 3.0 (https://www.chessprogramming.org/PeSTO%27s_Evaluation_Function).
      * Search techniques follow the Chess Programming Wiki descriptions of PVS,
        aspiration windows, transposition tables, null move pruning, LMR/LMP, futility
        and reverse futility pruning, razoring, SEE, killer/countermove/history
        heuristics, check and singular extensions. No code was copied from GPL engines.
]]

local Engine = {}
Engine.Name = "OcilotX"
Engine.Version = "1.0.0"
Engine.Description = "OcilotX main engine: fail-soft PVS with aspiration windows, bucketed TT, null-move/LMR/LMP/futility pruning, SEE, singular extensions, threat-aware tapered evaluation (PeSTO tables), wall-clock time management with cooperative yielding"

local band, bor, bxor, rshift, lshift = bit32.band, bit32.bor, bit32.bxor, bit32.rshift, bit32.lshift
local floor, abs, max, min, mlog = math.floor, math.abs, math.max, math.min, math.log
local clock = os.clock
local tcreate = table.create or function(n, v)
    local t = {}
    for i = 1, n do t[i] = v end
    return t
end
local yieldFn = (type(task) == "table" and type(task.wait) == "function") and task.wait or nil

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------
local OFF = 99
local INF, MATE, MAX_PLY = 32000, 30000, 96
local MATE_BOUND = MATE - MAX_PLY          -- |score| >= MATE_BOUND  <=> forced mate
local MAX_DEPTH = 64

local FL_EP, FL_CASTLE, FL_DOUBLE, FL_CAP = 524288, 1048576, 2097152, 4194304 -- flags * 2^19
local MOVE_PROMO_UNIT = 65536

local TT_EXACT, TT_LOWER, TT_UPPER = 1, 2, 3

local KN = {33, 31, 18, 14, -14, -18, -31, -33}
local KG = {1, -1, 16, -16, 15, -15, 17, -17}
local BD = {15, 17, -15, -17}
local RD = {1, -1, 16, -16}

-- piece codes: 0 empty, 1..6 = P N B R Q K (white), 7..12 = p n b r q k (black)
local PT, PCOL = {[0] = 0, [OFF] = 0}, {[0] = 2, [OFF] = 3}
for p = 1, 12 do
    PT[p] = (p - 1) % 6 + 1
    PCOL[p] = p <= 6 and 0 or 1
end
local SEEV = {[0] = 0, 100, 325, 335, 500, 1000, 20000}   -- material used by SEE / ordering / pruning
local PHASE_INC = {[0] = 0, 0, 1, 1, 2, 4, 0}

-- squares: sq = 48 + rank*16 + file  (a1 = 48, h1 = 55, a8 = 160, h8 = 167)
local SQFILE, SQRANK, SQ64 = {}, {}, {}
for r = 0, 7 do
    for f = 0, 7 do
        local sq = 48 + r * 16 + f
        SQFILE[sq] = f
        SQRANK[sq] = r
        SQ64[#SQ64 + 1] = sq
    end
end
local A1, E1, H1, A8, E8, H8 = 48, 52, 55, 160, 164, 167

-- castling rights bits: 1 = K, 2 = Q, 4 = k, 8 = q ; CMASK[sq] clears rights when sq is touched
local CMASK = {}
for i = 0, 255 do CMASK[i] = 15 end
CMASK[E1] = 12; CMASK[A1] = 13; CMASK[H1] = 14
CMASK[E8] = 3; CMASK[A8] = 7; CMASK[H8] = 11

------------------------------------------------------------------------
-- PeSTO piece values and piece-square tables (Ronald Friederich, CC BY-SA 3.0)
-- Tables are listed from White's point of view, rank 8 first (index 0 = a8).
------------------------------------------------------------------------
local MG_VALUE = {82, 337, 365, 477, 1025, 0}
local EG_VALUE = {94, 281, 297, 512, 936, 0}
local PST_MG = {
    {  0,   0,   0,   0,   0,   0,  0,   0,
      98, 134,  61,  95,  68, 126, 34, -11,
      -6,   7,  26,  31,  65,  56, 25, -20,
     -14,  13,   6,  21,  23,  12, 17, -23,
     -27,  -2,  -5,  12,  17,   6, 10, -25,
     -26,  -4,  -4, -10,   3,   3, 33, -12,
     -35,  -1, -20, -23, -15,  24, 38, -22,
       0,   0,   0,   0,   0,   0,  0,   0},
    {-167, -89, -34, -49,  61, -97, -15, -107,
      -73, -41,  72,  36,  23,  62,   7,  -17,
      -47,  60,  37,  65,  84, 129,  73,   44,
       -9,  17,  19,  53,  37,  69,  18,   22,
      -13,   4,  16,  13,  28,  19,  21,   -8,
      -23,  -9,  12,  10,  19,  17,  25,  -16,
      -29, -53, -12,  -3,  -1,  18, -14,  -19,
     -105, -21, -58, -33, -17, -28, -19,  -23},
    { -29,   4, -82, -37, -25, -42,   7,  -8,
      -26,  16, -18, -13,  30,  59,  18, -47,
      -16,  37,  43,  40,  35,  50,  37,  -2,
       -4,   5,  19,  50,  37,  37,   7,  -2,
       -6,  13,  13,  26,  34,  12,  10,   4,
        0,  15,  15,  15,  14,  27,  18,  10,
        4,  15,  16,   0,   7,  21,  33,   1,
      -33,  -3, -14, -21, -13, -12, -39, -21},
    {  32,  42,  32,  51, 63,  9,  31,  43,
       27,  32,  58,  62, 80, 67,  26,  44,
       -5,  19,  26,  36, 17, 45,  61,  16,
      -24, -11,   7,  26, 24, 35,  -8, -20,
      -36, -26, -12,  -1,  9, -7,   6, -23,
      -45, -25, -16, -17,  3,  0,  -5, -33,
      -44, -16, -20,  -9, -1, 11,  -6, -71,
      -19, -13,   1,  17, 16,  7, -37, -26},
    { -28,   0,  29,  12,  59,  44,  43,  45,
      -24, -39,  -5,   1, -16,  57,  28,  54,
      -13, -17,   7,   8,  29,  56,  47,  57,
      -27, -27, -16, -16,  -1,  17,  -2,   1,
       -9, -26,  -9, -10,  -2,  -4,   3,  -3,
      -14,   2, -11,  -2,  -5,   2,  14,   5,
      -35,  -8,  11,   2,   8,  15,  -3,   1,
       -1, -18,  -9,  10, -15, -25, -31, -50},
    { -65,  23,  16, -15, -56, -34,   2,  13,
       29,  -1, -20,  -7,  -8,  -4, -38, -29,
       -9,  24,   2, -16, -20,   6,  22, -22,
      -17, -20, -12, -27, -30, -25, -14, -36,
      -49,  -1, -27, -39, -46, -44, -33, -51,
      -14, -14, -22, -46, -44, -30, -15, -27,
        1,   7,  -8, -64, -43, -16,   9,   8,
      -15,  36,  12, -54,   8, -28,  24,  14},
}
local PST_EG = {
    {  0,   0,   0,   0,   0,   0,   0,   0,
     178, 173, 158, 134, 147, 132, 165, 187,
      94, 100,  85,  67,  56,  53,  82,  84,
      32,  24,  13,   5,  -2,   4,  17,  17,
      13,   9,  -3,  -7,  -7,  -8,   3,  -1,
       4,   7,  -6,   1,   0,  -5,  -1,  -8,
      13,   8,   8,  10,  13,   0,   2,  -7,
       0,   0,   0,   0,   0,   0,   0,   0},
    { -58, -38, -13, -28, -31, -27, -63, -99,
      -25,  -8, -25,  -2,  -9, -25, -24, -52,
      -24, -20,  10,   9,  -1,  -9, -19, -41,
      -17,   3,  22,  22,  22,  11,   8, -18,
      -18,  -6,  16,  25,  16,  17,   4, -18,
      -23,  -3,  -1,  15,  10,  -3, -20, -22,
      -42, -20, -10,  -5,  -2, -20, -23, -44,
      -29, -51, -23, -15, -22, -18, -50, -64},
    { -14, -21, -11,  -8,  -7,  -9, -17, -24,
       -8,  -4,   7, -12,  -3, -13,  -4, -14,
        2,  -8,   0,  -1,  -2,   6,   0,   4,
       -3,   9,  12,   9,  14,  10,   3,   2,
       -6,   3,  13,  19,   7,  10,  -3,  -9,
      -12,  -3,   8,  10,  13,   3,  -7, -15,
      -14, -18,  -7,  -1,   4,  -9, -15, -27,
      -23,  -9, -23,  -5,  -9, -16,  -5, -17},
    {  13, 10, 18, 15, 12,  12,   8,   5,
       11, 13, 13, 11, -3,   3,   8,   3,
        7,  7,  7,  5,  4,  -3,  -5,  -3,
        4,  3, 13,  1,  2,   1,  -1,   2,
        3,  5,  8,  4, -5,  -6,  -8, -11,
       -4,  0, -5, -1, -7, -12,  -8, -16,
       -6, -6,  0,  2, -9,  -9, -11,  -3,
       -9,  2,  3, -1, -5, -13,   4, -20},
    {  -9,  22,  22,  27,  27,  19,  10,  20,
      -17,  20,  32,  41,  58,  25,  30,   0,
      -20,   6,   9,  49,  47,  35,  19,   9,
        3,  22,  24,  45,  57,  40,  57,  36,
      -18,  28,  19,  47,  31,  34,  39,  23,
      -16, -27,  15,   6,   9,  17,  10,   5,
      -22, -23, -30, -16, -16, -23, -36, -32,
      -33, -28, -22, -43,  -5, -32, -20, -41},
    { -74, -35, -18, -18, -11,  15,   4, -17,
      -12,  17,  14,  17,  17,  38,  23,  11,
       10,  17,  23,  15,  20,  45,  44,  13,
       -8,  22,  24,  27,  26,  33,  26,   3,
      -18,  -4,  21,  24,  27,  23,   9, -11,
      -19,  -3,  11,  21,  23,  16,   7,  -9,
      -27, -11,   4,  13,  14,   4,  -5, -17,
      -53, -34, -21, -11, -28, -14, -24, -43},
}

-- PMG/PEG[p * 256 + sq]: signed (white +, black -) material + PST, used incrementally
local PMG, PEG = {}, {}
for p = 1, 12 do
    local t, col = PT[p], PCOL[p]
    local sign = col == 0 and 1 or -1
    for i = 1, 64 do
        local sq = SQ64[i]
        local r, f = SQRANK[sq], SQFILE[sq]
        local idx = (col == 0) and ((7 - r) * 8 + f + 1) or (r * 8 + f + 1)
        PMG[p * 256 + sq] = sign * (MG_VALUE[t] + PST_MG[t][idx])
        PEG[p * 256 + sq] = sign * (EG_VALUE[t] + PST_EG[t][idx])
    end
end

------------------------------------------------------------------------
-- Zobrist keys: two independent 32-bit halves (Luau has no 64-bit integers)
------------------------------------------------------------------------
local zA, zB, zEpA, zEpB, zCA, zCB = {}, {}, {}, {}, {}, {}
local zSideA, zSideB
do
    local seed = 0x6D2B79F5
    local function rnd()
        seed = bxor(seed, lshift(seed, 13))
        seed = bxor(seed, rshift(seed, 17))
        seed = bxor(seed, lshift(seed, 5))
        return seed
    end
    for p = 1, 12 do
        for i = 1, 64 do
            local k = p * 256 + SQ64[i]
            zA[k] = rnd(); zB[k] = rnd()
        end
    end
    for f = 0, 15 do zEpA[f] = rnd(); zEpB[f] = rnd() end
    for c = 0, 15 do zCA[c] = rnd(); zCB[c] = rnd() end
    zSideA, zSideB = rnd(), rnd()
end

------------------------------------------------------------------------
-- Position state (module-level upvalues: fastest access in Luau)
------------------------------------------------------------------------
local board = {}
for i = 0, 255 do board[i] = OFF end
local side, castle, ep, halfmove = 0, 0, -1, 0
local kingSq = {[0] = -1, [1] = -1}
local h1, h2 = 0, 0
local mgS, egS, phase = 0, 0, 0
local npm = {[0] = 0, [1] = 0}          -- non-pawn material per colour (SEEV units)
local cnt = {}                           -- piece counts by piece code
for p = 0, 12 do cnt[p] = 0 end
local gamePly = 0                        -- index into the stack / hash history

-- stack (indexed by gamePly)
local sMove, sCap, sCastle, sEp, sHalf, sH1, sH2 = {}, {}, {}, {}, {}, {}, {}
local sMg, sEg, sPh, sN0, sN1 = {}, {}, {}, {}, {}
local hA, hB = {}, {}                    -- hash history for repetition detection

local function addPiece(p, sq)
    board[sq] = p
    local k = p * 256 + sq
    h1 = bxor(h1, zA[k]); h2 = bxor(h2, zB[k])
    mgS = mgS + PMG[k]; egS = egS + PEG[k]
    local t = PT[p]
    phase = phase + PHASE_INC[t]
    cnt[p] = cnt[p] + 1
    if t ~= 1 and t ~= 6 then
        local c = PCOL[p]
        npm[c] = npm[c] + SEEV[t]
    end
end

local function removePiece(p, sq)
    board[sq] = 0
    local k = p * 256 + sq
    h1 = bxor(h1, zA[k]); h2 = bxor(h2, zB[k])
    mgS = mgS - PMG[k]; egS = egS - PEG[k]
    local t = PT[p]
    phase = phase - PHASE_INC[t]
    cnt[p] = cnt[p] - 1
    if t ~= 1 and t ~= 6 then
        local c = PCOL[p]
        npm[c] = npm[c] - SEEV[t]
    end
end

-- is `sq` attacked by colour `by` (0 white, 1 black)?
local function attacked(sq, by)
    if by == 0 then
        if board[sq - 15] == 1 or board[sq - 17] == 1 then return true end
    else
        if board[sq + 15] == 7 or board[sq + 17] == 7 then return true end
    end
    local base = by * 6
    local kn, kg, bi, ro, qu = 2 + base, 6 + base, 3 + base, 4 + base, 5 + base
    for i = 1, 8 do
        if board[sq + KN[i]] == kn then return true end
        if board[sq + KG[i]] == kg then return true end
    end
    for i = 1, 4 do
        local d = BD[i]
        local s = sq + d
        while board[s] == 0 do s = s + d end
        local p = board[s]
        if p == bi or p == qu then return true end
        d = RD[i]
        s = sq + d
        while board[s] == 0 do s = s + d end
        p = board[s]
        if p == ro or p == qu then return true end
    end
    return false
end

------------------------------------------------------------------------
-- Make / unmake.  Move encoding: from + to*256 + promo*65536 + flags*524288
------------------------------------------------------------------------
local function makeMove(m)
    local gp = gamePly
    sMove[gp] = m; sCastle[gp] = castle; sEp[gp] = ep; sHalf[gp] = halfmove
    sH1[gp] = h1; sH2[gp] = h2; sMg[gp] = mgS; sEg[gp] = egS; sPh[gp] = phase
    sN0[gp] = npm[0]; sN1[gp] = npm[1]

    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    local promo = band(rshift(m, 16), 7)
    local flags = rshift(m, 19)
    local piece, cap = board[from], board[to]
    sCap[gp] = cap
    local us = side

    if ep >= 0 then
        local f = ep % 16
        h1 = bxor(h1, zEpA[f]); h2 = bxor(h2, zEpB[f])
    end
    h1 = bxor(h1, zCA[castle]); h2 = bxor(h2, zCB[castle])

    if cap ~= 0 then removePiece(cap, to) end
    removePiece(piece, from)
    if promo ~= 0 then addPiece(promo + us * 6, to) else addPiece(piece, to) end

    if band(flags, 1) ~= 0 then               -- en passant: remove the captured pawn
        local cs = (us == 0) and (to - 16) or (to + 16)
        removePiece(board[cs], cs)
    end
    if band(flags, 2) ~= 0 then               -- castling: move the rook
        local rf, rt
        if to > from then rf, rt = from + 3, from + 1 else rf, rt = from - 4, from - 1 end
        local rook = board[rf]
        removePiece(rook, rf)
        addPiece(rook, rt)
    end

    if PT[piece] == 6 then kingSq[us] = to end
    castle = band(castle, CMASK[from], CMASK[to])
    if band(flags, 4) ~= 0 then ep = (us == 0) and (from + 16) or (from - 16) else ep = -1 end
    if PT[piece] == 1 or cap ~= 0 or band(flags, 1) ~= 0 then halfmove = 0 else halfmove = halfmove + 1 end

    h1 = bxor(h1, zCA[castle]); h2 = bxor(h2, zCB[castle])
    if ep >= 0 then
        local f = ep % 16
        h1 = bxor(h1, zEpA[f]); h2 = bxor(h2, zEpB[f])
    end
    side = 1 - us
    h1 = bxor(h1, zSideA); h2 = bxor(h2, zSideB)
    gamePly = gp + 1
    hA[gp + 1] = h1; hB[gp + 1] = h2
end

local function unmakeMove()
    gamePly = gamePly - 1
    local gp = gamePly
    local m = sMove[gp]
    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    local promo = band(rshift(m, 16), 7)
    local flags = rshift(m, 19)
    side = 1 - side
    local us = side
    local piece = board[to]
    if promo ~= 0 then
        cnt[piece] = cnt[piece] - 1
        piece = 1 + us * 6
        cnt[piece] = cnt[piece] + 1
    end
    board[from] = piece
    local cap = sCap[gp]
    if band(flags, 1) ~= 0 then
        board[to] = 0
        if us == 0 then board[to - 16] = 7; cnt[7] = cnt[7] + 1 else board[to + 16] = 1; cnt[1] = cnt[1] + 1 end
    else
        board[to] = cap
        if cap ~= 0 then cnt[cap] = cnt[cap] + 1 end
    end
    if band(flags, 2) ~= 0 then
        local rf, rt
        if to > from then rf, rt = from + 3, from + 1 else rf, rt = from - 4, from - 1 end
        board[rf] = board[rt]
        board[rt] = 0
    end
    if PT[piece] == 6 then kingSq[us] = from end
    castle = sCastle[gp]; ep = sEp[gp]; halfmove = sHalf[gp]
    h1 = sH1[gp]; h2 = sH2[gp]; mgS = sMg[gp]; egS = sEg[gp]; phase = sPh[gp]
    npm[0] = sN0[gp]; npm[1] = sN1[gp]
end

local function makeNull()
    local gp = gamePly
    sMove[gp] = 0; sEp[gp] = ep; sHalf[gp] = halfmove; sH1[gp] = h1; sH2[gp] = h2
    if ep >= 0 then
        local f = ep % 16
        h1 = bxor(h1, zEpA[f]); h2 = bxor(h2, zEpB[f])
    end
    ep = -1
    halfmove = halfmove + 1
    side = 1 - side
    h1 = bxor(h1, zSideA); h2 = bxor(h2, zSideB)
    gamePly = gp + 1
    hA[gp + 1] = h1; hB[gp + 1] = h2
end

local function unmakeNull()
    gamePly = gamePly - 1
    local gp = gamePly
    side = 1 - side
    ep = sEp[gp]; halfmove = sHalf[gp]; h1 = sH1[gp]; h2 = sH2[gp]
end

------------------------------------------------------------------------
-- Move generation into preallocated per-ply buffers (pseudo-legal)
------------------------------------------------------------------------
local mvList, mvScore = {}, {}
for i = 0, MAX_PLY + 4 do mvList[i] = {}; mvScore[i] = {} end
local exList, exScore = {}, {}          -- separate buffers for singular (exclusion) searches
for i = 0, MAX_PLY + 4 do exList[i] = {}; exScore[i] = {} end

local function genMoves(list, capsOnly)
    local n = 0
    local us = side
    local them = 1 - us
    local bd = board
    for i = 1, 64 do
        local sq = SQ64[i]
        local p = bd[sq]
        if p ~= 0 and PCOL[p] == us then
            local t = PT[p]
            if t == 1 then
                local r = SQRANK[sq]
                local dir = (us == 0) and 16 or -16
                local promoFrom = (us == 0) and 6 or 1
                local startR = (us == 0) and 1 or 6
                local one = sq + dir
                if bd[one] == 0 then
                    if r == promoFrom then
                        n = n + 1; list[n] = sq + one * 256 + 5 * MOVE_PROMO_UNIT
                        if not capsOnly then
                            n = n + 1; list[n] = sq + one * 256 + 2 * MOVE_PROMO_UNIT
                            n = n + 1; list[n] = sq + one * 256 + 4 * MOVE_PROMO_UNIT
                            n = n + 1; list[n] = sq + one * 256 + 3 * MOVE_PROMO_UNIT
                        end
                    elseif not capsOnly then
                        n = n + 1; list[n] = sq + one * 256
                        if r == startR and bd[one + dir] == 0 then
                            n = n + 1; list[n] = sq + (one + dir) * 256 + FL_DOUBLE
                        end
                    end
                end
                for k = -1, 1, 2 do
                    local to = one + k
                    local tp = bd[to]
                    if tp ~= 0 and tp ~= OFF and PCOL[tp] == them then
                        if r == promoFrom then
                            n = n + 1; list[n] = sq + to * 256 + 5 * MOVE_PROMO_UNIT + FL_CAP
                            if not capsOnly then
                                n = n + 1; list[n] = sq + to * 256 + 2 * MOVE_PROMO_UNIT + FL_CAP
                                n = n + 1; list[n] = sq + to * 256 + 4 * MOVE_PROMO_UNIT + FL_CAP
                                n = n + 1; list[n] = sq + to * 256 + 3 * MOVE_PROMO_UNIT + FL_CAP
                            end
                        else
                            n = n + 1; list[n] = sq + to * 256 + FL_CAP
                        end
                    elseif to == ep then
                        n = n + 1; list[n] = sq + to * 256 + FL_EP + FL_CAP
                    end
                end
            elseif t == 2 then
                for k = 1, 8 do
                    local to = sq + KN[k]
                    local tp = bd[to]
                    if tp == 0 then
                        if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                    elseif PCOL[tp] == them then
                        n = n + 1; list[n] = sq + to * 256 + FL_CAP
                    end
                end
            elseif t == 6 then
                for k = 1, 8 do
                    local to = sq + KG[k]
                    local tp = bd[to]
                    if tp == 0 then
                        if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                    elseif PCOL[tp] == them then
                        n = n + 1; list[n] = sq + to * 256 + FL_CAP
                    end
                end
                if not capsOnly and castle ~= 0 then
                    if us == 0 and sq == E1 then
                        if band(castle, 1) ~= 0 and bd[53] == 0 and bd[54] == 0 and bd[H1] == 4
                            and not attacked(52, 1) and not attacked(53, 1) and not attacked(54, 1) then
                            n = n + 1; list[n] = 52 + 54 * 256 + FL_CASTLE
                        end
                        if band(castle, 2) ~= 0 and bd[51] == 0 and bd[50] == 0 and bd[49] == 0 and bd[A1] == 4
                            and not attacked(52, 1) and not attacked(51, 1) and not attacked(50, 1) then
                            n = n + 1; list[n] = 52 + 50 * 256 + FL_CASTLE
                        end
                    elseif us == 1 and sq == E8 then
                        if band(castle, 4) ~= 0 and bd[165] == 0 and bd[166] == 0 and bd[H8] == 10
                            and not attacked(164, 0) and not attacked(165, 0) and not attacked(166, 0) then
                            n = n + 1; list[n] = 164 + 166 * 256 + FL_CASTLE
                        end
                        if band(castle, 8) ~= 0 and bd[163] == 0 and bd[162] == 0 and bd[161] == 0 and bd[A8] == 10
                            and not attacked(164, 0) and not attacked(163, 0) and not attacked(162, 0) then
                            n = n + 1; list[n] = 164 + 162 * 256 + FL_CASTLE
                        end
                    end
                end
            else
                if t ~= 4 then
                    for k = 1, 4 do
                        local d = BD[k]
                        local to = sq + d
                        local tp = bd[to]
                        while tp == 0 do
                            if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                            to = to + d
                            tp = bd[to]
                        end
                        if tp ~= OFF and PCOL[tp] == them then n = n + 1; list[n] = sq + to * 256 + FL_CAP end
                    end
                end
                if t ~= 3 then
                    for k = 1, 4 do
                        local d = RD[k]
                        local to = sq + d
                        local tp = bd[to]
                        while tp == 0 do
                            if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                            to = to + d
                            tp = bd[to]
                        end
                        if tp ~= OFF and PCOL[tp] == them then n = n + 1; list[n] = sq + to * 256 + FL_CAP end
                    end
                end
            end
        end
    end
    return n
end

-- is move m pseudo-legal in the current position? (lets the search try a TT move before
-- generating the move list; TT moves may come from hash collisions, so everything is checked)
local function pseudoLegal(m)
    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    if not SQFILE[from] or not SQFILE[to] or from == to then return false end
    local promo = band(rshift(m, 16), 7)
    local flags = rshift(m, 19)
    local piece = board[from]
    if piece == 0 or PCOL[piece] ~= side then return false end
    local target = board[to]
    local t = PT[piece]
    local us = side
    if band(flags, 1) ~= 0 then                       -- en passant
        if t ~= 1 or to ~= ep or target ~= 0 then return false end
        local d = to - from
        return (us == 0 and (d == 15 or d == 17)) or (us == 1 and (d == -15 or d == -17))
    end
    if band(flags, 8) ~= 0 then
        if target == 0 or PCOL[target] ~= 1 - us then return false end
    elseif target ~= 0 then
        return false
    end
    if band(flags, 2) ~= 0 then                       -- castling: full re-validation
        if t ~= 6 or promo ~= 0 then return false end
        if us == 0 then
            if from ~= E1 then return false end
            if to == 54 then
                return band(castle, 1) ~= 0 and board[53] == 0 and board[54] == 0 and board[H1] == 4
                    and not attacked(52, 1) and not attacked(53, 1) and not attacked(54, 1)
            elseif to == 50 then
                return band(castle, 2) ~= 0 and board[51] == 0 and board[50] == 0 and board[49] == 0 and board[A1] == 4
                    and not attacked(52, 1) and not attacked(51, 1) and not attacked(50, 1)
            end
            return false
        else
            if from ~= E8 then return false end
            if to == 166 then
                return band(castle, 4) ~= 0 and board[165] == 0 and board[166] == 0 and board[H8] == 10
                    and not attacked(164, 0) and not attacked(165, 0) and not attacked(166, 0)
            elseif to == 162 then
                return band(castle, 8) ~= 0 and board[163] == 0 and board[162] == 0 and board[161] == 0 and board[A8] == 10
                    and not attacked(164, 0) and not attacked(163, 0) and not attacked(162, 0)
            end
            return false
        end
    end
    if band(flags, 4) ~= 0 then                       -- double pawn push
        if t ~= 1 or promo ~= 0 or target ~= 0 then return false end
        local dir = (us == 0) and 16 or -16
        return SQRANK[from] == ((us == 0) and 1 or 6) and to == from + 2 * dir and board[from + dir] == 0
    end
    if t == 1 then
        local dir = (us == 0) and 16 or -16
        local promoRank = (us == 0) and 7 or 0
        if (SQRANK[to] == promoRank) ~= (promo ~= 0) then return false end
        if promo ~= 0 and (promo < 2 or promo > 5) then return false end
        if band(flags, 8) ~= 0 then return to == from + dir - 1 or to == from + dir + 1 end
        return to == from + dir
    end
    if promo ~= 0 then return false end
    local d = to - from
    if t == 2 then
        for i = 1, 8 do if KN[i] == d then return true end end
        return false
    elseif t == 6 then
        for i = 1, 8 do if KG[i] == d then return true end end
        return false
    end
    local df, dr = SQFILE[to] - SQFILE[from], SQRANK[to] - SQRANK[from]
    local step
    if df == 0 then step = (dr > 0) and 16 or -16
    elseif dr == 0 then step = (df > 0) and 1 or -1
    elseif df == dr then step = (df > 0) and 17 or -17
    elseif df == -dr then step = (df > 0) and -15 or 15
    else return false end
    local diag = (step == 15 or step == -15 or step == 17 or step == -17)
    if (t == 3 and not diag) or (t == 4 and diag) then return false end
    local s = from + step
    while s ~= to do
        if board[s] ~= 0 then return false end
        s = s + step
    end
    return true
end

------------------------------------------------------------------------
-- Static Exchange Evaluation (x-rays handled by removing pieces from the board)
------------------------------------------------------------------------
local function leastAttacker(sq, by)
    if by == 0 then
        if board[sq - 15] == 1 then return sq - 15 end
        if board[sq - 17] == 1 then return sq - 17 end
    else
        if board[sq + 15] == 7 then return sq + 15 end
        if board[sq + 17] == 7 then return sq + 17 end
    end
    local base = by * 6
    local kn = 2 + base
    for i = 1, 8 do
        local s = sq + KN[i]
        if board[s] == kn then return s end
    end
    local bi, ro, qu, kg = 3 + base, 4 + base, 5 + base, 6 + base
    local rookSq, queenSq
    for i = 1, 4 do
        local d = BD[i]
        local s = sq + d
        while board[s] == 0 do s = s + d end
        local p = board[s]
        if p == bi then return s elseif p == qu then queenSq = queenSq or s end
    end
    for i = 1, 4 do
        local d = RD[i]
        local s = sq + d
        while board[s] == 0 do s = s + d end
        local p = board[s]
        if p == ro then rookSq = rookSq or s elseif p == qu then queenSq = queenSq or s end
    end
    if rookSq then return rookSq end
    if queenSq then return queenSq end
    for i = 1, 8 do
        local s = sq + KG[i]
        if board[s] == kg then return s end
    end
    return nil
end

local seeGain, seeSq, seePc = {}, {}, {}
local function see(m)
    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    local promo = band(rshift(m, 16), 7)
    local flags = rshift(m, 19)
    local piece = board[from]
    local captured = board[to]
    local gain0 = (band(flags, 1) ~= 0) and 100 or SEEV[PT[captured]]
    local aVal = SEEV[PT[piece]]
    if promo ~= 0 then
        gain0 = gain0 + SEEV[promo] - 100
        aVal = SEEV[promo]
    end
    seeGain[0] = gain0
    local stm = 1 - PCOL[piece]
    -- lift the mover off the board; the target square keeps the victim (irrelevant for attacks)
    seeSq[1] = from; seePc[1] = piece; board[from] = 0
    local removed = 1
    local d = 0
    while true do
        d = d + 1
        seeGain[d] = aVal - seeGain[d - 1]
        if max(-seeGain[d - 1], seeGain[d]) < 0 then break end
        local s = leastAttacker(to, stm)
        if not s then break end
        local ap = board[s]
        aVal = SEEV[PT[ap]]
        if PT[ap] == 6 then
            -- a king may only capture if the other side has no further attackers
            board[s] = 0
            local reply = leastAttacker(to, 1 - stm)
            board[s] = ap
            if reply then break end
        end
        removed = removed + 1
        seeSq[removed] = s; seePc[removed] = ap
        board[s] = 0
        stm = 1 - stm
    end
    for i = 1, removed do board[seeSq[i]] = seePc[i] end
    d = d - 1
    while d > 0 do
        seeGain[d - 1] = -max(-seeGain[d - 1], seeGain[d])
        d = d - 1
    end
    return seeGain[0]
end

------------------------------------------------------------------------
-- Styles: evaluation weights + search/contempt parameters.
-- Every style keeps full legality and the same search; it only re-weights terms.
------------------------------------------------------------------------
local STYLES = {
    --            king attack, own king safety, mobility, pawn structure, passed pawns, threats, contempt, checksInQS, pawnValue, knightBonus
    Balanced     = {att = 1.00, safe = 1.00, mob = 1.00, pawn = 1.00, passed = 1.00, threat = 1.00, contempt = 6,  qchecks = false, pawnScale = 1.00, knight = 0, trade = 0},
    Aggressive   = {att = 1.30, safe = 0.90, mob = 1.10, pawn = 0.90, passed = 1.00, threat = 1.10, contempt = 18, qchecks = true,  pawnScale = 0.97, knight = 0, trade = 0},
    Calm         = {att = 0.85, safe = 1.15, mob = 1.00, pawn = 1.10, passed = 1.00, threat = 1.00, contempt = 0,  qchecks = false, pawnScale = 1.00, knight = 0, trade = 0},
    Defensive    = {att = 0.75, safe = 1.40, mob = 0.95, pawn = 1.10, passed = 0.95, threat = 1.30, contempt = -8, qchecks = false, pawnScale = 1.00, knight = 0, trade = 0},
    Tactical     = {att = 1.20, safe = 0.95, mob = 1.15, pawn = 0.90, passed = 1.00, threat = 1.20, contempt = 12, qchecks = true,  pawnScale = 1.00, knight = 0, trade = 0},
    Trickery     = {att = 1.20, safe = 0.90, mob = 1.15, pawn = 0.85, passed = 1.00, threat = 1.35, contempt = 24, qchecks = true,  pawnScale = 0.98, knight = 0, trade = 0},
    Positional   = {att = 0.85, safe = 1.05, mob = 1.25, pawn = 1.35, passed = 1.10, threat = 1.00, contempt = 4,  qchecks = false, pawnScale = 1.00, knight = 0, trade = 0},
    Endgame      = {att = 0.80, safe = 0.90, mob = 1.00, pawn = 1.20, passed = 1.35, threat = 1.00, contempt = 0,  qchecks = false, pawnScale = 1.03, knight = 0, trade = 1},
    ["Alien Gambit"] = {att = 1.45, safe = 0.80, mob = 1.20, pawn = 0.80, passed = 1.00, threat = 1.15, contempt = 30, qchecks = true, pawnScale = 0.90, knight = 0, trade = 0},
    ["Willy Alien"]  = {att = 1.35, safe = 0.85, mob = 1.25, pawn = 0.85, passed = 1.00, threat = 1.15, contempt = 30, qchecks = true, pawnScale = 0.95, knight = 12, trade = 0},
}
local W = STYLES.Balanced
local contempt = W.contempt

------------------------------------------------------------------------
-- Evaluation
------------------------------------------------------------------------
local PASS_MG = {[0] = 0, 2, 6, 12, 26, 52, 92, 0}
local PASS_EG = {[0] = 0, 10, 18, 32, 58, 102, 164, 0}
local MOB_N_MG, MOB_N_EG = 4, 4
local MOB_B_MG, MOB_B_EG = 4, 5
local MOB_R_MG, MOB_R_EG = 2, 4
local MOB_Q_MG, MOB_Q_EG = 1, 2
local ATT_W = {[0] = 0, 0, 2, 2, 3, 5, 0}     -- king-zone attack units per attacking piece type
local LAZY_MARGIN = 420
local TEMPO = 10

-- scratch (reused between calls, no allocation per evaluation)
local wFile, bFile = {}, {}               -- pawn counts per file (index 1..8, sentinels 0 and 9)
local wMinR, bMaxR = {}, {}               -- least advanced white pawn rank / most advanced black pawn rank per file
local pawn0, pawn1, pieceSq = {}, {}, {}  -- square lists
local aStamp0, aMin0 = {}, {}             -- attack maps: stamp, minimum attacker value (white)
local aStamp1, aMin1 = {}, {}             -- (black)
local EVAL_CACHE = 131072
local eKey1, eKey2, eVal = tcreate(EVAL_CACHE, -1), tcreate(EVAL_CACHE, -1), tcreate(EVAL_CACHE, 0)   -- evaluation cache
local zone0, zone1 = {}, {}               -- king zone stamps (zone0 = squares around the white king)
local evalStamp = 0
for i = 0, 255 do
    aStamp0[i] = 0; aMin0[i] = 0
    aStamp1[i] = 0; aMin1[i] = 0
    zone0[i] = 0; zone1[i] = 0
end

local function kdist(a, b)
    local df = abs(SQFILE[a] - SQFILE[b])
    local dr = abs(SQRANK[a] - SQRANK[b])
    return df > dr and df or dr
end

local function safetyCurve(units)
    if units <= 0 then return 0 end
    if units <= 30 then return floor(units * units / 3) end
    return min(600, 300 + (units - 30) * 12)
end

-- King shelter and pawn storm for `col` whose king is on ksq (middlegame only)
local function kingShelter(col, ksq, ownFile, enemyFile)
    local kf, kr = SQFILE[ksq], SQRANK[ksq]
    local rr = (col == 0) and kr or 7 - kr
    if rr > 2 then return -14 * (rr - 2) end       -- king walked forward: exposed
    local ownP = (col == 0) and 1 or 7
    local enP = (col == 0) and 7 or 1
    local dir = (col == 0) and 16 or -16
    local s = 0
    for f = max(0, kf - 1), min(7, kf + 1) do
        local base = ksq + (f - kf)
        local sq1, sq2 = base + dir, base + 2 * dir
        if board[sq1] == ownP then s = s + 14
        elseif board[sq2] == ownP then s = s + 7
        else
            s = s - 14
            if ownFile[f + 1] == 0 then
                s = s - 10
                if enemyFile[f + 1] == 0 then s = s - 10 end   -- fully open file next to the king
            end
        end
        -- pawn storm: enemy pawns close to the king on this file
        local st = base + dir
        for k = 1, 3 do
            if board[st] == enP then
                s = s - (k == 1 and 16 or (k == 2 and 10 or 5))
                break
            end
            st = st + dir
        end
    end
    return s
end

local function evaluateRaw()
    local mg, eg = mgS, egS
    local ph = phase
    if ph > 24 then ph = 24 end

    -- material-only quick exits ------------------------------------------------
    local nW, nB = cnt[1], cnt[7]
    local npm0, npm1 = npm[0], npm[1]
    if nW == 0 and nB == 0 then
        if npm0 <= 335 and npm1 <= 335 then return 0 end                            -- K(+minor) vs K(+minor)
        if npm0 + npm1 == 650 and (cnt[2] == 2 or cnt[8] == 2) then return 0 end     -- KNN vs K
    end

    evalStamp = evalStamp + 1
    local stamp = evalStamp
    for i = 0, 9 do wFile[i] = 0; bFile[i] = 0; wMinR[i] = 8; bMaxR[i] = -1 end

    local nP, nPW, nPB = 0, 0, 0
    local wk, bk = kingSq[0], kingSq[1]
    local bd = board

    -- pawns: lists, file info, pawn attack maps (pawns are the cheapest attackers -> fill minimum first)
    for i = 1, 64 do
        local sq = SQ64[i]
        local p = bd[sq]
        if p ~= 0 then
            if p == 1 then
                local fi = SQFILE[sq] + 1
                wFile[fi] = wFile[fi] + 1
                local r = SQRANK[sq]
                if r < wMinR[fi] then wMinR[fi] = r end
                nPW = nPW + 1
                pawn0[nPW] = sq
                for k = 15, 17, 2 do
                    local a = sq + k
                    aStamp0[a] = stamp; aMin0[a] = 100
                end
            elseif p == 7 then
                local fi = SQFILE[sq] + 1
                bFile[fi] = bFile[fi] + 1
                local r = SQRANK[sq]
                if r > bMaxR[fi] then bMaxR[fi] = r end
                nPB = nPB + 1
                pawn1[nPB] = sq
                for k = 15, 17, 2 do
                    local a = sq - k
                    aStamp1[a] = stamp; aMin1[a] = 100
                end
            elseif p ~= 6 and p ~= 12 then
                nP = nP + 1
                pieceSq[nP] = sq
            end
        end
    end

    -- king zones (king square + neighbours + one more rank towards the enemy)
    zone0[wk] = stamp; zone1[bk] = stamp
    for i = 1, 8 do zone0[wk + KG[i]] = stamp; zone1[bk + KG[i]] = stamp end
    for d = -1, 1 do zone0[wk + 32 + d] = stamp; zone1[bk - 32 + d] = stamp end
    -- king attacks (kings defend their zone)
    for i = 1, 8 do
        local a = wk + KG[i]
        if SQFILE[a] and aStamp0[a] ~= stamp then aStamp0[a] = stamp; aMin0[a] = 20000 end
        a = bk + KG[i]
        if SQFILE[a] and aStamp1[a] ~= stamp then aStamp1[a] = stamp; aMin1[a] = 20000 end
    end

    local wPawn, wPassed = W.pawn, W.passed
    local pMg, pEg = 0, 0                 -- pawn structure (white minus black)

    -- white pawns ---------------------------------------------------------------
    for i = 1, nPW do
        local sq = pawn0[i]
        local f, r = SQFILE[sq], SQRANK[sq]
        local fi = f + 1
        local supported = (bd[sq - 15] == 1 or bd[sq - 17] == 1)
        local phalanx = (bd[sq - 1] == 1 or bd[sq + 1] == 1)
        if wFile[fi - 1] == 0 and wFile[fi + 1] == 0 then pMg = pMg - 10; pEg = pEg - 16 end
        if supported then pMg = pMg + 3 + r * 2; pEg = pEg + 4 + r * 2
        elseif phalanx then pMg = pMg + 2 + r; pEg = pEg + 3 + r end
        -- backward: cannot be supported, stop square attacked by an enemy pawn
        if not supported and not phalanx and wMinR[fi - 1] >= r and wMinR[fi + 1] >= r then
            local stop = sq + 16
            if bd[stop - 15] == 7 or bd[stop - 17] == 7 or bd[stop + 15] == 7 or bd[stop + 17] == 7 then
                pMg = pMg - 8; pEg = pEg - 12
                if bFile[fi] == 0 then pMg = pMg - 8 end
            end
        end
        if bMaxR[fi - 1] <= r and bMaxR[fi] <= r and bMaxR[fi + 1] <= r then
            local bm, be = PASS_MG[r], PASS_EG[r]
            local stop = sq + 16
            if bd[stop] ~= 0 then bm = bm * 0.6; be = be * 0.6
            elseif aStamp1[stop] == stamp and aStamp0[stop] ~= stamp then bm = bm * 0.75; be = be * 0.75 end
            if supported or phalanx then be = be + r * 4 end
            if r >= 2 then be = be + (kdist(bk, stop) * 5 - kdist(wk, stop) * 2) * r * 0.5 end
            -- rook behind the passer
            local s = sq - 16
            while bd[s] == 0 do s = s - 16 end
            if bd[s] == 4 then be = be + 16 elseif bd[s] == 10 then be = be - 14 end
            -- unstoppable passer in a pawn ending (rule of the square incl. tempo)
            if npm1 == 0 and r >= 1 then
                local clear, t = true, stop
                while SQFILE[t] do
                    if bd[t] ~= 0 then clear = false; break end
                    t = t + 16
                end
                if clear then
                    local promo = 160 + f
                    local dist = 7 - r
                    if r == 1 then dist = dist - 1 end
                    if side == 1 then dist = dist + 1 end
                    if dist < kdist(bk, promo) then be = be + 320 end
                end
            end
            pMg = pMg + bm * wPassed; pEg = pEg + be * wPassed
        end
    end
    -- black pawns ---------------------------------------------------------------
    for i = 1, nPB do
        local sq = pawn1[i]
        local f, r = SQFILE[sq], SQRANK[sq]
        local rr = 7 - r
        local fi = f + 1
        local supported = (bd[sq + 15] == 7 or bd[sq + 17] == 7)
        local phalanx = (bd[sq - 1] == 7 or bd[sq + 1] == 7)
        if bFile[fi - 1] == 0 and bFile[fi + 1] == 0 then pMg = pMg + 10; pEg = pEg + 16 end
        if supported then pMg = pMg - (3 + rr * 2); pEg = pEg - (4 + rr * 2)
        elseif phalanx then pMg = pMg - (2 + rr); pEg = pEg - (3 + rr) end
        if not supported and not phalanx and bMaxR[fi - 1] <= r and bMaxR[fi + 1] <= r then
            local stop = sq - 16
            if bd[stop + 15] == 1 or bd[stop + 17] == 1 or bd[stop - 15] == 1 or bd[stop - 17] == 1 then
                pMg = pMg + 8; pEg = pEg + 12
                if wFile[fi] == 0 then pMg = pMg + 8 end
            end
        end
        if wMinR[fi - 1] >= r and wMinR[fi] >= r and wMinR[fi + 1] >= r then
            local bm, be = PASS_MG[rr], PASS_EG[rr]
            local stop = sq - 16
            if bd[stop] ~= 0 then bm = bm * 0.6; be = be * 0.6
            elseif aStamp0[stop] == stamp and aStamp1[stop] ~= stamp then bm = bm * 0.75; be = be * 0.75 end
            if supported or phalanx then be = be + rr * 4 end
            if rr >= 2 then be = be + (kdist(wk, stop) * 5 - kdist(bk, stop) * 2) * rr * 0.5 end
            local s = sq + 16
            while bd[s] == 0 do s = s + 16 end
            if bd[s] == 10 then be = be + 16 elseif bd[s] == 4 then be = be - 14 end
            if npm0 == 0 and rr >= 1 then
                local clear, t = true, stop
                while SQFILE[t] do
                    if bd[t] ~= 0 then clear = false; break end
                    t = t - 16
                end
                if clear then
                    local promo = 48 + f
                    local dist = 7 - rr
                    if rr == 1 then dist = dist - 1 end
                    if side == 0 then dist = dist + 1 end
                    if dist < kdist(wk, promo) then be = be + 320 end
                end
            end
            pMg = pMg - bm * wPassed; pEg = pEg - be * wPassed
        end
    end
    for fi = 1, 8 do
        local c = wFile[fi]
        if c > 1 then pMg = pMg - (c - 1) * 10; pEg = pEg - (c - 1) * 20 end
        c = bFile[fi]
        if c > 1 then pMg = pMg + (c - 1) * 10; pEg = pEg + (c - 1) * 20 end
    end
    mg = mg + pMg * wPawn; eg = eg + pEg * wPawn

    -- pieces: mobility, attack maps, king-zone pressure, outposts, rook files ----
    local wMob = W.mob
    local units0, atk0, units1, atk1 = 0, 0, 0, 0        -- attack units against the black king (by white) / white king (by black)
    local bishopsW0, bishopsW1 = 0, 0                     -- light/dark squared white bishops
    local bishopsB0, bishopsB1 = 0, 0
    local pcMg, pcEg = 0, 0
    for i = 1, nP do
        local sq = pieceSq[i]
        local p = bd[sq]
        local t = PT[p]
        local col = PCOL[p]
        local f, r = SQFILE[sq], SQRANK[sq]
        local rr = (col == 0) and r or 7 - r
        local aStamp, aMin, zone
        if col == 0 then aStamp, aMin, zone = aStamp0, aMin0, zone1
        else aStamp, aMin, zone = aStamp1, aMin1, zone0 end
        local val = SEEV[t]
        local mob, hits = 0, 0
        local tm, te = 0, 0
        if t == 2 then
            for k = 1, 8 do
                local to = sq + KN[k]
                local tp = bd[to]
                if tp ~= OFF then
                    if aStamp[to] ~= stamp then aStamp[to] = stamp; aMin[to] = val elseif val < aMin[to] then aMin[to] = val end
                    if zone[to] == stamp then hits = hits + 1 end
                    if PCOL[tp] ~= col then
                        local pawnAtk = (col == 0) and (bd[to + 15] == 7 or bd[to + 17] == 7) or (col == 1) and (bd[to - 15] == 1 or bd[to - 17] == 1)
                        if not pawnAtk then mob = mob + 1 end
                    end
                end
            end
            tm = (mob - 4) * MOB_N_MG; te = (mob - 4) * MOB_N_EG
            tm = tm + W.knight
            -- outpost: protected by a pawn, cannot be attacked by enemy pawns
            if rr >= 3 and rr <= 5 then
                local prot, safe
                if col == 0 then
                    prot = bd[sq - 15] == 1 or bd[sq - 17] == 1
                    safe = bMaxR[f] <= r and bMaxR[f + 2] <= r
                else
                    prot = bd[sq + 15] == 7 or bd[sq + 17] == 7
                    safe = wMinR[f] >= r and wMinR[f + 2] >= r
                end
                if prot and safe then tm = tm + 26; te = te + 12 end
            end
        elseif t == 3 then
            for k = 1, 4 do
                local d = BD[k]
                local to = sq + d
                local tp = bd[to]
                while tp ~= OFF do
                    if aStamp[to] ~= stamp then aStamp[to] = stamp; aMin[to] = val elseif val < aMin[to] then aMin[to] = val end
                    if zone[to] == stamp then hits = hits + 1 end
                    if PCOL[tp] ~= col then
                        local pawnAtk = (col == 0) and (bd[to + 15] == 7 or bd[to + 17] == 7) or (col == 1) and (bd[to - 15] == 1 or bd[to - 17] == 1)
                        if not pawnAtk then mob = mob + 1 end
                    end
                    if tp ~= 0 then break end
                    to = to + d
                    tp = bd[to]
                end
            end
            tm = (mob - 6) * MOB_B_MG; te = (mob - 6) * MOB_B_EG
            local dark = (f + r) % 2 == 0
            if col == 0 then
                if dark then bishopsW0 = bishopsW0 + 1 else bishopsW1 = bishopsW1 + 1 end
            else
                if dark then bishopsB0 = bishopsB0 + 1 else bishopsB1 = bishopsB1 + 1 end
            end
            -- bad bishop: own pawns on the bishop's colour (centre pawns weigh more)
            local same = 0
            local list, n = (col == 0) and pawn0 or pawn1, (col == 0) and nPW or nPB
            for j = 1, n do
                local ps = list[j]
                if ((SQFILE[ps] + SQRANK[ps]) % 2 == 0) == dark then same = same + 1 end
            end
            if same > 2 then tm = tm - (same - 2) * 3; te = te - (same - 2) * 5 end
            if rr >= 3 and rr <= 5 then
                local prot, safe
                if col == 0 then
                    prot = bd[sq - 15] == 1 or bd[sq - 17] == 1
                    safe = bMaxR[f] <= r and bMaxR[f + 2] <= r
                else
                    prot = bd[sq + 15] == 7 or bd[sq + 17] == 7
                    safe = wMinR[f] >= r and wMinR[f + 2] >= r
                end
                if prot and safe then tm = tm + 14; te = te + 6 end
            end
        elseif t == 4 then
            for k = 1, 4 do
                local d = RD[k]
                local to = sq + d
                local tp = bd[to]
                while tp ~= OFF do
                    if aStamp[to] ~= stamp then aStamp[to] = stamp; aMin[to] = val elseif val < aMin[to] then aMin[to] = val end
                    if zone[to] == stamp then hits = hits + 1 end
                    if PCOL[tp] ~= col then
                        local pawnAtk = (col == 0) and (bd[to + 15] == 7 or bd[to + 17] == 7) or (col == 1) and (bd[to - 15] == 1 or bd[to - 17] == 1)
                        if not pawnAtk then mob = mob + 1 end
                    end
                    if tp ~= 0 then break end
                    to = to + d
                    tp = bd[to]
                end
            end
            tm = (mob - 7) * MOB_R_MG; te = (mob - 7) * MOB_R_EG
            local ownC = (col == 0) and wFile[f + 1] or bFile[f + 1]
            local enC = (col == 0) and bFile[f + 1] or wFile[f + 1]
            if ownC == 0 then
                if enC == 0 then tm = tm + 24; te = te + 12 else tm = tm + 11; te = te + 8 end
            end
            if rr == 6 then
                local ek = (col == 0) and bk or wk
                local ekr = (col == 0) and SQRANK[ek] or 7 - SQRANK[ek]
                if ekr == 7 then tm = tm + 14; te = te + 24 else tm = tm + 4; te = te + 10 end
            end
            -- trapped rook next to an uncastled king that can no longer castle
            if rr == 0 and mob <= 3 then
                local ownK = (col == 0) and wk or bk
                local kf = SQFILE[ownK]
                local rights = (col == 0) and band(castle, 3) or band(castle, 12)
                if rights == 0 and SQRANK[ownK] == r and ((kf >= 4 and f > kf) or (kf <= 3 and f < kf)) then
                    tm = tm - 40
                end
            end
        elseif t == 5 then
            for k = 1, 8 do
                local d = KG[k]
                local to = sq + d
                local tp = bd[to]
                while tp ~= OFF do
                    if aStamp[to] ~= stamp then aStamp[to] = stamp; aMin[to] = val elseif val < aMin[to] then aMin[to] = val end
                    if zone[to] == stamp then hits = hits + 1 end
                    if PCOL[tp] ~= col then
                        local pawnAtk = (col == 0) and (bd[to + 15] == 7 or bd[to + 17] == 7) or (col == 1) and (bd[to - 15] == 1 or bd[to - 17] == 1)
                        if not pawnAtk then mob = mob + 1 end
                    end
                    if tp ~= 0 then break end
                    to = to + d
                    tp = bd[to]
                end
            end
            tm = (mob - 13) * MOB_Q_MG; te = (mob - 13) * MOB_Q_EG
        end
        tm = tm * wMob
        if hits > 0 then
            if col == 0 then atk0 = atk0 + 1; units0 = units0 + ATT_W[t] * 2 + hits
            else atk1 = atk1 + 1; units1 = units1 + ATT_W[t] * 2 + hits end
        end
        if col == 0 then pcMg = pcMg + tm; pcEg = pcEg + te else pcMg = pcMg - tm; pcEg = pcEg - te end
    end
    mg = mg + pcMg; eg = eg + pcEg

    -- bishop pair and simple material imbalance ---------------------------------
    if bishopsW0 > 0 and bishopsW1 > 0 then mg = mg + 28; eg = eg + 52 end
    if bishopsB0 > 0 and bishopsB1 > 0 then mg = mg - 28; eg = eg - 52 end
    do
        local pawnsW, pawnsB = nW, nB
        -- knights like closed positions (more pawns), rooks like open ones
        local kn = (cnt[2] - cnt[8]) * (pawnsW + pawnsB - 10) * 2
        local rk = (cnt[4] - cnt[10]) * (10 - pawnsW - pawnsB) * 2
        mg = mg + kn + rk; eg = eg + kn + rk
    end

    -- king safety ---------------------------------------------------------------
    if ph > 6 then
        local shW = kingShelter(0, wk, wFile, bFile)
        local shB = kingShelter(1, bk, bFile, wFile)
        mg = mg + (shW - shB) * W.safe
        -- queen on the board multiplies the danger; attacks by a single piece are harmless
        if atk0 >= 2 then
            local d = safetyCurve(units0)
            if cnt[5] == 0 then d = d * 0.5 end
            mg = mg + d * W.att
        end
        if atk1 >= 2 then
            local d = safetyCurve(units1)
            if cnt[11] == 0 then d = d * 0.5 end
            mg = mg - d * W.att
        end
    end

    -- threats (both sides) using the attack maps ---------------------------------
    local thW, thB, thWe, thBe = 0, 0, 0, 0      -- threats against white / black pieces (mg, eg)
    local hgW, hgB, hgWe, hgBe = 0, 0, 0, 0      -- hanging-piece part, kept separate
    local hangW, hangB = 0, 0
    for i = 1, nP do
        local sq = pieceSq[i]
        local p = bd[sq]
        local t = PT[p]
        local col = PCOL[p]
        local val = SEEV[t]
        local eStamp, eMin, oStamp = aStamp1, aMin1, aStamp0
        if col == 1 then eStamp, eMin, oStamp = aStamp0, aMin0, aStamp1 end
        if eStamp[sq] == stamp then
            local em = eMin[sq]
            local defended = oStamp[sq] == stamp
            if em == 100 then                         -- attacked by a pawn
                local pm = (t == 5) and 60 or (t == 4 and 48 or 36)
                if col == 0 then thW = thW + pm; thWe = thWe + pm * 0.7 else thB = thB + pm; thBe = thBe + pm * 0.7 end
            elseif not defended then                  -- hanging piece
                local pm = (t == 5) and 52 or (t == 4 and 44 or 32)
                if col == 0 then hangW = hangW + 1; hgW = hgW + pm; hgWe = hgWe + pm * 0.8
                else hangB = hangB + 1; hgB = hgB + pm; hgBe = hgBe + pm * 0.8 end
            elseif em < val then                      -- attacked by a cheaper piece
                local pm = (t == 5) and 40 or (t == 4 and 28 or 14)
                if col == 0 then thW = thW + pm; thWe = thWe + pm * 0.7 else thB = thB + pm; thBe = thBe + pm * 0.7 end
            end
        end
    end
    -- the side to move can usually rescue a single hanging piece; two or more means material loss
    if side == 0 and hangW == 1 then hgW = hgW * 0.5; hgWe = hgWe * 0.5 end
    if side == 1 and hangB == 1 then hgB = hgB * 0.5; hgBe = hgBe * 0.5 end
    if hangW >= 2 then hgW = hgW + 30; hgWe = hgWe + 30 end
    if hangB >= 2 then hgB = hgB + 30; hgBe = hgBe + 30 end
    local wTh = W.threat
    mg = mg + (thB + hgB - thW - hgW) * wTh
    eg = eg + (thBe + hgBe - thWe - hgWe) * wTh

    -- endgame knowledge: mop-up against a bare king, drawish scaling ---------------
    if ph <= 10 then
        if nB == 0 and npm1 == 0 and npm0 >= 500 then
            local f, r = SQFILE[bk], SQRANK[bk]
            local cd = max(3 - f, f - 4) + max(3 - r, r - 4)
            eg = eg + cd * 10 + (14 - kdist(wk, bk)) * 4
        elseif nW == 0 and npm0 == 0 and npm1 >= 500 then
            local f, r = SQFILE[wk], SQRANK[wk]
            local cd = max(3 - f, f - 4) + max(3 - r, r - 4)
            eg = eg - (cd * 10 + (14 - kdist(wk, bk)) * 4)
        end
    end

    local score = (mg * ph + eg * (24 - ph)) / 24

    -- the side ahead has no pawns and only a small material edge: hard to win
    if score > 0 and nW == 0 and npm0 - npm1 <= 335 then score = score / 4
    elseif score < 0 and nB == 0 and npm1 - npm0 <= 335 then score = score / 4 end
    -- opposite-coloured bishops with nothing else: drawish
    if cnt[3] == 1 and cnt[9] == 1 and npm0 == 335 and npm1 == 335 then
        if (bishopsW0 > 0) ~= (bishopsB0 > 0) then score = score * 0.6 end
    end
    -- trade down when ahead (Endgame style only)
    if W.trade ~= 0 then
        local lead = npm0 - npm1
        if lead > 200 then score = score + (24 - ph) * 2 elseif lead < -200 then score = score - (24 - ph) * 2 end
    end

    if side == 1 then score = -score end
    return floor(score + TEMPO)
end

-- cached evaluation (hash keyed); the fifty-move drift is applied outside the cache
local function evaluate()
    local ci = band(h2, EVAL_CACHE - 1) + 1
    local score
    if eKey1[ci] == h1 and eKey2[ci] == h2 then
        score = eVal[ci]
    else
        score = evaluateRaw()
        eKey1[ci] = h1; eKey2[ci] = h2; eVal[ci] = score
    end
    if halfmove > 20 then score = floor(score * (120 - min(halfmove, 100)) / 100) end
    return score
end
local function clearEvalCache()
    for i = 1, EVAL_CACHE do eKey1[i] = -1; eKey2[i] = -1 end
end

-- lazy evaluation: material + PST first, full evaluation only near the window
local function lazyEval(alpha, beta)
    local ph = phase
    if ph > 24 then ph = 24 end
    local quick = (mgS * ph + egS * (24 - ph)) / 24
    if side == 1 then quick = -quick end
    quick = quick + TEMPO
    if quick + LAZY_MARGIN <= alpha or quick - LAZY_MARGIN >= beta then return floor(quick) end
    return evaluate()
end

------------------------------------------------------------------------
-- Transposition table: 2-slot buckets, depth/age replacement, parallel arrays
-- tMeta = depth + flag*128 + age*512 (0 = empty slot)
------------------------------------------------------------------------
local ttBits, ttMask = 18, 0
local tKey, tMove, tScore, tMeta
local ttAge = 0
local function allocTT(bits)
    ttBits = bits
    local size = lshift(1, bits)
    ttMask = size - 1
    tKey = tcreate(size, 0)
    tMove = tcreate(size, 0)
    tScore = tcreate(size, 0)
    tMeta = tcreate(size, 0)
end
allocTT(ttBits)

local function ttProbe()
    local base = band(h1, ttMask)
    local i = base + 1
    if tKey[i] == h2 and tMeta[i] ~= 0 then return i end
    i = bxor(base, 1) + 1
    if tKey[i] == h2 and tMeta[i] ~= 0 then return i end
    return 0
end

local function ttStore(depth, score, flag, move, ply)
    if depth < 0 then depth = 0 end
    local base = band(h1, ttMask)
    local i1, i2 = base + 1, bxor(base, 1) + 1
    local idx
    if tKey[i1] == h2 and tMeta[i1] ~= 0 then idx = i1
    elseif tKey[i2] == h2 and tMeta[i2] ~= 0 then idx = i2
    else
        local m1, m2 = tMeta[i1], tMeta[i2]
        local p1 = band(m1, 127) + ((m1 ~= 0 and rshift(m1, 9) == ttAge) and 64 or 0)
        local p2 = band(m2, 127) + ((m2 ~= 0 and rshift(m2, 9) == ttAge) and 64 or 0)
        idx = (p1 <= p2) and i1 or i2
        tMove[idx] = 0
        tMeta[idx] = 0
    end
    local meta = tMeta[idx]
    if meta ~= 0 then
        -- same position already stored: keep a deeper entry from this search unless ours is exact
        if depth < band(meta, 127) - 3 and flag ~= TT_EXACT and rshift(meta, 9) == ttAge then
            if move ~= 0 and tMove[idx] == 0 then tMove[idx] = move end
            return
        end
        if move == 0 then move = tMove[idx] end
    end
    if score >= MATE_BOUND then score = score + ply elseif score <= -MATE_BOUND then score = score - ply end
    tKey[idx] = h2
    tMove[idx] = move
    tScore[idx] = score
    tMeta[idx] = depth + flag * 128 + ttAge * 512
end

------------------------------------------------------------------------
-- Search state
------------------------------------------------------------------------
local nodes, aborted = 0, false
local hardDeadline = 0
local waited, sliceStart, sliceLen, yieldOn, lastYieldCost = 0, 0, 0.02, true, 0
local nodeLimit, cancelFn, mustFinish = 1e18, nil, false
local qChecks = false

local killer1, killer2, counterMove = {}, {}, {}
local hist = tcreate(3328, 0)                -- [piece*256 + to]
local chist = {}                             -- continuation history [(prevPiece*256+prevTo)*4096 + piece*256+to]
local plyMove, plyPiece, staticStack = {}, {}, {}
local quietBuf, exQuiet = {}, {}
for i = 0, MAX_PLY + 4 do quietBuf[i] = {}; exQuiet[i] = {}; plyMove[i] = 0; plyPiece[i] = 0; staticStack[i] = -INF end
local pvTable, pvLen = {}, {}
for i = 0, MAX_PLY + 4 do pvTable[i] = {}; pvLen[i] = i end
local rootBest, rootScore, rootPrevBest = 0, -INF, 0

local LMR = {}
for d = 1, 63 do
    LMR[d] = {}
    for m = 1, 63 do LMR[d][m] = floor(0.75 + mlog(d) * mlog(m) / 2.25) end
end
local HIST_MAX = 16384
local SINGULAR_DEPTH = 99          -- singular extensions disabled (measured worse at this node rate)

local function checkTime()
    if mustFinish then return end
    if nodes >= nodeLimit then aborted = true; return end
    local now = clock()
    if now >= hardDeadline then aborted = true; return end
    if cancelFn and cancelFn() then aborted = true; return end
    if yieldOn and yieldFn and now - sliceStart >= sliceLen then
        -- skip the frame wait when it would overrun the deadline
        if now + lastYieldCost * 1.25 + 0.002 < hardDeadline then
            yieldFn()
            local t2 = clock()
            lastYieldCost = t2 - now
            waited = waited + lastYieldCost
            sliceStart = t2
            if t2 >= hardDeadline then aborted = true end
        end
    end
end

local function drawScore(ply)
    return (ply % 2 == 0) and -contempt or contempt
end

local function isRepetition()
    local lim = gamePly - halfmove
    if lim < 0 then lim = 0 end
    local a, b = h1, h2
    for i = gamePly - 2, lim, -2 do
        if hA[i] == a and hB[i] == b then return true end
    end
    return false
end

local function addHist(key, bonus)
    local v = hist[key]
    hist[key] = v + bonus - floor(v * abs(bonus) / HIST_MAX)
end
local function addChist(key, bonus)
    local v = chist[key] or 0
    chist[key] = v + bonus - floor(v * abs(bonus) / HIST_MAX)
end

-- score moves for ordering; ttMove first, then good captures (MVV-LVA, SEE for risky ones),
-- promotions, killers, countermove, history + continuation history
local function scoreMoves(list, sc, n, ttMove, ply)
    local k1, k2 = killer1[ply], killer2[ply]
    local cm, prevKey = 0, nil
    if ply > 0 then
        local pm = plyMove[ply - 1]
        if pm ~= 0 then
            prevKey = plyPiece[ply - 1] * 256 + band(rshift(pm, 8), 255)
            cm = counterMove[prevKey] or 0
        end
    end
    local bd = board
    for i = 1, n do
        local m = list[i]
        local s
        if m == ttMove then
            s = 10000000
        else
            local from = band(m, 255)
            local to = band(rshift(m, 8), 255)
            local promo = band(rshift(m, 16), 7)
            local flags = rshift(m, 19)
            local piece = bd[from]
            if band(flags, 8) ~= 0 then
                local vv = (band(flags, 1) ~= 0) and 100 or SEEV[PT[bd[to]]]
                local at = PT[piece]
                local av = SEEV[at]
                if vv >= av or see(m) >= 0 then
                    s = 3000000 + vv * 16 - at
                else
                    s = -2000000 + vv * 16 - at
                end
                if promo ~= 0 then
                    if promo == 5 then s = s + 200000 else s = -2500000 - at end
                end
            elseif promo ~= 0 then
                s = (promo == 5) and 3600000 or -3000000
            elseif m == k1 then s = 2000000
            elseif m == k2 then s = 1900000
            elseif m == cm then s = 1800000
            else
                s = hist[piece * 256 + to]
                if prevKey then s = s + (chist[prevKey * 4096 + piece * 256 + to] or 0) end
            end
        end
        sc[i] = s
    end
end

local function pickMove(list, sc, i, n)
    local bi, bs = i, sc[i]
    for j = i + 1, n do
        if sc[j] > bs then bs = sc[j]; bi = j end
    end
    if bi ~= i then
        list[i], list[bi] = list[bi], list[i]
        sc[i], sc[bi] = sc[bi], sc[i]
    end
    return list[i], bs
end

-- does the (pseudo-legal, not yet made) quiet move give a direct check? (discovered checks ignored)
local function directCheck(m)
    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    local piece = board[from]
    local t = PT[piece]
    local ksq = kingSq[1 - PCOL[piece]]
    if t == 1 then
        local dir = (PCOL[piece] == 0) and 16 or -16
        return ksq == to + dir - 1 or ksq == to + dir + 1
    elseif t == 2 then
        local d = ksq - to
        for i = 1, 8 do if KN[i] == d then return true end end
        return false
    elseif t == 6 then
        return false
    end
    local df, dr = SQFILE[ksq] - SQFILE[to], SQRANK[ksq] - SQRANK[to]
    local step
    if df == 0 then step = (dr > 0) and 16 or -16
    elseif dr == 0 then step = (df > 0) and 1 or -1
    elseif df == dr then step = (df > 0) and 17 or -17
    elseif df == -dr then step = (df > 0) and -15 or 15
    else return false end
    local diag = (step == 17 or step == -17 or step == 15 or step == -15)
    if (t == 3 and not diag) or (t == 4 and diag) then return false end
    board[from] = 0
    local s = to + step
    while board[s] == 0 do s = s + step end
    board[from] = piece
    return s == ksq
end

------------------------------------------------------------------------
-- Quiescence search
------------------------------------------------------------------------
local qsearch
qsearch = function(alpha, beta, ply, qd, inChkKnown)
    nodes = nodes + 1
    if band(nodes, 127) == 0 then checkTime() end
    if aborted then return 0 end
    local us = side
    local them = 1 - us
    if ply >= MAX_PLY - 1 then return evaluate() end
    if halfmove >= 100 then return drawScore(ply) end
    local isPV = (beta - alpha) > 1
    local alpha0 = alpha

    local ttMove = 0
    local idx = ttProbe()
    if idx ~= 0 then
        ttMove = tMove[idx]
        if not isPV then
            local ts = tScore[idx]
            if ts >= MATE_BOUND then ts = ts - ply elseif ts <= -MATE_BOUND then ts = ts + ply end
            local fl = band(rshift(tMeta[idx], 7), 3)
            if fl == TT_EXACT or (fl == TT_LOWER and ts >= beta) or (fl == TT_UPPER and ts <= alpha) then
                return ts
            end
        end
    end

    local inChk = inChkKnown
    if inChk == nil then inChk = attacked(kingSq[us], them) end
    local best, stand = -INF, 0
    if not inChk then
        stand = lazyEval(alpha, beta)
        if stand >= beta then
            if idx == 0 then ttStore(0, stand, TT_LOWER, 0, ply) end
            return stand
        end
        if stand > alpha then alpha = stand end
        best = stand
        if qd >= 24 then return stand end
    end

    local list, sc = mvList[ply], mvScore[ply]
    local n
    if qChecks and qd == 0 and not inChk then
        -- tactical styles: also try quiet moves that give a direct check at the first quiescence ply
        local all = genMoves(list, false)
        n = 0
        for i = 1, all do
            local m = list[i]
            if band(m, 4194304) ~= 0 or band(rshift(m, 16), 7) ~= 0 or directCheck(m) then
                n = n + 1
                list[n] = m
            end
        end
    else
        n = genMoves(list, not inChk)
    end
    for i = 1, n do
        local m = list[i]
        if m == ttMove then
            sc[i] = 9000000
        else
            local flags = rshift(m, 19)
            local promo = band(rshift(m, 16), 7)
            if band(flags, 8) ~= 0 then
                local vv = (band(flags, 1) ~= 0) and 100 or SEEV[PT[board[band(rshift(m, 8), 255)]]]
                sc[i] = 1000000 + vv * 16 - PT[board[band(m, 255)]]
            elseif promo ~= 0 then
                sc[i] = (promo == 5) and 900000 or 100
            else
                sc[i] = 500000 + hist[board[band(m, 255)] * 256 + band(rshift(m, 8), 255)]
            end
        end
    end

    local legal, bestMove = 0, 0
    local lateEndgame = phase <= 4
    for i = 1, n do
        local m = pickMove(list, sc, i, n)
        local skip = false
        if not inChk then
            local flags = rshift(m, 19)
            local promo = band(rshift(m, 16), 7)
            if band(flags, 8) ~= 0 then
                local to = band(rshift(m, 8), 255)
                local vv = (band(flags, 1) ~= 0) and 100 or SEEV[PT[board[to]]]
                local av = SEEV[PT[board[band(m, 255)]]]
                if promo == 0 then
                    if not lateEndgame and stand + vv + 180 <= alpha then
                        skip = true                           -- delta pruning
                    elseif vv < av and m ~= ttMove and see(m) < 0 then
                        skip = true                           -- losing capture
                    end
                end
            elseif promo ~= 0 then
                if promo ~= 5 then skip = true end            -- underpromotion without capture
            elseif not lateEndgame and stand + 120 <= alpha then
                skip = true                                   -- quiet check that cannot raise alpha
            end
        end
        if not skip then
            makeMove(m)
            if attacked(kingSq[us], them) then
                unmakeMove()
            else
                legal = legal + 1
                local score = -qsearch(-beta, -alpha, ply + 1, qd + 1)
                unmakeMove()
                if aborted then return 0 end
                if score > best then
                    best = score
                    bestMove = m
                    if score > alpha then
                        alpha = score
                        if score >= beta then
                            ttStore(0, score, TT_LOWER, m, ply)
                            return score
                        end
                    end
                end
            end
        end
    end
    if inChk and legal == 0 then return -MATE + ply end
    ttStore(0, best, (best > alpha0) and TT_EXACT or TT_UPPER, bestMove, ply)
    return best
end

------------------------------------------------------------------------
-- Main search (fail-soft PVS)
------------------------------------------------------------------------
local search
search = function(depth, alpha, beta, ply, nullOk, excluded, inChkKnown)
    nodes = nodes + 1
    if band(nodes, 127) == 0 then checkTime() end
    if aborted then return 0 end

    pvLen[ply] = ply
    local isPV = (beta - alpha) > 1
    local us = side
    local them = 1 - us
    local inChk = inChkKnown
    if inChk == nil then inChk = attacked(kingSq[us], them) end

    if ply > 0 then
        if halfmove >= 100 or isRepetition() then return drawScore(ply) end
        if ply >= MAX_PLY - 1 then return evaluate() end
        -- mate distance pruning
        local a = -MATE + ply
        if alpha < a then alpha = a end
        local b = MATE - ply - 1
        if beta > b then beta = b end
        if alpha >= beta then return alpha end
    end

    if inChk then depth = depth + 1 end
    if depth <= 0 then return qsearch(alpha, beta, ply, 0, inChk) end

    -- transposition table
    local ttMove, ttScore, ttDepth, ttFlag = 0, 0, -1, 0
    local idx = ttProbe()
    if idx ~= 0 then
        ttMove = tMove[idx]
        local meta = tMeta[idx]
        ttDepth = band(meta, 127)
        ttFlag = band(rshift(meta, 7), 3)
        ttScore = tScore[idx]
        if ttScore >= MATE_BOUND then ttScore = ttScore - ply elseif ttScore <= -MATE_BOUND then ttScore = ttScore + ply end
        if excluded == 0 and not isPV and ply > 0 and ttDepth >= depth then
            if ttFlag == TT_EXACT or (ttFlag == TT_LOWER and ttScore >= beta) or (ttFlag == TT_UPPER and ttScore <= alpha) then
                return ttScore
            end
        end
    end
    if ply == 0 and rootPrevBest ~= 0 then ttMove = rootPrevBest end

    -- static evaluation (refined by TT bounds), improving flag
    local static = -INF
    local improving = false
    if not inChk then
        static = lazyEval(alpha, beta)
        if idx ~= 0 and abs(ttScore) < MATE_BOUND then
            if ttFlag == TT_EXACT or (ttFlag == TT_LOWER and ttScore > static) or (ttFlag == TT_UPPER and ttScore < static) then
                static = ttScore
            end
        end
        staticStack[ply] = static
        improving = ply >= 2 and staticStack[ply - 2] ~= -INF and static > staticStack[ply - 2]
    else
        staticStack[ply] = -INF
    end

    if ply > 0 and not isPV and not inChk and excluded == 0 and abs(beta) < MATE_BOUND then
        -- reverse futility pruning (static null move)
        if depth <= 7 and static - (85 * depth - (improving and 45 or 0)) >= beta then
            return static
        end
        -- null move pruning (with verification at high depth)
        if nullOk and depth >= 3 and static >= beta and npm[us] > 0
            and not (idx ~= 0 and ttFlag == TT_UPPER and ttScore < beta) then
            local R = 3 + floor(depth / 4) + min(3, floor((static - beta) / 180))
            makeNull()
            plyMove[ply] = 0
            local sc = -search(depth - 1 - R, -beta, -beta + 1, ply + 1, false, 0)
            unmakeNull()
            if aborted then return 0 end
            if sc >= beta then
                if sc >= MATE_BOUND then sc = beta end
                if depth < 10 then return sc end
                local v = search(depth - R, beta - 1, beta, ply, false, 0)
                if aborted then return 0 end
                if v >= beta then return sc end
            end
        end
    end

    -- internal iterative deepening (PV) / internal iterative reduction (non-PV)
    if ttMove == 0 and excluded == 0 then
        if isPV and depth >= 5 then
            search(depth - 2, alpha, beta, ply, false, 0)
            if aborted then return 0 end
            local i2 = ttProbe()
            if i2 ~= 0 then ttMove = tMove[i2] end
        end
    end

    local list, sc, quiets
    if excluded ~= 0 then list, sc, quiets = exList[ply], exScore[ply], exQuiet[ply]
    else list, sc, quiets = mvList[ply], mvScore[ply], quietBuf[ply] end
    -- staged: try a pseudo-legal TT move before generating anything else
    local staged = ttMove ~= 0 and ttMove ~= excluded and pseudoLegal(ttMove)
    local n
    if staged then
        n = 1
        list[1] = ttMove
        sc[1] = 10000000
    else
        n = genMoves(list, false)
        scoreMoves(list, sc, n, ttMove, ply)
    end
    local nq = 0
    local best, bestMove = -INF, 0
    local origAlpha = alpha
    local legal = 0
    local k1, k2 = killer1[ply], killer2[ply]
    local prevKey = nil
    if ply > 0 and plyMove[ply - 1] ~= 0 then
        prevKey = plyPiece[ply - 1] * 256 + band(rshift(plyMove[ply - 1], 8), 255)
    end
    local lmpLimit = 3 + depth * depth
    if not improving then lmpLimit = floor(lmpLimit / 2) end

    local i = 0
    while true do
        i = i + 1
        if i > n then
            if not staged then break end
            staged = false
            n = genMoves(list, false)
            scoreMoves(list, sc, n, 0, ply)
            for j = 1, n do if list[j] == ttMove then sc[j] = -1000000000 end end
            i = 1
            if n == 0 then break end
        end
        local m, ms = pickMove(list, sc, i, n)
        if m ~= excluded and ms ~= -1000000000 then
            local from = band(m, 255)
            local to = band(rshift(m, 8), 255)
            local promo = band(rshift(m, 16), 7)
            local flags = rshift(m, 19)
            local piece = board[from]
            local isCap = band(flags, 8) ~= 0
            local isQuiet = (not isCap) and promo == 0
            local badCap = isCap and ms < -1000000
            local prune = false

            -- move-count / futility / SEE pruning at shallow non-PV nodes
            if not isPV and not inChk and legal >= 1 and best > -MATE_BOUND then
                if isQuiet then
                    -- late move pruning / futility, but never for a quiet move that gives check
                    if (depth <= 4 and nq >= lmpLimit) or (depth <= 3 and static + 90 + 110 * depth <= alpha) then
                        if not directCheck(m) then prune = true end
                    end
                elseif badCap and depth <= 3 then
                    prune = true
                end
            end

            if not prune then
                -- singular extension of the TT move (with multi-cut)
                local ext = 0
                if m == ttMove and excluded == 0 and ply > 0 and depth >= SINGULAR_DEPTH and ttDepth >= depth - 3
                    and (ttFlag == TT_EXACT or ttFlag == TT_LOWER) and abs(ttScore) < MATE_BOUND then
                    local sBeta = ttScore - 2 * depth
                    local v = search(floor((depth - 1) / 2), sBeta - 1, sBeta, ply, false, m)
                    if aborted then return 0 end
                    if v < sBeta then
                        ext = 1
                    elseif sBeta >= beta then
                        return sBeta
                    elseif ttScore >= beta then
                        ext = -1
                    end
                end

                makeMove(m)
                if attacked(kingSq[us], them) then
                    unmakeMove()
                else
                    legal = legal + 1
                    plyMove[ply] = m
                    plyPiece[ply] = piece
                    local gives = attacked(kingSq[them], us)
                    local newDepth = depth - 1 + ext
                    local score
                    if legal == 1 then
                        score = -search(newDepth, -beta, -alpha, ply + 1, true, 0, gives)
                    else
                        local r = 0
                        if depth >= 3 and (isQuiet or badCap) and not gives then
                            r = LMR[min(depth, 63)][min(legal, 63)]
                            if isPV then r = r - 1 end
                            if not improving then r = r + 1 end
                            if m == k1 or m == k2 then r = r - 1 end
                            if isQuiet then
                                local adj = floor(ms / 6000)
                                if adj > 2 then adj = 2 elseif adj < -2 then adj = -2 end
                                r = r - adj
                            else
                                r = r - 1
                            end
                            if r < 0 then r = 0 end
                            if r > newDepth - 1 then r = max(0, newDepth - 1) end
                        end
                        score = -search(newDepth - r, -alpha - 1, -alpha, ply + 1, true, 0, gives)
                        if score > alpha and r > 0 then
                            score = -search(newDepth, -alpha - 1, -alpha, ply + 1, true, 0, gives)
                        end
                        if score > alpha and score < beta then
                            score = -search(newDepth, -beta, -alpha, ply + 1, true, 0, gives)
                        end
                    end
                    unmakeMove()
                    if aborted then return 0 end

                    if score > best then
                        best = score
                        bestMove = m
                        if score > alpha then
                            alpha = score
                            if ply == 0 then rootBest = m; rootScore = score end
                            local pv = pvTable[ply]
                            pv[ply] = m
                            local child, len = pvTable[ply + 1], pvLen[ply + 1]
                            for j = ply + 1, len - 1 do pv[j] = child[j] end
                            pvLen[ply] = (len > ply + 1) and len or (ply + 1)
                            if score >= beta then
                                if isQuiet then
                                    if killer1[ply] ~= m then killer2[ply] = killer1[ply]; killer1[ply] = m end
                                    local bonus = min(depth * depth * 32, 1600)
                                    local key = piece * 256 + to
                                    addHist(key, bonus)
                                    if prevKey then
                                        counterMove[prevKey] = m
                                        addChist(prevKey * 4096 + key, bonus)
                                    end
                                    for q = 1, nq do
                                        local qm = quiets[q]
                                        local qk = board[band(qm, 255)] * 256 + band(rshift(qm, 8), 255)
                                        addHist(qk, -bonus)
                                        if prevKey then addChist(prevKey * 4096 + qk, -bonus) end
                                    end
                                end
                                break
                            end
                        end
                    end
                    if isQuiet then nq = nq + 1; quiets[nq] = m end
                end
            end
        end
    end

    if legal == 0 then
        if excluded ~= 0 then return alpha end
        if inChk then return -MATE + ply end
        return drawScore(ply)
    end

    if excluded == 0 then
        local flag = TT_EXACT
        if best >= beta then flag = TT_LOWER elseif best <= origAlpha then flag = TT_UPPER end
        ttStore(depth, best, flag, bestMove, ply)
    end
    return best
end

------------------------------------------------------------------------
-- FEN handling
------------------------------------------------------------------------
local CHAR2P = {P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6, p = 7, n = 8, b = 9, r = 10, q = 11, k = 12}
local P2CHAR = {"P", "N", "B", "R", "Q", "K", "p", "n", "b", "r", "q", "k"}
local PROMO_CHAR = {[2] = "n", [3] = "b", [4] = "r", [5] = "q"}
local lastFullmove = 1

local function sqName(sq)
    return string.char(97 + SQFILE[sq]) .. tostring(SQRANK[sq] + 1)
end

local function moveToUCI(m)
    if not m or m == 0 then return nil end
    local from = band(m, 255)
    local to = band(rshift(m, 8), 255)
    local promo = band(rshift(m, 16), 7)
    return sqName(from) .. sqName(to) .. (PROMO_CHAR[promo] or "")
end

local function clearState()
    for i = 0, 255 do board[i] = OFF end
    for i = 1, 64 do board[SQ64[i]] = 0 end
    side, castle, ep, halfmove, gamePly = 0, 0, -1, 0, 0
    kingSq[0], kingSq[1] = -1, -1
    h1, h2, mgS, egS, phase = 0, 0, 0, 0, 0
    npm[0], npm[1] = 0, 0
    for p = 0, 12 do cnt[p] = 0 end
end

-- Parse and validate a FEN. Returns true, or false plus a reason. Inconsistent castling
-- rights and impossible en-passant squares are dropped instead of rejected.
local function setupPosition(fen)
    if type(fen) ~= "string" then return false, "FEN must be a string" end
    clearState()
    local parts = {}
    for token in string.gmatch(fen, "%S+") do parts[#parts + 1] = token end
    if #parts < 2 then return false, "FEN needs piece placement and side to move" end
    local placement = parts[1]
    if string.sub(placement, 1, 1) == "/" or string.sub(placement, -1) == "/" or string.find(placement, "//", 1, true) then
        return false, "empty rank in FEN"
    end
    local rows = {}
    for row in string.gmatch(placement, "[^/]+") do rows[#rows + 1] = row end
    if #rows ~= 8 then return false, "FEN needs 8 ranks" end
    for ri = 1, 8 do
        local rank = 8 - ri
        local row = rows[ri]
        local file = 0
        for i = 1, #row do
            local c = string.sub(row, i, i)
            local num = tonumber(c)
            if num then
                if num < 1 or num > 8 then return false, "bad empty-square count" end
                file = file + num
            else
                local p = CHAR2P[c]
                if not p then return false, "bad piece character" end
                if file > 7 then return false, "rank too long" end
                if (p == 1 or p == 7) and (rank == 0 or rank == 7) then return false, "pawn on a back rank" end
                local sq = 48 + rank * 16 + file
                addPiece(p, sq)
                if p == 6 then kingSq[0] = sq elseif p == 12 then kingSq[1] = sq end
                file = file + 1
            end
        end
        if file ~= 8 then return false, "rank needs 8 squares" end
    end
    if cnt[6] ~= 1 or cnt[12] ~= 1 then return false, "each side needs exactly one king" end

    if parts[2] == "b" then
        side = 1
        h1 = bxor(h1, zSideA); h2 = bxor(h2, zSideB)
    elseif parts[2] ~= "w" then
        return false, "side to move must be w or b"
    end

    local cs = parts[3] or "-"
    if cs ~= "-" then
        if string.find(cs, "[^KQkq]") or #cs > 4 then return false, "bad castling field" end
        if string.find(cs, "K", 1, true) then castle = bor(castle, 1) end
        if string.find(cs, "Q", 1, true) then castle = bor(castle, 2) end
        if string.find(cs, "k", 1, true) then castle = bor(castle, 4) end
        if string.find(cs, "q", 1, true) then castle = bor(castle, 8) end
    end
    if board[E1] ~= 6 then castle = band(castle, 12) end
    if board[E8] ~= 12 then castle = band(castle, 3) end
    if board[H1] ~= 4 then castle = band(castle, 14) end
    if board[A1] ~= 4 then castle = band(castle, 13) end
    if board[H8] ~= 10 then castle = band(castle, 11) end
    if board[A8] ~= 10 then castle = band(castle, 7) end
    h1 = bxor(h1, zCA[castle]); h2 = bxor(h2, zCB[castle])

    local eps = parts[4]
    if eps and eps ~= "-" then
        if not string.match(eps, "^[a-h][36]$") then return false, "bad en-passant square" end
        local f = string.byte(eps, 1) - 97
        local r = tonumber(string.sub(eps, 2, 2)) - 1
        local sq = 48 + r * 16 + f
        local okRank = (side == 0 and r == 5) or (side == 1 and r == 2)
        local victim = (side == 0) and board[sq - 16] == 7 or (side == 1) and board[sq + 16] == 1
        local capturer = (side == 0) and (board[sq - 15] == 1 or board[sq - 17] == 1)
            or (side == 1) and (board[sq + 15] == 7 or board[sq + 17] == 7)
        if okRank and board[sq] == 0 and victim and capturer then
            ep = sq
            h1 = bxor(h1, zEpA[f]); h2 = bxor(h2, zEpB[f])
        end
    end
    halfmove = tonumber(parts[5]) or 0
    if halfmove < 0 then halfmove = 0 elseif halfmove > 150 then halfmove = 150 end
    halfmove = floor(halfmove)
    lastFullmove = tonumber(parts[6]) or 1
    if lastFullmove < 1 then lastFullmove = 1 end

    -- the side that just moved may not have left its own king in check
    if attacked(kingSq[1 - side], side) then return false, "side not to move is in check" end
    hA[0] = h1; hB[0] = h2
    return true
end

local function toFEN()
    local rows = {}
    for r = 7, 0, -1 do
        local row, empty = "", 0
        for f = 0, 7 do
            local p = board[48 + r * 16 + f]
            if p == 0 then
                empty = empty + 1
            else
                if empty > 0 then row = row .. tostring(empty); empty = 0 end
                row = row .. P2CHAR[p]
            end
        end
        if empty > 0 then row = row .. tostring(empty) end
        rows[#rows + 1] = row
    end
    local cs = ""
    if band(castle, 1) ~= 0 then cs = cs .. "K" end
    if band(castle, 2) ~= 0 then cs = cs .. "Q" end
    if band(castle, 4) ~= 0 then cs = cs .. "k" end
    if band(castle, 8) ~= 0 then cs = cs .. "q" end
    if cs == "" then cs = "-" end
    return table.concat(rows, "/") .. " " .. ((side == 0) and "w" or "b") .. " " .. cs .. " "
        .. ((ep >= 0) and sqName(ep) or "-") .. " " .. tostring(halfmove) .. " " .. tostring(lastFullmove)
end

local function rootLegalMoves()
    local list = mvList[MAX_PLY + 3]
    local n = genMoves(list, false)
    local res = {}
    local us = side
    for i = 1, n do
        local m = list[i]
        makeMove(m)
        if not attacked(kingSq[us], 1 - us) then res[#res + 1] = m end
        unmakeMove()
    end
    return res
end

------------------------------------------------------------------------
-- Engine API
------------------------------------------------------------------------
Engine.Style = "Balanced"
Engine.LastSearch = nil
Engine.Yield = yieldFn ~= nil

function Engine:SetStyle(style)
    style = tostring(style or "Balanced")
    local st = STYLES[style]
    if not st then return false end
    if st ~= W then clearEvalCache() end
    W = st
    contempt = st.contempt
    self.Style = style
    return true
end

function Engine:Configure(options)
    if type(options) ~= "table" then return false end
    if options.HashBits then
        local b = floor(tonumber(options.HashBits) or ttBits)
        if b < 14 then b = 14 elseif b > 20 then b = 20 end
        if b ~= ttBits then allocTT(b) end
    end
    if options.SliceTime then
        local s = tonumber(options.SliceTime) or 0.02
        if s < 0.004 then s = 0.004 elseif s > 0.2 then s = 0.2 end
        sliceLen = s
    end
    if options.Yield ~= nil then yieldOn = options.Yield and true or false end
    self.Yield = yieldOn and yieldFn ~= nil
    return true
end

function Engine:NewGame()
    allocTT(ttBits)
    clearEvalCache()
    for i = 1, 3328 do hist[i] = 0 end
    counterMove = {}
    chist = {}
    for i = 0, MAX_PLY + 4 do killer1[i] = 0; killer2[i] = 0 end
    ttAge = 0
    rootPrevBest = 0
    return true
end

function Engine:Perft(fen, depth)
    if not setupPosition(fen) then return nil end
    depth = floor(tonumber(depth) or 1)
    local function perft(d, ply)
        if d == 0 then return 1 end
        local list = mvList[ply]
        local n = genMoves(list, false)
        local total = 0
        local us = side
        if d == 1 then
            for i = 1, n do
                makeMove(list[i])
                if not attacked(kingSq[us], 1 - us) then total = total + 1 end
                unmakeMove()
            end
            return total
        end
        for i = 1, n do
            makeMove(list[i])
            if not attacked(kingSq[us], 1 - us) then total = total + perft(d - 1, ply + 1) end
            unmakeMove()
        end
        return total
    end
    return perft(depth, 0)
end

-- static evaluation of a position (centipawns, side-to-move perspective); nil for invalid FENs
function Engine:StaticEval(fen)
    if not setupPosition(fen) then return nil end
    return evaluate()
end

function Engine:MakeMoveFEN(fen, uci)
    if not setupPosition(fen) then return nil end
    local mover = side
    for _, m in ipairs(rootLegalMoves()) do
        if moveToUCI(m) == uci then
            makeMove(m)
            if mover == 1 then lastFullmove = lastFullmove + 1 end
            return toFEN()
        end
    end
    return nil
end

function Engine:GetPV(fen, maxPly)
    if not setupPosition(fen) then return "" end
    maxPly = floor(tonumber(maxPly) or 12)
    local out, seen = {}, {}
    for i = 1, maxPly do
        local idx = ttProbe()
        if idx == 0 or tMove[idx] == 0 then break end
        local m = tMove[idx]
        local key = h1 .. ":" .. h2
        if seen[key] then break end
        seen[key] = true
        local found = false
        for _, lm in ipairs(rootLegalMoves()) do
            if lm == m then found = true; break end
        end
        if not found then break end
        out[#out + 1] = moveToUCI(m)
        makeMove(m)
    end
    return table.concat(out, " ")
end

function Engine:GetBestMoveFromFEN(fen, seconds, options)
    local t0 = clock()
    local limit = tonumber(seconds) or 2.5
    if limit < 0.02 then limit = 0.02 elseif limit > 600 then limit = 600 end
    local opts = (type(options) == "table") and options or nil

    -- game history (for repetition detection): options.History or a bare array of FENs
    local historyFens = nil
    if opts then
        if type(opts.History) == "table" then historyFens = opts.History
        elseif type(opts[1]) == "string" then historyFens = opts end
    end
    local seeds = {}
    if historyFens then
        for _, hf in ipairs(historyFens) do
            if type(hf) == "string" and setupPosition(hf) then seeds[#seeds + 1] = {h1, h2} end
        end
    end

    local ok, why = setupPosition(fen)
    if not ok then
        self.LastSearch = {requestedTime = limit, elapsed = clock() - t0, depth = 0, nodes = 0, error = why, style = self.Style}
        return nil
    end
    if #seeds > 0 then
        local c1, c2 = h1, h2
        for i, s in ipairs(seeds) do hA[i - 1] = s[1]; hB[i - 1] = s[2] end
        gamePly = #seeds
        hA[gamePly] = c1; hB[gamePly] = c2
    end

    local legal = rootLegalMoves()
    local rootInCheck = attacked(kingSq[side], 1 - side)
    if #legal == 0 then
        local sc = rootInCheck and -MATE or 0
        self.LastSearch = {requestedTime = limit, elapsed = clock() - t0, depth = 0, nodes = 0, score = sc, move = nil, style = self.Style,
            terminal = rootInCheck and "checkmate" or "stalemate"}
        return nil, sc
    end

    -- search bookkeeping
    nodes, aborted, mustFinish = 0, false, false
    hardDeadline = t0 + limit - min(0.012, limit * 0.04)
    waited, sliceStart, lastYieldCost = 0, t0, 0
    nodeLimit = (opts and tonumber(opts.NodeLimit)) or 1e18
    cancelFn = (opts and type(opts.Cancel) == "function") and opts.Cancel or nil
    qChecks = W.qchecks
    ttAge = (ttAge + 1) % 64
    for i = 0, MAX_PLY + 4 do killer1[i] = 0; killer2[i] = 0; staticStack[i] = -INF; plyMove[i] = 0 end
    counterMove = {}
    chist = {}
    for i = 1, 3328 do
        local v = hist[i]
        if v ~= 0 then hist[i] = floor(v / 2) end
    end
    rootBest, rootScore, rootPrevBest = 0, -INF, 0

    if #legal == 1 then
        local sc = evaluate()
        local m = legal[1]
        self.LastSearch = {requestedTime = limit, elapsed = clock() - t0, computeTime = 0, depth = 0, nodes = 0, nps = 0,
            score = sc, move = moveToUCI(m), pv = moveToUCI(m), style = self.Style, forced = true}
        return moveToUCI(m), sc
    end

    local bestMove, bestScore = legal[1], -INF
    local prevScore, completed = 0, 0
    local stable, lastBest = 0, 0
    local softFrac = 0.60
    local maxDepth = MAX_DEPTH
    if opts and tonumber(opts.MaxDepth) then maxDepth = max(1, min(MAX_DEPTH, floor(tonumber(opts.MaxDepth)))) end
    local pvString = ""
    local mateIters = 0

    for depth = 1, maxDepth do
        local elapsed = clock() - t0
        if depth > 1 and elapsed >= limit * softFrac then break end
        mustFinish = (depth <= 1)

        local alpha, beta, delta = -INF, INF, 28
        if depth >= 5 and abs(prevScore) < MATE_BOUND then
            alpha, beta = prevScore - delta, prevScore + delta
        end
        local score
        while true do
            rootBest = 0
            score = search(depth, alpha, beta, 0, false, 0)
            if aborted then break end
            if score <= alpha and alpha > -INF then
                beta = floor((alpha + beta) / 2)
                alpha = max(score - delta, -INF)
                delta = delta + floor(delta / 2) + 8
                if delta > 700 then alpha = -INF end
            elseif score >= beta and beta < INF then
                beta = min(score + delta, INF)
                delta = delta + floor(delta / 2) + 8
                if delta > 700 then beta = INF end
            else
                break
            end
        end
        mustFinish = false

        if aborted then
            -- a root move that completed its search and raised alpha in this iteration is at least as good
            if rootBest ~= 0 then bestMove = rootBest; bestScore = rootScore end
            break
        end

        if rootBest ~= 0 then bestMove = rootBest end
        bestScore = score
        completed = depth
        rootPrevBest = bestMove

        local pv = {}
        for j = 0, pvLen[0] - 1 do
            local pm = pvTable[0][j]
            if pm and pm ~= 0 then pv[#pv + 1] = moveToUCI(pm) end
        end
        pvString = table.concat(pv, " ")

        -- time management: the budget is a fixed per-move allowance, so it is only shortened when a mate is
        -- found or the best move stayed stable for very long; it is extended on instability or score drops
        if bestMove == lastBest then stable = stable + 1 else stable = 0 end
        if depth > 1 and bestMove ~= lastBest then softFrac = min(0.75, softFrac + 0.12) end
        if depth > 1 and prevScore - score > 30 then softFrac = min(0.8, softFrac + 0.15) end
        lastBest = bestMove
        prevScore = score

        if abs(score) >= MATE_BOUND then
            mateIters = mateIters + 1
            if mateIters >= 2 and depth >= 4 then break end
        else
            mateIters = 0
        end
        local spent = clock() - t0
        if depth >= 12 and stable >= 10 and spent >= limit * 0.5 then break end
        if spent >= hardDeadline - t0 then break end
    end
    mustFinish = false

    local elapsed = clock() - t0
    local compute = elapsed - waited
    local uci = moveToUCI(bestMove)
    local reaction = nil
    if bestScore >= MATE_BOUND then
        reaction = {notify = true, tag = "MATE", message = "Forced mate in " .. tostring(floor((MATE - bestScore + 1) / 2)) .. ".", icon = "swords"}
    elseif bestScore <= -MATE_BOUND then
        reaction = {notify = true, tag = "DANGER", message = "The position is lost by force; best resistance chosen.", icon = "triangle-alert"}
    elseif completed >= 8 then
        reaction = {notify = false, tag = "DEEP", message = "Depth " .. tostring(completed) .. " search completed.", icon = "scan-search"}
    end
    self.LastSearch = {
        requestedTime = limit,
        elapsed = elapsed,
        computeTime = compute,
        depth = completed,
        nodes = nodes,
        nps = floor(nodes / max(compute, 0.001)),
        score = bestScore,
        move = uci,
        pv = pvString,
        style = self.Style,
        aborted = aborted,
    }
    return uci, bestScore, reaction
end

function Engine:Analyze(fen, seconds, options)
    local move, score, reaction = self:GetBestMoveFromFEN(fen, seconds, options)
    local info = self.LastSearch or {}
    return {
        move = move, score = score, reaction = reaction,
        api = self.Name, version = self.Version,
        nodes = info.nodes, depth = info.depth, elapsed = info.elapsed, computeTime = info.computeTime,
        nps = info.nps, pv = info.pv, requestedTime = info.requestedTime, style = self.Style,
        Move = move, Score = score, Reaction = reaction, Stats = info,
    }
end

return Engine

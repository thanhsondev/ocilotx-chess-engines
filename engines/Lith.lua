local API = {}
API.Name = "Auralith Sovereign"
API.Version = "1.0.0"
API.Description = "Positional-squeeze chess engine: PVS/LMR/null-move/SEE search with a tapered, mobility- and space-driven evaluation"

local band, bor, bxor, rshift, lshift = bit32.band, bit32.bor, bit32.bxor, bit32.rshift, bit32.lshift
local floor, abs, max, min = math.floor, math.abs, math.max, math.min
local clock = os.clock
local yieldFn = (task and task.wait) or function() end

local OFF = 99
local INF, MATE, MAX_PLY = 32000, 30000, 96
local MATE_BOUND = MATE - MAX_PLY
local MAX_DEPTH = 64

local FL_EP, FL_CASTLE, FL_DOUBLE, FL_CAP = 1 * 524288, 2 * 524288, 4 * 524288, 8 * 524288

local TT_EXACT, TT_LOWER, TT_UPPER = 1, 2, 3
local TT_SIZE = 131072

local KN = {33, 31, 18, 14, -14, -18, -31, -33}
local KG = {1, -1, 16, -16, 15, -15, 17, -17}
local BD = {15, 17, -15, -17}
local RD = {1, -1, 16, -16}

local SEEV = {[0] = 0, 100, 320, 330, 500, 900, 20000}

local PT, PCOL = {[0] = 0, [OFF] = 0}, {[0] = 2, [OFF] = 3}
for p = 1, 12 do
    PT[p] = (p - 1) % 6 + 1
    PCOL[p] = p <= 6 and 0 or 1
end

local SQFILE, SQRANK = {}, {}
for r = 0, 7 do
    for f = 0, 7 do
        local sq = 48 + r * 16 + f
        SQFILE[sq] = f
        SQRANK[sq] = r
    end
end

local CMASK = {}
for i = 0, 255 do CMASK[i] = 15 end
CMASK[52] = 12; CMASK[48] = 13; CMASK[55] = 14
CMASK[164] = 3; CMASK[160] = 7; CMASK[167] = 11

local STYLES = {
    Squeeze  = {mob = 1.25, space = 1.6, outpost = 1.3, king = 0.9, shield = 1.0, passed = 1.0, pawns = 1.0, contempt = 22},
    Fortress = {mob = 0.9, space = 0.9, outpost = 1.0, king = 1.5, shield = 1.5, passed = 0.9, pawns = 1.1, contempt = 0},
    Hunter   = {mob = 1.1, space = 1.0, outpost = 1.0, king = 1.6, shield = 0.8, passed = 1.0, pawns = 0.9, contempt = 30},
    Surgeon  = {mob = 1.0, space = 0.8, outpost = 1.0, king = 0.9, shield = 1.0, passed = 1.5, pawns = 1.4, contempt = 12},
    Balanced = {mob = 1.0, space = 1.0, outpost = 1.0, king = 1.0, shield = 1.0, passed = 1.0, pawns = 1.0, contempt = 10},
}
local W = STYLES.Squeeze
local contempt = W.contempt
API.Style = "Squeeze"

function API:SetStyle(style)
    style = tostring(style or "Squeeze")
    if STYLES[style] then
        W = STYLES[style]
        contempt = W.contempt
        self.Style = style
        return true
    end
    return false
end

local PMG, PEG = {}, {}
local PHV = {[0] = 0}
local NPV = {[0] = 0}
for p = 1, 12 do
    local t = PT[p]
    PHV[p] = (t == 2 or t == 3) and 1 or (t == 4 and 2 or (t == 5 and 4 or 0))
    NPV[p] = (t >= 2 and t <= 5) and SEEV[t] or 0
end

do
    local pawnRankMg = {[0] = 0, [1] = 0, [2] = 3, [3] = 10, [4] = 22, [5] = 42, [6] = 75, [7] = 0}
    local pawnRankEg = {[0] = 0, [1] = 0, [2] = 5, [3] = 14, [4] = 30, [5] = 60, [6] = 105, [7] = 0}
    local kingBack = {8, 28, 12, -8, -12, 4, 32, 12}
    for color = 0, 1 do
        local sign = color == 0 and 1 or -1
        for t = 1, 6 do
            local p = t + color * 6
            for r = 0, 7 do
                for f = 0, 7 do
                    local sq = 48 + r * 16 + f
                    local rr = color == 0 and r or 7 - r
                    local cd = abs(f - 3.5) + abs(rr - 3.5)
                    local mg, eg = 0, 0
                    if t == 1 then
                        mg = 82 + pawnRankMg[rr]
                        eg = 96 + pawnRankEg[rr]
                        if (f == 3 or f == 4) then
                            if rr >= 2 and rr <= 4 then mg = mg + 12 end
                            if rr == 1 then mg = mg - 10 end
                        elseif (f == 2 or f == 5) and rr >= 2 and rr <= 4 then
                            mg = mg + 5
                        end
                        if f == 0 or f == 7 then mg = mg - 8; eg = eg - 4 end
                    elseif t == 2 then
                        mg = 335 + (4 - cd) * 8 - (rr == 0 and 8 or 0)
                        eg = 292 + (4 - cd) * 5
                    elseif t == 3 then
                        mg = 352 + (4 - cd) * 4 - (rr == 0 and 6 or 0)
                        eg = 306 + (4 - cd) * 3
                        if rr == 1 and (f == 1 or f == 6) then mg = mg + 8 end
                    elseif t == 4 then
                        mg = 480 + (rr == 6 and 14 or 0) + ((rr == 0 and (f == 3 or f == 4)) and 6 or 0)
                        eg = 516 + (rr == 6 and 12 or 0)
                    elseif t == 5 then
                        mg = 1000 + (4 - cd) * 2
                        eg = 952 + (4 - cd) * 5
                    else
                        if rr == 0 then mg = kingBack[f + 1]
                        elseif rr == 1 then mg = floor(kingBack[f + 1] / 2) - 20
                        else mg = -35 * (rr - 1) - 20 end
                        eg = (4 - cd) * 13 - (rr == 0 and 5 or 0)
                    end
                    PMG[p * 256 + sq] = sign * mg
                    PEG[p * 256 + sq] = sign * eg
                end
            end
        end
    end
end

local zA, zB, zEpA, zEpB, zCA, zCB = {}, {}, {}, {}, {}, {}
local zSideA, zSideB
do
    local seed = 0x9E3779B9
    local function rnd()
        seed = bxor(seed, lshift(seed, 13))
        seed = bxor(seed, rshift(seed, 17))
        seed = bxor(seed, lshift(seed, 5))
        return seed
    end
    for p = 1, 12 do
        for r = 0, 7 do
            for f = 0, 7 do
                local k = p * 256 + 48 + r * 16 + f
                zA[k] = rnd(); zB[k] = rnd()
            end
        end
    end
    for f = 0, 15 do zEpA[f] = rnd(); zEpB[f] = rnd() end
    for c = 0, 15 do zCA[c] = rnd(); zCB[c] = rnd() end
    zSideA, zSideB = rnd(), rnd()
end

local board = {}
for i = 0, 255 do board[i] = OFF end
local side, castle, ep, halfmove = 0, 0, -1, 0
local kingSq = {[0] = -1, [1] = -1}
local h1, h2 = 0, 0
local mgS, egS, phase = 0, 0, 0
local npm = {[0] = 0, [1] = 0}
local gamePly = 0

local sMove, sCap, sCastle, sEp, sHalf, sH1, sH2, sMg, sEg, sPh, sN0, sN1 = {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}
local hA, hB = {}, {}

local function addPiece(p, sq)
    board[sq] = p
    local k = p * 256 + sq
    h1 = bxor(h1, zA[k]); h2 = bxor(h2, zB[k])
    mgS = mgS + PMG[k]; egS = egS + PEG[k]
    phase = phase + PHV[p]
    local c = PCOL[p]
    npm[c] = npm[c] + NPV[p]
end

local function removePiece(p, sq)
    board[sq] = 0
    local k = p * 256 + sq
    h1 = bxor(h1, zA[k]); h2 = bxor(h2, zB[k])
    mgS = mgS - PMG[k]; egS = egS - PEG[k]
    phase = phase - PHV[p]
    local c = PCOL[p]
    npm[c] = npm[c] - NPV[p]
end

local function attacked(sq, by)
    if by == 0 then
        if board[sq - 15] == 1 or board[sq - 17] == 1 then return true end
    else
        if board[sq + 15] == 7 or board[sq + 17] == 7 then return true end
    end
    local kn, kg, bi, ro, qu = 2 + by * 6, 6 + by * 6, 3 + by * 6, 4 + by * 6, 5 + by * 6
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

    if band(flags, 1) ~= 0 then
        local cs = us == 0 and to - 16 or to + 16
        removePiece(board[cs], cs)
    end
    if band(flags, 2) ~= 0 then
        local rf, rt
        if to > from then rf, rt = from + 3, from + 1 else rf, rt = from - 4, from - 1 end
        local rook = board[rf]
        removePiece(rook, rf)
        addPiece(rook, rt)
    end

    local pt = PT[piece]
    if pt == 6 then kingSq[us] = to end
    castle = band(castle, CMASK[from], CMASK[to])
    if band(flags, 4) ~= 0 then ep = us == 0 and from + 16 or from - 16 else ep = -1 end
    if pt == 1 or cap ~= 0 or band(flags, 1) ~= 0 then halfmove = 0 else halfmove = halfmove + 1 end

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
    if promo ~= 0 then piece = 1 + us * 6 end
    board[from] = piece
    if band(flags, 1) ~= 0 then
        board[to] = 0
        if us == 0 then board[to - 16] = 7 else board[to + 16] = 1 end
    else
        board[to] = sCap[gp]
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

local mvList, mvScore = {}, {}
for i = 0, MAX_PLY + 4 do mvList[i] = {}; mvScore[i] = {} end

local function genMoves(ply, capsOnly)
    local list = mvList[ply]
    local n = 0
    local us = side
    local them = 1 - us
    local bd = board
    for r = 0, 7 do
        local base = 48 + r * 16
        for sq = base, base + 7 do
            local p = bd[sq]
            if p ~= 0 and PCOL[p] == us then
                local t = PT[p]
                if t == 1 then
                    local dir = us == 0 and 16 or -16
                    local promoFrom = us == 0 and 6 or 1
                    local startR = us == 0 and 1 or 6
                    local one = sq + dir
                    if bd[one] == 0 then
                        if r == promoFrom then
                            n = n + 1; list[n] = sq + one * 256 + 5 * 65536
                            if not capsOnly then
                                n = n + 1; list[n] = sq + one * 256 + 4 * 65536
                                n = n + 1; list[n] = sq + one * 256 + 3 * 65536
                                n = n + 1; list[n] = sq + one * 256 + 2 * 65536
                            end
                        elseif not capsOnly then
                            n = n + 1; list[n] = sq + one * 256
                            if r == startR and bd[one + dir] == 0 then
                                n = n + 1; list[n] = sq + (one + dir) * 256 + FL_DOUBLE
                            end
                        end
                    end
                    for k = 1, 2 do
                        local to = sq + dir + (k == 1 and -1 or 1)
                        local tp = bd[to]
                        if tp ~= 0 and PCOL[tp] == them then
                            if r == promoFrom then
                                n = n + 1; list[n] = sq + to * 256 + 5 * 65536 + FL_CAP
                                n = n + 1; list[n] = sq + to * 256 + 4 * 65536 + FL_CAP
                                n = n + 1; list[n] = sq + to * 256 + 3 * 65536 + FL_CAP
                                n = n + 1; list[n] = sq + to * 256 + 2 * 65536 + FL_CAP
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
                        if us == 0 and sq == 52 then
                            if band(castle, 1) ~= 0 and bd[53] == 0 and bd[54] == 0 and bd[55] == 4
                                and not attacked(52, 1) and not attacked(53, 1) and not attacked(54, 1) then
                                n = n + 1; list[n] = 52 + 54 * 256 + FL_CASTLE
                            end
                            if band(castle, 2) ~= 0 and bd[51] == 0 and bd[50] == 0 and bd[49] == 0 and bd[48] == 4
                                and not attacked(52, 1) and not attacked(51, 1) and not attacked(50, 1) then
                                n = n + 1; list[n] = 52 + 50 * 256 + FL_CASTLE
                            end
                        elseif us == 1 and sq == 164 then
                            if band(castle, 4) ~= 0 and bd[165] == 0 and bd[166] == 0 and bd[167] == 10
                                and not attacked(164, 0) and not attacked(165, 0) and not attacked(166, 0) then
                                n = n + 1; list[n] = 164 + 166 * 256 + FL_CASTLE
                            end
                            if band(castle, 8) ~= 0 and bd[163] == 0 and bd[162] == 0 and bd[161] == 0 and bd[160] == 10
                                and not attacked(164, 0) and not attacked(163, 0) and not attacked(162, 0) then
                                n = n + 1; list[n] = 164 + 162 * 256 + FL_CASTLE
                            end
                        end
                    end
                else
                    local doDiag = t == 3 or t == 5
                    local doOrth = t == 4 or t == 5
                    if doDiag then
                        for k = 1, 4 do
                            local d = BD[k]
                            local to = sq + d
                            while true do
                                local tp = bd[to]
                                if tp == 0 then
                                    if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                                    to = to + d
                                else
                                    if PCOL[tp] == them then n = n + 1; list[n] = sq + to * 256 + FL_CAP end
                                    break
                                end
                            end
                        end
                    end
                    if doOrth then
                        for k = 1, 4 do
                            local d = RD[k]
                            local to = sq + d
                            while true do
                                local tp = bd[to]
                                if tp == 0 then
                                    if not capsOnly then n = n + 1; list[n] = sq + to * 256 end
                                    to = to + d
                                else
                                    if PCOL[tp] == them then n = n + 1; list[n] = sq + to * 256 + FL_CAP end
                                    break
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return n
end

local function leastAttacker(sq, by)
    if by == 0 then
        local s = sq - 15; if board[s] == 1 then return s end
        s = sq - 17; if board[s] == 1 then return s end
    else
        local s = sq + 15; if board[s] == 7 then return s end
        s = sq + 17; if board[s] == 7 then return s end
    end
    local kn = 2 + by * 6
    for i = 1, 8 do
        local s = sq + KN[i]
        if board[s] == kn then return s end
    end
    local bi, ro, qu, kg = 3 + by * 6, 4 + by * 6, 5 + by * 6, 6 + by * 6
    local bishopSq, rookSq, queenSq
    for i = 1, 4 do
        local d = BD[i]
        local s = sq + d
        while board[s] == 0 do s = s + d end
        local p = board[s]
        if p == bi then bishopSq = bishopSq or s elseif p == qu then queenSq = queenSq or s end
    end
    if bishopSq then return bishopSq end
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
    local flags = rshift(m, 19)
    local piece = board[from]
    local captured = board[to]
    seeGain[0] = band(flags, 1) ~= 0 and 100 or SEEV[PT[captured]]
    local aVal = SEEV[PT[piece]]
    local stm = 1 - PCOL[piece]
    local removed = 0
    seeSq[1] = from; seePc[1] = piece; board[from] = 0
    removed = 1
    local d = 0
    while true do
        d = d + 1
        seeGain[d] = aVal - seeGain[d - 1]
        if max(-seeGain[d - 1], seeGain[d]) < 0 then break end
        local s = leastAttacker(to, stm)
        if not s then break end
        local ap = board[s]
        aVal = SEEV[PT[ap]]
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

local wCnt, bCnt, wMin, bMax = {}, {}, {}, {}
local wAtk, bAtk = {}, {}
local pawnW, pawnB, pcSq = {}, {}, {}
local PASS_MG = {[0] = 0, 3, 7, 16, 34, 62, 100, 0}
local PASS_EG = {[0] = 0, 8, 16, 34, 62, 110, 170, 0}

local function kdist(a, b)
    local df = abs(SQFILE[a] - SQFILE[b])
    local dr = abs(SQRANK[a] - SQRANK[b])
    return df > dr and df or dr
end

local function kingShield(col, ksq)
    local kf = SQFILE[ksq]
    local ownP = col == 0 and 1 or 7
    local dir = col == 0 and 16 or -16
    local s = 0
    for f = max(0, kf - 1), min(7, kf + 1) do
        local own = col == 0 and wCnt[f + 1] or bCnt[f + 1]
        local enemy = col == 0 and bCnt[f + 1] or wCnt[f + 1]
        local sq1 = ksq + (f - kf) + dir
        if board[sq1] == ownP then s = s + 12
        elseif board[sq1 + dir] == ownP then s = s + 6 end
        if own == 0 then
            s = s - 14
            if enemy == 0 then s = s - 10 end
        end
    end
    return s
end

local function evaluate()
    local mg, eg = mgS, egS
    for i = 0, 9 do wCnt[i] = 0; bCnt[i] = 0; wMin[i] = 8; bMax[i] = -1 end
    local nW, nB, nP = 0, 0, 0
    local bishW, bishB = 0, 0

    for r = 0, 7 do
        local base = 48 + r * 16
        for sq = base, base + 7 do
            local p = board[sq]
            if p ~= 0 then
                if p == 1 then
                    nW = nW + 1; pawnW[nW] = sq
                    local fi = sq - base + 1
                    wCnt[fi] = wCnt[fi] + 1
                    if r < wMin[fi] then wMin[fi] = r end
                elseif p == 7 then
                    nB = nB + 1; pawnB[nB] = sq
                    local fi = sq - base + 1
                    bCnt[fi] = bCnt[fi] + 1
                    if r > bMax[fi] then bMax[fi] = r end
                elseif p ~= 6 and p ~= 12 then
                    nP = nP + 1; pcSq[nP] = sq
                    if p == 3 then bishW = bishW + 1 elseif p == 9 then bishB = bishB + 1 end
                end
            end
        end
    end

    if nW == 0 and nB == 0 and npm[0] <= 330 and npm[1] <= 330 then return 0 end

    local wk, bk = kingSq[0], kingSq[1]

    local spW, spB = 0, 0
    for i = 1, nW do
        local sq = pawnW[i]
        for k = 15, 17, 2 do
            local a = sq + k
            if not wAtk[a] then
                wAtk[a] = true
                local rk = SQRANK[a]
                if rk and rk >= 2 and rk <= 5 then
                    local ff = SQFILE[a]
                    if ff >= 1 and ff <= 6 then spW = spW + 1 end
                end
            end
        end
    end
    for i = 1, nB do
        local sq = pawnB[i]
        for k = 15, 17, 2 do
            local a = sq - k
            if not bAtk[a] then
                bAtk[a] = true
                local rk = SQRANK[a]
                if rk and rk >= 2 and rk <= 5 then
                    local ff = SQFILE[a]
                    if ff >= 1 and ff <= 6 then spB = spB + 1 end
                end
            end
        end
    end
    mg = mg + (spW - spB) * 2 * W.space

    local sMg, sEg, pMg, pEg = 0, 0, 0, 0
    for i = 1, nW do
        local sq = pawnW[i]
        local f = sq % 16
        local r = SQRANK[sq]
        local fi = f + 1
        if bMax[fi - 1] <= r and bMax[fi] <= r and bMax[fi + 1] <= r then
            local pm, pe = PASS_MG[r], PASS_EG[r]
            if board[sq + 16] ~= 0 then pm = pm / 2; pe = pe / 2 end
            pe = pe + (kdist(bk, sq + 16) * 3 - kdist(wk, sq + 16) * 2) * r / 3
            pMg = pMg + pm; pEg = pEg + pe
        end
        if wCnt[fi - 1] == 0 and wCnt[fi + 1] == 0 then sMg = sMg - 9; sEg = sEg - 13 end
        if wCnt[fi] > 1 then sMg = sMg - 7; sEg = sEg - 11 end
        if board[sq - 15] == 1 or board[sq - 17] == 1 then
            sMg = sMg + 4 + r; sEg = sEg + 3
        elseif board[sq + 1] == 1 then
            sMg = sMg + 3 + r; sEg = sEg + 2
        end
    end
    for i = 1, nB do
        local sq = pawnB[i]
        local f = sq % 16
        local r = SQRANK[sq]
        local rr = 7 - r
        local fi = f + 1
        if wMin[fi - 1] >= r and wMin[fi] >= r and wMin[fi + 1] >= r then
            local pm, pe = PASS_MG[rr], PASS_EG[rr]
            if board[sq - 16] ~= 0 then pm = pm / 2; pe = pe / 2 end
            pe = pe + (kdist(wk, sq - 16) * 3 - kdist(bk, sq - 16) * 2) * rr / 3
            pMg = pMg - pm; pEg = pEg - pe
        end
        if bCnt[fi - 1] == 0 and bCnt[fi + 1] == 0 then sMg = sMg + 9; sEg = sEg + 13 end
        if bCnt[fi] > 1 then sMg = sMg + 7; sEg = sEg + 11 end
        if board[sq + 15] == 7 or board[sq + 17] == 7 then
            sMg = sMg - (4 + rr); sEg = sEg - 3
        elseif board[sq + 1] == 7 then
            sMg = sMg - (3 + rr); sEg = sEg - 2
        end
    end
    mg = mg + sMg * W.pawns + pMg * W.passed
    eg = eg + sEg * W.pawns + pEg * W.passed

    local unitsW, unitsB, attW, attB = 0, 0, 0, 0
    local pieceMg, pieceEg = 0, 0
    for i = 1, nP do
        local sq = pcSq[i]
        local p = board[sq]
        local t = PT[p]
        local col = PCOL[p]
        local enemy = 1 - col
        local eAtk = col == 0 and bAtk or wAtk
        local ekSq = col == 0 and bk or wk
        local ekf, ekr = SQFILE[ekSq], SQRANK[ekSq]
        local zLo, zHi
        if col == 0 then zLo, zHi = -2, 1 else zLo, zHi = -1, 2 end
        local f, r = SQFILE[sq], SQRANK[sq]
        local fi = f + 1
        local cnt, hits = 0, 0
        local pm, pe = 0, 0
        local wgt

        if t == 2 then
            wgt = 2
            for k = 1, 8 do
                local to = sq + KN[k]
                local tp = board[to]
                if tp == 0 or PCOL[tp] == enemy then
                    if not eAtk[to] then cnt = cnt + 1 end
                    local dr = SQRANK[to] - ekr
                    if abs(SQFILE[to] - ekf) <= 1 and dr >= zLo and dr <= zHi then hits = hits + 1 end
                end
            end
            pm = (cnt - 4) * 4 * W.mob; pe = (cnt - 4) * 3
            local rr = col == 0 and r or 7 - r
            if rr >= 3 and rr <= 5 then
                local prot, safe
                if col == 0 then
                    prot = board[sq - 15] == 1 or board[sq - 17] == 1
                    safe = bMax[fi - 1] <= r and bMax[fi + 1] <= r
                else
                    prot = board[sq + 15] == 7 or board[sq + 17] == 7
                    safe = wMin[fi - 1] >= r and wMin[fi + 1] >= r
                end
                if prot and safe then pm = pm + 20 * W.outpost; pe = pe + 10 end
            end
        elseif t == 3 then
            wgt = 2
            for k = 1, 4 do
                local d = BD[k]
                local to = sq + d
                while true do
                    local tp = board[to]
                    if tp == 0 or PCOL[tp] == enemy then
                        if not eAtk[to] then cnt = cnt + 1 end
                        local dr = SQRANK[to] - ekr
                        if abs(SQFILE[to] - ekf) <= 1 and dr >= zLo and dr <= zHi then hits = hits + 1 end
                        if tp ~= 0 then break end
                        to = to + d
                    else
                        break
                    end
                end
            end
            pm = (cnt - 6) * 4 * W.mob; pe = (cnt - 6) * 5
            local rr = col == 0 and r or 7 - r
            if rr >= 3 and rr <= 5 then
                local prot, safe
                if col == 0 then
                    prot = board[sq - 15] == 1 or board[sq - 17] == 1
                    safe = bMax[fi - 1] <= r and bMax[fi + 1] <= r
                else
                    prot = board[sq + 15] == 7 or board[sq + 17] == 7
                    safe = wMin[fi - 1] >= r and wMin[fi + 1] >= r
                end
                if prot and safe then pm = pm + 10 * W.outpost; pe = pe + 5 end
            end
        elseif t == 4 then
            wgt = 3
            for k = 1, 4 do
                local d = RD[k]
                local to = sq + d
                while true do
                    local tp = board[to]
                    if tp == 0 or PCOL[tp] == enemy then
                        if not eAtk[to] then cnt = cnt + 1 end
                        local dr = SQRANK[to] - ekr
                        if abs(SQFILE[to] - ekf) <= 1 and dr >= zLo and dr <= zHi then hits = hits + 1 end
                        if tp ~= 0 then break end
                        to = to + d
                    else
                        break
                    end
                end
            end
            pm = (cnt - 7) * 2 * W.mob; pe = (cnt - 7) * 4
            local ownC = col == 0 and wCnt[fi] or bCnt[fi]
            local enC = col == 0 and bCnt[fi] or wCnt[fi]
            if ownC == 0 then
                if enC == 0 then pm = pm + 22; pe = pe + 12 else pm = pm + 12; pe = pe + 8 end
            end
        else
            wgt = 5
            for k = 1, 8 do
                local d = KG[k]
                local to = sq + d
                while true do
                    local tp = board[to]
                    if tp == 0 or PCOL[tp] == enemy then
                        if not eAtk[to] then cnt = cnt + 1 end
                        local dr = SQRANK[to] - ekr
                        if abs(SQFILE[to] - ekf) <= 1 and dr >= zLo and dr <= zHi then hits = hits + 1 end
                        if tp ~= 0 then break end
                        to = to + d
                    else
                        break
                    end
                end
            end
            pm = (cnt - 14) * 1 * W.mob; pe = (cnt - 14) * 2
        end

        if eAtk[sq] then pm = pm - 18; pe = pe - 12 end

        if hits > 0 then
            if col == 0 then attW = attW + 1; unitsW = unitsW + wgt + hits
            else attB = attB + 1; unitsB = unitsB + wgt + hits end
        end
        if col == 0 then pieceMg = pieceMg + pm; pieceEg = pieceEg + pe
        else pieceMg = pieceMg - pm; pieceEg = pieceEg - pe end
    end
    mg = mg + pieceMg; eg = eg + pieceEg

    if attW >= 2 then mg = mg + min(500, unitsW * unitsW / 4) * W.king end
    if attB >= 2 then mg = mg - min(500, unitsB * unitsB / 4) * W.king end
    mg = mg + (kingShield(0, wk) - kingShield(1, bk)) * W.shield

    if bishW >= 2 then mg = mg + 32; eg = eg + 50 end
    if bishB >= 2 then mg = mg - 32; eg = eg - 50 end

    for i = 1, nW do local sq = pawnW[i]; wAtk[sq + 15] = nil; wAtk[sq + 17] = nil end
    for i = 1, nB do local sq = pawnB[i]; bAtk[sq - 15] = nil; bAtk[sq - 17] = nil end

    local ph = phase
    if ph > 24 then ph = 24 end

    if ph <= 6 then
        local lead = egS + pEg
        if lead > 350 or lead < -350 then
            local winK, loseK = wk, bk
            if lead < 0 then winK, loseK = bk, wk end
            local lf, lr = SQFILE[loseK], SQRANK[loseK]
            local cdist = abs(lf - 3.5) + abs(lr - 3.5)
            local mop = cdist * 8 + (7 - kdist(winK, loseK)) * 5
            if lead > 0 then eg = eg + mop else eg = eg - mop end
        end
    end

    local score = (mg * ph + eg * (24 - ph)) / 24

    if score > 0 and nW == 0 and npm[0] - npm[1] < 400 then score = score / 4
    elseif score < 0 and nB == 0 and npm[1] - npm[0] < 400 then score = score / 4 end

    if side == 1 then score = -score end
    score = score + 10
    if halfmove > 24 then score = score * (124 - min(halfmove, 100)) / 100 end
    return floor(score)
end

local tKey, tMove, tScore, tDepth, tFlag, tAge = {}, {}, {}, {}, {}, {}
for i = 1, TT_SIZE do tKey[i] = 0; tMove[i] = 0; tScore[i] = 0; tDepth[i] = 0; tFlag[i] = 0; tAge[i] = 0 end
local curAge = 0

local killer1, killer2, counter, hist = {}, {}, {}, {}
local plyMove, plyPiece, staticStack, quietList = {}, {}, {}, {}
for i = 0, MAX_PLY + 4 do quietList[i] = {} end
local pvTable, pvLen = {}, {}
for i = 0, MAX_PLY + 4 do pvTable[i] = {}; pvLen[i] = i end

local LMR = {}
for d = 1, 63 do
    LMR[d] = {}
    for m = 1, 63 do LMR[d][m] = floor(0.75 + math.log(d) * math.log(m) / 2.25) end
end
local LMP = {[1] = 4, [2] = 7, [3] = 12, [4] = 19, [5] = 28}

local nodes, aborted = 0, false
local startClock, budget, wallCap, waited, sliceStart = 0, 1, 1, 0, 0
local mustFinish = false
local yieldEnabled = task ~= nil
local SLICE = 0.006
local rootBest, rootScore, rootPrevBest = 0, 0, 0

API.Yield = yieldEnabled
function API:SetYield(v) yieldEnabled = v and true or false; self.Yield = yieldEnabled end

local function timeUp()
    if mustFinish then return false end
    local t = clock()
    local real = t - startClock
    if real - waited >= budget or real >= wallCap then
        aborted = true
        return true
    end
    if yieldEnabled and t - sliceStart >= SLICE then
        yieldFn()
        local t2 = clock()
        waited = waited + (t2 - t)
        sliceStart = t2
    end
    return false
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

local function scoreMoves(ply, n, ttMove)
    local list, sc = mvList[ply], mvScore[ply]
    local k1, k2 = killer1[ply], killer2[ply]
    local cm = 0
    if ply > 0 then
        local pm = plyMove[ply - 1]
        if pm and pm ~= 0 then
            cm = counter[plyPiece[ply - 1] * 256 + band(rshift(pm, 8), 255)] or 0
        end
    end
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
            if band(flags, 8) ~= 0 then
                local vv = band(flags, 1) ~= 0 and 100 or SEEV[PT[board[to]]]
                local at = PT[board[from]]
                local av = SEEV[at]
                if vv >= av or see(m) >= 0 then
                    s = 3000000 + vv * 16 - at
                else
                    s = -2000000 + vv * 16 - at
                end
                if promo ~= 0 then
                    if promo == 5 then s = s + 100000 else s = -2500000 end
                end
            elseif promo ~= 0 then
                s = promo == 5 and 3500000 or -3000000
            elseif m == k1 then s = 2000000
            elseif m == k2 then s = 1900000
            elseif m == cm then s = 1800000
            else
                s = hist[board[from] * 256 + to] or 0
            end
        end
        sc[i] = s
    end
end

local qsearch
qsearch = function(alpha, beta, ply)
    nodes = nodes + 1
    if band(nodes, 127) == 0 then timeUp() end
    if aborted then return 0 end
    local us = side
    local inChk = attacked(kingSq[us], 1 - us)
    if ply >= MAX_PLY - 1 then return evaluate() end
    local best, stand = -INF, 0
    if not inChk then
        stand = evaluate()
        best = stand
        if stand >= beta then return stand end
        if stand > alpha then alpha = stand end
    end
    local n = genMoves(ply, not inChk)
    scoreMoves(ply, n, 0)
    local list, sc = mvList[ply], mvScore[ply]
    local legal = 0
    for i = 1, n do
        local bi, bs = i, sc[i]
        for j = i + 1, n do
            if sc[j] > bs then bs = sc[j]; bi = j end
        end
        if bi ~= i then
            list[i], list[bi] = list[bi], list[i]
            sc[i], sc[bi] = sc[bi], sc[i]
        end
        local m = list[i]
        local skip = false
        if not inChk then
            local promo = band(rshift(m, 16), 7)
            if bs < 0 then
                skip = true
            elseif promo == 0 then
                local to = band(rshift(m, 8), 255)
                local flags = rshift(m, 19)
                local vv = band(flags, 1) ~= 0 and 100 or SEEV[PT[board[to]]]
                if stand + vv + 200 <= alpha then skip = true end
            end
        end
        if not skip then
            makeMove(m)
            if not attacked(kingSq[us], 1 - us) then
                legal = legal + 1
                local score = -qsearch(-beta, -alpha, ply + 1)
                unmakeMove()
                if aborted then return 0 end
                if score > best then
                    best = score
                    if score > alpha then
                        alpha = score
                        if score >= beta then break end
                    end
                end
            else
                unmakeMove()
            end
        end
    end
    if inChk and legal == 0 then return -MATE + ply end
    return best
end

local search
search = function(depth, alpha, beta, ply, nullOk)
    nodes = nodes + 1
    if band(nodes, 127) == 0 then timeUp() end
    if aborted then return 0 end

    pvLen[ply] = ply
    local isPV = (beta - alpha) > 1
    local us = side
    local them = 1 - us
    local inChk = attacked(kingSq[us], them)

    if ply > 0 then
        if halfmove >= 100 or isRepetition() then return drawScore(ply) end
        if ply >= MAX_PLY - 1 then return evaluate() end
        local a = -MATE + ply
        if alpha < a then alpha = a end
        local b = MATE - ply - 1
        if beta > b then beta = b end
        if alpha >= beta then return alpha end
    end

    if inChk then depth = depth + 1 end
    if depth <= 0 then return qsearch(alpha, beta, ply) end

    local ttMove = 0
    local idx = h1 % TT_SIZE + 1
    if tKey[idx] == h2 then
        ttMove = tMove[idx]
        local ttScore = tScore[idx]
        if ttScore >= MATE_BOUND then ttScore = ttScore - ply
        elseif ttScore <= -MATE_BOUND then ttScore = ttScore + ply end
        if not isPV and ply > 0 and tDepth[idx] >= depth then
            local fl = tFlag[idx]
            if fl == TT_EXACT or (fl == TT_LOWER and ttScore >= beta) or (fl == TT_UPPER and ttScore <= alpha) then
                return ttScore
            end
        end
    end
    if ply == 0 and rootPrevBest ~= 0 then ttMove = rootPrevBest end

    local static = 0
    local improving = false
    if not inChk then
        static = evaluate()
        staticStack[ply] = static
        improving = ply >= 2 and staticStack[ply - 2] ~= -INF and static > staticStack[ply - 2]
    else
        staticStack[ply] = -INF
    end

    if ply > 0 and not isPV and not inChk then
        if depth <= 7 and static - 75 * depth >= beta and abs(beta) < MATE_BOUND then
            return static - 75 * depth
        end
        if depth <= 2 and static + 260 * depth <= alpha then
            local v = qsearch(alpha, beta, ply)
            if aborted then return 0 end
            if v <= alpha then return v end
        end
        if nullOk and depth >= 3 and static >= beta and npm[us] > 0 then
            local R = 3 + floor(depth / 4) + min(2, floor((static - beta) / 200))
            makeNull()
            plyMove[ply] = 0
            local sc = -search(depth - 1 - R, -beta, -beta + 1, ply + 1, false)
            unmakeNull()
            if aborted then return 0 end
            if sc >= beta then
                if sc >= MATE_BOUND then sc = beta end
                return sc
            end
        end
    end

    if depth >= 6 and ttMove == 0 then depth = depth - 1 end

    local n = genMoves(ply, false)
    scoreMoves(ply, n, ttMove)
    local list, sc = mvList[ply], mvScore[ply]
    local quiets = quietList[ply]
    local nq = 0
    local best, bestMove = -INF, 0
    local origAlpha = alpha
    local legal = 0
    local k1, k2 = killer1[ply], killer2[ply]

    for i = 1, n do
        local bi, bs = i, sc[i]
        for j = i + 1, n do
            if sc[j] > bs then bs = sc[j]; bi = j end
        end
        if bi ~= i then
            list[i], list[bi] = list[bi], list[i]
            sc[i], sc[bi] = sc[bi], sc[i]
        end
        local m = list[i]
        local from = band(m, 255)
        local to = band(rshift(m, 8), 255)
        local promo = band(rshift(m, 16), 7)
        local flags = rshift(m, 19)
        local piece = board[from]
        local isCap = band(flags, 8) ~= 0
        local isQuiet = (not isCap) and promo == 0
        local badCap = isCap and bs < -1000000

        makeMove(m)
        if not attacked(kingSq[us], them) then
            legal = legal + 1
            plyMove[ply] = m
            plyPiece[ply] = piece
            local givesCheck = attacked(kingSq[them], us)
            local skip = false

            if ply > 0 and legal > 1 and best > -MATE_BOUND and not inChk and not givesCheck then
                if isQuiet then
                    if depth <= 3 and static + 90 + 110 * depth <= alpha then
                        skip = true
                    elseif depth <= 5 and not isPV then
                        local lim = LMP[depth]
                        if not improving then lim = floor(lim / 2) end
                        if legal > lim then skip = true end
                    end
                elseif badCap and depth <= 3 then
                    skip = true
                end
            end

            if skip then
                unmakeMove()
            else
                local newDepth = depth - 1
                local score
                if legal == 1 then
                    score = -search(newDepth, -beta, -alpha, ply + 1, true)
                else
                    local r = 0
                    if depth >= 3 and legal >= 3 and (isQuiet or badCap) and not inChk and not givesCheck then
                        r = LMR[min(depth, 63)][min(legal, 63)]
                        if isPV then r = r - 1 end
                        if not improving then r = r + 1 end
                        if m == k1 or m == k2 then r = r - 1 end
                        if isQuiet and (hist[piece * 256 + to] or 0) > 6000 then r = r - 1 end
                        if r < 0 then r = 0 end
                        if r > newDepth - 1 then r = newDepth - 1 end
                    end
                    score = -search(newDepth - r, -alpha - 1, -alpha, ply + 1, true)
                    if score > alpha and r > 0 then
                        score = -search(newDepth, -alpha - 1, -alpha, ply + 1, true)
                    end
                    if score > alpha and score < beta then
                        score = -search(newDepth, -beta, -alpha, ply + 1, true)
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
                        local child = pvTable[ply + 1]
                        local len = pvLen[ply + 1]
                        for j = ply + 1, len - 1 do pv[j] = child[j] end
                        pvLen[ply] = len > ply + 1 and len or ply + 1
                        if score >= beta then
                            if isQuiet then
                                if killer1[ply] ~= m then killer2[ply] = killer1[ply]; killer1[ply] = m end
                                local bonus = min(depth * depth * 4, 1600)
                                local key = piece * 256 + to
                                local hv = hist[key] or 0
                                hist[key] = hv + bonus - hv * bonus / 16384
                                for q = 1, nq do
                                    local qm = quiets[q]
                                    local qk = board[band(qm, 255)] * 256 + band(rshift(qm, 8), 255)
                                    local qv = hist[qk] or 0
                                    hist[qk] = qv - bonus - qv * bonus / 16384
                                end
                                if ply > 0 then
                                    local pm = plyMove[ply - 1]
                                    if pm and pm ~= 0 then
                                        counter[plyPiece[ply - 1] * 256 + band(rshift(pm, 8), 255)] = m
                                    end
                                end
                            end
                            break
                        end
                    end
                end
                if isQuiet then nq = nq + 1; quiets[nq] = m end
            end
        else
            unmakeMove()
        end
    end

    if legal == 0 then
        if inChk then return -MATE + ply end
        return 0
    end

    local flag = TT_EXACT
    if best >= beta then flag = TT_LOWER elseif best <= origAlpha then flag = TT_UPPER end
    if tKey[idx] ~= h2 or tAge[idx] ~= curAge or depth >= tDepth[idx] then
        local s = best
        if s >= MATE_BOUND then s = s + ply elseif s <= -MATE_BOUND then s = s - ply end
        tKey[idx] = h2
        tMove[idx] = bestMove
        tScore[idx] = s
        tDepth[idx] = depth
        tFlag[idx] = flag
        tAge[idx] = curAge
    end
    return best
end

local CHAR2P = {P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6, p = 7, n = 8, b = 9, r = 10, q = 11, k = 12}
local PROMO_CHAR = {[2] = "n", [3] = "b", [4] = "r", [5] = "q"}

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
    for r = 0, 7 do
        for f = 0, 7 do board[48 + r * 16 + f] = 0 end
    end
    side, castle, ep, halfmove, gamePly = 0, 0, -1, 0, 0
    kingSq[0], kingSq[1] = -1, -1
    h1, h2, mgS, egS, phase = 0, 0, 0, 0, 0
    npm[0], npm[1] = 0, 0
end

local function setupPosition(fen)
    clearState()
    local parts = {}
    for token in tostring(fen):gmatch("%S+") do parts[#parts + 1] = token end
    if #parts < 2 then return false end

    local rank = 7
    for row in parts[1]:gmatch("[^/]+") do
        local file = 0
        for i = 1, #row do
            local c = row:sub(i, i)
            local num = tonumber(c)
            if num then
                file = file + num
            else
                local p = CHAR2P[c]
                if not p or file > 7 or rank < 0 then return false end
                local sq = 48 + rank * 16 + file
                addPiece(p, sq)
                if p == 6 then kingSq[0] = sq elseif p == 12 then kingSq[1] = sq end
                file = file + 1
            end
        end
        rank = rank - 1
    end
    if kingSq[0] < 0 or kingSq[1] < 0 then return false end

    if parts[2] == "b" then
        side = 1
        h1 = bxor(h1, zSideA); h2 = bxor(h2, zSideB)
    end
    local cs = parts[3] or "-"
    if cs:find("K", 1, true) then castle = bor(castle, 1) end
    if cs:find("Q", 1, true) then castle = bor(castle, 2) end
    if cs:find("k", 1, true) then castle = bor(castle, 4) end
    if cs:find("q", 1, true) then castle = bor(castle, 8) end
    if board[52] ~= 6 then castle = band(castle, 12) end
    if board[164] ~= 12 then castle = band(castle, 3) end
    if board[55] ~= 4 then castle = band(castle, 14) end
    if board[48] ~= 4 then castle = band(castle, 13) end
    if board[167] ~= 10 then castle = band(castle, 11) end
    if board[160] ~= 10 then castle = band(castle, 7) end
    h1 = bxor(h1, zCA[castle]); h2 = bxor(h2, zCB[castle])

    local eps = parts[4]
    if eps and eps ~= "-" and #eps >= 2 then
        local f = string.byte(eps, 1) - 97
        local r = tonumber(eps:sub(2, 2))
        if f and r and f >= 0 and f <= 7 and r >= 1 and r <= 8 then
            ep = 48 + (r - 1) * 16 + f
            h1 = bxor(h1, zEpA[ep % 16]); h2 = bxor(h2, zEpB[ep % 16])
        end
    end
    halfmove = tonumber(parts[5]) or 0
    hA[0] = h1; hB[0] = h2
    return true
end

local function rootLegal()
    local n = genMoves(0, false)
    local list = mvList[0]
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

local BOOK = {
    ["rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq"] = {"d2d4", "c2c4", "g1f3"},
    ["rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq"] = {"e7e5", "c7c5", "c7c6"},
    ["rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq"] = {"g8f6", "d7d5"},
    ["rnbqkbnr/pppppppp/8/8/2P5/8/PP1PPPPP/RNBQKBNR b KQkq"] = {"e7e5", "g8f6"},
    ["rnbqkbnr/pppppppp/8/8/8/5N2/PPPPPPPP/RNBQKB1R b KQkq"] = {"g8f6", "d7d5"},
    ["rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq"] = {"g1f3"},
    ["rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq"] = {"g1f3"},
    ["rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w KQkq"] = {"c2c4"},
    ["rnbqkb1r/pppppppp/5n2/8/3P4/8/PPP1PPPP/RNBQKBNR w KQkq"] = {"c2c4"},
    ["rnbqkbnr/ppp1pppp/8/3p4/8/5N2/PPPPPPPP/RNBQKB1R w KQkq"] = {"d2d4"},
    ["r1bqkbnr/pppp1ppp/2n5/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w KQkq"] = {"f1b5"},
    ["rnbqkbnr/ppp1pppp/8/3p4/2PP4/8/PP2PPPP/RNBQKBNR b KQkq"] = {"e7e6", "c7c6"},
}
API.UseBook = true

local function bookKey(fen)
    local parts = {}
    for token in tostring(fen):gmatch("%S+") do parts[#parts + 1] = token end
    return (parts[1] or "") .. " " .. (parts[2] or "w") .. " " .. (parts[3] or "-")
end

function API:NewGame()
    for i = 1, TT_SIZE do tKey[i] = 0; tDepth[i] = 0 end
    killer1, killer2, counter, hist = {}, {}, {}, {}
end

function API:GetBestMoveFromFEN(fen, seconds, historyFENs)
    local seeds = {}
    if type(historyFENs) == "table" then
        for _, hf in ipairs(historyFENs) do
            if setupPosition(hf) then seeds[#seeds + 1] = {h1, h2} end
        end
    end
    if not setupPosition(fen) then return nil end
    if #seeds > 0 then
        local cur1, cur2 = h1, h2
        for i, s in ipairs(seeds) do hA[i - 1] = s[1]; hB[i - 1] = s[2] end
        gamePly = #seeds
        hA[gamePly] = cur1; hB[gamePly] = cur2
    end

    local limit = max(0.02, tonumber(seconds) or 2.5)
    local legal = rootLegal()
    if #legal == 0 then return nil end

    if self.UseBook then
        local entry = BOOK[bookKey(fen)]
        if entry then
            local pick = entry[math.random(1, #entry)]
            for _, m in ipairs(legal) do
                if moveToUCI(m) == pick then
                    self.LastSearch = {requestedTime = limit, elapsed = 0, depth = 0, nodes = 0, score = 0, move = pick, book = true, style = self.Style}
                    return pick, 0
                end
            end
        end
    end

    if #legal == 1 then
        local sc = evaluate()
        self.LastSearch = {requestedTime = limit, elapsed = 0, depth = 0, nodes = 0, score = sc, move = moveToUCI(legal[1]), style = self.Style}
        return moveToUCI(legal[1]), sc
    end

    nodes, aborted, mustFinish = 0, false, false
    startClock = clock()
    budget = limit
    waited = 0
    wallCap = yieldEnabled and (limit * 8 + 0.25) or (limit * 1.5 + 0.05)
    sliceStart = startClock
    curAge = (curAge + 1) % 250
    killer1, killer2, counter = {}, {}, {}
    for k, v in pairs(hist) do hist[k] = v / 2 end
    for i = 0, MAX_PLY + 4 do staticStack[i] = -INF end
    rootPrevBest = 0

    local bestMove, bestScore = legal[1], 0
    local prevScore = 0
    local completed = 0
    local stable, lastBest = 0, 0
    local pvString = ""

    for depth = 1, MAX_DEPTH do
        mustFinish = depth <= 2
        local alpha, beta, delta = -INF, INF, 28
        if depth >= 5 then alpha, beta = prevScore - delta, prevScore + delta end

        local score
        while true do
            rootBest = 0
            score = search(depth, alpha, beta, 0, false)
            if aborted then break end
            if score <= alpha and alpha > -INF then
                beta = floor((alpha + beta) / 2)
                alpha = max(score - delta, -INF)
                delta = delta * 2
                if delta > 700 then alpha = -INF end
            elseif score >= beta and beta < INF then
                beta = min(score + delta, INF)
                delta = delta * 2
                if delta > 700 then beta = INF end
            else
                break
            end
        end

        if aborted then
            if rootBest ~= 0 then bestMove = rootBest; bestScore = rootScore end
            break
        end

        if rootBest ~= 0 then bestMove = rootBest end
        bestScore = score
        prevScore = score
        completed = depth
        rootPrevBest = bestMove

        local pv = {}
        for j = 0, pvLen[0] - 1 do
            local pm = pvTable[0][j]
            if pm and pm ~= 0 then pv[#pv + 1] = moveToUCI(pm) end
        end
        pvString = table.concat(pv, " ")

        if bestMove == lastBest then stable = stable + 1 else stable = 0 end
        lastBest = bestMove

        local spent = (clock() - startClock) - waited
        if abs(score) >= MATE_BOUND and depth >= 4 then break end
        if spent >= limit * 0.55 then break end
        if depth >= 8 and stable >= 4 and spent >= limit * 0.3 then break end
    end
    mustFinish = false

    local elapsed = clock() - startClock
    self.LastSearch = {
        requestedTime = limit,
        elapsed = elapsed,
        computeTime = elapsed - waited,
        depth = completed,
        nodes = nodes,
        score = bestScore,
        move = moveToUCI(bestMove),
        pv = pvString,
        style = self.Style,
    }
    return moveToUCI(bestMove), bestScore
end

function API:Analyze(fen, seconds, historyFENs)
    local move, score = self:GetBestMoveFromFEN(fen, seconds, historyFENs)
    local info = self.LastSearch or {}
    return {
        move = move,
        score = score,
        api = self.Name,
        version = self.Version,
        nodes = info.nodes or nodes,
        depth = info.depth,
        elapsed = info.elapsed,
        requestedTime = info.requestedTime,
        pv = info.pv,
        style = self.Style,
    }
end

function API:MakeMoveFEN(fen, uci)
    if not setupPosition(fen) then return nil end
    local fullmove = 1
    do
        local t = {}
        for token in tostring(fen):gmatch("%S+") do t[#t + 1] = token end
        fullmove = tonumber(t[6]) or 1
    end
    for _, m in ipairs(rootLegal()) do
        if moveToUCI(m) == uci then
            local mover = side
            makeMove(m)
            local rows = {}
            for r = 7, 0, -1 do
                local row, empty = "", 0
                for f = 0, 7 do
                    local p = board[48 + r * 16 + f]
                    if p == 0 then empty = empty + 1
                    else
                        if empty > 0 then row = row .. empty; empty = 0 end
                        local ch = ("PNBRQKpnbrqk"):sub(p, p)
                        row = row .. ch
                    end
                end
                if empty > 0 then row = row .. empty end
                rows[#rows + 1] = row
            end
            local cs = ""
            if band(castle, 1) ~= 0 then cs = cs .. "K" end
            if band(castle, 2) ~= 0 then cs = cs .. "Q" end
            if band(castle, 4) ~= 0 then cs = cs .. "k" end
            if band(castle, 8) ~= 0 then cs = cs .. "q" end
            if cs == "" then cs = "-" end
            local eps = "-"
            if ep >= 0 then eps = sqName(ep) end
            if mover == 1 then fullmove = fullmove + 1 end
            return table.concat(rows, "/") .. " " .. (side == 0 and "w" or "b") .. " " .. cs .. " " .. eps
                .. " " .. halfmove .. " " .. fullmove
        end
    end
    return nil
end

function API:Perft(fen, depth)
    if not setupPosition(fen) then return nil end
    local function perft(d, ply)
        if d == 0 then return 1 end
        local n = genMoves(ply, false)
        local total = 0
        local us = side
        local list = mvList[ply]
        local local_moves = {}
        for i = 1, n do local_moves[i] = list[i] end
        for i = 1, n do
            makeMove(local_moves[i])
            if not attacked(kingSq[us], 1 - us) then total = total + perft(d - 1, ply + 1) end
            unmakeMove()
        end
        return total
    end
    return perft(depth, 0)
end

return API

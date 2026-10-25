local API = {}
API.Name = "OcilotX Nova"
API.Version = "2.0.3-frame-safe"
API.Description = "Deep-search chess analysis API with exact time budgeting and cooperative scheduling"

local WHITE = 0
local BLACK = 1

local INF = 1000000
local MATE = 900000
local MAX_PLY = 64

local PIECE_VALUE = {
    p = 100,
    n = 320,
    b = 330,
    r = 500,
    q = 900,
    k = 20000,
}

local KNIGHT_DELTAS = {31, 33, 14, -14, -31, -33, 18, -18}
local BISHOP_DELTAS = {15, -15, 17, -17}
local ROOK_DELTAS = {1, -1, 16, -16}
local KING_DELTAS = {1, -1, 15, -15, 16, -16, 17, -17}

local PST = {
    p = {
        0,  0,  0,  0,  0,  0,  0,  0,
       10, 10,  0,-10,-10,  0, 10, 10,
        5,  5,  5, 10, 10,  5,  5,  5,
        0,  0,  8, 15, 15,  8,  0,  0,
        0,  0,  6, 12, 12,  6,  0,  0,
        5,  5,  0, -8, -8,  0,  5,  5,
       -5,-10,-10,-20,-20,-10,-10, -5,
        0,  0,  0,  0,  0,  0,  0,  0,
    },
    n = {
      -50,-40,-30,-30,-30,-30,-40,-50,
      -40,-20,  0,  5,  5,  0,-20,-40,
      -30,  5, 15, 20, 20, 15,  5,-30,
      -30,  0, 20, 25, 25, 20,  0,-30,
      -30,  5, 20, 25, 25, 20,  5,-30,
      -30,  0, 15, 20, 20, 15,  0,-30,
      -40,-20,  0,  0,  0,  0,-20,-40,
      -50,-40,-30,-30,-30,-30,-40,-50,
    },
    b = {
      -20,-10,-10,-10,-10,-10,-10,-20,
      -10,  5,  0,  0,  0,  0,  5,-10,
      -10, 10, 10, 10, 10, 10, 10,-10,
      -10,  0, 10, 15, 15, 10,  0,-10,
      -10,  5,  5, 15, 15,  5,  5,-10,
      -10,  0,  5, 10, 10,  5,  0,-10,
      -10,  0,  0,  0,  0,  0,  0,-10,
      -20,-10,-10,-10,-10,-10,-10,-20,
    },
    r = {
        0,  0,  5, 10, 10,  5,  0,  0,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
        5, 10, 10, 10, 10, 10, 10,  5,
        0,  0,  5, 10, 10,  5,  0,  0,
    },
    q = {
      -20,-10,-10, -5, -5,-10,-10,-20,
      -10,  0,  0,  0,  0,  0,  0,-10,
      -10,  0,  5,  5,  5,  5,  0,-10,
       -5,  0,  5,  5,  5,  5,  0, -5,
        0,  0,  5,  5,  5,  5,  0, -5,
      -10,  5,  5,  5,  5,  5,  0,-10,
      -10,  0,  5,  0,  0,  0,  0,-10,
      -20,-10,-10, -5, -5,-10,-10,-20,
    },
    k = {
       20, 30, 10,  0,  0, 10, 30, 20,
       20, 20,  0,  0,  0,  0, 20, 20,
      -10,-20,-20,-20,-20,-20,-20,-10,
      -20,-30,-30,-40,-40,-30,-30,-20,
      -30,-40,-40,-50,-50,-40,-40,-30,
      -30,-40,-40,-50,-50,-40,-40,-30,
      -30,-40,-40,-50,-50,-40,-40,-30,
      -30,-40,-40,-50,-50,-40,-40,-30,
    },
}

local TT = {}
local killer1 = {}
local killer2 = {}
local history = {}
local nodes = 0
local deadline = 0
local aborted = false

local CLOCK_CHECK_EVERY_NODES = 8
local SEARCH_SLICE_SECONDS = 0.0025

local function isInside(sq)
    return sq >= 0 and sq < 128 and (sq % 16) < 8
end

local function isWhitePiece(p)
    return p and p ~= "." and p:match("%u") ~= nil
end

local function pieceSide(p)
    if not p or p == "." then return nil end
    return isWhitePiece(p) and WHITE or BLACK
end

local function opposite(side)
    return side == WHITE and BLACK or WHITE
end

local function copyState(s)
    local n = {
        board = {},
        side = s.side,
        castling = s.castling,
        ep = s.ep,
        halfmove = s.halfmove,
        fullmove = s.fullmove,
    }
    for i = 0, 127 do
        n.board[i] = s.board[i]
    end
    return n
end

local function squareName(sq)
    local file = sq % 16
    local rank = math.floor(sq / 16)
    return string.char(97 + file) .. tostring(rank + 1)
end

local function parseSquare(text)
    if type(text) ~= "string" or #text < 2 then return nil end
    local file = string.byte(text, 1) - 97
    local rank = tonumber(text:sub(2, 2))
    if not file or not rank or file < 0 or file > 7 or rank < 1 or rank > 8 then
        return nil
    end
    return (rank - 1) * 16 + file
end

local function parseFEN(fen)
    local parts = {}
    for token in tostring(fen):gmatch("%S+") do
        parts[#parts + 1] = token
    end
    if #parts < 4 then return nil end

    local state = {
        board = {},
        side = parts[2] == "b" and BLACK or WHITE,
        castling = parts[3] == "-" and "" or parts[3],
        ep = parts[4] == "-" and -1 or (parseSquare(parts[4]) or -1),
        halfmove = tonumber(parts[5]) or 0,
        fullmove = tonumber(parts[6]) or 1,
    }

    for i = 0, 127 do
        state.board[i] = nil
    end

    local rank = 7
    for row in parts[1]:gmatch("[^/]+") do
        local file = 0
        for i = 1, #row do
            local c = row:sub(i, i)
            local n = tonumber(c)
            if n then
                for _ = 1, n do
                    state.board[rank * 16 + file] = "."
                    file = file + 1
                end
            else
                state.board[rank * 16 + file] = c
                file = file + 1
            end
        end
        rank = rank - 1
    end

    return state
end

local function findKing(state, side)
    local wanted = side == WHITE and "K" or "k"
    for sq = 0, 127 do
        if isInside(sq) and state.board[sq] == wanted then
            return sq
        end
    end
    return nil
end

local function attackedBy(state, sq, attacker)
    if not sq then return false end

    local pawn = attacker == WHITE and "P" or "p"
    local knight = attacker == WHITE and "N" or "n"
    local bishop = attacker == WHITE and "B" or "b"
    local rook = attacker == WHITE and "R" or "r"
    local queen = attacker == WHITE and "Q" or "q"
    local king = attacker == WHITE and "K" or "k"

    local pawnSources
    if attacker == WHITE then
        pawnSources = {sq - 15, sq - 17}
    else
        pawnSources = {sq + 15, sq + 17}
    end
    for _, from in ipairs(pawnSources) do
        if isInside(from) and state.board[from] == pawn then
            return true
        end
    end

    for _, d in ipairs(KNIGHT_DELTAS) do
        local from = sq + d
        if isInside(from) and state.board[from] == knight then
            return true
        end
    end

    for _, d in ipairs(KING_DELTAS) do
        local from = sq + d
        if isInside(from) and state.board[from] == king then
            return true
        end
    end

    for _, d in ipairs(BISHOP_DELTAS) do
        local from = sq + d
        while isInside(from) do
            local p = state.board[from]
            if p and p ~= "." then
                if p == bishop or p == queen then return true end
                break
            end
            from = from + d
        end
    end

    for _, d in ipairs(ROOK_DELTAS) do
        local from = sq + d
        while isInside(from) do
            local p = state.board[from]
            if p and p ~= "." then
                if p == rook or p == queen then return true end
                break
            end
            from = from + d
        end
    end

    return false
end

local function inCheck(state, side)
    return attackedBy(state, findKing(state, side), opposite(side))
end

local function makeMove(state, move)
    local n = copyState(state)
    local p = n.board[move.from]
    local captured = n.board[move.to]
    n.board[move.from] = "."

    if move.ep then
        local capSq = state.side == WHITE and (move.to - 16) or (move.to + 16)
        captured = n.board[capSq]
        n.board[capSq] = "."
    end

    local placed = move.promotion and (state.side == WHITE and move.promotion:upper() or move.promotion:lower()) or p
    n.board[move.to] = placed

    if move.castle then
        if move.to > move.from then
            local rookFrom = state.side == WHITE and 7 or 119
            local rookTo = state.side == WHITE and 5 or 117
            n.board[rookTo] = n.board[rookFrom]
            n.board[rookFrom] = "."
        else
            local rookFrom = state.side == WHITE and 0 or 112
            local rookTo = state.side == WHITE and 3 or 115
            n.board[rookTo] = n.board[rookFrom]
            n.board[rookFrom] = "."
        end
    end

    local rights = n.castling
    local fromName = squareName(move.from)
    local toName = squareName(move.to)
    if p == "K" then rights = rights:gsub("K", ""):gsub("Q", "") end
    if p == "k" then rights = rights:gsub("k", ""):gsub("q", "") end
    if fromName == "a1" or toName == "a1" then rights = rights:gsub("Q", "") end
    if fromName == "h1" or toName == "h1" then rights = rights:gsub("K", "") end
    if fromName == "a8" or toName == "a8" then rights = rights:gsub("q", "") end
    if fromName == "h8" or toName == "h8" then rights = rights:gsub("k", "") end
    n.castling = rights

    if math.abs(move.to - move.from) == 32 and p:lower() == "p" then
        n.ep = state.side == WHITE and move.from + 16 or move.from - 16
    else
        n.ep = -1
    end

    n.halfmove = (p:lower() == "p" or captured ~= ".") and 0 or (state.halfmove + 1)
    n.fullmove = state.fullmove + (state.side == BLACK and 1 or 0)
    n.side = opposite(state.side)

    return n
end

local function pushMove(list, from, to, promotion, castle, ep)
    list[#list + 1] = {
        from = from,
        to = to,
        promotion = promotion,
        castle = castle,
        ep = ep,
    }
end

local function pseudoMoves(state, capturesOnly)
    local moves = {}
    local side = state.side

    for sq = 0, 127 do
        if isInside(sq) then
            local p = state.board[sq]
            if p and p ~= "." and pieceSide(p) == side then
                local kind = p:lower()

                if kind == "p" then
                    local dir = side == WHITE and 16 or -16
                    local startRank = side == WHITE and 1 or 6
                    local promoRank = side == WHITE and 7 or 0
                    local one = sq + dir
                    if not capturesOnly and isInside(one) and state.board[one] == "." then
                        if math.floor(one / 16) == promoRank then
                            for _, promo in ipairs({"q", "r", "b", "n"}) do
                                pushMove(moves, sq, one, promo)
                            end
                        else
                            pushMove(moves, sq, one)
                            local two = sq + dir * 2
                            if math.floor(sq / 16) == startRank and state.board[two] == "." then
                                pushMove(moves, sq, two)
                            end
                        end
                    end

                    for _, dd in ipairs(side == WHITE and {15,17} or {-15,-17}) do
                        local to = sq + dd
                        if isInside(to) then
                            local target = state.board[to]
                            if target and target ~= "." and pieceSide(target) ~= side then
                                if math.floor(to / 16) == promoRank then
                                    for _, promo in ipairs({"q", "r", "b", "n"}) do
                                        pushMove(moves, sq, to, promo)
                                    end
                                else
                                    pushMove(moves, sq, to)
                                end
                            elseif to == state.ep then
                                pushMove(moves, sq, to, nil, nil, true)
                            end
                        end
                    end

                elseif kind == "n" then
                    for _, d in ipairs(KNIGHT_DELTAS) do
                        local to = sq + d
                        if isInside(to) then
                            local target = state.board[to]
                            if target == "." or (target and pieceSide(target) ~= side) then
                                if not capturesOnly or (target and target ~= ".") then
                                    pushMove(moves, sq, to)
                                end
                            end
                        end
                    end

                elseif kind == "b" or kind == "r" or kind == "q" then
                    local deltas
                    if kind == "b" then deltas = BISHOP_DELTAS
                    elseif kind == "r" then deltas = ROOK_DELTAS
                    else
                        deltas = {1,-1,16,-16,15,-15,17,-17}
                    end
                    for _, d in ipairs(deltas) do
                        local to = sq + d
                        while isInside(to) do
                            local target = state.board[to]
                            if target == "." then
                                if not capturesOnly then pushMove(moves, sq, to) end
                            else
                                if pieceSide(target) ~= side then pushMove(moves, sq, to) end
                                break
                            end
                            to = to + d
                        end
                    end

                elseif kind == "k" then
                    for _, d in ipairs(KING_DELTAS) do
                        local to = sq + d
                        if isInside(to) then
                            local target = state.board[to]
                            if target == "." or (target and pieceSide(target) ~= side) then
                                if not capturesOnly or (target and target ~= ".") then
                                    pushMove(moves, sq, to)
                                end
                            end
                        end
                    end

                    if not capturesOnly and not inCheck(state, side) then
                        if side == WHITE and state.castling:find("K", 1, true) then
                            if state.board[5] == "." and state.board[6] == "." and
                               not attackedBy(state, 5, BLACK) and not attackedBy(state, 6, BLACK) then
                                pushMove(moves, sq, 6, nil, true)
                            end
                        elseif side == WHITE and state.castling:find("Q", 1, true) then
                            if state.board[1] == "." and state.board[2] == "." and state.board[3] == "." and
                               not attackedBy(state, 3, BLACK) and not attackedBy(state, 2, BLACK) then
                                pushMove(moves, sq, 2, nil, true)
                            end
                        elseif side == BLACK and state.castling:find("k", 1, true) then
                            if state.board[117] == "." and state.board[118] == "." and
                               not attackedBy(state, 117, WHITE) and not attackedBy(state, 118, WHITE) then
                                pushMove(moves, sq, 118, nil, true)
                            end
                        elseif side == BLACK and state.castling:find("q", 1, true) then
                            if state.board[113] == "." and state.board[114] == "." and state.board[115] == "." and
                               not attackedBy(state, 115, WHITE) and not attackedBy(state, 114, WHITE) then
                                pushMove(moves, sq, 114, nil, true)
                            end
                        end
                    end
                end
            end
        end
    end

    return moves
end

local function legalMoves(state)
    local result = {}
    for _, move in ipairs(pseudoMoves(state, false)) do
        local nextState = makeMove(state, move)
        if not inCheck(nextState, state.side) then
            result[#result + 1] = move
        end
    end
    return result
end

local function captureMoves(state)
    local all = pseudoMoves(state, true)
    local result = {}
    for _, move in ipairs(all) do
        local nextState = makeMove(state, move)
        if not inCheck(nextState, state.side) then
            result[#result + 1] = move
        end
    end
    return result
end

local function moveKey(move)
    return squareName(move.from) .. squareName(move.to) .. (move.promotion or "")
end

local function hashState(state)
    local h = 2166136261
    for sq = 0, 127 do
        if isInside(sq) then
            local p = state.board[sq] or "."
            h = (h * 16777619 + string.byte(p)) % 2147483647
        end
    end
    h = (h * 31 + state.side) % 2147483647
    h = (h * 31 + #state.castling) % 2147483647
    h = (h * 31 + (state.ep or -1) + 2) % 2147483647
    return tostring(h)
end

local function mirroredIndex(index)
    local rank = math.floor(index / 16)
    local file = index % 16
    return (7 - rank) * 8 + file + 1
end

local function countMaterial(state, sideWanted)
    local total = 0
    for sq = 0, 127 do
        if isInside(sq) then
            local p = state.board[sq]
            if p and p ~= "." and pieceSide(p) == sideWanted then
                local k = p:lower()
                if k ~= "p" and k ~= "k" then
                    total = total + (PIECE_VALUE[k] or 0)
                end
            end
        end
    end
    return total
end

local function pawnStructureScore(state, whitePawns, blackPawns)
    local score = 0
    local whiteFiles, blackFiles = {}, {}
    for _, sq in ipairs(whitePawns) do
        local f = sq % 16
        whiteFiles[f] = (whiteFiles[f] or 0) + 1
    end
    for _, sq in ipairs(blackPawns) do
        local f = sq % 16
        blackFiles[f] = (blackFiles[f] or 0) + 1
    end

    for f = 0, 7 do
        local wf = whiteFiles[f] or 0
        local bf = blackFiles[f] or 0
        if wf > 1 then score = score - 14 * (wf - 1) end
        if bf > 1 then score = score + 14 * (bf - 1) end

        local whiteIsolated = wf > 0 and (f == 0 or (whiteFiles[f - 1] or 0) == 0) and (f == 7 or (whiteFiles[f + 1] or 0) == 0)
        local blackIsolated = bf > 0 and (f == 0 or (blackFiles[f - 1] or 0) == 0) and (f == 7 or (blackFiles[f + 1] or 0) == 0)
        if whiteIsolated then score = score - 12 * wf end
        if blackIsolated then score = score + 12 * bf end
    end

    local function passed(pawns, enemies, sign)
        local bonus = 0
        for _, sq in ipairs(pawns) do
            local file = sq % 16
            local rank = math.floor(sq / 16)
            local blocked = false
            for _, enemySq in ipairs(enemies) do
                local ef = enemySq % 16
                local er = math.floor(enemySq / 16)
                if math.abs(ef - file) <= 1 then
                    if sign > 0 and er > rank then blocked = true break end
                    if sign < 0 and er < rank then blocked = true break end
                end
            end
            if not blocked then
                local advance = sign > 0 and rank or (7 - rank)
                bonus = bonus + (10 + advance * 9)
            end
        end
        return bonus
    end

    score = score + (passed(whitePawns, blackPawns, 1))
    score = score - (passed(blackPawns, whitePawns, -1))

    local function connected(pawns, sign)
        local bonus = 0
        for _, sq in ipairs(pawns) do
            local f = sq % 16
            local r = math.floor(sq / 16)
            local left = f > 0 and state.board[r * 16 + f - 1]
            local right = f < 7 and state.board[r * 16 + f + 1]
            local wanted = sign > 0 and "P" or "p"
            if left == wanted then bonus = bonus + 5 end
            if right == wanted then bonus = bonus + 5 end
        end
        return bonus
    end

    score = score + (connected(whitePawns, 1))
    score = score - (connected(blackPawns, -1))
    return score
end

local function rookAndKingSafetyScore(state, whitePawns, blackPawns, whiteKing, blackKing)
    local score = 0

    local whitePawnFiles, blackPawnFiles = {}, {}
    for _, sq in ipairs(whitePawns) do whitePawnFiles[sq % 16] = true end
    for _, sq in ipairs(blackPawns) do blackPawnFiles[sq % 16] = true end

    local function scanRooks(side, enemyPawns, sign)
        local bonus = 0
        local wanted = side == WHITE and "R" or "r"
        for sq = 0, 127 do
            if isInside(sq) and state.board[sq] == wanted then
                local file = sq % 16
                local rank = math.floor(sq / 16)
                local ownPawn = side == WHITE and whitePawnFiles[file] or blackPawnFiles[file]
                local enemyPawn = side == WHITE and blackPawnFiles[file] or whitePawnFiles[file]
                if not ownPawn then bonus = bonus + 10 end
                if not ownPawn and not enemyPawn then bonus = bonus + 18 end
                if (side == WHITE and rank == 6) or (side == BLACK and rank == 1) then
                    bonus = bonus + (18)
                end
            end
        end
        return bonus * sign
    end

    score = score + (scanRooks(WHITE, blackPawns, 1))
    score = score + (scanRooks(BLACK, whitePawns, -1))

    local function kingSafety(kingSq, side)
        if not kingSq then return 0 end
        local enemy = opposite(side)
        local danger = 0
        local kf, kr = kingSq % 16, math.floor(kingSq / 16)
        for df = -1, 1 do
            for dr = -1, 1 do
                if not (df == 0 and dr == 0) then
                    local sq = (kr + dr) * 16 + (kf + df)
                    if isInside(sq) and attackedBy(state, sq, enemy) then
                        danger = danger + (1)
                    end
                end
            end
        end
        local shield = 0
        local dir = side == WHITE and 1 or -1
        for df = -1, 1 do
            local file = kf + df
            local rank = kr + dir
            if file >= 0 and file <= 7 and rank >= 0 and rank <= 7 then
                local p = state.board[rank * 16 + file]
                if p == (side == WHITE and "P" or "p") then shield = shield + 1 end
            end
        end
        return -(danger * 14) + shield * 7
    end

    score = score + (kingSafety(whiteKing, WHITE))
    score = score - (kingSafety(blackKing, BLACK))
    return score
end

local STYLE = {
    Balanced = {quiet = 0, capture = 0, center = 0, king = 0, pawn = 0, odd = 0},
    Aggressive = {quiet = -2, capture = 14, center = 5, king = -1, pawn = 8, odd = 3},
    Calm = {quiet = 7, capture = -3, center = 4, king = 10, pawn = 2, odd = -2},
    Defensive = {quiet = 8, capture = 1, center = 2, king = 15, pawn = 6, odd = -3},
    Tactical = {quiet = 0, capture = 18, center = 4, king = 3, pawn = 5, odd = 2},
    Trickery = {quiet = 4, capture = 5, center = 1, king = 0, pawn = 2, odd = 14},
    Positional = {quiet = 7, capture = 2, center = 12, king = 5, pawn = 9, odd = 1},
    Endgame = {quiet = 3, capture = 7, center = 2, king = 12, pawn = 16, odd = 2},
    ["Alien Gambit"] = {quiet = 4, capture = 13, center = 4, king = 2, pawn = 8, odd = 11},
    ["Willy Alien"] = {quiet = 5, capture = 11, center = 6, king = 4, pawn = 9, odd = 20},
}

API.Style = API.Style or "Balanced"
function API:SetStyle(style)
    style = tostring(style or "Balanced")
    if STYLE[style] then
        self.Style = style
        return true
    end
    return false
end

local function moveStyleScore(state, move)
    local p = STYLE[API.Style] or STYLE.Balanced
    local attacker = state.board[move.from]
    local target = state.board[move.to]
    if not attacker then return 0 end
    local piece = attacker:lower()
    local score = p.quiet
    if target and target ~= "." then
        score = score + (p.capture + math.min(20, (PIECE_VALUE[target:lower()] or 0) / 100))
    end
    if move.promotion then score = score + 25 end
    local file = move.to % 16
    local rank = math.floor(move.to / 16)
    local centerDist = math.abs(3.5 - file) + math.abs(3.5 - rank)
    score = score + (math.max(0, 5 - centerDist) * p.center)
    if piece == "k" then score = score + p.king end
    if piece == "p" then score = score + p.pawn * (math.abs(math.floor(move.to / 16) - math.floor(move.from / 16))) end
    if piece == "n" then
        local fromFile = move.from % 16
        local toFile = move.to % 16
        if math.abs(toFile - fromFile) >= 2 then score = score + p.odd end
    end
    if API.Style == "Willy Alien" and piece == "n" and target == "." then
        score = score + (10)
    end
    return score
end

local function evaluate(state)
    local score = 0
    local whiteBishops, blackBishops = 0, 0
    local whitePawns, blackPawns = {}, {}
    local whiteKing, blackKing
    local phase = 0

    for sq = 0, 127 do
        if isInside(sq) then
            local p = state.board[sq]
            if p and p ~= "." then
                local lower = p:lower()
                local value = PIECE_VALUE[lower] or 0
                local pst = PST[lower]
                local pstIndex
                if isWhitePiece(p) then
                    pstIndex = math.floor(sq / 16) * 8 + (sq % 16) + 1
                    score = score + (value + (pst and pst[pstIndex] or 0))
                    if lower == "b" then whiteBishops = whiteBishops + 1 end
                    if lower == "p" then whitePawns[#whitePawns + 1] = sq end
                    if lower == "k" then whiteKing = sq end
                    if lower == "q" or lower == "r" or lower == "b" or lower == "n" then phase = phase + (({q=4,r=2,b=1,n=1})[lower] or 0) end
                else
                    pstIndex = mirroredIndex(sq)
                    score = score - (value + (pst and pst[pstIndex] or 0))
                    if lower == "b" then blackBishops = blackBishops + 1 end
                    if lower == "p" then blackPawns[#blackPawns + 1] = sq end
                    if lower == "k" then blackKing = sq end
                    if lower == "q" or lower == "r" or lower == "b" or lower == "n" then phase = phase + (({q=4,r=2,b=1,n=1})[lower] or 0) end
                end
            end
        end
    end

    if whiteBishops >= 2 then score = score + 34 end
    if blackBishops >= 2 then score = score - 34 end

    score = score + (pawnStructureScore(state, whitePawns, blackPawns))
    score = score + (rookAndKingSafetyScore(state, whitePawns, blackPawns, whiteKing, blackKing))

    local savedSide = state.side
    state.side = WHITE
    local whiteMobility = #pseudoMoves(state, false)
    state.side = BLACK
    local blackMobility = #pseudoMoves(state, false)
    state.side = savedSide
    score = score + ((whiteMobility - blackMobility) * 2.4)

    if whiteKing and blackKing then
        local wf, wr = whiteKing % 16, math.floor(whiteKing / 16)
        local bf, br = blackKing % 16, math.floor(blackKing / 16)
        if phase <= 10 then
            score = score + ((3.5 - (math.abs(3.5 - wf) + math.abs(3.5 - wr))) * 6)
            score = score - ((3.5 - (math.abs(3.5 - bf) + math.abs(3.5 - br))) * 6)
        end
    end

    return score
end

local function staticForSide(state)
    local eval = evaluate(state)
    return state.side == WHITE and eval or -eval
end

local function orderedMoves(state, moves, ttMove, ply)
    local scored = {}
    for _, move in ipairs(moves) do
        local target = state.board[move.to]
        local attacker = state.board[move.from]
        local score = moveStyleScore(state, move)
        local key = moveKey(move)
        if ttMove and key == ttMove then score = score + 2000000 end
        if move.promotion then score = score + 900000 + (PIECE_VALUE[move.promotion] or 0) end
        if target and target ~= "." then
            score = score + (650000 + (PIECE_VALUE[target:lower()] or 0) * 12 - (PIECE_VALUE[attacker:lower()] or 0))
        end
        if ply > 0 and killer1[ply] == key then score = score + 250000 end
        if ply > 0 and killer2[ply] == key then score = score + 230000 end
        score = score + (history[attacker .. ":" .. key] or 0)
        scored[#scored + 1] = {move = move, score = score}
    end
    table.sort(scored, function(a, b) return a.score > b.score end)
    local result = {}
    for i, entry in ipairs(scored) do result[i] = entry.move end
    return result
end

local sliceClock = 0

local function timeUp(force)
    local now = os.clock()

    if not force and nodes % CLOCK_CHECK_EVERY_NODES ~= 0 then
        return false
    end

    if now >= deadline then
        aborted = true
        return true
    end
    if sliceClock == 0 then
        sliceClock = now
    elseif now - sliceClock >= SEARCH_SLICE_SECONDS then
        task.wait()
        sliceClock = os.clock()

        if sliceClock >= deadline then
            aborted = true
            return true
        end
    end

    return false
end

local function quiescence(state, alpha, beta, ply)
    nodes = nodes + (1)
    if timeUp() then return 0 end

    local checked = inCheck(state, state.side)
    local stand = checked and -INF or staticForSide(state)
    if not checked then
        if stand >= beta then return beta end
        if stand > alpha then alpha = stand end
    end
    if ply >= MAX_PLY then return checked and (-MATE + ply) or stand end

    local rawMoves = checked and legalMoves(state) or captureMoves(state)
    if checked and #rawMoves == 0 then return -MATE + ply end
    local moves = orderedMoves(state, rawMoves, nil, ply)
    for _, move in ipairs(moves) do
        local nextState = makeMove(state, move)
        local score = -quiescence(nextState, -beta, -alpha, ply + 1)
        if aborted then return 0 end
        if score >= beta then return beta end
        if score > alpha then alpha = score end
    end
    return alpha
end

local function isEndgame(state)
    return countMaterial(state, WHITE) + countMaterial(state, BLACK) <= 2600
end

local function makeNullState(state)
    local n = copyState(state)
    n.side = opposite(state.side)
    n.ep = -1
    n.halfmove = state.halfmove + 1
    return n
end

local function negamax(state, depth, alpha, beta, ply)
    nodes = nodes + (1)
    if timeUp() then return 0, nil end

    local check = inCheck(state, state.side)
    if depth <= 0 and not check then
        return quiescence(state, alpha, beta, ply), nil
    end
    if depth <= 0 and check then depth = 1 end

    local key = hashState(state)
    local entry = TT[key]
    if entry and entry.depth >= depth then
        if entry.flag == "EXACT" then return entry.score, entry.move end
        if entry.flag == "LOWER" and entry.score > alpha then alpha = entry.score end
        if entry.flag == "UPPER" and entry.score < beta then beta = entry.score end
        if alpha >= beta then return entry.score, entry.move end
    end

    if depth >= 4 and not check and not isEndgame(state) then
        local static = staticForSide(state)
        if static >= beta then
            local nullDepth = depth - 3
            local nullState = makeNullState(state)
            local nullScore = -negamax(nullState, nullDepth, -beta, -beta + 1, ply + 1)
            if aborted then return 0, nil end
            if nullScore >= beta then return nullScore, nil end
        end
    end

    local moves = legalMoves(state)
    if #moves == 0 then
        if check then return -MATE + ply, nil end
        return 0, nil
    end

    local ttMove = entry and entry.move or nil
    moves = orderedMoves(state, moves, ttMove, ply)

    local bestScore = -INF
    local bestMove = nil
    local originalAlpha = alpha
    local first = true

    for index, move in ipairs(moves) do
        local nextState = makeMove(state, move)
        local nextDepth = depth - 1
        local givesCheck = inCheck(nextState, nextState.side)
        if givesCheck and depth >= 3 then nextDepth = nextDepth + 1 end

        local score
        local quiet = not move.promotion and (state.board[move.to] == ".") and not check
        if not first and quiet and depth >= 4 and index >= 5 then
            local reduction = depth >= 7 and 2 or 1
            local probe = -negamax(nextState, math.max(1, nextDepth - reduction), -alpha - 1, -alpha, ply + 1)
            score = probe
            if not aborted and score > alpha and score < beta then
                score = -negamax(nextState, nextDepth, -beta, -alpha, ply + 1)
            end
        elseif first then
            score = -negamax(nextState, nextDepth, -beta, -alpha, ply + 1)
        else
            score = -negamax(nextState, nextDepth, -alpha - 1, -alpha, ply + 1)
            if not aborted and score > alpha and score < beta then
                score = -negamax(nextState, nextDepth, -beta, -alpha, ply + 1)
            end
        end

        if aborted then return 0, nil end
        first = false

        if score > bestScore then
            bestScore = score
            bestMove = move
        end

        if score > alpha then
            alpha = score
            if ply > 0 then
                local k = moveKey(move)
                history[state.board[move.from] .. ":" .. k] = math.min(100000, (history[state.board[move.from] .. ":" .. k] or 0) + depth * depth * 2)
            end
        end

        if alpha >= beta then
            local k = moveKey(move)
            if killer1[ply] ~= k then
                killer2[ply] = killer1[ply]
                killer1[ply] = k
            end
            break
        end
    end

    local flag = "EXACT"
    if bestScore <= originalAlpha then flag = "UPPER"
    elseif bestScore >= beta then flag = "LOWER" end
    TT[key] = {depth = depth, score = bestScore, flag = flag, move = moveKey(bestMove)}
    return bestScore, bestMove
end

local function moveToUCI(move)
    if not move then return nil end
    return squareName(move.from) .. squareName(move.to) .. (move.promotion or "")
end

local function rootSearch(state, depth, previousMove, alpha, beta)
    local moves = legalMoves(state)
    if #moves == 0 then
        return nil, inCheck(state, state.side) and (-MATE) or 0
    end

    moves = orderedMoves(state, moves, previousMove, 0)
    local bestScore = -INF
    local bestMove = nil
    local first = true

    for _, move in ipairs(moves) do
        local nextState = makeMove(state, move)
        local score
        if first then
            score = -negamax(nextState, depth - 1, -beta, -alpha, 1)
        else
            score = -negamax(nextState, depth - 1, -alpha - 1, -alpha, 1)
            if not aborted and score > alpha and score < beta then
                score = -negamax(nextState, depth - 1, -beta, -alpha, 1)
            end
        end
        if aborted then break end
        first = false
        if score > bestScore then
            bestScore = score
            bestMove = move
        end
        if score > alpha then alpha = score end
        if alpha >= beta then break end
    end

    return bestMove, bestScore
end

function API:GetBestMoveFromFEN(fen, seconds)
    local state = parseFEN(fen)
    if not state then return nil end

    local limit = tonumber(seconds) or 2.5
    limit = math.max(0.05, limit)
    local startClock = os.clock()
    deadline = startClock + limit
    nodes = 0
    aborted = false
    sliceClock = os.clock()

    TT = {}
    killer1 = {}
    killer2 = {}
    history = {}

    local legal = legalMoves(state)
    if #legal == 0 then return nil end
    if #legal == 1 then
        self.LastSearch = {requestedTime = limit, elapsed = os.clock() - startClock, depth = 0, nodes = 0, score = staticForSide(state)}
        return moveToUCI(legal[1]), staticForSide(state)
    end

    local bestMove = legal[1]
    local bestScore = -INF
    local previous = nil
    local completedDepth = 0
    local previousScore = nil

    for depth = 1, 64 do
        if os.clock() >= deadline then break end
        aborted = false

        local alpha, beta = -INF, INF
        if previousScore then
            local window = math.max(20, 80 - depth * 2)
            alpha = previousScore - window
            beta = previousScore + window
        end

        local move, score = rootSearch(state, depth, previous, alpha, beta)
        if aborted then break end

        if previousScore and move and (score <= alpha or score >= beta) then
            aborted = false
            move, score = rootSearch(state, depth, previous, -INF, INF)
            if aborted then break end
        end

        if move then
            bestMove = move
            bestScore = score
            previous = moveToUCI(move)
            previousScore = score
            completedDepth = depth
        end

        if math.abs(bestScore) >= MATE - 100 then break end
    end

    local elapsed = os.clock() - startClock
    self.LastSearch = {
        requestedTime = limit,
        elapsed = elapsed,
        depth = completedDepth,
        nodes = nodes,
        score = bestScore,
        move = moveToUCI(bestMove),
        style = self.Style,
    }

    return moveToUCI(bestMove), bestScore
end

function API:Analyze(fen, seconds)
    local move, score = self:GetBestMoveFromFEN(fen, seconds)
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
        style = self.Style,
    }
end

return API

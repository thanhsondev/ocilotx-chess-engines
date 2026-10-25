-- Independent rule implementation used only for offline tests.
local Chess = (function()
    local C = {}
    C.START = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
    local abs, floor = math.abs, math.floor
    local function file(s) return (s - 1) % 8 end
    local function rank(s) return floor((s - 1) / 8) end
    local function square(f, r) if f >= 0 and f < 8 and r >= 0 and r < 8 then return r * 8 + f + 1 end end
    local function color(p) if p and p ~= "." then return p == p:upper() and "w" or "b" end end
    local function other(c) return c == "w" and "b" or "w" end
    function C.name(s) return string.char(97 + file(s)) .. tostring(rank(s) + 1) end
    function C.index(s)
        if type(s) ~= "string" or not s:match("^[a-h][1-8]$") then return nil end
        return (tonumber(s:sub(2)) - 1) * 8 + s:byte(1) - 96
    end
    C.color, C.other = color, other
    function C.copy(p)
        local n = {b = {}, turn = p.turn, rights = p.rights, ep = p.ep, half = p.half, full = p.full}
        for s = 1, 64 do n.b[s] = p.b[s] end
        return n
    end
    function C.signature(p) return table.concat(p.b) end
    function C.parse(fen)
        if type(fen) ~= "string" then return nil, "FEN phai la chuoi" end
        local rows, turn, rights, ep, half, full = fen:match("^%s*(%S+)%s+(%S+)%s+(%S+)%s+(%S+)%s+(%d+)%s+(%d+)%s*$")
        if not rows or (turn ~= "w" and turn ~= "b") then return nil, "FEN can du 6 truong, luot w/b" end
        if rows:sub(1,1)=="/" or rows:sub(-1)=="/" or rows:find("//",1,true) then return nil,"FEN co hang rong" end
        if rights ~= "-" and (rights:find("[^KQkq]") or #rights > 4) then return nil, "Quyen nhap thanh sai" end
        local seenRights={}
        for flag in rights:gmatch(".") do if seenRights[flag] then return nil,"Lap quyen nhap thanh" end; seenRights[flag]=true end
        if tonumber(full) < 1 then return nil, "So nuoc phai >= 1" end
        local p = {b = {}, turn = turn, rights = rights == "-" and "" or rights, half = tonumber(half), full = tonumber(full)}
        local r, kings = 7, {w = 0, b = 0}
        for row in rows:gmatch("[^/]+") do
            if r < 0 then return nil, "FEN thua hang" end
            local f = 0
            for ch in row:gmatch(".") do
                local count = tonumber(ch)
                if count then
                    if count < 1 or count > 8 then return nil, "FEN sai o trong" end
                    for _ = 1, count do f = f + 1; p.b[r * 8 + f] = "." end
                elseif ch:match("[prnbqkPRNBQK]") then
                    f = f + 1; p.b[r * 8 + f] = ch
                    if ch:lower() == "k" then kings[color(ch)] = kings[color(ch)] + 1 end
                    if ch:lower() == "p" and (r == 0 or r == 7) then return nil, "Tot chua phong cap o hang cuoi" end
                else return nil, "Ky tu quan khong hop le" end
            end
            if f ~= 8 then return nil, "Moi hang FEN can dung 8 o" end
            r = r - 1
        end
        if r ~= -1 or kings.w ~= 1 or kings.b ~= 1 then return nil, "Can 8 hang va moi ben 1 vua" end
        for flag, pair in pairs({K = {5,8}, Q = {5,1}, k = {61,64}, q = {61,57}}) do
            if p.rights:find(flag,1,true) then
                local white = flag == flag:upper()
                if p.b[pair[1]] ~= (white and "K" or "k") or p.b[pair[2]] ~= (white and "R" or "r") then
                    return nil, "Quyen nhap thanh khong khop vua/xe"
                end
            end
        end
        if ep ~= "-" then
            p.ep = C.index(ep)
            if not p.ep or rank(p.ep) ~= (turn == "w" and 5 or 2) or p.b[p.ep] ~= "." or
                p.b[p.ep + (turn == "w" and -8 or 8)] ~= (turn == "w" and "p" or "P") then
                return nil, "O bat tot qua duong sai"
            end
        end
        return p
    end
    function C.fen(p)
        local rows = {}
        for r = 7, 0, -1 do
            local row, empty = "", 0
            for f = 0, 7 do
                local ch = p.b[r * 8 + f + 1]
                if ch == "." then empty = empty + 1 else
                    if empty > 0 then row = row .. empty; empty = 0 end
                    row = row .. ch
                end
            end
            if empty > 0 then row = row .. empty end
            rows[#rows + 1] = row
        end
        return table.concat(rows,"/") .. " " .. p.turn .. " " .. (p.rights ~= "" and p.rights or "-") .. " " ..
            (p.ep and C.name(p.ep) or "-") .. " " .. p.half .. " " .. p.full
    end
    local knight = {{1,2},{2,1},{2,-1},{1,-2},{-1,-2},{-2,-1},{-2,1},{-1,2}}
    local diagonal = {{1,1},{1,-1},{-1,1},{-1,-1}}
    local straight = {{1,0},{-1,0},{0,1},{0,-1}}
    function C.attacked(p, s, by)
        local f, r = file(s), rank(s)
        for _, dx in ipairs({-1,1}) do
            local a = square(f + dx, r + (by == "w" and -1 or 1))
            if a and p.b[a] == (by == "w" and "P" or "p") then return true end
        end
        for _, d in ipairs(knight) do
            local a = square(f + d[1], r + d[2])
            if a and p.b[a] == (by == "w" and "N" or "n") then return true end
        end
        for _, group in ipairs({diagonal,straight}) do
            for _, d in ipairs(group) do
                for distance = 1, 7 do
                    local a = square(f + d[1] * distance, r + d[2] * distance)
                    if not a then break end
                    local ch = p.b[a]
                    if ch ~= "." then
                        if color(ch) == by then
                            local k = ch:lower()
                            if k == "q" or (group == diagonal and k == "b") or (group == straight and k == "r") or (distance == 1 and k == "k") then return true end
                        end
                        break
                    end
                end
            end
        end
        return false
    end
    function C.inCheck(p, side)
        local king = side == "w" and "K" or "k"
        for s = 1, 64 do if p.b[s] == king then return C.attacked(p,s,other(side)) end end
        return true
    end
    function C.valid(p)
        if C.inCheck(p,other(p.turn)) then return false, "Ben vua di van bi chieu; kiem tra luot/FEN" end
        return true
    end
    function C.apply(p, m)
        local n, piece = C.copy(p), p.b[m.from]
        local capture = p.b[m.to] ~= "." or m.ep
        n.b[m.from], n.b[m.to] = ".", m.promo and (p.turn == "w" and m.promo:upper() or m.promo) or piece
        if m.ep then n.b[m.to + (p.turn == "w" and -8 or 8)] = "." end
        if m.castle then
            local rf, rt = m.to > m.from and m.from + 3 or m.from - 4, m.to > m.from and m.from + 1 or m.from - 1
            n.b[rt], n.b[rf] = n.b[rf], "."
        end
        if piece == "K" then n.rights = n.rights:gsub("[KQ]","") end
        if piece == "k" then n.rights = n.rights:gsub("[kq]","") end
        for s, flag in pairs({[1]="Q",[8]="K",[57]="q",[64]="k"}) do
            if m.from == s or m.to == s then n.rights = n.rights:gsub(flag,"") end
        end
        n.ep = piece:lower() == "p" and abs(m.to-m.from) == 16 and (m.from+m.to)/2 or nil
        n.half = (piece:lower() == "p" or capture) and 0 or p.half+1
        n.full, n.turn = p.full + (p.turn == "b" and 1 or 0), other(p.turn)
        return n
    end
    function C.legal(p)
        local moves = {}
        local function add(from, to, opts)
            if not to or color(p.b[to]) == p.turn or p.b[to]:lower() == "k" then return end
            local m = {from=from, to=to}
            if opts then for k,v in pairs(opts) do m[k]=v end end
            m.uci = C.name(from) .. C.name(to) .. (m.promo or "")
            if not C.inCheck(C.apply(p,m),p.turn) then moves[#moves+1]=m end
        end
        local function pawnMove(from,to,opts)
            if rank(to) == 0 or rank(to) == 7 then
                for _,q in ipairs({"q","r","b","n"}) do add(from,to,{promo=q}) end
            else add(from,to,opts) end
        end
        for s=1,64 do
            local piece=p.b[s]
            if color(piece)==p.turn then
                local kind,f,r=piece:lower(),file(s),rank(s)
                if kind=="p" then
                    local direction=p.turn=="w" and 1 or -1
                    local to=square(f,r+direction)
                    if to and p.b[to]=="." then
                        pawnMove(s,to)
                        local two=square(f,r+2*direction)
                        if r==(p.turn=="w" and 1 or 6) and two and p.b[two]=="." then add(s,two) end
                    end
                    for _,dx in ipairs({-1,1}) do
                        to=square(f+dx,r+direction)
                        if to and color(p.b[to])==other(p.turn) then pawnMove(s,to)
                        elseif to and to==p.ep then add(s,to,{ep=true}) end
                    end
                elseif kind=="n" then
                    for _,d in ipairs(knight) do add(s,square(f+d[1],r+d[2])) end
                else
                    local groups=kind=="b" and {diagonal} or kind=="r" and {straight} or {diagonal,straight}
                    for _,group in ipairs(groups) do
                        for _,d in ipairs(group) do
                            for dist=1,(kind=="k" and 1 or 7) do
                                local to=square(f+d[1]*dist,r+d[2]*dist)
                                if not to then break end
                                add(s,to)
                                if p.b[to]~="." then break end
                            end
                        end
                    end
                    if kind=="k" and s==(p.turn=="w" and 5 or 61) and not C.inCheck(p,p.turn) then
                        for _,kingSide in ipairs({true,false}) do
                            local flag=p.turn=="w" and (kingSide and "K" or "Q") or (kingSide and "k" or "q")
                            local delta=kingSide and 1 or -1
                            local rook=s+(kingSide and 3 or -4)
                            if p.rights:find(flag,1,true) and p.b[rook]==(p.turn=="w" and "R" or "r") and
                                p.b[s+delta]=="." and p.b[s+2*delta]=="." and (kingSide or p.b[s-3]==".") and
                                not C.attacked(p,s+delta,other(p.turn)) and not C.attacked(p,s+2*delta,other(p.turn)) then
                                add(s,s+2*delta,{castle=true})
                            end
                        end
                    end
                end
            end
        end
        return moves
    end
    function C.find(p, uci)
        for _,m in ipairs(C.legal(p)) do if m.uci == uci then return m end end
    end
    local values={p=100,n=320,b=335,r=500,q=900,k=0}
    function C.evaluate(p)
        local score=0
        for s=1,64 do
            local ch=p.b[s]
            if ch~="." then
                local kind,side=ch:lower(),color(ch)
                local r=side=="w" and rank(s) or 7-rank(s)
                local center=7-abs(3.5-file(s))-abs(3.5-rank(s))
                local bonus=kind=="p" and (r*7+center*3) or (kind=="n" or kind=="b") and center*9 or kind=="r" and r*2 or 0
                score=score+(side=="w" and 1 or -1)*(values[kind]+bonus)
            end
        end
        return p.turn=="w" and score or -score
    end
    function C.best(p, seconds, yieldFn)
        local started,nodes,aborted=os.clock(),0,false
        local root=C.legal(p)
        if #root==0 then return nil,{nodes=0,depth=0,check=C.inCheck(p,p.turn)} end
        local best,score,doneDepth=root[1],0,0
        local function order(pos,list)
            table.sort(list,function(a,b)
                local function value(m) return (values[pos.b[m.to]:lower()] or 0)*10-(values[pos.b[m.from]:lower()] or 0)+(m.promo and 9000 or 0)+(m.ep and 1000 or 0) end
                return value(a)>value(b)
            end)
        end
        local function search(pos,depth,alpha,beta,ply)
            nodes=nodes+1
            if nodes%64==0 then
                if yieldFn then yieldFn() end
                if os.clock()-started>seconds then aborted=true; return 0 end
            end
            local list=C.legal(pos)
            if #list==0 then return C.inCheck(pos,pos.turn) and -100000+ply or 0 end
            if pos.half>=100 then return 0 end
            if depth==0 then return C.evaluate(pos) end
            order(pos,list)
            local result=-1000000
            for _,m in ipairs(list) do
                local value=-search(C.apply(pos,m),depth-1,-beta,-alpha,ply+1)
                if aborted then return 0 end
                result=math.max(result,value); alpha=math.max(alpha,value)
                if alpha>=beta then break end
            end
            return result
        end
        order(p,root)
        for depth=1,4 do
            local iterBest,iterScore=nil,-1000000
            for _,m in ipairs(root) do
                local value=-search(C.apply(p,m),depth-1,-1000000,-iterScore,1)
                if aborted then break end
                if value>iterScore then iterBest,iterScore=m,value end
            end
            if aborted then break end
            best,score,doneDepth=iterBest,iterScore,depth
            for i,m in ipairs(root) do if m==best then table.remove(root,i); table.insert(root,1,best); break end end
            if os.clock()-started>seconds then break end
        end
        return best,{nodes=nodes,depth=doneDepth,score=score,ms=math.floor((os.clock()-started)*1000)}
    end
    local book={}
    -- Small verified opening repertoire; exact positions only, not generic advice.
    local lines={
        {"Italian", "e2e4 e7e5 g1f3 b8c6 f1c4 g8f6 d2d3 f8c5 e1g1 d7d6 c2c3 e8g8"},
        {"Ruy Lopez", "e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4 g8f6 e1g1 f8e7 f1e1 b7b5 a4b3 d7d6"},
        {"Sicilian", "e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6"},
        {"Caro-Kann", "e2e4 c7c6 d2d4 d7d5 b1c3 d5e4 c3e4 c8f5"},
        {"French", "e2e4 e7e6 d2d4 d7d5 b1c3 g8f6 e4e5 f6d7"},
        {"Queen's Gambit", "d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 c1g5 f8e7 e2e3 e8g8"},
        {"Slav", "d2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 e7e6"},
        {"King's Indian", "d2d4 g8f6 c2c4 g7g6 b1c3 f8g7 e2e4 d7d6 g1f3 e8g8"},
        {"London", "d2d4 d7d5 g1f3 g8f6 c1f4 e7e6 e2e3 f8d6 f1d3 e8g8"},
        {"Scotch", "e2e4 e7e5 g1f3 b8c6 d2d4 e5d4 f3d4 g8f6 b1c3 f8b4"}
    }
    local function bookKey(p) return C.signature(p)..p.turn..p.rights..tostring(p.ep) end
    for _,line in ipairs(lines) do
        local pos=assert(C.parse(C.START))
        for uci in line[2]:gmatch("%S+") do
            local move=C.find(pos,uci)
            assert(move,"Invalid book move "..line[1].." "..uci)
            local key=bookKey(pos)
            if not book[key] then book[key]={move=uci,name=line[1]} end
            pos=C.apply(pos,move)
        end
    end
    function C.bookMove(p)
        local entry=book[bookKey(p)]
        if entry then return C.find(p,entry.move),entry.name end
    end
    C.book=book
    return C
end)()


return Chess

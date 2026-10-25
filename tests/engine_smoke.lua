-- Offline engine smoke checks; no Roblox API or network is available.
local bit=require('bit')
bit32={}
for _,n in ipairs({'band','bor','bxor','bnot','rshift','lshift','arshift'}) do
    bit32[n]=function(...) return bit[n](...) % 4294967296 end
end
math.clamp=function(x,a,b)return math.max(a,math.min(b,x))end
table.create=function(n,v)local t={};for i=1,n do t[i]=v end;return t end
task={wait=function()end}
local core=dofile('tests/chess_rules.lua')
local cases={core.START,
    'rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq e6 0 2',
    'r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1',
    '8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1',
    '7k/5Q2/6K1/8/8/8/8/8 w - - 0 1'}
for _,name in ipairs({'Nova','Lith','Null','Muse'})do
    local engine=dofile('engines/'..name..'.lua')
    for i,fen in ipairs(cases)do
        local pos=assert(core.parse(fen))
        local started=os.clock()
        local ok,move,score=pcall(engine.GetBestMoveFromFEN,engine,fen,.1)
        assert(ok,name..' case '..i..' crashed: '..tostring(move))
        assert(type(move)=='string' and core.find(pos,move),name..' illegal move '..tostring(move))
        print(name,i,move,score,string.format('%.3fs',os.clock()-started))
    end
    if engine.Perft then
        local n=engine:Perft(core.START,3)
        assert(n==8902,name..' perft mismatch '..tostring(n))
        print(name,'perft3',n)
        local kiwipete=engine:Perft(cases[3],2)
        assert(kiwipete==2039,name..' Kiwipete mismatch '..tostring(kiwipete))
        local endgame=engine:Perft(cases[4],3)
        assert(endgame==2812,name..' rook endgame mismatch '..tostring(endgame))
        print(name,'kiwipete2',kiwipete,'endgame3',endgame)
    end
end

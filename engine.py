# tiny-chess engine: 0x88 board, alpha-beta + transposition table + killer
# moves + quiescence, material + piece-square evaluation, fixed node budget
# (deterministic: no clock, no unseeded randomness). Talks to the env only.
import json, os, sys, urllib.request, urllib.error

E = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("no env")
MATE = 100000
LIMIT = 30000          # nodes per move; tune after benchmarking
MAXD = 12

# piece codes: 0 empty, 1-6 white P N B R Q K, 7-12 black p n b r q k
V = [0, 100, 320, 330, 500, 900, 0, 100, 320, 330, 500, 900, 0]
TY = [0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6]

# piece-square tables, rank 8 first (standard teaching tables)
TAB = [
(0,0,0,0,0,0,0,0, 50,50,50,50,50,50,50,50, 10,10,20,30,30,20,10,10, 5,5,10,25,25,10,5,5, 0,0,0,20,20,0,0,0, 5,-5,-10,0,0,-10,-5,5, 5,10,10,-20,-20,10,10,5, 0,0,0,0,0,0,0,0),
(-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,0,0,0,-20,-40, -30,0,10,15,15,10,0,-30, -30,5,15,20,20,15,5,-30, -30,0,15,20,20,15,0,-30, -30,5,10,15,15,10,5,-30, -40,-20,0,5,5,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50),
(-20,-10,-10,-10,-10,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,10,10,5,0,-10, -10,5,5,10,10,5,5,-10, -10,0,10,10,10,10,0,-10, -10,10,10,10,10,10,10,-10, -10,5,0,0,0,0,5,-10, -20,-10,-10,-10,-10,-10,-10,-20),
(0,0,0,0,0,0,0,0, 5,10,10,10,10,10,10,5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 0,0,0,5,5,0,0,0),
(-20,-10,-10,-5,-5,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,5,5,5,0,-10, -5,0,5,5,5,5,0,-5, 0,0,5,5,5,5,0,-5, -10,5,5,5,5,5,0,-10, -10,0,5,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20),
(-30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -20,-30,-30,-40,-40,-30,-30,-20, -10,-20,-20,-20,-20,-20,-20,-10, 20,20,0,0,0,0,20,20, 20,30,10,0,0,10,30,20),
(-50,-40,-30,-20,-20,-30,-40,-50, -30,-20,-10,0,0,-10,-20,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-30,0,0,0,0,-30,-30, -50,-30,-30,-30,-30,-30,-30,-50),
]
# PST lookup by 0x88 square: PW white, PB black; tables 0-4 = P N B R Q, 5 = king mg, 6 = king eg
PW = [[0] * 64 for _ in range(7)]
PB = [[0] * 64 for _ in range(7)]
for _t in range(7):
    for _s in range(64):
        _r, _f = _s // 8, _s % 8
        PW[_t][_s] = TAB[_t][(7 - _r) * 8 + _f]
        PB[_t][_s] = TAB[_t][_r * 8 + _f]

SQS = [s for s in range(128) if not s & 0x88]
ND = (31, 33, 14, 18, -31, -33, -14, -18)
KD = (1, -1, 16, -16, 15, 17, -15, -17)
BD = (15, 17, -15, -17)
RD = (1, -1, 16, -16)

bd = bytearray(128)
side = 1
castle = 0
ep = -1
half = 0
K = [4, 116]
TT = {}
kill = [[0, 0] for _ in range(128)]
nodes = 0
abort = False
path = set()
ghist = set()
st = []

def atk(sq, by):
    # is sq attacked by colour by (1 white, -1 black)?
    if by > 0:
        for t in (sq - 15, sq - 17):
            if not t & 0x88 and bd[t] == 1:
                return 1
        n, k, bq, rq = 2, 6, (3, 5), (4, 5)
    else:
        for t in (sq + 15, sq + 17):
            if not t & 0x88 and bd[t] == 7:
                return 1
        n, k, bq, rq = 8, 12, (9, 11), (10, 11)
    for d in ND:
        t = sq + d
        if not t & 0x88 and bd[t] == n:
            return 1
    for d in KD:
        t = sq + d
        if not t & 0x88 and bd[t] == k:
            return 1
    for d in BD:
        t = sq + d
        while not t & 0x88:
            c = bd[t]
            if c:
                if c in bq:
                    return 1
                break
            t += d
    for d in RD:
        t = sq + d
        while not t & 0x88:
            c = bd[t]
            if c:
                if c in rq:
                    return 1
                break
            t += d
    return 0

def gen(cap=False):
    # pseudo-legal moves; move = from + to*128 + promo*16384
    ms = []
    w = side == 1
    for sq in SQS:
        c = bd[sq]
        if not c or (c < 7) != w:
            continue
        t = TY[c]
        if t == 1:
            d = 16 if w else -16
            last = 7 if w else 0
            start = 1 if w else 6
            one = sq + d
            if not cap and bd[one] == 0:
                if (one >> 4) == last:
                    for p in (5, 4, 3, 2):
                        ms.append(sq + one * 128 + p * 16384)
                else:
                    ms.append(sq + one * 128)
                    if (sq >> 4) == start and bd[one + d] == 0:
                        ms.append(sq + (one + d) * 128)
            for dd in (d - 1, d + 1):
                to = sq + dd
                if to & 0x88:
                    continue
                if bd[to] and (bd[to] < 7) != w:
                    if (to >> 4) == last:
                        for p in (5, 4, 3, 2):
                            ms.append(sq + to * 128 + p * 16384)
                    else:
                        ms.append(sq + to * 128)
                elif to == ep and bd[to] == 0:
                    ms.append(sq + to * 128)
        elif t == 2 or t == 6:
            for d in (ND if t == 2 else KD):
                to = sq + d
                if to & 0x88:
                    continue
                o = bd[to]
                if not o:
                    if not cap:
                        ms.append(sq + to * 128)
                elif (o < 7) != w:
                    ms.append(sq + to * 128)
        else:
            for d in (BD if t == 3 else RD if t == 4 else BD + RD):
                to = sq + d
                while not to & 0x88:
                    o = bd[to]
                    if not o:
                        if not cap:
                            ms.append(sq + to * 128)
                    elif (o < 7) != w:
                        ms.append(sq + to * 128)
                        break
                    else:
                        break
                    to += d
    if not cap:
        if w:
            if bd[4] == 6 and castle & 1 and bd[5] == 0 and bd[6] == 0 and not atk(4, -1) and not atk(5, -1) and not atk(6, -1):
                ms.append(4 + 6 * 128)
            if bd[4] == 6 and castle & 2 and bd[1] == 0 and bd[2] == 0 and bd[3] == 0 and not atk(4, -1) and not atk(3, -1) and not atk(2, -1):
                ms.append(4 + 2 * 128)
        else:
            if bd[116] == 12 and castle & 4 and bd[117] == 0 and bd[118] == 0 and not atk(116, 1) and not atk(117, 1) and not atk(118, 1):
                ms.append(116 + 118 * 128)
            if bd[116] == 12 and castle & 8 and bd[113] == 0 and bd[114] == 0 and bd[115] == 0 and not atk(116, 1) and not atk(115, 1) and not atk(114, 1):
                ms.append(116 + 114 * 128)
    return ms

def make(m):
    global side, castle, ep, half
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 7
    pc = bd[f]
    cap = bd[t]
    cs = t
    w = side == 1
    if TY[pc] == 1 and t == ep and cap == 0 and (f & 7) != (t & 7):
        cs = t - 16 if w else t + 16
        cap = bd[cs]
        bd[cs] = 0
    rk = -1
    if TY[pc] == 6 and abs(t - f) == 2:
        if t > f:
            rk = f + 3
            bd[f + 1] = bd[rk]
            bd[rk] = 0
        else:
            rk = f - 4
            bd[f - 1] = bd[rk]
            bd[rk] = 0
    bd[t] = (p + 6 if not w else p) if p else pc
    bd[f] = 0
    if TY[pc] == 6:
        K[0 if w else 1] = t
    nc = castle
    if TY[pc] == 6:
        nc &= ~(3 if w else 12)
    if f == 0 or t == 0:
        nc &= ~2
    if f == 7 or t == 7:
        nc &= ~1
    if f == 112 or t == 112:
        nc &= ~8
    if f == 119 or t == 119:
        nc &= ~4
    nep = -1
    if TY[pc] == 1 and abs(t - f) == 32:
        nep = (f + t) // 2
    nh = 0 if TY[pc] == 1 or cap else half + 1
    st.append((m, cap, cs, castle, ep, half, rk))
    castle, ep, half = nc, nep, nh
    side = -side
    if atk(K[0] if side == -1 else K[1], side):
        unmake()
        return False
    return True

def unmake():
    global side, castle, ep, half
    m, cap, cs, castle, ep, half, rk = st.pop()
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 7
    side = -side
    pc = bd[t]
    if TY[pc] == 6:
        K[0 if side == 1 else 1] = f
    bd[f] = pc if not p else (1 if side == 1 else 7)
    bd[t] = 0
    if cap:
        bd[cs] = cap
    if rk >= 0:
        if t > f:
            bd[rk] = bd[f + 1]
            bd[f + 1] = 0
        else:
            bd[rk] = bd[f - 1]
            bd[f - 1] = 0

def key():
    return (bytes(bd), side, castle, ep)

def ev():
    s = 0
    npm = 0
    nb = [0, 0]
    for sq in SQS:
        c = bd[sq]
        if not c:
            continue
        t = TY[c]
        if t == 6:
            continue
        q = (sq >> 4) * 8 + (sq & 7)
        if c < 7:
            s += V[c] + PW[t - 1][q]
            if t != 1:
                npm += V[c]
            if t == 3:
                nb[0] += 1
        else:
            s -= V[c] + PB[t - 1][q]
            if t != 1:
                npm += V[c]
            if t == 3:
                nb[1] += 1
    ph = npm if npm < 6400 else 6400
    wq = (K[0] >> 4) * 8 + (K[0] & 7)
    bq = (K[1] >> 4) * 8 + (K[1] & 7)
    s += (PW[5][wq] * ph + PW[6][wq] * (6400 - ph)) // 6400
    s -= (PB[5][bq] * ph + PB[6][bq] * (6400 - ph)) // 6400
    if nb[0] >= 2:
        s += 30
    if nb[1] >= 2:
        s -= 30
    return s if side == 1 else -s

def order(ms, ply, ttm):
    k0 = kill[ply][0]
    k1 = kill[ply][1]
    def sc(m):
        f = m & 127
        t = (m >> 7) & 127
        p = (m >> 14) & 7
        if m == ttm:
            return 1000000
        v = bd[t]
        if not v and t == ep and TY[bd[f]] == 1:
            v = 1
        if v:
            return 100000 + 10 * V[v] - V[bd[f]]
        if p:
            return 90000 + V[p]
        if m == k0:
            return 50000
        if m == k1:
            return 40000
        return 0
    ms.sort(key=sc, reverse=True)
    return ms

def qs(a, b, ply):
    global nodes, abort
    nodes += 1
    if nodes >= LIMIT:
        abort = True
        return 0
    if ply > 64:
        return ev()
    chk = atk(K[0] if side == 1 else K[1], -side)
    if not chk:
        s = ev()
        if s >= b:
            return s
        if s > a:
            a = s
        best = s
    else:
        best = -MATE - 1
    k = key()
    path.add(k)
    ms = order(gen() if chk else gen(True), ply, 0)
    legal = 0
    for m in ms:
        if not make(m):
            continue
        legal += 1
        s = -qs(-b, -a, ply + 1)
        unmake()
        if abort:
            path.discard(k)
            return 0
        if s > best:
            best = s
        if s > a:
            a = s
        if a >= b:
            path.discard(k)
            return a
    path.discard(k)
    if chk and legal == 0:
        return -MATE + ply
    return best

def search(d, a, b, ply):
    global nodes, abort
    if half >= 100:
        return 0
    k = key()
    if ply > 0 and (k in path or k in ghist):
        return 0
    if d <= 0:
        return qs(a, b, ply)
    nodes += 1
    if nodes >= LIMIT:
        abort = True
        return 0
    e = TT.get(k)
    ttm = 0
    if e:
        s, dd, fl, tm = e
        ttm = tm
        if dd >= d:
            if s > MATE - 1000:
                s -= ply
            elif s < -MATE + 1000:
                s += ply
            if fl == 0:
                return s
            if fl == 1 and s >= b:
                return s
            if fl == 2 and s <= a:
                return s
    path.add(k)
    ms = order(gen(), ply, ttm)
    best = -MATE - 1
    bm = 0
    legal = 0
    a0 = a
    for m in ms:
        t2 = (m >> 7) & 127
        cap = bd[t2] != 0
        if not make(m):
            continue
        legal += 1
        s = -search(d - 1, -b, -a, ply + 1)
        unmake()
        if abort:
            path.discard(k)
            return 0
        if s > best:
            best = s
            bm = m
        if s > a:
            a = s
        if a >= b:
            if not cap and kill[ply][0] != m:
                kill[ply][1] = kill[ply][0]
                kill[ply][0] = m
            break
    path.discard(k)
    if legal == 0:
        return -MATE + ply if atk(K[0] if side == 1 else K[1], -side) else 0
    bs = best + ply if best > MATE - 1000 else best - ply if best < -MATE + 1000 else best
    fl = 2 if best <= a0 else 1 if best >= b else 0
    TT[k] = (bs, d, fl, bm)
    return best

def legal():
    out = []
    for m in gen():
        if make(m):
            out.append(m)
            unmake()
    return out

def choose():
    global nodes, abort
    ms = order(legal(), 0, 0)
    if not ms:
        return None
    if len(ms) == 1:
        return ms[0]
    best = ms[0]
    nodes = 0
    abort = False
    path.clear()
    for d in range(1, MAXD + 1):
        a = -MATE - 1
        scored = []
        for m in ms:
            make(m)
            s = -search(d - 1, -MATE - 1, -a, 1)
            unmake()
            if abort:
                break
            scored.append((s, m))
            if s > a:
                a = s
        if abort:
            break
        scored.sort(key=lambda x: -x[0])
        best = scored[0][1]
        ms = [m for _, m in scored]
        if scored[0][0] > MATE - 1000:
            break
        if nodes >= LIMIT:
            break
    return best

def parse(fen):
    global side, castle, ep, half
    bd[:] = bytes(128)
    p = fen.split()
    for r, row in enumerate(p[0].split("/")):
        f = 0
        for ch in row:
            if ch.isdigit():
                f += int(ch)
            else:
                sq = (7 - r) * 16 + f
                bd[sq] = "PNBRQKpnbrqk".index(ch) + 1
                if ch == "K":
                    K[0] = sq
                if ch == "k":
                    K[1] = sq
                f += 1
    side = 1 if p[1] == "w" else -1
    castle = 0
    for ch in p[2]:
        castle |= {"K": 1, "Q": 2, "k": 4, "q": 8}.get(ch, 0)
    ep = -1
    if p[3] != "-":
        ep = (int(p[3][1]) - 1) * 16 + ord(p[3][0]) - 97
    half = int(p[4]) if len(p) > 4 else 0

def uci(u):
    f = (int(u[1]) - 1) * 16 + ord(u[0]) - 97
    t = (int(u[3]) - 1) * 16 + ord(u[2]) - 97
    p = "nbrq".index(u[4]) + 2 if len(u) == 5 else 0
    return f + t * 128 + p * 16384

def mou(m):
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 7
    s = chr((f & 7) + 97) + str((f >> 4) + 1) + chr((t & 7) + 97) + str((t >> 4) + 1)
    if p:
        s += "nbrq"[p - 2]
    return s

def post(path, body):
    req = urllib.request.Request(E + path, data=json.dumps(body).encode(), headers={"content-type": "application/json"})
    try:
        with urllib.request.urlopen(req) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")

START = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

while True:
    g = post("/game", {})
    if g["status"] == "done":
        break
    while g["status"] == "your_move":
        parse(g["fen"])
        parse(START)
        ghist.clear()
        ghist.add(key())
        for u in g["moves"]:
            make(uci(u))
            if half == 0:
                ghist.clear()
            ghist.add(key())
        parse(g["fen"])
        m = choose()
        if m is None:
            g = post("/resign", {"game": g["game"]})
        else:
            g = post("/move", {"game": g["game"], "move": mou(m)})
    print(f"game {g['game']}: {g['outcome']} by {g['reason']}", file=sys.stderr)
print(f"done: {g.get('wins')} won, {g.get('draws')} drawn, {g.get('losses')} lost", file=sys.stderr)

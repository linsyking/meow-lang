"""rev-wall round 1, sweep 2: CELL-LOCAL slope measurement.

Fix for sweep 1's artifacts (cell crossings and residue sawtooths):
probe each axis with 13 points at step 2 (range 24); compute the two
half-line slopes s1 (t in [0,12]) and s2 (t in [12,24]); a slope is
ACCEPTED (as the cell's linear part) only when |s1 - s2| <= AGREE --
i.e. the line stayed inside one piece.  A violation is flagged only
when the accepted slope in one axis beats the accepted slope in the
dominant axis by > MARGIN in BOTH halves.  Bounded sawtooths then
contribute <= amplitude/12 ~ 0.25 noise, below MARGIN = 0.45.

Checks (on constructible values over W2 = a^i b a^j b a^k):
  D1  lead i-dominance          D2  tail k-dominance
  P1  every prefix-sum i-dominant    P2  every suffix-sum k-dominant
  VH  V_h (k,...,i) flank swap, P1f  L-family a^i b a^{j+k},
  P2f mirror a^{i+j} b a^k
"""
import sys, random
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S, pp

X = V(0)
def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
def valtry(e, w):
    try:
        return PV.content(PV.lden(e, (PV.lab_input(w),)))
    except PV.Undefined:
        return None
def runs_of(v):
    out, cur = [], 0
    for c in v:
        if c == 'a': cur += 1
        else: out.append(cur); cur = 0
    out.append(cur)
    return out

BASES = [(5, 5, 5), (2, 8, 4), (8, 2, 4), (4, 4, 9), (9, 3, 2), (3, 9, 3),
         (6, 2, 8), (2, 6, 8)]
CAP = 300000
AGREE = 0.30
MARGIN = 0.45
TLINE = list(range(0, 26, 2))          # 13 points, range 24

def runvec(e, i, j, k):
    v = valtry(e, w2(i, j, k))
    if v is None or len(v) > CAP: return None
    return runs_of(v)

def cell_slopes(f):
    """f(t) along the line; returns (s1, s2) if all defined else None"""
    col = [f(t) for t in TLINE]
    if any(c is None for c in col): return None
    s1 = (col[6] - col[0]) / 12.0
    s2 = (col[12] - col[6]) / 12.0
    return (s1, s2)

def accepted(s):
    return s is not None and abs(s[0] - s[1]) <= AGREE

def expr_slopes(e):
    cache = {}
    def rv(i, j, k):
        if (i, j, k) not in cache: cache[(i, j, k)] = runvec(e, i, j, k)
        return cache[(i, j, k)]
    for (i0, j0, k0) in BASES:
        for t in TLINE:
            if rv(i0 + t, j0, k0) is None or rv(i0, j0 + t, k0) is None \
               or rv(i0, j0, k0 + t) is None:
                return None
    nb = len(rv(*BASES[0])) - 1
    for (i0, j0, k0) in BASES:
        for t in TLINE:
            if len(rv(i0 + t, j0, k0)) - 1 != nb or \
               len(rv(i0, j0 + t, k0)) - 1 != nb or \
               len(rv(i0, j0, k0 + t)) - 1 != nb:
                return None
    out = []
    for u in range(nb + 1):
        per = []
        for (i0, j0, k0) in BASES:
            d_i = cell_slopes(lambda t: rv(i0 + t, j0, k0)[u])
            d_j = cell_slopes(lambda t: rv(i0, j0 + t, k0)[u])
            d_k = cell_slopes(lambda t: rv(i0, j0, k0 + t)[u])
            per.append((d_i, d_j, d_k))
        out.append(per)
    return nb, out, cache

CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb', 'baab', 'bab']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

def check(e):
    res = expr_slopes(e)
    if res is None: return None
    nb, sl, cache = res
    m = nb
    fs = []
    def rv(i, j, k):
        return cache[(i, j, k)]
    for (i0, j0, k0) in BASES:
        di = cell_slopes(lambda t: rv(i0 + t, j0, k0)[0])
        dj = cell_slopes(lambda t: rv(i0, j0 + t, k0)[0])
        dk = cell_slopes(lambda t: rv(i0, j0, k0 + t)[0])
        if accepted(di) and accepted(dk) and \
           (di[0] < dk[0] - MARGIN and di[1] < dk[1] - MARGIN):
            fs.append('D1k'); break
        if accepted(di) and accepted(dj) and \
           (di[0] < dj[0] - MARGIN and di[1] < dj[1] - MARGIN):
            fs.append('D1j'); break
    for (i0, j0, k0) in BASES:
        di = cell_slopes(lambda t: rv(i0 + t, j0, k0)[m])
        dj = cell_slopes(lambda t: rv(i0, j0 + t, k0)[m])
        dk = cell_slopes(lambda t: rv(i0, j0, k0 + t)[m])
        if accepted(dk) and accepted(di) and \
           (dk[0] < di[0] - MARGIN and dk[1] < di[1] - MARGIN):
            fs.append('D2i'); break
        if accepted(dk) and accepted(dj) and \
           (dk[0] < dj[0] - MARGIN and dk[1] < dj[1] - MARGIN):
            fs.append('D2j'); break
    for u in range(m + 1):
        done = False
        for (i0, j0, k0) in BASES:
            pi = cell_slopes(lambda t: sum(rv(i0 + t, j0, k0)[:u + 1]))
            pj = cell_slopes(lambda t: sum(rv(i0, j0 + t, k0)[:u + 1]))
            pk = cell_slopes(lambda t: sum(rv(i0, j0, k0 + t)[:u + 1]))
            if accepted(pi) and accepted(pk) and \
               (pi[0] < pk[0] - MARGIN and pi[1] < pk[1] - MARGIN):
                fs.append('P1k@%d' % u); done = True; break
            if accepted(pi) and accepted(pj) and \
               (pi[0] < pj[0] - MARGIN and pi[1] < pj[1] - MARGIN):
                fs.append('P1j@%d' % u); done = True; break
            si = cell_slopes(lambda t: sum(rv(i0 + t, j0, k0)[u:]))
            sj = cell_slopes(lambda t: sum(rv(i0, j0 + t, k0)[u:]))
            sk = cell_slopes(lambda t: sum(rv(i0, j0, k0 + t)[u:]))
            if accepted(sk) and accepted(si) and \
               (sk[0] < si[0] - MARGIN and sk[1] < si[1] - MARGIN):
                fs.append('P2i@%d' % u); done = True; break
            if accepted(sk) and accepted(sj) and \
               (sk[0] < sj[0] - MARGIN and sk[1] < sj[1] - MARGIN):
                fs.append('P2j@%d' % u); done = True; break
        if done: break
    if m == 2:
        for (i0, j0, k0) in BASES:
            l0i = cell_slopes(lambda t: rv(i0 + t, j0, k0)[0])
            l0j = cell_slopes(lambda t: rv(i0, j0 + t, k0)[0])
            l0k = cell_slopes(lambda t: rv(i0, j0, k0 + t)[0])
            t2i = cell_slopes(lambda t: rv(i0 + t, j0, k0)[2])
            t2j = cell_slopes(lambda t: rv(i0, j0 + t, k0)[2])
            t2k = cell_slopes(lambda t: rv(i0, j0, k0 + t)[2])
            if all(accepted(s) for s in (l0i, l0j, l0k, t2i, t2j, t2k)):
                lead_k = (l0k[0] + l0k[1]) / 2
                lead_i = (l0i[0] + l0i[1]) / 2
                lead_j = (l0j[0] + l0j[1]) / 2
                tail_i = (t2i[0] + t2i[1]) / 2
                tail_k = (t2k[0] + t2k[1]) / 2
                tail_j = (t2j[0] + t2j[1]) / 2
                if lead_k - lead_i > MARGIN and tail_i - tail_k > MARGIN \
                   and abs(lead_j) < MARGIN and abs(tail_j) < MARGIN:
                    fs.append('VH')
    if m == 1:
        for (i0, j0, k0) in BASES:
            l0i = cell_slopes(lambda t: rv(i0 + t, j0, k0)[0])
            l0j = cell_slopes(lambda t: rv(i0, j0 + t, k0)[0])
            l0k = cell_slopes(lambda t: rv(i0, j0, k0 + t)[0])
            t1i = cell_slopes(lambda t: rv(i0 + t, j0, k0)[1])
            t1j = cell_slopes(lambda t: rv(i0, j0 + t, k0)[1])
            t1k = cell_slopes(lambda t: rv(i0, j0, k0 + t)[1])
            if all(accepted(s) for s in (l0i, l0j, l0k, t1i, t1j, t1k)):
                li = (l0i[0] + l0i[1]) / 2; lj = (l0j[0] + l0j[1]) / 2
                lk = (l0k[0] + l0k[1]) / 2
                ti = (t1i[0] + t1i[1]) / 2; tj = (t1j[0] + t1j[1]) / 2
                tk = (t1k[0] + t1k[1]) / 2
                if abs(li - 1) < MARGIN and abs(lj) < MARGIN and \
                   abs(lk) < MARGIN and (tj + tk - 2 * ti) > 2 * MARGIN:
                    fs.append('P1f')
                if abs(li - 1) < MARGIN and abs(lj - 1) < MARGIN and \
                   abs(lk) < MARGIN and abs(ti) < MARGIN and \
                   abs(tj) < MARGIN and abs(tk - 1) < MARGIN:
                    fs.append('P2f')
                if abs(lk - 1) < MARGIN and abs(li) < MARGIN and \
                   abs(lj) < MARGIN:
                    fs.append('D1k-oneb')
    return fs

def main():
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 424242
    rng = random.Random(seed)
    n_expr = n_ok = 0
    viol = {}
    examples = []
    NTRY = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    while n_expr < NTRY:
        e = rand_expr(rng, DEPTH)
        n_expr += 1
        fs = check(e)
        if fs is None:
            continue
        n_ok += 1
        if fs:
            for f in fs:
                viol[f] = viol.get(f, 0) + 1
            examples.append((fs, e))
    print('tried %d, cleanly evaluated %d' % (n_expr, n_ok))
    print('violations:', viol)
    seen = set()
    for (fs, e) in examples[:10]:
        s = pp(e)
        if s in seen: continue
        seen.add(s)
        print('%s : %s' % (fs, s[:170]))

if __name__ == '__main__':
    main()

def chain_main():
    """chain-biased sweep: pure S-chains over a computed-pattern library"""
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 987654321
    rng = random.Random(seed)
    libs = [X, K(''), K('a'), K('b'), K('aa'), K('ab'), K('ba'), K('bb'),
            K('aab'), K('abb'), K('baab'), K('bab'),
            S(K(''), K('b'), X),                    # merge2
            C(C(S(K(''), K('b'), X), K('b')), S(K(''), K('b'), X)),  # big2
            C(X, X),                                # ww
            S(K('a'), K('aa'), S(K(''), K('b'), X)),  # halfm
            S(K('aa'), K('a'), X),                  # dbl2
            S(K(''), S(K(''), K('b'), X), S(K('aa'), K('a'), X)),  # diff2
            S(K('b'), X, C(C(S(K(''), K('b'), X), K('b')),
                            S(K(''), K('b'), X))),   # E_swap analogue? [b/X]big2
            C(K('b'), S(K(''), K('b'), X)),          # b.merge
            C(S(K(''), K('b'), X), K('b')),          # merge.b
            ]
    n = 0; ok = 0; viol = {}; examples = []
    NTRY = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    while n < NTRY:
        n += 1
        e = rng.choice(libs)
        for _ in range(rng.randint(1, DEPTH)):
            R = rng.choice(libs); P = rng.choice(libs)
            e = S(R, P, e)
        fs = check(e)
        if fs is None:
            continue
        ok += 1
        if fs:
            for f in fs: viol[f] = viol.get(f, 0) + 1
            examples.append((fs, e))
    print('chain sweep: tried %d, clean %d, violations %s' % (n, ok, viol))
    seen = set()
    for (fs, e) in examples[:8]:
        s = pp(e)
        if s in seen: continue
        seen.add(s)
        print('%s : %s' % (fs, s[:170]))

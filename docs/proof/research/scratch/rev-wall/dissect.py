"""Dissect the sweep's flagged expressions: dump run vectors along the
three directional probe lines so violations can be eyeballed as real
vs artifacts (cell crossings, long-period residues, CAP effects)."""
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

BASES = [(5, 5, 5), (2, 8, 4), (8, 2, 4), (4, 4, 9), (9, 3, 2), (3, 9, 3)]
TS = [0, 3, 6, 9]
CAP = 300000

def runvec(e, i, j, k):
    v = valtry(e, w2(i, j, k))
    if v is None or len(v) > CAP: return None
    return runs_of(v)

def dump(e, tag):
    print('--- %s : %s' % (tag, pp(e)[:200]))
    for b in BASES:
        rows = []
        for t in TS:
            rows.append(('i+%d' % t, runvec(e, b[0] + t, b[1], b[2])))
        for t in TS:
            rows.append(('j+%d' % t, runvec(e, b[0], b[1] + t, b[2])))
        for t in TS:
            rows.append(('k+%d' % t, runvec(e, b[0], b[1], b[2] + t)))
        print('  base', b)
        for (lab, rv) in rows:
            print('    %-4s %s' % (lab, rv))

# rebuild the flagged expressions from the same seed sequence
CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb', 'baab', 'bab']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

MARGIN = 0.34
def slopes_from(col):
    if any(c is None for c in col): return None
    return (col[3] - col[0]) / 9.0

def analyze(e):
    cache = {}
    def rv(i, j, k):
        if (i, j, k) not in cache: cache[(i, j, k)] = runvec(e, i, j, k)
        return cache[(i, j, k)]
    for (i0, j0, k0) in BASES:
        for t in TS:
            if rv(i0 + t, j0, k0) is None or rv(i0, j0 + t, k0) is None \
               or rv(i0, j0, k0 + t) is None:
                return None
    nb = len(rv(*BASES[0])) - 1
    for (i0, j0, k0) in BASES:
        for t in TS:
            if len(rv(i0 + t, j0, k0)) - 1 != nb or \
               len(rv(i0, j0 + t, k0)) - 1 != nb or \
               len(rv(i0, j0, k0 + t)) - 1 != nb:
                return None
    out = []
    for u in range(nb + 1):
        per = []
        for (i0, j0, k0) in BASES:
            d_i = slopes_from([rv(i0 + t, j0, k0)[u] for t in TS])
            d_j = slopes_from([rv(i0, j0 + t, k0)[u] for t in TS])
            d_k = slopes_from([rv(i0, j0, k0 + t)[u] for t in TS])
            per.append((d_i, d_j, d_k))
        out.append(per)
    return nb, out, cache

def flags_of(e):
    res = analyze(e)
    if res is None: return []
    nb, sl, _ = res
    m = nb; fs = []
    for (d_i, d_j, d_k) in sl[0]:
        if d_i < d_j - MARGIN or d_i < d_k - MARGIN:
            fs.append('D1'); break
    for (d_i, d_j, d_k) in sl[m]:
        if d_k < d_i - MARGIN or d_k < d_j - MARGIN:
            fs.append('D2'); break
    for u in range(m + 1):
        for (i0, j0, k0) in BASES:
            p = [sum(rv[:u+1]) for rv in [runvec(e, i0+t, j0, k0) for t in TS]]
            p_i = slopes_from(p)
            p = [sum(rv[:u+1]) for rv in [runvec(e, i0, j0+t, k0) for t in TS]]
            p_j = slopes_from(p)
            p = [sum(rv[:u+1]) for rv in [runvec(e, i0, j0, k0+t) for t in TS]]
            p_k = slopes_from(p)
            if p_i is not None and (p_i < p_j - MARGIN or p_i < p_k - MARGIN):
                fs.append('P1@%d' % u); break
            s = [sum(rv[u:]) for rv in [runvec(e, i0+t, j0, k0) for t in TS]]
            s_i = slopes_from(s)
            s = [sum(rv[u:]) for rv in [runvec(e, i0, j0+t, k0) for t in TS]]
            s_j = slopes_from(s)
            s = [sum(rv[u:]) for rv in [runvec(e, i0, j0, k0+t) for t in TS]]
            s_k = slopes_from(s)
            if s_k is not None and (s_k < s_i - MARGIN or s_k < s_j - MARGIN):
                fs.append('P2@%d' % u); break
    return fs

rng = random.Random(20260922)
shown = 0
for n in range(1500):
    e = rand_expr(rng, 3)
    fs = flags_of(e)
    if fs:
        shown += 1
        dump(e, ','.join(fs))
        if shown >= 9:
            break

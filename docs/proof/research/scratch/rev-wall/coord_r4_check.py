#!/usr/bin/env python3
# Coordinator round-4 verification battery (rev-wall). Fresh encodings; < 60 s.
# Part I : replay Lane D's part A with skip/mismatch classification.
# Part II: D1'' probe -- fresh tagged evaluator, engine sanity + targeted
#          mutation/random search for multi-label F-pure single-label runs
#          on outputs equal to rev(D(k;3)).
# Part III: recompute the report's structural constants independently.
import sys, time, random
sys.path.insert(0, '.')
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))

# ---- my own tagged evaluator (fresh encoding: route-list + leaf) -------
# atom = [ch, route, leaf]; route = tuple of nids passed through (in order);
# leaf = input position (int) or None for constant atoms.
# F-pure (never routed) <=> route == () and leaf is not None.
class Bail(Exception): pass
class MyUndef(Exception): pass
LIMIT = 20000
def mtev(e, w, ctr):
    t = e[0]
    if t == 'K':
        ctr[0] += 1
        return [[c, (), None] for c in e[1]]
    if t == 'V':
        return [[c, (), i] for i, c in enumerate(w)]
    if t == 'C':
        return mtev(e[1], w, ctr) + mtev(e[2], w, ctr)
    if t == 'S':
        ctr[0] += 1; nid = ctr[0]
        R = mtev(e[1], w, ctr); P = mtev(e[2], w, ctr); F = mtev(e[3], w, ctr)
        if len(P) == 0: raise MyUndef
        if max(len(R), len(P), len(F)) > LIMIT: raise Bail
        Ps = ''.join(a[0] for a in P); Fs = ''.join(a[0] for a in F)
        out, i, n = [], 0, len(Fs)
        while i < n:
            j = Fs.find(Ps, i)
            if j < 0:
                out.extend(F[i:]); break
            out.extend(F[i:j])
            out.extend([[a[0], (nid,) + a[1], a[2]] for a in R])
            i = j + len(Ps)
        return out
    raise ValueError(t)
def mchars(v): return ''.join(a[0] for a in v)

def runidx_map(w):
    out, r = [], 0
    for ch in w:
        out.append(r if ch == 'a' else None)
        if ch == 'b': r += 1
    return out
def fpure_single_labels(v, runmap):
    """labels of output runs that are F-pure (route==()) and single-label"""
    labs, cur = [], []
    for a in v:
        if a[0] == 'a':
            cur.append(a)
        else:
            if cur: labs.append(cur); cur = []
    if cur: labs.append(cur)
    res = []
    for r in labs:
        if all(a[1] == () and a[2] is not None for a in r):
            ls = set(runmap[a[2]] for a in r)
            if len(ls) == 1: res.append(ls.pop())
    return res

# =================== Part I: replay part A with classification ==========
print('== I: replay of Lane D part A (same seed), skip classification ==')
CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'abb']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))
def snodes(e, acc=None):
    if acc is None: acc = []
    if e[0] == 'S':
        acc.append(e); snodes(e[1], acc); snodes(e[2], acc); snodes(e[3], acc)
    elif e[0] == 'C':
        snodes(e[1], acc); snodes(e[2], acc)
    return acc
rng = random.Random(20260922)
nexpr = nchk = nskip = nnodemis = 0
why = {'undef': 0, 'bail': 0, 'topmis': 0}
while nexpr < 300:
    e = rand_expr(rng, 3); nexpr += 1
    nodes = snodes(e)
    # campaign side first: does IT raise Undefined / what is its value?
    try:
        cval = ev(e, dk(3)); cundef = False
    except PV.Undefined:
        cundef = True
    # tagged side
    try:
        top = mtev(e, dk(3), [0])
        if cundef or mchars(top) != cval:
            nskip += 1
            why['topmis'] += 1
            continue
    except MyUndef:
        nskip += 1; why['undef'] += 1; continue
    except Bail:
        nskip += 1; why['bail'] += 1; continue
    for nd in nodes:
        try:
            vN = mtev(nd, dk(3), [200000])
            if mchars(vN) != ev(nd, dk(3)):
                nnodemis += 1; continue
            nchk += 1
        except (MyUndef, Bail, PV.Undefined):
            continue
print('  I: %d exprs, %d node-checks, %d skips (%s), %d per-node mismatches'
      % (nexpr, nchk, nskip, why, nnodemis))
print('  I: skips all Undefined-class as claimed:',
      why['undef'] == 98 and why['bail'] == 0 and why['topmis'] == 0)
MARK('I done')

# =================== Part II: D1'' probe =================================
print('== II: D1\'\' probe (fresh evaluator) ==')
# IIa. engine sanity (rebuild Lane D's build() independently? no -- use the
# same construction source; the probe needs rev-true expressions. Re-type
# the construction from the 15C record independently of demand_check.py.)
def build_engine(k):
    mrg = S(K(''), K('b'), X)
    def del_last(E):
        return S(K(''), C(K('b'), C(mrg, K('a'))), C(C(E, mrg), K('a')))
    def del_first(E):
        return S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), E))
    Ds = []
    for m in range(k):
        E = X
        for t in range(m):          E = del_first(E)
        for t in range(k - 1, m, -1): E = del_last(E)
        Ds.append(S(K('b'), E, C(C(mrg, K('b')), mrg)))
    T = Ds[k - 1]
    for m in range(k - 2, -1, -1): T = C(C(T, K('a')), Ds[m])
    return S(K('b'), C(K('b'), C(mrg, K('a'))), T)
for k in (2, 3, 4):
    w = dk(k); E = build_engine(k)
    ok = ev(E, w) == w[::-1]
    v = mtev(E, w, [0])
    labs = fpure_single_labels(v, runidx_map(w))
    print('  IIa k=%d: rev %s; F-pure single-label run labels %s (count %d)'
          % (k, ok, sorted(set(labs)), len(labs)))
# IIb. mutation probe at k=2: single-point edits of the engine's constants
print('  IIb: engine mutations at k=2 (filter rev) ...')
k = 2; w = dk(k); base = build_engine(k)
hits = 0; multis = 0; tried = 0
def to_lists(e):
    if e[0] in ('K', 'V'): return [e[0], e[1]]
    if e[0] == 'C': return ['C', to_lists(e[1]), to_lists(e[2])]
    return ['S', to_lists(e[1]), to_lists(e[2]), to_lists(e[3])]
def to_tuples(e):
    if e[0] in ('K', 'V'): return (e[0], e[1])
    if e[0] == 'C': return ('C', to_tuples(e[1]), to_tuples(e[2]))
    return ('S', to_tuples(e[1]), to_tuples(e[2]), to_tuples(e[3]))
def mutate(e, rng):
    """swap one constant leaf in place; return a new expression"""
    e2 = to_lists(e)
    leaves = []
    def collect(x):
        if x[0] == 'K': leaves.append(x)
        elif x[0] == 'V': return
        elif x[0] == 'C': collect(x[1]); collect(x[2])
        else: collect(x[1]); collect(x[2]); collect(x[3])
    collect(e2)
    tgt = rng.choice(leaves)
    tgt[1] = rng.choice(['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa'])
    return to_tuples(e2)
rng = random.Random(777)
for it in range(4000):
    e = mutate(base, rng); tried += 1
    try:
        if ev(e, w) != w[::-1]: continue
    except PV.Undefined:
        continue
    hits += 1
    v = mtev(e, w, [0])
    labs = fpure_single_labels(v, runidx_map(w))
    if len(set(labs)) > 1:
        multis += 1
        print('    MULTI-LABEL HIT: labels %s' % sorted(set(labs)))
print('  IIb: %d mutants tried, %d rev-true, %d multi-label'
      % (tried, hits, multis))
MARK('IIb done')
# IIc. random composition search at k=2 over the engine vocabulary
print('  IIc: random vocabulary compositions at k=2 (filter rev) ...')
mrg = S(K(''), K('b'), X)
def del_last(E):
    return S(K(''), C(K('b'), C(mrg, K('a'))), C(C(E, mrg), K('a')))
def del_first(E):
    return S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), E))
VOCAB = [
    lambda r: mrg,
    lambda r: S(K(''), K('b'), X),
    lambda r: S(K('a'), K('aa'), X),
    lambda r: S(K('aa'), K('a'), X),
    lambda r: S(K('b'), K('b'), r.choice([C(C(mrg, K('b')), mrg),
                                          C(K('b'), C(mrg, K('a'))),
                                          C(C(K('a'), mrg), K('b'))])),
    lambda r: del_last(r.choice([X, mrg, C(X, X)])),
    lambda r: del_first(r.choice([X, mrg, C(X, X)])),
]
def rand_comp(rng, n):
    e = r0 = rng.choice([X, mrg, C(X, X)])
    for _ in range(n):
        if rng.random() < 0.3:
            e = C(e, rng.choice([X, mrg, K('a'), K('b'), K('aa'), K('')]))
        else:
            e = rng.choice(VOCAB)(rng) if rng.random() < 0.25 else \
                S(K(rng.choice(['', 'a', 'b', 'aa'])),
                  K(rng.choice(['b', 'a', 'ab', 'ba', 'bb', 'aa', 'b'])),
                  e)
    return e
rng = random.Random(424242)
hits = multis = tried = 0
for it in range(20000):
    e = rand_comp(rng, rng.randint(1, 5)); tried += 1
    try:
        if ev(e, w) != w[::-1]: continue
    except PV.Undefined:
        continue
    hits += 1
    v = mtev(e, w, [0])
    labs = fpure_single_labels(v, runidx_map(w))
    if len(set(labs)) > 1:
        multis += 1
        print('    MULTI-LABEL HIT: labels %s' % sorted(set(labs)))
print('  IIc: %d compositions tried, %d rev-true, %d multi-label'
      % (tried, hits, multis))
MARK('IIc done')

# =================== Part III: independent structural constants ==========
print('== III: structural constants recomputed ==')
def build_Ds(k):
    mrg = S(K(''), K('b'), X)
    def del_last(E):
        return S(K(''), C(K('b'), C(mrg, K('a'))), C(C(E, mrg), K('a')))
    def del_first(E):
        return S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), E))
    Ds = []
    for m in range(k):
        E = X
        for t in range(m):          E = del_first(E)
        for t in range(k - 1, m, -1): E = del_last(E)
        Ds.append(S(K('b'), E, C(C(mrg, K('b')), mrg)))
    T = Ds[k - 1]
    for m in range(k - 2, -1, -1): T = C(C(T, K('a')), Ds[m])
    Efull = S(K('b'), C(K('b'), C(mrg, K('a'))), T)
    return Efull, Ds
for k in (4, 5):
    Efull, Ds = build_Ds(k)
    print('  III k=%d: tree S-nodes %d (report: %s); walks %s (report: %s)'
          % (k, len(snodes(Efull)), {4: 50, 5: 77}[k],
             [len(snodes(D[2])) for D in Ds],
             {4: [9, 9, 9, 9], 5: [12] * 5}[k]))
k = 4
Efull, Ds = build_Ds(k); w = dk(k)
v = mtev(Efull, w, [0])
amass, plants = 0, []
for a in v:
    if a[0] == 'a': amass += 1
    else: plants.append(amass)
tops = [sum(B ** s for s in range(k - t, k + 1)) for t in range(k)]
print('  III k=4 plants %s vs top-anchored sums %s: %s'
      % (plants, tops, 'MATCH' if plants == tops else 'MISMATCH'))
MARK('III done')
print('COORD R4 CHECK COMPLETE')

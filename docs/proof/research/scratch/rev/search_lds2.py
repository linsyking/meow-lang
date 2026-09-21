"""Targeted search v2 (fast): maximize LDS(prov) at mult=1.

Precompute the LABELED VALUES of every library pattern/replacement on each
test input (they are functions of the original w); pipeline evaluation is
then a fold of lsubst -- fast.
"""
import random
import sys

import lcore as L
from lcore import K, V, C, comp, pipe, battery
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN
rng = random.Random(2718)

LIB_P = dict(RL.PATTERNS)
LIB_R = dict(RL.REPLACEMENTS)
LIB_R['XX'] = lambda: C(V(0), V(0))
LIB_R['rot1X'] = lambda: tk.cat(sg, tk.tail(sg, V(0)), tk.head(sg, V(0)))
LIB_R['XaX'] = lambda: C(C(V(0), K('a')), V(0))

WS = [''.join(rng.choice('ab') for _ in range(16)),
      ''.join(rng.choice('ab') for _ in range(24)),
      'a' * 12 + 'b' * 12, 'a' * 8 + 'b', 'b' + 'a' * 8,
      'ab' * 12, 'aab' * 8, 'a' * 24,
      'aaaaabbbbbaaaaabbbbb', 'abababab' * 3]
FIT_W = battery(5) + WS[:4]         # fitness battery (fast)
FULL_W = battery(6) + WS           # re-verification battery

# precompute labeled values
PVals = {}
RVals = {}
for p, b in LIB_P.items():
    ast = b()
    PVals[p] = {}
    for w in FULL_W:
        try:
            PVals[p][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            PVals[p][w] = None
for r, b in LIB_R.items():
    ast = b()
    RVals[r] = {}
    for w in FULL_W:
        try:
            RVals[r][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            RVals[r][w] = None

PASSES = [(p, r) for p in PVals for r in RVals
          if PVals[p] and all(PVals[p][w] is not None for w in FIT_W)]
print(f'pass space: {len(PASSES)}', flush=True)


def run(pipeline, Ws, cap=3000):
    out = {}
    for w in Ws:
        T = PV.lab_input(w)
        for (p, r) in pipeline:
            B = PVals[p].get(w)
            A = RVals[r].get(w)
            if B is None or not B or not A:
                return None
            T = PV.lsubst(A, B, T)
            if len(T) > cap:
                return None
        out[w] = T
    return out


def fit(pipeline, Ws=FIT_W):
    res = run(pipeline, Ws)
    if res is None:
        return (-1, 0, 0)
    mB = mD = mM = 0
    for w, T in res.items():
        pr = PV.labels(T)
        if not pr:
            continue
        d, m = PV.lds(pr), PV.mult(pr)
        mD, mM = max(mD, d), max(mM, m)
        if m == 1:
            mB = max(mB, d)
    return (mB, mD, mM)


POP, GEN = 300, 400


def rand_ind():
    return [rng.choice(PASSES) for _ in range(rng.randrange(2, 11))]


def mutate(m):
    m = list(m)
    op = rng.random()
    if op < 0.4 and m:
        m[rng.randrange(len(m))] = rng.choice(PASSES)
    elif op < 0.6:
        m.insert(rng.randrange(len(m) + 1), rng.choice(PASSES))
    elif op < 0.75 and len(m) > 1:
        del m[rng.randrange(len(m))]
    else:
        m = rand_ind()
    return m[:12]


pop = [rand_ind() for _ in range(POP)]
fits = [fit(p) for p in pop]
best = (None, (-1, 0, 0))
import time
t0 = time.time()
for g in range(GEN):
    order = sorted(range(POP), key=lambda i: fits[i], reverse=True)
    if fits[order[0]] > best[1]:
        best = (pop[order[0]], fits[order[0]])
        print(f'  gen {g}: best {fits[order[0]]} {pop[order[0]]} '
              f'({time.time()-t0:.0f}s)', flush=True)
    elite = [pop[i] for i in order[:20]]
    new = [list(x) for x in elite]
    while len(new) < POP:
        a, b = rng.randrange(POP), rng.randrange(POP)
        if rng.random() < 0.6:
            new.append(mutate(pop[a]))
        else:
            i = rng.randrange(len(pop[a]) + 1)
            j = rng.randrange(len(pop[b]) + 1)
            new.append((pop[a][:i] + pop[b][j:])[:12])
    pop, fits = new, [fit(p) for p in new]
print(f'final best: {best[1]}  pipeline: {best[0]}')
if best[0]:
    print('re-verify on full battery:')
    print('   ', fit(best[0], FULL_W))

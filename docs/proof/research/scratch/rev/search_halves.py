"""Litmus search: can L compute the QUADRATIC-crossing content functions?
Targets (even |w| = 2m):
  halves(w)  = w[m:] + w[:m]        (swap halves = rotate by n/2)
  secondhalf = w[m:]                (drop the first half)
  firsthalf  = w[:m]
All need a variable-length left-anchored deletion (or equivalent).
Genetic search over library pipelines, same machinery as search_r2.
"""
import random
import sys
import time

import lcore as L
from lcore import K, V, C, comp, battery
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN
rng = random.Random(555)

LIB_P = dict(RL.PATTERNS)
LIB_R = dict(RL.REPLACEMENTS)

# battery: EVEN lengths only (targets defined there), plus odd for totality
def bat(nlo, nhi):
    import itertools
    out = []
    for n in range(nlo, nhi + 1):
        if n % 2:
            continue
        out += [''.join(t) for t in itertools.product('ab', repeat=n)]
    return out


BS = bat(2, 6)                    # 2+4+16+64 = 86 strings
BV = [''.join(rng.choice('ab') for _ in range(2 * m)) for m in (5, 6, 7)]


def targets(w):
    m = len(w) // 2
    return {'halves': w[m:] + w[:m], 'second': w[m:], 'first': w[:m]}


TGT = {k: {w: targets(w)[k] for w in BS} for k in ('halves', 'second', 'first')}

# precompute library values on the battery
PV_, RV_ = {}, {}
ALLW = BS + BV
for p, b in LIB_P.items():
    ast = b()
    PV_[p] = {}
    for w in ALLW:
        r = L.den_try(ast, (w,))
        PV_[p][w] = r[1] if r[0] == 'ok' and r[1] else None
for r_, b in LIB_R.items():
    ast = b()
    RV_[r_] = {}
    for w in ALLW:
        r = L.den_try(ast, (w,))
        RV_[r_][w] = r[1] if r[0] == 'ok' else None

PN = [p for p in PV_ if all(PV_[p][w] is not None for w in BS)]
assert all(PV_[p][w] is not None for p in PN for w in ALLW)
RN = list(RV_)
PASSES = [(p, r) for p in PN for r in RN]
print(f'pass space: {len(PASSES)}', flush=True)


def eval_pipeline(pl, Ws):
    out = {}
    for w in Ws:
        T = w
        for (p, r) in pl:
            T = T.replace(PV_[p][w], RV_[r][w])
        out[w] = T
    return out


def fitness(pl, key):
    out = eval_pipeline(pl, BS)
    exact = sum(1 for w in BS if out[w] == TGT[key][w])
    lcp = sum(next((j for j in range(min(len(out[w]), len(TGT[key][w])) + 1)
                    if j == min(len(out[w]), len(TGT[key][w]))
                    or out[w][j] != TGT[key][w][j]), 0) for w in BS)
    mism = sum(sum(1 for a, b in zip(out[w], TGT[key][w]) if a != b)
               + abs(len(out[w]) - len(TGT[key][w])) for w in BS)
    return (exact, lcp, -mism)


POP, GEN = 400, 350
for key in ('halves', 'second', 'first'):
    pop = [[rng.choice(PASSES) for _ in range(rng.randrange(2, 11))]
           for _ in range(POP)]
    fits = [fitness(p, key) for p in pop]
    best = (None, (-1, 0, 0))
    for g in range(GEN):
        order = sorted(range(POP), key=lambda i: fits[i], reverse=True)
        if fits[order[0]] > best[1]:
            best = (pop[order[0]], fits[order[0]])
        elite = [pop[i] for i in order[:20]]
        new = [list(x) for x in elite]
        while len(new) < POP:
            if rng.random() < 0.6:
                m = list(pop[rng.randrange(POP)])
                op = rng.random()
                if op < 0.4 and m:
                    m[rng.randrange(len(m))] = rng.choice(PASSES)
                elif op < 0.6:
                    m.insert(rng.randrange(len(m) + 1), rng.choice(PASSES))
                elif op < 0.75 and len(m) > 1:
                    del m[rng.randrange(len(m))]
                else:
                    m = [rng.choice(PASSES)
                         for _ in range(rng.randrange(2, 11))]
                new.append(m[:12])
            else:
                a = pop[rng.randrange(POP)]
                b = pop[rng.randrange(POP)]
                i = rng.randrange(len(a) + 1)
                j = rng.randrange(len(b) + 1)
                new.append((a[:i] + b[j:])[:12])
        pop, fits = new, [fitness(p, key) for p in new]
    # re-verify on longer random inputs
    out = eval_pipeline(best[0], BV)
    tg = {w: targets(w)[key] for w in BV}
    ok_v = sum(1 for w in BV if out[w] == tg[w])
    print(f'target {key}: best on |w|<=6 battery: exact={best[1][0]}/86 '
          f'(lcp={best[1][1]}, mism={-best[1][2]}); on |w|=10..14: '
          f'{ok_v}/{len(BV)}')
    print(f'   pipeline: {best[0]}')

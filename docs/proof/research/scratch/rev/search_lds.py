"""Search: maximum provenance disorder achievable in L.

For E in Exp_1 and input w, prov = the input-position sequence of the value's
w-atoms; mult = max multiplicity; LDS = longest strictly decreasing
subsequence.  rev needs LDS = n at mult = 1.  rot1 has LDS 2, swapfl 3.

CONJECTURE B: sup { LDS(prov) : mult(prov) = 1 } is bounded by C(E).

This script measures the frontier: random expressions + curated families,
max LDS at mult=1 (and max LDS/mult), on batteries including long inputs.
Also: the UNFOLDING construction -- rev is trivially computable on each
FIXED length by cat(head(tail^j X),...); the open problem is uniformity, so
we also record size(E) vs the length up to which E matches rev.
"""
import random
import sys

import lcore as L
from lcore import K, V, C, S, comp, pipe, battery
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN
rng = random.Random(20260921)

W_SHORT = battery(8)
W_LONG = [''.join(rng.choice('ab') for _ in range(n))
          for n in (10, 12, 14, 16)] + [
    'a' * 8 + 'b', 'b' + 'a' * 8, ('ab' * 8), ('aab' * 6),
    'a' * 6 + 'b' * 6, ('ab' * 4) + 'a', 'a' * 12, 'b' * 12,
    'a' * 5 + 'b' * 5 + 'a', 'b' * 3 + 'a' * 9]
import random as _r
W_LONG += [''.join(_r.Random(7).choice('ab') for _ in range(n)) for n in (20, 24)]
W_ALL = W_SHORT + W_LONG


def rand_expr(depth, cons=('', 'a', 'b', 'aa', 'ab', 'ba', 'bb')):
    t = rng.random()
    if depth == 0 or t < 0.3:
        return V(0) if rng.random() < 0.5 else K(rng.choice(cons))
    if t < 0.62:
        return C(rand_expr(depth - 1), rand_expr(depth - 1))
    return S(rand_expr(depth - 1), rand_expr(depth - 1), rand_expr(depth - 1))


def probe(e):
    """returns (max LDS at mult=1, max LDS/mult, max LDS, max mult)"""
    mB = mr = mD = mM = 0
    for w in W_ALL:
        st = PV.stats(e, w)
        if st is None:
            continue
        mD = max(mD, st['lds'])
        mM = max(mM, st['mult'])
        mr = max(mr, st['lds'] / st['mult'])
        if st['mult'] == 1:
            mB = max(mB, st['lds'])
    return mB, mr, mD, mM


# ---------------------------------------------------------------- curated
curated = {
    'X': V(0), 'XX': C(V(0), V(0)),
    'rot1': tk.cat(sg, tk.tail(sg, V(0)), tk.head(sg, V(0))),
    'rot2': tk.cat(sg, tk.tail(sg, tk.tail(sg, V(0))),
                   tk.cat(sg, tk.head(sg, V(0)),
                          tk.head(sg, tk.tail(sg, V(0))))),
    'rotr1': RL.rotr1_expr(), 'swapfl': RL.swapfl_expr(),
    'lastX': RL.last_expr(), 'initX': RL.init_expr(),
    'nearmiss': pipe([('c', 'aa'), ('bc', 'cb'), ('c', 'aa')], V(0)),
    'nearmiss2': pipe([('c', 'bb'), ('bc', 'cb'), ('c', 'bb')], V(0)),
    'bub1': comp([('ab', 'ba')], V(0)),
    'bub1b': comp([('ab', 'ba'), ('ab', 'ba')], V(0)),
    'bub3': comp([('ab', 'ba'), ('ab', 'ba'), ('ab', 'ba')], V(0)),
    'swappairs': pipe([('c', 'ab'), ('bc', 'ac'), ('c', 'ba')], V(0)),
}
print('curated expressions:')
for name, e in curated.items():
    mB, mr, mD, mM = probe(e)
    print(f'  {name:10s} size={L.size(e):4d}  LDS@mult1={mB:3d}  '
          f'LDS/mult={mr:5.2f}  maxLDS={mD:3d}  maxmult={mM:3d}')

# ---------------------------------------------------------------- random
N = 3000
bestB = []
for _ in range(N):
    e = rand_expr(rng.choice([2, 3, 4, 5]))
    mB, mr, mD, mM = probe(e)
    bestB.append((mB, mr, mD, mM, e))
bestB.sort(key=lambda x: (-x[0], -x[1]))
print(f'\nrandom corpus ({N} exprs, depth<=5):')
print(f'  max LDS@mult1 = {bestB[0][0]} (LDS/mult={bestB[0][1]:.2f}, '
      f'maxLDS={bestB[0][2]}, maxmult={bestB[0][3]})')
print(f'  distribution of LDS@mult1:',
      sorted([b[0] for b in bestB], reverse=True)[:20])
from collections import Counter
print('  histogram:', dict(sorted(Counter(b[0] for b in bestB).items())))
for mB, mr, mD, mM, e in bestB[:6]:
    print(f'  LDS@mult1={mB}: {L.pp(e)}')

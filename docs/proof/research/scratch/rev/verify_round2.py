"""R2/R3 verification: provenance evaluator + the LDS/mult conjectures.

1. lden (provenance evaluator) == den on content, and its definedness
   matches, on random expressions.
2. Controls (positive controls any rev-excluding invariant must survive):
   X, XX, [X/a]X, [eps/a]X, rot1, rotr1, last, init, swapfl, enc, enc2,
   halve, tail, head, and the near-miss constant pipelines.
3. CONJECTURE A (LDS <= C(E)*mult): random corpus, sup_w LDS/mult per E —
   does it stabilize as |w| grows?
4. CONJECTURE B (LDS bounded when mult = 1): the money invariant; rev
   violates it (LDS = n, mult = 1); controls must satisfy it.
"""
import itertools
import random
import sys

import lcore as L
from lcore import K, V, C, S, comp, pipe, den, den_try, battery, rev
import prov as PV
import r2lib as RL
from r2lib import sg

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

rng = random.Random(20260921)


# ---------------------------------------------------------------- 1. lden ok
def rand_expr(depth, cons=('', 'a', 'b', 'ab', 'ba')):
    t = rng.random()
    if depth == 0 or t < 0.3:
        return V(0) if rng.random() < 0.55 else K(rng.choice(cons))
    if t < 0.6:
        return C(rand_expr(depth - 1), rand_expr(depth - 1))
    return S(rand_expr(depth - 1), rand_expr(depth - 1), rand_expr(depth - 1))


nbad = 0
for _ in range(3000):
    e = rand_expr(rng.choice([1, 2, 3, 4]))
    w = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 8)))
    try:
        val = PV.lden(e, (PV.lab_input(w),))
        got = ('ok', PV.content(val))
    except PV.Undefined:
        got = ('undef', None)
    if got != den_try(e, (w,)):
        nbad += 1
        print('  MISMATCH', e, w, got, den_try(e, (w,)))
        break
print(f'1. lden == den (content + definedness) on 3000 random (e,w): '
      f'{nbad} mismatches', flush=True)

# ---------------------------------------------------------------- 2. controls
controls = {
    'X': V(0),
    'XX': C(V(0), V(0)),
    '[X/a]X': comp([('X', 'a')], V(0)),
    '[eps/a]X': comp([('', 'a')], V(0)),
    '[a/X]X': comp([('a', 'X')], V(0)),
    '[Xb/X]X': comp([('X' + 'b', 'X')], V(0)),
    '[Xa/X]X': comp([('X' + 'a', 'X')], V(0)),
    'rot1': RL.PATTERNS and tk.cat(sg, tk.tail(sg, V(0)), tk.head(sg, V(0))),
    'tail': tk.tail(sg, V(0)),
    'head': tk.head(sg, V(0)),
    'enc': tk.enc(sg, V(0)),
    'enc2': tk.enc2(sg, V(0)),
    'halve': RL.halve_expr(),
    'lastX': RL.last_expr(),
    'initX': RL.init_expr(),
    'rotr1X': RL.rotr1_expr(),
    'swapflX': RL.swapfl_expr(),
}
# near-miss constant pipelines over Sigma={a,b,c}
controls['nearmiss_aa'] = pipe([('c', 'aa'), ('bc', 'cb'), ('c', 'aa')], V(0))
controls['X^|X|'] = comp([(V(0), 'ab')], V(0))     # [X/ab]X: replace 'ab' by w
controls['[XX/X]X'] = comp([(C(V(0), V(0)), 'X')], V(0))

Ws = battery(9)
print('2. controls: (name, max LDS at mult=1 [conjecture B], '
      'max LDS/mult [conjecture A], max mult)')
Bviol = []
for name, e in controls.items():
    mB = 0      # max LDS among w with mult == 1
    mA = 0.0    # max LDS / mult
    mm = 0
    for w in Ws:
        st = PV.stats(e, w)
        if st is None:
            continue
        mm = max(mm, st['mult'])
        if st['mult'] == 1:
            mB = max(mB, st['lds'])
        mA = max(mA, st['lds'] / st['mult'])
    flag = ''
    print(f'   {name:12s} B:{mB:4d}  A:{mA:6.2f}  mult:{mm:5d}')
    if name in ('X', 'XX', 'rot1', 'tail', 'head', 'enc', 'enc2', 'halve',
                'lastX', 'initX', 'rotr1X', 'swapflX') and mB > 6:
        Bviol.append((name, mB))
print(f'   controls with LDS@mult1 > 6 (suspicious): {Bviol}')

# ---------------------------------------------------------------- 3. corpus
# random expressions: track sup_w LDS/mult and sup_w LDS@mult=1 as |w| grows
print('3. random corpus (conjecture A/B): per-expression sup over |w|<=9')
N = 800
supA = []
supB = []
undef_ct = 0
for trial in range(N):
    e = rand_expr(rng.choice([1, 2, 3, 4]))
    a = b = 0
    for w in Ws:
        st = PV.stats(e, w)
        if st is None:
            undef_ct += 1
            continue
        a = max(a, st['lds'] / st['mult'])
        if st['mult'] == 1:
            b = max(b, st['lds'])
    supA.append(a)
    supB.append(b)
supA.sort()
supB.sort()
print(f'   {N} exprs; sup LDS/mult: median {supA[N//2]:.1f}, '
      f'p90 {supA[int(N*0.9)]:.1f}, max {supA[-1]:.1f}')
print(f'   sup LDS@mult=1: median {supB[N//2]}, p90 {supB[int(N*0.9)]}, '
      f'max {supB[-1]}')
# the tail: how big do they get relative to expression size?
print('   (rev itself: LDS = n, mult = 1 -> supB would be unbounded in n)')

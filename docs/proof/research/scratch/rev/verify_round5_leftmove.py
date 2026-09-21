"""ROUND 5 SUPPLEMENT (coordinator): the Left-Move Wall -- the crux fact
that verify_round5_phases.py does NOT verify (no code existed for it).

Fact to check (REPORT 5.3 / fragment fact:leftmove): after one deletion
pass [eps/B] on a text of copies of A separated by gaps, among copies
whose (nonempty) residuals are pairwise disjoint as position sets, there
is no chain of three copies in text order whose pickable positions admit
p1 > p2 > p3 -- the longest strictly decreasing position chain has length
exactly 2.

Exhaustive domain (as reported): all binary A with 1 <= |A| <= 4, all
binary B with 1 <= |B| <= 3, all gap strings over {a,b} of length <= 2,
texts with 2 and 3 copies (= 30 x 14 x (7^3 + 7^4) = 1,152,480 texts),
plus 40,000 random texts up to |A| = 7, |B| = 6, 6 copies.
"""
import random
import sys
from itertools import product

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/rev')
from verify_round5_phases import make_text_tagged, scan_oj


def residuals_of(gapstrs, A, B):
    T = make_text_tagged(gapstrs, A)
    out, oj = scan_oj(T, B)
    ncopies = len(gapstrs) - 1
    res = [set() for _ in range(ncopies)]
    for _, lab in out:
        if lab[0] == 'c':
            res[lab[1]].add(lab[2])
    return [r for r in res if r]      # nonempty residuals, text order


def max_chain(res):
    """Longest strictly decreasing pick chain: copies in text order,
    one pick per copy at p in R_c, positions strictly decreasing,
    and the involved copies' residuals pairwise disjoint."""
    n = len(res)
    best = 0

    def rec(mask, last_copy, last_p, count):
        nonlocal best
        best = max(best, count)
        for c in range(last_copy + 1, n):
            if mask >> c & 1:
                continue
            if any(res[c] & res[u] for u in range(n) if mask >> u & 1):
                continue
            for p in res[c]:
                if p < last_p:
                    rec(mask | (1 << c), c, p, count + 1)

    rec(0, -1, 10 ** 9, 0)
    return best


GAPS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
AS = [a for L in range(1, 5) for a in map(''.join, product('ab', repeat=L))]
BS = [b for L in range(1, 4) for b in map(''.join, product('ab', repeat=L))]

print('exhaustive: |A|<=4, |B|<=3, gaps<=2, 2 and 3 copies')
ntext = nge2 = 0
worst = 0
triple = None
for A in AS:
    for B in BS:
        for ncopies in (2, 3):
            for gapstrs in product(GAPS, repeat=ncopies + 1):
                ntext += 1
                res = residuals_of(gapstrs, A, B)
                if len(res) < 2:
                    continue
                # >= 2 pairwise-disjoint nonempty residuals?
                have2 = any(not (res[i] & res[j])
                            for i in range(len(res))
                            for j in range(i + 1, len(res)))
                if not have2:
                    continue
                nge2 += 1
                k = max_chain(res)
                if k > worst:
                    worst = k
                if k >= 3 and triple is None:
                    triple = (A, B, gapstrs, res)
print(f'  texts checked: {ntext} (expect 1,152,480)')
print(f'  texts with >= 2 pairwise-disjoint nonempty residuals: '
      f'{nge2} (reported: 4,730)')
print(f'  max strictly decreasing position chain: {worst} '
      f'(claim: exactly 2)')
print(f'  {"COUNTEREXAMPLE: " + repr(triple) if triple else "no chain of 3 anywhere"}')

rng = random.Random(51000)
print('random stress: 40,000 texts, |A|<=7, |B|<=6, <=6 copies')
worst2 = 0
triple2 = None
for t in range(40000):
    A = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 8)))
    B = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 7)))
    nc = rng.randrange(1, 7)
    gapstrs = [''.join(rng.choice('ab')
                      for _ in range(rng.randrange(0, 4)))
               for _ in range(nc + 1)]
    if t % 3 == 0:      # run-biased
        A = rng.choice(['ab', 'aab', 'abb', 'aaab', 'bbba', 'aabb',
                        'bbbaaaa', 'aabbaa', 'ababab'])
        gapstrs = [rng.choice(['', 'b', 'bb', 'a', 'aa', 'ab', 'ba'])
                   for _ in range(nc + 1)]
    res = residuals_of(gapstrs, A, B)
    if len(res) < 2:
        continue
    k = max_chain(res)
    if k > worst2:
        worst2 = k
    if k >= 3 and triple2 is None:
        triple2 = (A, B, gapstrs, [sorted(r) for r in res])
print(f'  max chain: {worst2} (claim: 2)')
print(f'  {"COUNTEREXAMPLE: " + repr(triple2) if triple2 else "no chain of 3 anywhere"}')
print('RESULT: ' + ('ALL GREEN' if worst == 2 and not triple and not triple2
                    else 'DISCREPANCY'))

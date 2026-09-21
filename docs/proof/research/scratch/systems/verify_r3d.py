"""R3 supplement (coordinator): verify_r3.py parts D1-D2 under adequate caps.

My earlier full run of verify_r3.py died inside part D (hours of pure-Python
occ() scanning), and at the script's DEFAULT caps (5000 steps / 5000 length)
the rank-0 census would misclassify the cap-sensitive family (needs output
length 6,569) as divergent -- reproducing the paper's original 170 bug.
This driver:

  0. proves occ_fast (repeated str.find with skipping) == occ (the greedy
     leftmost-first non-overlapping scan) on an exhaustive battery, then
     patches it in -- verification-grade speed, no semantic change;
  1. runs D1 (rank-0 semantics == restart verbatim, 200 rules x 40 inputs)
     with restart cap 5000;
  2. runs the D2 census at ranks 0, 1, 2 over the full 930-rule domain,
     all 1,023 inputs |S| <= 9, with ADEQUATE caps (5000 steps / 8000
     length: above the slow family's 3,280 steps and 6,569 length), and
     checks the R3 REPORT's claims:
       rank 0: 166 divergent = 162 with B in A + the four
               [aabb/ba], [bbaa/ab], [abba/bab], [baab/aba];
       rank 1: 166, the SAME set (no cures, no creations);
       rank 2: 148; the 18 cures vs rank 1 are exactly the 16 A=B,
               |A|=4 rules plus [abba/bab], [baab/aba]; no creations.

D3'/D4'/D5'/D6 were already verified green under my run of verify_r3c.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import systems
import verify_r3 as V
from systems import occ, restart
from verify_r2 import strings

SIGMA = ['a', 'b']


# ---------------------------------------------------------------- 0. occ_fast
def occ_fast(C, B):
    """Greedy leftmost-first, non-overlapping occurrences of B in C --
    the same scan as systems.occ, via repeated str.find (C speed)."""
    O, i, m = [], 0, len(B)
    while True:
        i = C.find(B, i)
        if i < 0:
            return O
        O.append(i)
        i += m


bad = 0
for B in strings(SIGMA, 3):
    if not B:
        continue
    for C in strings(SIGMA, 8):
        if occ(C, B) != occ_fast(C, B):
            bad += 1
            if bad <= 3:
                print('OCC MISMATCH', repr(C), repr(B))
print(f'0. occ_fast == occ: all |C|<=8 x 1<=|B|<=3 binary '
      f'({sum(1 for _ in strings(SIGMA, 8))} strings): '
      f'{"PASS" if bad == 0 else f"FAIL({bad})"}')
assert bad == 0

V.occ = occ_fast          # patch into verify_r3's run_rank
V.run_rank.__defaults__ = (5000, 8000)   # adequate: > (3,280 steps, 6,569 len)

# ------------------------------------------------------------------- 1. D1
ok = 0
for (A, B) in V.all_rules(3, 3)[:200]:
    for S in strings(SIGMA, 5)[:40]:
        assert V.run_rank(0, A, B, S) == restart(A, B, S, cap=5000), (A, B, S)
        ok += 1
print(f'1. D1 rank-0 == restart verbatim: {ok} exact agreements')

# ------------------------------------------------------------------- 2. D2
FOUR = {('aabb', 'ba'), ('bbaa', 'ab'), ('abba', 'bab'), ('baab', 'aba')}
inputs = strings(SIGMA, 9)
rules = V.all_rules(4, 4)
print(f'2. D2 census: {len(rules)} rules, {len(inputs)} inputs |S|<=9, '
      f'caps (5000 steps / 8000 length)')
results = {}
for k in (0, 1, 2):
    div = set()
    for (A, B) in rules:
        for S in inputs:
            if V.run_rank(k, A, B, S) is None:
                div.add((A, B))
                break
    results[k] = div
    print(f'   rank {k}: {len(div)} divergent rules')

d0, d1, d2 = results[0], results[1], results[2]
bsubA = {(A, B) for (A, B) in rules if B in A}
extra = d0 - bsubA

AB4 = {(A, B) for (A, B) in rules if A == B and len(A) == 4}
expect_cures = AB4 | {('abba', 'bab'), ('baab', 'aba')}

checks = [
    ('rank0 = 166', len(d0) == 166),
    ('rank0 = 162 B-in-A + the four',
     len(d0 & bsubA) == 162 and extra == FOUR),
    ('rank1 = 166, same set as rank0', d1 == d0),
    ('rank2 = 148', len(d2) == 148),
    ('rank2 cures vs rank1 = 16 A=B |A|=4 + 2 rules',
     d1 - d2 == expect_cures),
    ('rank2 creations: none', d2 - d1 == set()),
    ('no creations at rank1', d1 - d0 == set()),
]
allok = True
for name, res in checks:
    print(f'   [{"OK" if res else "FAIL"}] {name}')
    allok &= res
print(f'D1-D2 RESULT: {"ALL GREEN" if allok else "DISCREPANCY"}')

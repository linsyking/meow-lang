"""Parallel rank-k census (R3 part D, fast cross-check).

Caps: steps<=2000, length<=2000 -- SAFE for total rules: over inputs |S|<=9
with |A|<=4, the largest total single-rule outputs/steps are the amplifier
family (~2^8 = 256 steps, output ~2^8+9); lencap 2000 > 4x margin.  Rules
flagged divergent are re-checked individually at 5x caps (robustness)."""
import sys, os
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from systems import occ
from verify_r3 import all_rules, strings

SIGMA = ['a', 'b']

def run_rank(k, A, B, S, cap, lencap):
    s, steps = S, 0
    while True:
        O = occ(s, B)
        if len(O) <= k:
            return s
        i = O[k]
        t = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap or len(t) > lencap:
            return None
        s = t

INPUTS = strings(SIGMA, 9)

def work(arg):
    k, A, B = arg
    for S in INPUTS:
        if run_rank(k, A, B, S, 2000, 2000) is None:
            return (k, A, B, 'div')
    return (k, A, B, 'total')

if __name__ == '__main__':
    rules = all_rules(4, 4)
    jobs = [(k, A, B) for k in (0, 1, 2) for (A, B) in rules]
    print(f"{len(rules)} rules x 3 ranks = {len(jobs)} jobs, "
          f"{len(INPUTS)} inputs each", flush=True)
    with Pool(24) as p:
        res = p.map(work, jobs, chunksize=8)
    byk = {0: set(), 1: set(), 2: set()}
    for (k, A, B, st) in res:
        if st == 'div':
            byk[k].add((A, B))
    d0, d1, d2 = byk[0], byk[1], byk[2]
    print(f"rank 0: {len(d0)} divergent   (paper: 170)")
    print(f"rank 1: {len(d1)} divergent")
    print(f"rank 2: {len(d2)} divergent")
    bsubA = {(A, B) for (A, B) in rules if B in A}
    print(f"rank 0 with B subset A: {len(d0 & bsubA)} (paper: 162); "
          f"others: {sorted(d0 - bsubA)}")
    print(f"cured (div@0, total@1): {sorted(d0 - d1)}")
    print(f"created (total@0, div@1): {sorted(d1 - d0)}")
    print(f"rank2 cured vs rank1: {sorted(d1 - d2)}")
    print(f"rank2 created vs rank1: {sorted(d2 - d1)}")
    # robustness: re-check borderline rules at 5x caps
    bord = (d0 | d1 | d2)
    diff = []
    for (A, B) in bord:
        for k in (0, 1, 2):
            verdicts = set()
            for S in INPUTS:
                v = run_rank(k, A, B, S, 10000, 10000)
                verdicts.add(v is None)
                if v is None:
                    break
            want = (A, B) in byk[k]
            if any(verdicts) != want:
                diff.append((k, A, B))
    print(f"robustness recheck at 5x caps: {len(diff)} disagreements "
          f"{diff[:10]}")

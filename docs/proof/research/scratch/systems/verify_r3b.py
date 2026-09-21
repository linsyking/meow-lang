"""R3 follow-up (part D bis): growth census with sane thresholds; the rank-1
amplifier on FIRING inputs; re-verification of the rank-cures on larger
domains (short-domain artifact discipline)."""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from systems import occ, restart, rankm
from verify_r3 import all_rules, strings, run_rank

SIGMA = ['a', 'b']

def fmax(k, A, B, n):
    mx = 0
    for S in strings(SIGMA, n, n):
        out = run_rank(k, A, B, S)
        if out is None:
            return None
        mx = max(mx, len(out))
    return mx

def classify(f):
    # f[i] = max output length at input length i+1, i = 0..8
    if f is None or len(f) < 9:
        return 'n/a'
    if f[8] >= 64 and f[6] >= 16 and f[4] >= 4:      # ~2^{n/2+1} tail
        return 'exponential'
    if any(v > i + 5 for i, v in enumerate(f, 1)):
        return 'superlinear'
    return 'linear'

def main():
    rules = all_rules(4, 4)
    # rank-0 divergent set (from the census; recompute cheaply via paper facts
    # is risky -- recompute)
    d0 = set()
    for (A, B) in rules:
        for S in strings(SIGMA, 9):
            if run_rank(0, A, B, S) is None:
                d0.add((A, B)); break
    sub = [(A, B) for (A, B) in rules if len(A) <= 3 and len(B) <= 3
           and (A, B) not in d0]
    print(f"rank-0-total |A|,|B|<=3: {len(sub)} rules (paper: 162)")
    for k in (0, 1):
        buckets = {'linear': [], 'superlinear': [], 'exponential': [],
                   'n/a': []}
        for (A, B) in sub:
            f = [fmax(k, A, B, n) for n in range(1, 10)]
            if None in f:
                f = None            # diverges at rank k
            buckets[classify(f)].append((A, B))
        print(f"rank {k}: linear {len(buckets['linear'])}, "
              f"superlinear {len(buckets['superlinear'])}, "
              f"exponential {len(buckets['exponential'])}, "
              f"divergent-at-rank {len(buckets['n/a'])}")
        print(f"   exponential: {buckets['exponential']}")
        print(f"   superlinear: {buckets['superlinear'][:24]}"
              f"{' ...' if len(buckets['superlinear']) > 24 else ''}")
    # D4 redo: amplifier at rank 1 on FIRING inputs ((ab)^m) and at rank 0
    for k in (0, 1):
        lens = []
        for m in range(1, 9):
            S = 'ab' * m
            out = run_rank(k, 'baa', 'ab', S, cap=200000, lencap=2000000)
            lens.append(len(out) if out is not None else 'DIV')
        print(f"amplifier [baa/ab] rank {k} on (ab)^m, m=1..8: {lens}")
    # cure re-verification on larger domains
    cured1 = [('aaab', 'ba'), ('abbb', 'ba'), ('baaa', 'ab'), ('bbba', 'ab')]
    print("rank-1 cures re-verified on larger domains:")
    for (A, B) in cured1:
        still_total = True
        wit = None
        rng = random.Random(hash((A, B)) & 0xffff)
        tests = strings(SIGMA, 12) + \
            [''.join(rng.choice(SIGMA) for _ in range(rng.randrange(13, 25)))
             for _ in range(60)]
        for S in tests:
            if run_rank(1, A, B, S, cap=200000, lencap=2000000) is None:
                still_total = False; wit = S; break
        print(f"   [{A}/{B}] rank 1: "
              f"{'total on all larger tests' if still_total else f'DIVERGES at len {wit!r}'}"
              f"  (rank 0 diverges: "
              f"{restart(A, B, 'ba' + B, cap=100000) is None})")
    # rank-2 cures: artifact check -- do A=B rules really become total at
    # rank 2, or is it the domain?
    print("rank-2 'cures' artifact check (A=B rules need >=3 occurrences; "
          "fit 3 in longer inputs):")
    for (A, B) in [('aaaa', 'aaaa'), ('abba', 'bab')]:
        rng = random.Random(5)
        diverged = None
        for m in (12, 15, 18, 21, 24):
            for S in [A * 6, ('a' * m) if B == B[0] * len(B) else
                      (B + 'x')[:0] + B * (m // len(B) + 2),
                      ''.join(rng.choice(SIGMA) for _ in range(m))]:
                if run_rank(2, A, B, S, cap=100000, lencap=1000000) is None:
                    diverged = (S, len(S)); break
            if diverged: break
        print(f"   [{A}/{B}] rank 2: "
              f"{'cured for real (no divergence found)' if not diverged else f'DIVERGES on {diverged}'}")
    # robustness: no rank-1-CREATED divergence on longer inputs (sample)
    rng = random.Random(9)
    print("rank-1 'created: none' robustness sample (200 random rules, "
          "random inputs length 10-24):")
    bad = []
    for (A, B) in rng.sample([r for r in rules if r not in d0], 200):
        for _ in range(8):
            S = ''.join(rng.choice(SIGMA)
                        for _ in range(rng.randrange(10, 25)))
            if run_rank(1, A, B, S, cap=200000, lencap=2000000) is None:
                bad.append((A, B, S)); break
    print(f"   rank-1 divergences on longer inputs among 200 sampled "
          f"rank-0-total rules: {len(bad)} {bad[:6]}")

if __name__ == '__main__':
    main()

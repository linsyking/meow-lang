"""R3 part D, corrected and restructured after the cap-sensitivity discovery.

D3'  growth census among the rank-0-total |A|,|B|<=3 rules, with a sane
     classifier (paper sanity: rank 0 must give 140/18/4) and a cap
     re-check: any rule whose max step count reaches 80% of the cap is
     re-run at 10x caps before its bucket is believed.
D4'  the amplifier family at rank 1 on FIRING inputs.
D5   rank-2 cure artifact checks (A=B |A|=4 vs [abba/bab], [baab/aba]).
D6   'rank-1 creates nothing' robustness sample on longer inputs with a
     10x-cap re-check of every flagged candidate.
"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from systems import occ
from verify_r3 import all_rules, strings

SIGMA = ['a', 'b']
CAP = 50000

def run_rank(k, A, B, S, cap=CAP, lencap=CAP):
    """rank-k iterate-repOcc(k) with step/length caps; returns (out, steps)."""
    s, steps = S, 0
    while True:
        O = occ(s, B)
        if len(O) <= k:
            return s, steps
        i = O[k]
        s = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap or len(s) > lencap:
            return None, steps

def fmax(k, A, B, n):
    mx, mst = 0, 0
    for S in strings(SIGMA, n, n):
        out, st = run_rank(k, A, B, S)
        if out is None:
            return None, st
        mx = max(mx, len(out)); mst = max(mst, st)
    return mx, mst

def classify(f):
    if f is None:
        return 'n/a'
    if f[8] >= 64 and f[6] >= 16 and f[4] >= 4:
        return 'exponential'
    if any(v > i + 5 for i, v in enumerate(f, 1)):
        return 'superlinear'
    return 'linear'

print("D3' growth census (rank-0-total, |A|,|B|<=3, caps %d)" % CAP, flush=True)
# Within |A|<=3 the rank-0 divergent rules are exactly the B-in-A ones:
# the four cap-sensitive rules all have |A| = 4 (probe_slow.py), and the
# census cross-check (census_par.py) found no other cap flip.  The paper's
# growth census uses exactly this 162-rule subdomain.
import itertools
def allw(maxlen):
    out = []
    for L in range(0, maxlen + 1):
        for t in itertools.product('ab', repeat=L):
            out.append(''.join(t))
    return out
rules = all_rules(4, 4)
sub = [(A, B) for A in allw(3) for B in allw(3) if B and B not in A]
assert len(sub) == 162
d0 = set((A, B) for (A, B) in rules if B in A) |      {('aabb', 'ba'), ('abba', 'bab'), ('baab', 'aba'), ('bbaa', 'ab')}
print(f"   growth subdomain: {len(sub)} rules |A|,|B|<=3, B not-in A "
      f"(paper: 162); rank-0 divergent overall: {len(d0)} @ low caps, "
      f"166 @ adequate caps (census_par)", flush=True)
for k in (0, 1):
    buckets = {'linear': [], 'superlinear': [], 'exponential': [], 'n/a': []}
    recheck = []
    for (A, B) in sub:
        fs = [fmax(k, A, B, n) for n in range(1, 10)]
        if any(f is None for f in fs):
            buckets['n/a'].append((A, B)); continue
        if max(st for _, st in fs) > 0.8 * CAP:
            recheck.append((A, B))
        buckets[classify([f for f, _ in fs])].append((A, B))
    print(f"   rank {k}: linear {len(buckets['linear'])}, superlinear "
          f"{len(buckets['superlinear'])}, exponential "
          f"{len(buckets['exponential'])}, div-at-rank {len(buckets['n/a'])}"
          f"; cap-recheck needed: {recheck}", flush=True)
    print(f"      exponential: {buckets['exponential']}", flush=True)
    print(f"      superlinear ({len(buckets['superlinear'])}): "
          f"{buckets['superlinear'][:20]}", flush=True)

print("D4' amplifier family at rank 1 on FIRING inputs, caps 200k/2M:",
      flush=True)
for (A, B) in [('baa', 'ab'), ('aab', 'ba'), ('abb', 'ba'), ('bba', 'ab')]:
    lens = []
    for m in range(1, 9):
        S = 'ab' * m if B == 'ab' else 'ba' * m
        out, st = run_rank(1, A, B, S, 200000, 2000000)
        lens.append(len(out) if out is not None else 'DIV')
    lens0 = []
    for m in range(1, 9):
        S = 'ab' * m if B == 'ab' else 'ba' * m
        out, st = run_rank(0, A, B, S, 200000, 2000000)
        lens0.append(len(out) if out is not None else 'DIV')
    print(f"   [{A}/{B}] on (B)^m m=1..8: rank1 lens {lens}; rank0 lens {lens0}",
          flush=True)

print("D5 rank-2 cures: artifact or real?", flush=True)
for (A, B) in [('aaaa', 'aaaa'), ('abab', 'abab'), ('abba', 'bab'),
               ('baab', 'aba')]:
    wit = None
    tests = [A * 6] + [A * 3 + 'b' + A * 2, (A + 'ab') * 4]
    rng = random.Random(5)
    tests += [''.join(rng.choice('ab') for _ in range(m)) for m in
              (16, 20, 24)]
    for S in tests:
        out, st = run_rank(2, A, B, S, 20000, 200000)
        if out is None:
            wit = S; break
    print(f"   [{A}/{B}] rank2 on longer inputs: "
          f"{'fails on %r (len %d) at caps 20k/200k' % (wit, len(wit)) if wit else 'no failure found'}",
          flush=True)

print("D6 rank-1 'creates nothing' robustness sample: 200 random rank-0-total "
      "rules, 8 random inputs of length 10-24 each, caps 10k/100k; flagged "
      "candidates re-checked at 10x.", flush=True)
rng = random.Random(9)
pool = [r for r in rules if r not in d0]
bad = []
for (A, B) in rng.sample(pool, 200):
    for _ in range(8):
        S = ''.join(rng.choice(SIGMA) for _ in range(rng.randrange(10, 25)))
        out, st = run_rank(1, A, B, S, 10000, 100000)
        if out is None:
            bad.append((A, B, S)); break
print(f"   flagged at 10k/100k: {len(bad)}", flush=True)
still = []
for (A, B, S) in bad:
    out, st = run_rank(1, A, B, S, 100000, 1000000)
    if out is None:
        still.append((A, B, S))
print(f"   still failing at 10x caps (100k/1M): {len(still)} {still[:8]}",
      flush=True)
print("verify_r3c done", flush=True)

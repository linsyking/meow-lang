"""Boundary probe for the four cap-sensitive rules.
(1) rank-0 cascade profile on the 1-parameter family b^n . a (for [aaab/ba]).
(2) rank-1 behaviour on longer inputs (12..24): does rank 1 also fail there?
(3) minimal length with a non-terminating input (sampled), rank 0 vs rank 1."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def occ_(s, B):
    O, i = [], 0
    while True:
        j = s.find(B, i)
        if j < 0: return O
        O.append(j); i = j + len(B)

def run(k, A, B, S, cap, lencap):
    s, steps = S, 0
    while True:
        O = occ_(s, B)
        if len(O) <= k: return s, steps
        i = O[k]
        s = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap or len(s) > lencap: return None, steps

print("(1) [aaab/ba] rank 0 on b^n a, caps (10^5, 10^6):")
for n in range(8, 14):
    out, st = run(0, 'aaab', 'ba', 'b'*n + 'a', 10**5, 10**6)
    print(f"   n={n}: {'TERMINATES' if out is not None else 'no term.'}"
          f" steps={st} len={len(out) if out is not None else '-'}")

print("(2) the four slow rules at rank 1 on longer random inputs, "
      "caps (10^4, 10^5):")
SLOW = [('aaab', 'ba'), ('abbb', 'ba'), ('baaa', 'ab'), ('bbba', 'ab')]
rng = random.Random(3)
for (A, B) in SLOW:
    worst = (0, None)
    bad = None
    for _ in range(150):
        S = ''.join(rng.choice('ab') for _ in range(rng.randrange(12, 25)))
        out, st = run(1, A, B, S, 10**4, 10**5)
        if out is None:
            bad = S; break
        if st > worst[0]: worst = (st, S)
    print(f"   [{A}/{B}] rank1: "
          f"{'NO TERM on %r (len %d)' % (bad, len(bad)) if bad else 'all 150 terminate; worst %d steps on len-%d input' % (worst[0], len(worst[1]))}")

print("(3) minimal length with non-terminating sampled input, "
      "caps (3e4, 3e5), 120 random inputs per length, rank 0:")
for (A, B) in SLOW:
    found = None
    for L in range(12, 19):
        rngl = random.Random(100 + L)
        for _ in range(120):
            S = ''.join(rngl.choice('ab') for _ in range(L))
            if run(0, A, B, S, 3*10**4, 3*10**5)[0] is None:
                found = (L, S); break
        if found: break
    print(f"   [{A}/{B}] rank0: first sampled non-terminating input: "
          f"len {found[0]} {found[1]!r}" if found else
          f"   [{A}/{B}] rank0: none sampled at lengths 12..18")

"""Focused probe of the four cap-sensitive rules (rank-0 slow-but-total on
|S|<=9): exact step counts, length profiles, and divergence beyond the
census domain (|S| = 10, 11 exhaustive; random up to 20)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from systems import rankm
from verify_r3 import strings

SLOW = [('aaab', 'ba'), ('abbb', 'ba'), ('baaa', 'ab'), ('bbba', 'ab')]

def run(k, A, B, S, cap, lencap):
    s, steps = S, 0
    while True:
        O = occ_(s, B)
        if len(O) <= k:
            return s, steps
        i = O[k]
        s = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap or len(s) > lencap:
            return None, steps

def occ_(s, B):
    O, i = [], 0
    while True:
        j = s.find(B, i)
        if j < 0:
            return O
        O.append(j); i = j + len(B)

def flagged_inputs(A, B, k=0, cap=2000):
    return [S for S in strings(['a', 'b'], 9)
            if run(k, A, B, S, cap, 10**9)[0] is None]

for (A, B) in SLOW:
    fl = flagged_inputs(A, B)
    mx = (0, None, 0)
    for S in fl:
        out, st = run(0, A, B, S, 2*10**6, 2*10**6)
        if out is None:
            print(f"[{A}/{B}] rank0 DIVERGES on flagged input {S!r} even at 2M caps")
            break
        if st > mx[0]:
            mx = (st, S, len(out))
    else:
        print(f"[{A}/{B}] rank0: {len(fl)} inputs of <=9 need >2000 steps; "
              f"all terminate: worst {mx[0]} steps on {mx[1]!r} "
              f"(final len {mx[2]}); rank1 worst on same inputs: "
              f"{max(run(1, A, B, S, 2*10**6, 2*10**6)[1] for S in fl)} steps")
    # beyond the domain: length 10, 11 exhaustive; random up to 20
    div = None
    for S in strings(['a', 'b'], 10) + strings(['a', 'b'], 11):
        if run(0, A, B, S, 10**5, 10**6)[0] is None:
            div = S; break
    if div is None:
        rng = random.Random(11)
        for _ in range(400):
            S = ''.join(rng.choice('ab') for _ in range(rng.randrange(12, 21)))
            if run(0, A, B, S, 10**5, 10**6)[0] is None:
                div = S; break
    print(f"   [{A}/{B}] rank0 beyond domain (|S|<=11 exh, rand<=20): "
          f"{'DIVERGES on %r' % div if div else 'no divergence found'}")

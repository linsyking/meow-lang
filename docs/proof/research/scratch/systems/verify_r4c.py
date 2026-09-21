"""R4 part C2: depth-3 sampling + the occurrence lemma as a unit test."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(200000)
from verify_r4 import ev, strings
from verify_r4b import TR, O, PHI, F, ev_core, verify, cross_TR, size
import toolkit as tk
sg = tk.BIN

# O unit test: for total computed u, v over all small values: O = TOP iff
# u occurs in v (u != eps slice); u = eps slice: definedness only.
import itertools
vals = [''] + [''.join(t) for L in range(1, 4)
               for t in itertools.product('ab', repeat=L)]
bad = tot = 0
for u in vals:
    for v in vals:
        w = ev_core(O(tk.K(u), tk.K(v)), '')
        if w[0] == 'undef': tot += 1; continue
        if u:
            want = tk.BIN.top if u in v else tk.BIN.bot
            if w[1] != want: bad += 1
print(f"O unit test: {len(vals)}^2 pairs, {tot} undefined (expect 0), "
      f"{bad} wrong answers on u!=eps (expect 0)")

# depth-3 random lazy expressions vs TR
from verify_r4 import leaves
def rand_expr(rng, maxdepth):
    if maxdepth == 0 or rng.random() < 0.25:
        return rng.choice(leaves())
    if rng.random() < 0.3:
        return ('C', rand_expr(rng, maxdepth - 1),
                rand_expr(rng, maxdepth - 1))
    return ('S', rand_expr(rng, maxdepth - 1), rand_expr(rng, maxdepth - 1),
            rand_expr(rng, maxdepth - 1))
rng = random.Random(42)
IN4 = strings(4)
exprs = [rand_expr(rng, 3) for _ in range(120)]
big = [size(TR(e)) for e in exprs[:10]]
print(f"depth-3 TR sizes (first 10): {big}")
verify(exprs, IN4, "random depth-3 sample (120)")
cross_TR(exprs, IN4, n=6)
print("verify_r4c done")

"""Misc: minimal l2r/r2l difference examples, per-string agreement condition,
length bound, timing, and bounded searches for string reversal.
"""
import itertools
import sys
import time
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l, occurs, is_unbordered


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def main():
    alpha = ("a", "b")

    # 1. minimal difference examples (A,B,C) with [A/B]C != [A/B]^R C
    best = None
    for A in all_strings(alpha, 3):
        for B in [s for s in all_strings(alpha, 3) if s]:
            for C in all_strings(alpha, 6):
                if subst_l2r(A, B, C) != subst_r2l(A, B, C):
                    key = (len(C), len(B), len(A))
                    if best is None or key < best[0]:
                        best = (key, A, B, C)
    print("minimal (|C|,|B|,|A|) difference:", best)
    # a few canonical ones
    for (A, B, C) in [("b", "aa", "aaa"), ("", "aba", "ababa"), ("a", "bb", "abbba")]:
        print(f"  [A/B]C: [{{}}/{B}]{C}: l2r={subst_l2r(A,B,C)!r}  r2l={subst_r2l(A,B,C)!r}".format(A))

    # 2. per-string agreement condition: pairwise-disjoint occurrences => equal
    n = 0
    for B in [s for s in all_strings(alpha, 4) if s]:
        for A in all_strings(alpha, 3):
            for C in all_strings(alpha, 7):
                occ = occurs(B, C)
                disjoint = all(occ[i] + len(B) <= occ[i+1] for i in range(len(occ)-1))
                if disjoint and subst_l2r(A, B, C) != subst_r2l(A, B, C):
                    n += 1
    print("disjoint-occurrence strings where l2r != r2l (expect 0):", n)

    # 3. unbordered B => functions equal (already in duality run; re-verify on bigger C)
    n = 0
    for B in [s for s in all_strings(alpha, 4) if s and is_unbordered(s)]:
        for A in all_strings(alpha, 3):
            for C in all_strings(alpha, 8):
                if subst_l2r(A, B, C) != subst_r2l(A, B, C):
                    n += 1
    print("unbordered-pattern differences up to |C|=8 (expect 0):", n)

    # 4. length bound |[A/B]^R C| <= |C| * (1+|A|)
    n = 0
    for B in [s for s in all_strings(alpha, 3) if s]:
        for A in all_strings(alpha, 4):
            for C in all_strings(alpha, 7):
                r = subst_r2l(A, B, C)
                if len(r) > len(C) * (1 + len(A)):
                    n += 1
    print("length-bound violations (expect 0):", n)

    # 5. timing: single r2r/r2l pass and a pipeline, quadratic-ish check
    for L in [1000, 2000, 4000, 8000]:
        C = ("ab" * L)
        t0 = time.perf_counter()
        for _ in range(3):
            subst_r2l("b", "aa", C)
        t1 = time.perf_counter()
        print(f"  r2l pass |C|={len(C)}: {(t1-t0)/3*1000:.2f} ms")


if __name__ == "__main__":
    main()

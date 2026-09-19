"""Exhaustive check of the mirror duality and the l2r/r2l difference classification.

Domain: alphabets of size 2 and 3, all C with |C| <= 6, all B with 1 <= |B| <= 3,
all A with |A| <= 3 (including empty). For each (A,B) we also decide whether the
FUNCTIONS [A/B] and [A/B]^R agree on the whole tested domain of C.
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l, subst_r2l_via_rev, rev, occurs, is_unbordered


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def main():
    for alpha in [("a", "b"), ("a", "b", "c")]:
        Cs = all_strings(alpha, 6)
        As = all_strings(alpha, 3)
        Bs = [s for s in all_strings(alpha, 3) if s]
        duality_fail = 0
        diff_pairs = []          # (A,B) where the functions differ somewhere
        same_but_bordered = []   # (A,B) bordered B yet functions agree everywhere
        unbordered_pairs = 0
        for A in As:
            for B in Bs:
                func_diff = False
                for C in Cs:
                    if len(C) < len(B) and not occurs(B, C):
                        continue
                    l = subst_l2r(A, B, C)
                    r = subst_r2l(A, B, C)
                    if l != r:
                        func_diff = True
                    d = subst_r2l_via_rev(A, B, C)
                    if d != r:
                        duality_fail += 1
                        if duality_fail <= 5:
                            print("DUALITY FAIL", alpha, A, B, C, r, d)
                if is_unbordered(B):
                    unbordered_pairs += 1
                    if func_diff:
                        print("UNBORDERED BUT DIFFER", alpha, A, B)
                else:
                    (same_but_bordered if not func_diff else diff_pairs).append((A, B))
        print(f"alphabet={alpha}: duality failures={duality_fail}, "
              f"unbordered (A,B) pairs all agreeing={unbordered_pairs}, "
              f"bordered pairs with differing functions={len(diff_pairs)}, "
              f"bordered pairs with agreeing functions={len(same_but_bordered)}")
        print("  sample differing (A,B):", diff_pairs[:8])
        print("  sample bordered-but-agreeing (A,B):", same_but_bordered[:8])


if __name__ == "__main__":
    main()

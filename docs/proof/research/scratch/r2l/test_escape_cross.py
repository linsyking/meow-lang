"""Completing the escape direction-lock table: l2r semantics with the MIRRORED pair
scheme (u -> f(u) u1, post-fix), both rep constructions. Expect FAILURES
(mirror of Theorem 8: the escape scheme must match the scan direction).
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r
from toolkit import make_rep, make_rep_mirror


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


if __name__ == "__main__":
    for sigma in [("b", "x", "c"), ("b", "x", "c", "d")]:
        Ss = all_strings(sigma, 5)
        chars = list(sigma)
        for repmaker, cname in [(make_rep, "orig-const"), (make_rep_mirror, "mirror-const")]:
            tested = fails = 0
            first = None
            for r in range(1, len(chars) + 1):
                for U in itertools.combinations(chars, r):
                    for V in itertools.permutations(chars, r):
                        f = dict(zip(U, V))
                        fps = [u for u in U if f[u] == u]
                        if not fps:
                            continue
                        for u1 in fps:
                            rest = [u for u in U if u != u1]
                            order = [u1] + rest
                            n = len(order)
                            repE = repmaker(subst_l2r, sigma, n)
                            esc = [(u, f[u] + u1) for u in order]
                            une = [(f[u] + u1, u) for u in order]
                            for S in Ss:
                                tested += 1
                                E = repE(S, esc)
                                D = repE(E, une)
                                if D != S:
                                    fails += 1
                                    if first is None:
                                        first = (S, dict(f), u1, E, D)
            print(f"[{sigma}] l2r + mirror-scheme + {cname}: tested={tested} fails={fails} first={first}")

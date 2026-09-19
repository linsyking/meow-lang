"""Pin down the Independent Substitution failure: is it the mirror, or the paper's
own lemma? Hypotheses: A cap B = empty, A cap C = empty, C != eps.
Suspected missing hypothesis: B != eps (nonempty replacement).
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def main():
    for alpha in [("a", "b"), ("a", "b", "c")]:
        Ss = all_strings(alpha, 6)
        short = all_strings(alpha, 4)
        for sem, name in [(subst_l2r, "l2r"), (subst_r2l, "r2l")]:
            fail_asstated = []     # as stated in the paper (B may be eps)
            fail_Bnonempty = []    # with the added hypothesis B != eps
            for A in short:
                for B in short:        # B = replacement
                    for C in short:    # C = pattern
                        if not C: continue
                        if set(A) & set(B) or set(A) & set(C):
                            continue
                        for S in Ss:
                            lhs = A in sem(B, C, S)
                            rhs = A in S
                            if lhs != rhs:
                                rec = (A, B, C, S, sem(B, C, S))
                                fail_asstated.append(rec)
                                if B:
                                    fail_Bnonempty.append(rec)
            print(f"[{alpha}] {name}: failures as stated={len(fail_asstated)}, "
                  f"failures with B!=eps={len(fail_Bnonempty)}")
            if fail_asstated and not fail_Bnonempty:
                exs = fail_asstated[:3]
                print(f"   all failures have B=eps; e.g. "
                      + "; ".join(f"A={a},B={b!r},C={c},S={s} -> [B/C]S={r}" for a, b, c, s, r in exs))
            elif fail_Bnonempty:
                print("   !! failures even with B!=eps:", fail_Bnonempty[:3])


if __name__ == "__main__":
    main()

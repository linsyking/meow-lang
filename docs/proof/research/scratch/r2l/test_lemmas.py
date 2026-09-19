"""Verify the mirrors of the paper's Section 2 lemmas under r2l semantics.

Labels: each check prints FAIL lines on counterexamples; final summary lines.
Domain: |Sigma|=2 and 3, all strings up to length 6 (patterns up to 4 where noted).
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/scratch/r2l")  # noqa
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l, occurs, is_unbordered


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def check(name, n_fail):
    status = "OK" if n_fail == 0 else f"FAIL({n_fail})"
    print(f"{name}: {status}")
    return n_fail


def main():
    total = 0
    for alpha in [("a", "b"), ("a", "b", "c")]:
        Ss = all_strings(alpha, 6)
        short = all_strings(alpha, 4)
        Ss6 = all_strings(alpha, 6)

        # 1. Identity Substitution (mirror): A != eps => [A/A]^R S = S
        n = 0
        for A in short:
            if not A:
                continue
            for S in Ss6:
                if subst_r2l(A, A, S) != S:
                    n += 1
                    if n <= 3: print("  identity fail", A, S)
        total += check(f"[{alpha}] Identity Substitution mirror", n)

        # 2. Direct Substitution (mirror): B != eps => [A/B]^R B = A
        n = 0
        for A in short:
            for B in short:
                if B and subst_r2l(A, B, B) != A:
                    n += 1
                    if n <= 3: print("  direct fail", A, B)
        total += check(f"[{alpha}] Direct Substitution mirror", n)

        # 3. Substitution Elimination (mirror): B not in S => [A/B]^R S = S
        n = 0
        for A in short:
            for B in short:
                if not B: continue
                for S in Ss6:
                    if not occurs(B, S) and subst_r2l(A, B, S) != S:
                        n += 1
                        if n <= 3: print("  elim fail", A, B, S)
        total += check(f"[{alpha}] Substitution Elimination mirror", n)

        # 4. Independent Substitution (mirror):
        #    A cap B = eps, A cap C = eps, C != eps  =>  A in [B/C]^R S <=> A in S
        n = 0
        for A in short:
            for Bp in short:      # pattern C in the lemma
                if not Bp: continue
                for Cp in short:  # replacement B in the lemma
                    if set(A) & set(Bp) or set(A) & set(Cp): continue
                    for S in Ss6:
                        lhs = A in subst_r2l(Cp, Bp, S)
                        rhs = A in S
                        if lhs != rhs:
                            n += 1
                            if n <= 3: print("  indep fail", A, Bp, Cp, S)
        total += check(f"[{alpha}] Independent Substitution mirror", n)

        # 5. Double Substitution (mirror): X,Y nonempty, X in Y, Y unbordered
        #    => [X/Y]^R [Y/X]^R Z = Z
        n = 0
        for X in short:
            if not X: continue
            for Y in short:
                if not Y or X not in Y or not is_unbordered(Y): continue
                for Z in Ss6:
                    if subst_r2l(X, Y, subst_r2l(Y, X, Z)) != Z:
                        n += 1
                        if n <= 3: print("  doublesub fail", X, Y, Z)
        total += check(f"[{alpha}] Double Substitution mirror", n)

        # 5b. hypotheses still necessary in the mirror (expect failures; report)
        n_border = 0; n_nest = 0
        for X in short:
            if not X: continue
            for Y in short:
                if not Y or X not in Y: continue
                if not is_unbordered(Y):
                    for Z in Ss6:
                        if subst_r2l(X, Y, subst_r2l(Y, X, Z)) != Z:
                            n_border += 1
                            break
                else:  # Y unbordered but... skip (X in Y enforced)
                    pass
        print(f"[{alpha}] DoubleSub mirror: bordered-Y failures found: {n_border} (expected >0)")

        # 6. Original Stepping-into under r2l: [C/A]^R (AB) =? C ([C/A]^R B) -- expect FAILs
        n = []
        for A in short:
            if not A: continue
            for B in short:
                for C in short:
                    if subst_r2l(C, A, A + B) != C + subst_r2l(C, A, B):
                        n.append((A, B, C))
        total += check(f"[{alpha}] original Stepping-into under r2l (expected FAIL)",
                       1 if n else 0)
        print("   first counterexamples:", n[:4])

        # 7. Mirror Stepping-into: [C/A]^R (BA) = ([C/A]^R B) C
        n = 0
        for A in short:
            if not A: continue
            for B in short:
                for C in short:
                    if subst_r2l(C, A, B + A) != subst_r2l(C, A, B) + C:
                        n += 1
                        if n <= 3: print("  step-mirror fail", A, B, C)
        total += check(f"[{alpha}] Stepping-into mirror [C/A]^R(BA)=([C/A]^R B)C", n)

        # 8. Tail/Head Elimination (string facts, direction-free), as stated:
        #    B != eps, B cap A = eps:  CB in AB => C suffix of A
        #    BC in BA => C prefix of A
        n = 0
        for A in short:
            for B in short:
                if not B or set(A) & set(B): continue
                for C in short:
                    if C + B in A + B and not A.endswith(C):
                        n += 1
                        if n <= 3: print("  tailelim fail", A, B, C)
        total += check(f"[{alpha}] Tail Elimination (string fact)", n)
        n = 0
        for A in short:
            for B in short:
                if not B or set(A) & set(B): continue
                for C in short:
                    if B + C in B + A and not A.startswith(C):
                        n += 1
                        if n <= 3: print("  headelim fail", A, B, C)
        total += check(f"[{alpha}] Head Elimination (string fact)", n)

    print("TOTAL FAILURES:", total)


if __name__ == "__main__":
    main()

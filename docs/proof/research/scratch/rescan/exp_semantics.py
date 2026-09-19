"""Experiment 1: semantics of [A/B]^u vs [A/B] (safe).

Verifies computationally:
 T2: [A/B]^u = [A/B] on all C  <=>  (B not-in A) AND (no nonempty suffix of A
     is a proper prefix of B).
 T3: [A/B]^u total (halts on every C)  <=>  B not-in A.
     Step bound: #matches <= |C| - |B| + 1 (when total).
 Also: smallest counterexamples, [A/A]^u domain, stack-process equivalence.
"""
import itertools
from substlib import subst_safe, subst_unsafe, eq_unsafe, Diverge, all_strings

CAP = 400


def safe_pair(A, B):
    """Condition (*): B not in A, and no nonempty suffix of A is a proper prefix of B."""
    if B in A:
        return False
    for i in range(1, len(A) + 1):  # wait: suffixes of A, i in [0..|A|-1] nonempty
        suf = A[i:] if i < len(A) else ""
    # correct: all nonempty suffixes A[i:] for 0 <= i < len(A)
    for i in range(0, len(A)):
        suf = A[i:]
        if len(suf) < len(B) and B.startswith(suf):
            return False
    return True


def stack_process(A, B, C, cap=CAP):
    """Clean derived semantics: O='', T=C; while B in T: q=leftmost; O+=T[:q]; T=A+T[q+|B|:].
    Returns O+T. Used to cross-validate subst_unsafe."""
    if B == "":
        return None
    O, T = "", C
    steps = 0
    while B in T:
        steps += 1
        if steps > cap:
            raise Diverge((A, B, C))
        q = T.find(B)
        O += T[:q]
        T = A + T[q + len(B):]
    return O + T, steps


def run(sigma, maxA, maxB, maxC):
    n_differ_found, n_eq_violation = 0, 0
    tot_violation = 0
    smallest_diff = None
    smallest_div = None
    Cs = all_strings(sigma, maxC)
    for la in range(1, maxA + 1):
        for A in map("".join, itertools.product(sigma, repeat=la)):
            for lb in range(1, maxB + 1):
                for B in map("".join, itertools.product(sigma, repeat=lb)):
                    sp = safe_pair(A, B)
                    # totality + equality over all C
                    total = True
                    all_eq = True
                    for C in Cs:
                        s = subst_safe(A, B, C)
                        u = eq_unsafe(A, B, C, CAP)
                        if u != s:
                            all_eq = False
                            if u == "DIVERGE":
                                total = False
                                if smallest_div is None or (len(A)+len(B)+len(C)) < smallest_div[0]:
                                    smallest_div = (len(A)+len(B)+len(C), A, B, C)
                            elif smallest_diff is None or (len(A)+len(B)+len(C)) < smallest_diff[0]:
                                smallest_diff = (len(A)+len(B)+len(C), A, B, C, s, u)
                    # T3: total <=> B not in A
                    if total != (B not in A):
                        tot_violation += 1
                        print(f"T3 VIOLATION: A={A} B={B} total={total} BinA={B in A}")
                    # T2: all_eq <=> safe_pair
                    if all_eq != sp:
                        n_eq_violation += 1
                        pass  # : A={A} B={B} all_eq={all_eq} safe_pair={sp}")
    return tot_violation, n_eq_violation, smallest_diff, smallest_div


if __name__ == "__main__":
    for sigma, mA, mB, mC in [("ab", 3, 3, 5), ("ab", 4, 3, 6), ("abc", 3, 2, 5)]:
        tv, ev, sd, sv = run(sigma, mA, mB, mC)
        print(f"sigma={sigma} |A|<={mA} |B|<={mB} |C|<={mC}: T3 violations={tv}, T2 violations={ev}")
        print(f"  smallest (A,B,C) with values differing: {sd}")
        print(f"  smallest (A,B,C) with unsafe diverging: {sv}")
    # cross-validate stack process on a bunch
    import random
    random.seed(1)
    bad = 0
    for _ in range(3000):
        A = "".join(random.choice("ab") for _ in range(random.randint(1, 3)))
        B = "".join(random.choice("ab") for _ in range(random.randint(1, 3)))
        C = "".join(random.choice("ab") for _ in range(random.randint(0, 7)))
        try:
            u = subst_unsafe(A, B, C, CAP)
        except Diverge:
            u = "DIVERGE"
        try:
            r, st = stack_process(A, B, C, CAP)
        except Diverge:
            r = "DIVERGE"
        if u != r:
            bad += 1
            print("STACK MISMATCH", A, B, C, u, r)
    print("stack-process cross-validation mismatches:", bad)
    # step bound check: matches <= |C|-|B|+1 on total pairs
    viol = []
    for A in map("".join, itertools.product("ab", repeat=2)):
        for B in map("".join, itertools.product("ab", repeat=2)):
            if not B:
                continue
            for C in all_strings("ab", 6):
                try:
                    r, st = stack_process(A, B, C, CAP)
                except Diverge:
                    continue
                if st > len(C) - len(B) + 1:
                    viol.append((A, B, C, st))
    print("step-bound violations (steps <= |C|-|B|+1):", len(viol), viol[:5])

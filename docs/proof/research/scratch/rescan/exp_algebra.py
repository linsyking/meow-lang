"""Experiment 2: which of the paper's Section 2 theorems survive under V = [A/B]^u.

Tests, computationally, on stated finite domains:
 - Identity Substitution [A/A]^u S: claim = S iff A not-in S, else DIVERGE.
 - Direct Substitution [A/B]^u B: claim = A if B not-in A, else DIVERGE.
 - Substitution Elimination: B not-in S => [A/B]^u S = S.
 - Stepping-into [C/A]^u(A.B): holds iff safe_pair(C,A)... test equality [C/A]^u(AB)=C([C/A]^u B).
 - Independent Substitution (A,B,C pairwise char-disjoint): A in [B/C]^u S <=> A in S.
 - Double Substitution Lemma [X/Y]^u[Y/X]^u Z: REFUTED when X in Y (divergence);
   find smallest counterexample; also test the partial-function agreement rate.
 - enc/dec round trip [b/xb]^u[xb/b]^u: divergence census.
"""
import itertools
from substlib import subst_safe, eq_unsafe, all_strings

CAP = 300
SIG = "ab"
SIG3 = "abc"


def U(A, B, C):
    return eq_unsafe(A, B, C, CAP)


def check(name, cond_iter):
    bad = [x for x in cond_iter if not x[0]]
    print(f"{name}: {'OK' if not bad else str(len(bad)) + ' FAILURES e.g. ' + str(bad[:3])}")
    return bad


# 1. Identity substitution
bad = []
for A in ["".join(p) for n in range(1, 4) for p in itertools.product(SIG, repeat=n)]:
    for S in all_strings(SIG, 5):
        r = U(A, A, S)
        want = S if A not in S else "DIVERGE"
        if r != want:
            bad.append((A, S, r, want))
print(f"Identity [A/A]^u S = (S if A notin S else DIVERGE): {'OK' if not bad else bad[:5]}")

# 2. Direct substitution
bad = []
for A in ["".join(p) for n in range(0, 4) for p in itertools.product(SIG, repeat=n)]:
    for B in ["".join(p) for n in range(1, 4) for p in itertools.product(SIG, repeat=n)]:
        r = U(A, B, B)
        want = A if B not in A else "DIVERGE"
        if r != want:
            bad.append((A, B, r, want))
print(f"Direct [A/B]^u B = (A if B notin A else DIVERGE): {'OK' if not bad else bad[:5]}")

# 3. Substitution elimination
bad = []
for A in ["".join(p) for n in range(0, 3) for p in itertools.product(SIG, repeat=n)]:
    for B in ["".join(p) for n in range(1, 3) for p in itertools.product(SIG, repeat=n)]:
        for S in all_strings(SIG, 5):
            if B not in S and U(A, B, S) != S:
                bad.append((A, B, S))
print(f"Elimination B notin S => [A/B]^u S = S: {'OK' if not bad else bad[:5]}")

# 4. Stepping-into: [C/A]^u (A . B) = C . [C/A]^u B  -- for A,B,C arbitrary small
bad = []
for R in ["".join(p) for n in range(0, 3) for p in itertools.product(SIG, repeat=n)]:  # "C" in paper
    for P in ["".join(p) for n in range(1, 3) for p in itertools.product(SIG, repeat=n)]:  # "A"
        for Bt in all_strings(SIG, 4):
            lhs = U(R, P, P + Bt)
            rhs0 = U(R, P, Bt)
            rhs = None if rhs0 in ("DIVERGE", None) or R is None else (R + rhs0 if rhs0 != "DIVERGE" else "DIVERGE")
            if rhs0 == "DIVERGE":
                rhs = "DIVERGE"
            else:
                rhs = R + rhs0
            if lhs != rhs:
                bad.append((R, P, Bt, lhs, rhs))
print(f"Stepping-into [R/P]^u(PB) = R.[R/P]^u B: {'OK' if not bad else str(len(bad)) + ' failures, e.g. ' + str(bad[:4])}")

# 5. Independent substitution over 3 letters: A chars disjoint from B(replacement) and C(pattern)
bad = []
As = ["c", "cc", "ccc", "ca"]  # must share no char with B,C; B,C use only a,b
for A in As:
    if set(A) & set("ab"):
        continue
    for R in ["".join(p) for n in range(1, 3) for p in itertools.product("ab", repeat=n)]:
        for P in ["".join(p) for n in range(1, 3) for p in itertools.product("ab", repeat=n)]:
            for S in all_strings(SIG3, 4):
                r = U(R, P, S)
                lhs = (A in r) if r != "DIVERGE" else None
                if lhs != (A in S):
                    bad.append((A, R, P, S, r, A in S))
print(f"Independent Substitution (A disjoint chars): {'OK' if not bad else str(len(bad)) + ' failures e.g. ' + str(bad[:4])}")

# 6. Double Substitution Lemma: X nonempty in Y, Y unbordered => [X/Y]^u[Y/X]^u Z = Z ?
def unbordered(Y):
    for k in range(1, len(Y)):
        if Y[:k] == Y[len(Y) - k:]:
            return False
    return True

bad = []
found_div, found_val = None, None
for X in ["".join(p) for n in range(1, 3) for p in itertools.product(SIG3, repeat=n)]:
    for Y in ["".join(p) for n in range(1, 4) for p in itertools.product(SIG3, repeat=n)]:
        if X not in Y or not unbordered(Y) or X == Y:
            continue
        for Z in all_strings(SIG3, 4):
            inner = U(Y, X, Z)
            if inner == "DIVERGE":
                if found_div is None:
                    found_div = (X, Y, Z)
                continue
            outer = U(X, Y, inner)
            if outer == "DIVERGE":
                if found_div is None:
                    found_div = (X, Y, Z)
            elif outer != Z:
                if found_val is None:
                    found_val = (X, Y, Z, inner, outer)
print(f"Double Substitution Lemma: first divergence case (X,Y,Z) = {found_div}")
print(f"                              first wrong-value case = {found_val}")

# 7. enc/dec round trip census over Sigma={a,b} with b='a', x='b' (sigma1, sigma2)
#    enc = [xb/b]^u, dec = [b/xb]^u ; dec(enc(S)) =? S
div, wrong, ok = 0, 0, 0
ex_div, ex_wrong = None, None
for S in all_strings("ab", 6):
    e = U("ba", "a", S)  # [xb/b]^u with x=b,b=a: replacement 'ba', pattern 'a'
    if e == "DIVERGE":
        div += 1
        if ex_div is None:
            ex_div = S
        continue
    d = U("a", "ba", e)  # dec
    if d == "DIVERGE":
        div += 1
    elif d != S:
        wrong += 1
        if ex_wrong is None:
            ex_wrong = (S, e, d)
    else:
        ok += 1
print(f"enc/dec round trip (x=b,b=a): ok={ok}, diverged={div} (first at S={ex_div}), wrong={wrong} {ex_wrong}")
# also verify dec is a safe pair (total) and equals safe semantics:
agree = all(U("a", "ba", S) == subst_safe("a", "ba", S) for S in all_strings("ab", 6))
print(f"dec = [b/xb]^u alone equals safe dec on all |S|<=6: {agree}")

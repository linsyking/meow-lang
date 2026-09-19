"""Experiment 2b: refined hypotheses for Stepping-into and Independent Substitution."""
import itertools
from substlib import eq_unsafe, all_strings

CAP = 300
SIG = "ab"
SIG3 = "abc"


def U(A, B, C):
    return eq_unsafe(A, B, C, CAP)


# Stepping-into under hypothesis P notin R (totality of the node):
bad = []
for R in ["".join(p) for n in range(0, 4) for p in itertools.product(SIG, repeat=n)]:
    for P in ["".join(p) for n in range(1, 4) for p in itertools.product(SIG, repeat=n)]:
        if P in R:
            continue  # node diverges on P; hypothesis excludes
        for Bt in all_strings(SIG, 4):
            lhs = U(R, P, P + Bt)
            rhs0 = U(R, P, Bt)
            rhs = "DIVERGE" if rhs0 == "DIVERGE" else R + rhs0
            if lhs != rhs:
                bad.append((R, P, Bt, lhs, rhs))
print(f"Stepping-into with P notin R: {'OK' if not bad else str(len(bad)) + ' failures e.g. ' + str(bad[:5])}")

# Independent Substitution under hypothesis P notin R (total node), A char-disjoint from both:
bad = []
for A in ["c", "cc", "ccc", "acb"] if False else ["c", "cc", "ca"]:
    if set(A) & set("ab"):
        continue
    for R in ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]:
        for P in ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]:
            if P in R:
                continue
            for S in all_strings(SIG3, 4):
                r = U(R, P, S)
                if r == "DIVERGE":
                    bad.append(("DIVERGED despite P notin R", A, R, P, S))
                    continue
                if (A in r) != (A in S):
                    bad.append((A, R, P, S, r, A in S))
print(f"Independent Substitution with P notin R: {'OK' if not bad else str(len(bad)) + ' failures e.g. ' + str(bad[:5])}")

# DSL: characterize the composed partial function exactly:
# [X/Y]^u [Y/X]^u Z, X in Y, Y unbordered, X != Y. Claim: defined iff X notin Z, then = Z.
bad = []


def unbordered(Y):
    return all(Y[:k] != Y[len(Y) - k:] for k in range(1, len(Y)))


for X in ["".join(p) for n in range(1, 3) for p in itertools.product(SIG3, repeat=n)]:
    for Y in ["".join(p) for n in range(1, 4) for p in itertools.product(SIG3, repeat=n)]:
        if X not in Y or not unbordered(Y) or X == Y:
            continue
        for Z in all_strings(SIG3, 4):
            inner = U(Y, X, Z)
            if inner == "DIVERGE":
                if X in Z:
                    continue  # expected divergence
                bad.append(("diverged but X notin Z", X, Y, Z))
                continue
            if X not in Z and inner != Z:
                bad.append(("inner not identity", X, Y, Z, inner))
            outer = U(X, Y, inner)
            want = Z  # since X notin Z => Y notin Z (X in Y), outer inert => Z
            if outer != want:
                bad.append((X, Y, Z, inner, outer))
print(f"DSL partial characterization (defined iff X notin Z, value Z): {'OK' if not bad else str(len(bad)) + ' failures e.g. ' + str(bad[:5])}")

# enc/dec with roles SWAPPED: enc' = [xb^2/b]?? try to find ANY 2-pass pipeline over {a,b}
# of the form [W1/'a'][W2/'b'] or similar that is total+injective+roundtrippable.
# Brute: replacement for pattern 'a' is Wa, for pattern 'b' is Wb (each avoiding its own char).
def total_pipeline(passes, Cs):
    """passes = list of (repl, pat) applied leftmost-first? apply in given order: first in list first."""
    for C in Cs:
        cur = C
        for R, P in passes:
            r = eq_unsafe(R, P, cur, CAP)
            if r == "DIVERGE":
                return None
            cur = r
        yield_pass = cur
    return True


# Search: 2-char alphabet, per-char codes c -> w(c) with c notin w(c), both orders.
from substlib import subst_safe
results = []
for wa in ["", "b", "bb", "bbb"]:
    for wb in ["", "a", "aa", "aaa"]:
        if "a" in wa or "b" in wb:
            continue
        for order in [0, 1]:
            passes = [(wa, "a"), (wb, "b")] if order == 0 else [(wb, "b"), (wa, "a")]
            Cs = all_strings("ab", 5)
            mapping = {}
            ok = True
            for C in Cs:
                cur = C
                for R, P in passes:
                    r = eq_unsafe(R, P, cur, CAP)
                    if r == "DIVERGE":
                        ok = False
                        break
                    cur = r
                if not ok:
                    break
                mapping[C] = cur
            if ok:
                inj = len(set(mapping.values())) == len(mapping)
                results.append((passes, inj, len(mapping)))
print("per-char-code pipelines (total on |C|<=5):", results)

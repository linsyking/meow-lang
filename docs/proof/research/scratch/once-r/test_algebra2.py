"""Refined algebra tests: exact characterization of the once-r roundtrip,
k-fold iteration, commutation."""
import itertools
from core import subst_once_r as R

SIG = "ab"
def allstrings(sig, n):
    for L in range(n + 1):
        for t in itertools.product(sig, repeat=L):
            yield "".join(t)

def periods(Y):
    """i in [1, |Y|) with Y[j] = Y[i+j] for all valid j."""
    n = len(Y)
    return [i for i in range(1, n) if all(Y[j] == Y[i + j] for j in range(n - i))]

def roundtrip_ok_for_all(X, Y, maxlen=7):
    for Z in allstrings(SIG, maxlen):
        if R(X, Y, R(Y, X, Z)) != Z:
            return False, Z
    return True, None

def pred_exact(X, Y):
    """Conjectured exact condition: X in Y, and for every period i of Y,
    X occurs in the length-i suffix of Y."""
    if X not in Y:
        return False
    for i in periods(Y):
        if X not in Y[len(Y) - i:]:
            return False
    return True

fails = 0
for X in allstrings(SIG, 4):
    for Y in allstrings(SIG, 4):
        if not X or not Y:
            continue
        ok, wit = roundtrip_ok_for_all(X, Y, 7)
        p = pred_exact(X, Y)
        if ok != p:
            print(f"CHAR MISMATCH: X={X!r} Y={Y!r} ok={ok} pred={p} wit={wit}")
            fails += 1
print("exact roundtrip characterization (|X|,|Y|<=4, |Z|<=7):",
      "CONFIRMED" if fails == 0 else f"{fails} FAILURES")

# k-fold iteration with character-disjoint alphabets
def k_rightmost(A, B, C, k):
    for _ in range(k):
        C = R(A, B, C)
    return C

def sim_k_rightmost(A, B, C, k):
    """Replace the k rightmost non-overlapping occurrences of B in C,
    chosen greedily from the right, simultaneously."""
    if B not in C:
        return C
    ends = []  # chosen intervals, greedy from the right
    limit = len(C)  # next occurrence must end at or before this
    while len(ends) < k:
        # rightmost occurrence ending <= limit
        best = -1
        for i in range(len(C) - len(B), -1, -1):
            if i + len(B) <= limit and C.startswith(B, i):
                best = i
                break
        if best < 0:
            break
        ends.append(best)
        limit = best
    ends.reverse()
    out, prev = [], 0
    for j in ends:
        out.append(C[prev:j]); out.append(A); prev = j + len(B)
    out.append(C[prev:])
    return "".join(out)

bad = 0
for C in allstrings(SIG, 7):
    for A in allstrings("a", 3):
        for B in allstrings("b", 3):
            if not B: continue
            for k in range(4):
                if k_rightmost(A, B, C, k) != sim_k_rightmost(A, B, C, k):
                    print(f"K-IT FAIL: A={A} B={B} C={C} k={k}")
                    bad += 1
print("k-fold iteration = k rightmost replacements (disjoint alphabets):",
      "CONFIRMED" if bad == 0 else f"{bad} FAILURES")

# Show that 'B not substring of A' is NOT enough for the iteration lemma
c = k_rightmost("a", "aa", "aaa", 2)
s = sim_k_rightmost("a", "aa", "aaa", 2)
print(f"weak-hypothesis ctrex: [a/aa]_R twice on 'aaa' = {c!r}, "
      f"simultaneous-2-rightmost = {s!r}, equal={c==s}")

# Commutation: disjoint alphabets commute
from core import subst_once_r as Rr
def disjoint(u, v):
    return not (set(u) & set(v))
cf = 0
for S in allstrings(SIG, 6):
    for A1 in allstrings("a", 2):
        for B1 in allstrings("b", 2):
            for A2 in allstrings("b", 2):
                for B2 in allstrings("a", 2):
                    if not (B1 and B2): continue
                    lhs = Rr(A2, B2, Rr(A1, B1, S))
                    rhs = Rr(A1, B1, Rr(A2, B2, S))
                    if lhs != rhs:
                        print(f"COMMUTE FAIL {A1}/{B1} {A2}/{B2} {S}")
                        cf += 1
print("disjoint-alphabet commutation:",
      "CONFIRMED" if cf == 0 else f"{cf} FAILURES")

# Non-commutation: smallest counterexample with same alphabet
found = []
for n in range(0, 7):
    for S in allstrings(SIG, n):
        for A1, B1, A2, B2 in itertools.product(allstrings(SIG, 2), repeat=4):
            if not (B1 and B2): continue
            if Rr(A2, B2, Rr(A1, B1, S)) != Rr(A1, B1, Rr(A2, B2, S)):
                found.append((A1, B1, A2, B2, S))
    if found:
        break
print("smallest commutation failure:", found[0] if found else "none")

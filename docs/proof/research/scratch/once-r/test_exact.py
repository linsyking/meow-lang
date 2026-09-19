"""Exact characterization of the once-r double-substitution roundtrip.

Claim: [X/Y]_R [Y/X]_R Z = Z for ALL Z  iff
  (a) X in Y, and
  (b) for every period j in [1,|Y|) of Y, there is NO "admissible" Q
      starting with Y's length-j suffix, where admissible means:
        (i)  X not substring of Q          [Q is the part after the
        (ii) for every period j' in [1,|X|-1] of X:                rightmost X]
             Q[:j'] != X[|X|-j':]      [no junction occurrence of X]
Derivation: Z = P X Q (X rightmost) -> W = P Y Q; the roundtrip works iff the
rightmost occurrence of Y in W is the inserted copy; occurrences after |P|
are: inside Q (excluded by (i)), or starting at |P|+j, j>=1, which match Y
iff period_j(Y) and Q[:j] = Y's last j chars.
"""
import itertools
from core import subst_once_r as R

SIG = "ab"
def allstrings(sig, n):
    for L in range(n + 1):
        for t in itertools.product(sig, repeat=L):
            yield "".join(t)

def periods(Y):
    n = len(Y)
    return [i for i in range(1, n) if all(Y[j] == Y[i + j] for j in range(n - i))]

def admissible_exists_with_prefix(X, pref):
    """Is there a Q starting with `pref`, X not in Q, and for every period
    j' of X with j' <= |X|-1: Q[:j'] != X[|X|-j':]?
    Only prefixes of Q of length <= max(|X|-1, |pref|) matter for the
    constraints, so search over extensions up to that length."""
    # constraints only concern Q's prefix of length L0 = max(|X|-1, |pref|)
    L0 = max(len(X) - 1, len(pref))
    if not pref.startswith(X[:len(pref)]) and len(X) <= len(pref):
        pass
    for L in range(len(pref), L0 + 1):
        for ext in itertools.product(SIG, repeat=L - len(pref)):
            Q = pref + "".join(ext)
            if X in Q:
                continue
            ok = True
            for jp in periods(X):
                if jp <= len(X) - 1 and Q[:jp] == X[len(X) - jp:]:
                    ok = False
                    break
            if ok:
                return True, Q
    # if nothing short works, try a few random longer ones (the constraints
    # only depend on the first L0 chars unless X in Q triggers late)
    import random
    random.seed(1)
    for _ in range(200):
        Q = pref + "".join(random.choice(SIG) for _ in range(random.randint(0, 8)))
        if X in Q:
            continue
        ok = True
        for jp in periods(X):
            if jp <= len(Q) and Q[:jp] == X[len(X) - jp:]:
                ok = False
                break
        if ok:
            return True, Q
    return False, None

def pred_exact(X, Y):
    if X not in Y:
        return False
    for j in periods(Y):
        suff = Y[len(Y) - j:]
        exists, _ = admissible_exists_with_prefix(X, suff)
        if exists:
            return False
    return True

def roundtrip_ok_for_all(X, Y, maxlen=7):
    for Z in allstrings(SIG, maxlen):
        if R(X, Y, R(Y, X, Z)) != Z:
            return False, Z
    return True, None

fails = 0
checked = 0
for X in allstrings(SIG, 4):
    for Y in allstrings(SIG, 4):
        if not X or not Y:
            continue
        checked += 1
        ok, wit = roundtrip_ok_for_all(X, Y, 7)
        p = pred_exact(X, Y)
        if ok != p:
            print(f"CHAR MISMATCH: X={X!r} Y={Y!r} ok={ok} pred={p} wit={wit}")
            fails += 1
print(f"exact characterization ({checked} pairs, |Z|<=7):",
      "CONFIRMED" if fails == 0 else f"{fails} FAILURES")

# Sufficient-condition census: how much weaker is the exact condition vs the
# paper's (X in Y and Y unbordered)?
def unbordered(Y):
    return all(Y[:k] != Y[-k:] for k in range(1, len(Y)))
n_paper = n_exact = 0
for X in allstrings(SIG, 4):
    for Y in allstrings(SIG, 4):
        if not X or not Y: continue
        if X in Y and unbordered(Y): n_paper += 1
        if pred_exact(X, Y): n_exact += 1
print(f"sufficient-condition census: paper-cond on {n_paper} pairs, "
      f"exact-cond on {n_exact} pairs (of {checked})")

# commutation with FULLY disjoint alphabets (patterns and replacements)
cf = 0
for S in allstrings(SIG, 7):
    for A1 in allstrings("a", 2):
        for B1 in allstrings("a", 2):
            for A2 in allstrings("b", 2):
                for B2 in allstrings("b", 2):
                    if not (B1 and B2): continue
                    if R(A2, B2, R(A1, B1, S)) != R(A1, B1, R(A2, B2, S)):
                        print(f"COMMUTE FAIL [{A1}/{B1}] [{A2}/{B2}] S={S}")
                        cf += 1
print("fully-disjoint commutation:",
      "CONFIRMED" if cf == 0 else f"{cf} FAILURES")

# smallest same-alphabet commutation failure (nonempty replacements)
found = None
for n in range(0, 8):
    for S in allstrings(SIG, n):
        for A1, B1, A2, B2 in itertools.product(allstrings(SIG, 2), repeat=4):
            if not (B1 and B2): continue
            if R(A2, B2, R(A1, B1, S)) != R(A1, B1, R(A2, B2, S)):
                found = (A1, B1, A2, B2, S)
                break
        if found: break
    if found: break
print("smallest same-alphabet commutation failure (A1,B1,A2,B2,S):", found)

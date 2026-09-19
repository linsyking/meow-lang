"""Algebra checks for once-r: Section-2 analogs of the paper's theorems."""
import itertools
from core import subst_once_r as R

SIG = "ab"

def allstrings(sig, n):
    for L in range(n + 1):
        for t in itertools.product(sig, repeat=L):
            yield "".join(t)

def occurs(sub, s):
    return sub in s

def unbordered(Y):
    if not Y: return False
    for k in range(1, len(Y)):
        if Y[:k] == Y[-k:]:
            return False
    return True

fails = 0
def chk(name, ok, detail=""):
    global fails
    if not ok:
        print(f"FAIL {name} {detail}")
        fails += 1

# 1. Identity substitution
for S in allstrings(SIG, 5):
    for A in allstrings(SIG, 3):
        if A:
            chk("identity", R(A, A, S) == S, (A, S))

# 2. Direct substitution
for A in allstrings(SIG, 3):
    for B in allstrings(SIG, 3):
        if B:
            chk("direct", R(A, B, B) == A, (A, B))

# 3. Elimination
for S in allstrings(SIG, 4):
    for A in allstrings(SIG, 2):
        for B in allstrings(SIG, 3):
            if B and B not in S:
                chk("elim", R(A, B, S) == S, (A, B, S))

# 4. Independent substitution (character-disjoint version)
for S in allstrings(SIG, 5):
    for A in allstrings("a", 3):
        for B in allstrings("b", 2):
            for C in allstrings("b", 3):
                if A and C:  # C != eps, A,B,C pairwise disjoint chars
                    chk("independent",
                        occurs(A, R(B, C, S)) == occurs(A, S), (A, B, C, S))

# 5. Double substitution: X,Y nonempty, X subset Y, Y unbordered
for Z in allstrings(SIG, 6):
    for X in allstrings(SIG, 2):
        for Y in allstrings(SIG, 3):
            if X and Y and X in Y and unbordered(Y):
                chk("double-subst", R(X, Y, R(Y, X, Z)) == Z, (X, Y, Z))

# 5b. Necessity of unborderedness: X=ba, Y=aba (from the paper's remark)
X, Y = "ba", "aba"
found = False
for Z in allstrings("ab", 6):
    if R(X, Y, R(Y, X, Z)) != Z:
        found = True
        break
chk("double-subst-bordered-ctrex", found)

# 5c. Necessity of X subset Y: X=a, Y=bb, Z=aba (from the paper's remark)
X, Y, Z = "a", "bb", "aba"
chk("double-subst-nosubset-ctrex", R(X, Y, R(Y, X, Z)) != Z)

# 5d. EXACT characterization test (once-r only):
# [X/Y]_R [Y/X]_R Z = Z for all Z iff: for every decomposition Z = P X Q with
# X rightmost, no occurrence of Y in P Y Q starts after position |P|.
# Simpler equivalent to test exhaustively: just check whether the identity holds
# for all Z up to length 6, and compare with the structural criterion:
#   holds-for-all-Z  <=>  (X in Y or Y-empty...) -- we test the conjecture:
#   holds-for-all-Z  <=>  X in Y AND Y unbordered
def roundtrip_ok_for_all(X, Y, maxlen=6):
    for Z in allstrings(SIG, maxlen):
        if R(X, Y, R(Y, X, Z)) != Z:
            return False, Z
    return True, None

mismatches = 0
for X in allstrings(SIG, 3):
    for Y in allstrings(SIG, 3):
        if not X or not Y: continue
        ok, wit = roundtrip_ok_for_all(X, Y, 6)
        pred = (X in Y) and unbordered(Y)
        if ok != pred:
            mismatches += 1
            print(f"CHARACTERIZATION MISMATCH: X={X} Y={Y} ok={ok} pred={pred} wit={wit}")
chk("exact-characterization", mismatches == 0)

# 6. k-fold iteration: B not substring of A => applying [A/B]_R k times
#    replaces the k rightmost occurrences
def k_rightmost(A, B, C, k):
    for _ in range(k):
        C = R(A, B, C)
    return C

def replace_k_rightmost(A, B, C, k):
    # reference: replace the k rightmost occurrences of B in C by A
    pos = []
    i = C.rfind(B)
    while i >= 0 and len(pos) < k:
        pos.append(i)
        i = C.rfind(B, 0, i + len(B) - 1) if i + len(B) - 1 > 0 else -1
        # move left, but occurrences must not overlap the ones taken
        # simple approach: search left of i (occurrences may overlap; the
        # "next rightmost" is the next occurrence strictly left of i)
        if i >= 0 and C.find(B, i + 1) >= 0:
            pass
        if i >= 0 and C.startswith(B, i):
            continue
    # fallback reference implementation:
    pos = []
    start = len(C)
    while len(pos) < k:
        j = C.rfind(B, 0, start + len(B) - 1) if pos else C.rfind(B)
        # simpler: find rightmost occurrence that ends at or before `start`
        j = -1
        for i in range(len(C) - len(B), -1, -1):
            if i + len(B) <= start or not pos:
                if C.startswith(B, i):
                    j = i; break
        if j < 0: break
        pos.append(j)
        start = j
    pos.reverse()
    out = []
    prev = 0
    for j in pos:
        out.append(C[prev:j]); out.append(A); prev = j + len(B)
    out.append(C[prev:])
    return "".join(out)

for C in allstrings(SIG, 6):
    for A in allstrings(SIG, 2):
        for B in allstrings(SIG, 2):
            if B and B not in A:
                for k in range(4):
                    if k_rightmost(A, B, C, k) != replace_k_rightmost(A, B, C, k):
                        chk("k-rightmost", False, (A, B, C, k))
                        break
print("algebra checks:", "ALL PASS" if fails == 0 else f"{fails} FAILURES")

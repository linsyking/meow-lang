"""Sanity tests of the four semantics against hand-computed examples."""
from core import subst_L, subst_R2L, subst_once_l, subst_once_r

fails = 0
def chk(name, got, want):
    global fails
    if got != want:
        print(f"FAIL {name}: got {got!r} want {want!r}")
        fails += 1

# Paper's own examples
chk("L ab/b on b", subst_L("ab", "b", "b"), "ab")
chk("L b/aa on aaa", subst_L("b", "aa", "aaa"), "ba")
# once family on overlapping pattern
chk("once-l b/aa on aaa", subst_once_l("b", "aa", "aaa"), "ba")
chk("once-r b/aa on aaa", subst_once_r("b", "aa", "aaa"), "ab")
chk("R2L b/aa on aaa", subst_R2L("b", "aa", "aaa"), "ab")
# four occurrences, no overlap
chk("L b/aa on aaaa", subst_L("b", "aa", "aaaa"), "bb")
chk("once-l b/aa on aaaa", subst_once_l("b", "aa", "aaaa"), "baa")
chk("once-r b/aa on aaaa", subst_once_r("b", "aa", "aaaa"), "aab")
chk("R2L b/aa on aaaa", subst_R2L("b", "aa", "aaaa"), "bb")
# inert
for f in (subst_L, subst_R2L, subst_once_l, subst_once_r):
    chk("inert", f("x", "q", "abc"), "abc")
# replacement containing pattern (no rescan)
chk("L aa/a on aaa", subst_L("aa", "a", "aaa"), "aaaaaa")
chk("R2L aa/a on aaa", subst_R2L("aa", "a", "aaa"), "aaaaaa")
chk("once-l aa/a on aaa", subst_once_l("aa", "a", "aaa"), "aaaa")
chk("once-r aa/a on aaa", subst_once_r("aa", "a", "aaa"), "aaaa")
# paper Remark: double substitution counterexample X=ba Y=aba Z=baabba
chk("L aba/ba on baabba", subst_L("aba", "ba", "baabba"), "abaababa")
chk("L ba/aba on abaababa", subst_L("ba", "aba", "abaababa"), "bababa")
# once-r mirror of the same
chk("once-r aba/ba on baabba", subst_once_r("aba", "ba", "baabba"), "baababa")

# Cross-check L and R2L against a brute-force reference on random strings.
import itertools, random
random.seed(0)
SIG = "ab"
def brute_L(A, B, C):
    # recursive definition following the paper literally
    if B not in C: return C
    best = None
    for i in range(len(C) - len(B) + 1):
        if C.startswith(B, i):
            best = i; break
    # greedy leftmost, then rescan after inserted text = equivalent to scanning
    # left to right skipping inserted text; do it iteratively
    out = C[:best] + A
    return out + C[best + len(B):]  # NOT the full semantics; see below

# Full reference implementations of L and R2L by direct simulation:
def ref_L(A, B, C):
    assert B
    res = []
    i = 0
    while i < len(C):
        if C.startswith(B, i):
            res.append(A); i += len(B)
        else:
            res.append(C[i]); i += 1
    return "".join(res)
def ref_R2L(A, B, C):
    assert B
    res = []
    i = len(C)
    while i > 0:
        if i - len(B) >= 0 and C.startswith(B, i - len(B)):
            res.append(A); i -= len(B)
        else:
            i -= 1; res.append(C[i])
    return "".join(reversed(res))

for _ in range(3000):
    A = "".join(random.choice(SIG) for _ in range(random.randint(0, 3)))
    B = "".join(random.choice(SIG) for _ in range(random.randint(1, 3)))
    C = "".join(random.choice(SIG) for _ in range(random.randint(0, 6)))
    if subst_L(A, B, C) != ref_L(A, B, C):
        chk("refL", (A, B, C, subst_L(A, B, C), ref_L(A, B, C)), None)
    if subst_R2L(A, B, C) != ref_R2L(A, B, C):
        chk("refR2L", (A, B, C), None)
    # R2L is the mirror of L
    if subst_R2L(A, B, C) != subst_L(A[::-1], B[::-1], C[::-1])[::-1]:
        # note: mirror of L with reversed pattern/replacement
        chk("mirror", (A, B, C), None)

print("semantics tests:", "ALL PASS" if fails == 0 else f"{fails} FAILURES")

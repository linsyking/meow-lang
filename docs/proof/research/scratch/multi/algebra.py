"""Basic algebra under V (multi primitive): which Section-2 statements hold,
fail, or need modified hypotheses.  All claims verified by brute force here.
"""
import sys, itertools
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import subst, rep_ref, enc, dec, all_strings

def occurs(A, B):  # A occurs in B
    return A in B

# ---------------------------------------------------------------------------
# 1. ERRATUM to the paper's Lemma (Independent Substitution):
#    it is stated with "A cap B = empty, A cap C = empty, C != eps" and FAILS
#    for B = eps (deletion).  [B/C] with B = eps is legal (it is the A-slot).
# ---------------------------------------------------------------------------
A, B, C, S = "bc", "", "Z", "abZcd"
lhs = occurs(A, subst(B, C, S))   # A subset [B/C]S
rhs = occurs(A, S)
print("1. paper's Independent Substitution with B=eps:",
      f"A={A!r} B={B!r} C={C!r} S={S!r}: "
      f"[B/C]S={subst(B,C,S)!r}, A in output: {lhs}, A in S: {rhs} ->",
      "LEMMA FAILS (lhs True, rhs False)" if lhs and not rhs else "ok")

# ---------------------------------------------------------------------------
# 2. Multi version of Independent Substitution.
#    Claim: if A shares no character with any X_i and any Y_i, and all
#    Y_i != eps, then A subset rep(S;pairs) <=> A subset S.
#    The Y_i != eps hypothesis is necessary (same counterexample shape).
# ---------------------------------------------------------------------------
def chars(s): return set(s)

def multi_indep_holds(pairs, S, A):
    lhs = occurs(A, rep_ref(pairs, S))
    rhs = occurs(A, S)
    return lhs == rhs

bad = []
for alph in ["ab", "abc"]:
    for S in all_strings(alph, 5):
        for A in ["ab", "ba", "bc", "cb", "ac", "aa", "bb", "cc"]:
            if not set(A) <= set(alph):
                continue
            for Xs in itertools.product(["a", "b", "ab", "ba"], repeat=2):
                for Ys in itertools.product(["", "x", "xy"], repeat=2):
                    pairs = list(zip(Xs, Ys))
                    if set(A) & (chars(Xs[0]) | chars(Xs[1])):
                        continue
                    if any(Y == "" for Y in Ys):
                        continue  # hypothesis: all Yi nonempty
                    if not multi_indep_holds(pairs, S, A):
                        bad.append((pairs, S, A))
print(f"2a. multi Independent Substitution (all Yi != eps, A disjoint from all"
      f" Xi,Yi): tested over exhaustive small domain, "
      f"{'FAILURES: ' + str(bad[:3]) if bad else 'HOLDS everywhere [OK]'}")

# necessity of Yi != eps:
pairs = [("Z", "")]
S = "abZcd"
print(f"2b. with Y_1 = eps: pairs={pairs}, S={S!r}: rep={rep_ref(pairs, S)!r}: "
      f"'bc' in rep: {'bc' in rep_ref(pairs, S)}, 'bc' in S: {'bc' in S} -> "
      f"{'FAILS as predicted' if 'bc' in rep_ref(pairs,S) and 'bc' not in S else 'ok'}")

# ---------------------------------------------------------------------------
# 3. Round order matters (minimal example).
# ---------------------------------------------------------------------------
pairs12 = [("ab", "1"), ("b", "2")]
pairs21 = [("b", "2"), ("ab", "1")]
S = "ab"
print(f"3. round order: rep(S; ab->1; b->2) = {rep_ref(pairs12, S)!r} vs "
      f"rep(S; b->2; ab->1) = {rep_ref(pairs21, S)!r} on S={S!r}")

# exhaustive minimal search for round-order disagreement:
def minimal_roundorder():
    for SL in range(0, 5):
        for S in all_strings("ab", SL):
            for X1 in ["a", "b", "ab", "ba"]:
                for X2 in ["a", "b", "ab", "ba"]:
                    if X1 == X2: continue
                    for Y1 in ["1", "2"]:
                        for Y2 in ["1", "2"]:
                            p1 = [(X1, Y1), (X2, Y2)]
                            p2 = [(X2, Y2), (X1, Y1)]
                            if rep_ref(p1, S) != rep_ref(p2, S):
                                return (p1, p2, S)
print("   minimal witness:", minimal_roundorder())

# ---------------------------------------------------------------------------
# 4. Simultaneous vs sequential composition (the swap).
# ---------------------------------------------------------------------------
pairs = [("a", "b"), ("b", "a")]
S = "ab"
seq1 = subst("a", "b", subst("b", "a", S))  # b->a first, then a->b
seq2 = subst("b", "a", subst("a", "b", S))  # a->b first, then b->a
print(f"4. swap: rep(S; a->b; b->a) = {rep_ref(pairs, S)!r}; "
      f"sequential orders give {seq1!r} and {seq2!r} on S={S!r}")

# ---------------------------------------------------------------------------
# 5. cat is reachable in the CORE multi calculus:
#    cat(X,Y) = rep_2(ab; a->X; b->Y).
# ---------------------------------------------------------------------------
from core import rep_ref as rr
okcat = True
for X in all_strings("ab", 3):
    for Y in all_strings("ab", 3):
        if rr([("a", X), ("b", Y)], "ab") != X + Y:
            okcat = False
print(f"5. cat(X,Y) = rep_2(ab; a->X; b->Y) on all X,Y over {{a,b}} len<=3: "
      f"{'OK [PROVEN trivially by Definition]' if okcat else 'FAIL'}")

# ---------------------------------------------------------------------------
# 6. tail as a SINGLE multi node (the paper needs N ordered deletion passes).
#    tail_multi(X) = dec( rep( s1 s1 enc(X);
#         s1 s1 s2 s1 -> eps, s1 s1 s2 -> eps, s1 s1 si -> eps (i=3..N),
#         s1 s1 -> eps ) )
# ---------------------------------------------------------------------------
def tail_paper(alphabet, X):
    # the paper's sequential version (for comparison)
    s = list(alphabet)
    s1, s2 = s[0], s[1]
    T = s1 + s1 + enc(s1, s2, X)
    T = subst("", s1 + s1 + s2 + s1, T)
    T = subst("", s1 + s1 + s2, T)
    for i in range(2, len(s)):
        T = subst("", s1 + s1 + s[i], T)
    T = subst("", s1 + s1, T)
    return dec(s1, s2, T)

def tail_multi(alphabet, X):
    s = list(alphabet)
    s1, s2 = s[0], s[1]
    pats = [s1+s1+s2+s1, s1+s1+s2] + [s1+s1+c for c in s[2:]] + [s1+s1]
    return dec(s1, s2, rep_ref([(p, "") for p in pats], s1 + s1 + enc(s1, s2, X)))

badt = 0
for alph in ["ab", "abc", "abcd"]:
    for X in all_strings(alph, 4):
        want = X[1:] if X else ""
        for name, f in [("paper", tail_paper), ("multi", tail_multi)]:
            if f(alph, X) != want:
                badt += 1
                print(f"   tail({name}) FAIL on {alph} {X!r}")
print(f"6. tail via one multi node vs paper's ordered passes: "
      f"{'both OK on all strings len<=4 over ab/abc/abcd' if badt == 0 else str(badt)+' failures'}")

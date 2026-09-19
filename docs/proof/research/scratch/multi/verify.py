"""Verification suite for the multi variant.

Stage 0: sanity of subst against the Lean #eval examples.
Stage 1: the paper's shadowing counterexample (Remark rem:rep-hyp).
Stage 2: enc2/dec2 round trip (comma code).
Stage 3: the money test -- comma-code construction vs freezing semantics on
         the paper's shadowing instance.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import (subst, rep_ref, rep_onepass, enc, dec, repC_paper,
                  enc2, dec2, repC_comma, all_strings)

ok = True
def check(cond, msg):
    global ok
    if not cond:
        ok = False
        print("FAIL:", msg)
    else:
        print("ok:  ", msg)

# ---- Stage 0: subst sanity (Lean examples) --------------------------------
check(subst("ab", "b", "b") == "ab", "[ab/b]b = ab")
check(subst("ab", "b", "ab") == "aab", "[ab/b]ab = aab")
# NOTE: the Lean file's comment on this #eval says "[a]  ([a/a]aa = a)" but
# Definition 1 (and the paper's Identity Substitution theorem, and the Lean
# code itself) gives "aa".  The Lean comment is stale; the semantics is "aa".
check(subst("a", "a", "aa") == "aa", "[a/a]aa = aa (Lean comment '[a]' is stale)")
check(subst("xy", "x", "yx") == "yxy", "no restart in inserted text")
check(subst("a", "a", "aba" * 1) == "a" if False else subst("a", "aba", "aba") == "a",
      "Lean: subst [a] [a,b,a] [a,b,a] = [a]")
check(subst("", "a", "baa") == "b", "deletion A = epsilon")

# Double substitution lemma counterexample from the paper's Remark:
check(subst("aba", "ba", "baabba") == "abaababa", "border failure: [aba/ba]baabba")
check(subst("ba", "aba", subst("aba", "ba", "baabba")) == "bababa",
      "border failure roundtrip != Z")

# ---- enc/dec sanity --------------------------------------------------------
check(enc("b", "x", "aba c".replace(" ", "")) == "a x b a c".replace(" ", ""),
      "enc example")
check(dec("b", "x", enc("b", "x", "abacb")) == "abacb", "enc/dec roundtrip")

# ---- Stage 1: the paper's shadowing counterexample -------------------------
# b = sigma1, x = sigma2, S = s1 s2 s1 s1 s2, X1 = s1 s2 -> Y1 = s2 s2 s2 s1,
# X2 = s2 s2 s2 -> Y2 = s1 s1.
b, x = "a", "b"          # sigma1 = a, sigma2 = b  (so b_constr='a', x_constr='b')
pairs = [("ab", "bbba"), ("bbb", "aa")]
S = "abaab"
want_ref = "bbba" + "a"[0:0] + ""  # placeholder; compute below
got_ref = rep_ref(pairs, S)
got_paper = repC_paper(b, x, pairs, S)
check(got_ref == "bbbaabbba",
      f"rep_ref on shadowing instance = {got_ref} (expected s2s2s2s1 s1 s2s2s2s1 = 'bbbaabbba')")
check(got_paper == "bbbaaab",
      f"paper construction = {got_paper} (paper says s2s2s2s1 s1 s1 s2 = 'bbbaaab')")
check(got_paper != got_ref, "the paper's construction fails on its counterexample (as documented)")

# ---- Stage 2: enc2/dec2 round trip ------------------------------------------
for alph in ["ab", "abc", "abcd"]:
    bad = 0
    for s in all_strings(alph, 8):
        if dec2("a", "b", enc2("a", "b", s, alph), alph) != s:
            bad += 1
    check(bad == 0, f"enc2/dec2 round trip on all strings over {alph} up to len 8")

# Structural invariant (F1): enc2 images contain no run of the construction's
# b character longer than 1 (here b_constr='a', so no "aa"), and markers
# m_i = x*b^{i+1} = "b"+"a"*{i+1} therefore never occur inside images.
for alph in ["ab", "abc"]:
    bad = 0
    for s in all_strings(alph, 8):
        img = enc2("a", "b", s, alph)
        if "aa" in img:
            bad += 1
        if any((("b" + "a" * (i + 1)) in img) for i in range(1, 5)):
            bad += 1
    check(bad == 0, f"enc2 images avoid b^2 and all markers (F1) over {alph} up to len 8")

# ---- Stage 3: money test ----------------------------------------------------
got_comma = repC_comma(b, x, pairs, S, "ab")
check(got_comma == got_ref,
      f"comma construction on shadowing instance: {got_comma} == rep_ref {got_ref}")

print("\nALL OK" if ok else "\nSOME FAILURES")

"""Exp 9: wrap-up checks.
 (a) among total rules |A|,|B|<=3: is every non-amplifier rule's max output <= L + const?
 (b) tail/head: paper's construction inlined diverges (enc inside diverges).
 (c) baseline doubling [aa/a] is injective (L-witness for the separation).
 (d) bdec-style border deletion works under restart for [e/xb^2]^m (deletion nodes are total).
 (e) benc injectivity under restart-with-blackbox-enc (supporting eq).
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

print("=== (a) growth audit of total rules (|A|,|B|<=3) ===")
rows = []
for A in all_patterns("ab", 0, 3):
    for B in all_patterns("ab", 1, 3):
        ok = True
        ml = {}
        for L in range(0, 12):
            m = 0
            for s in all_strings("ab", L):
                try:
                    r, st = restart(A, B, s, cap=6000)
                except Diverge:
                    ok = False
                    break
                m = max(m, len(r))
            if not ok:
                break
            ml[L] = m
        if ok:
            rows.append((A, B, ml))
bad = [(A, B, ml) for (A, B, ml) in rows if ml[11] > 11 + 6]
print("   total rules:", len(rows))
print("   rules with max-out(11) > 11+6:", [(A, B, [ml[L] for L in range(8, 12) if L in ml]) for (A, B, ml) in bad])

print("=== (b) paper's tail with enc inlined: enc^m diverges on b-containing input ===")
# tail(X) = dec([e/ss][e/ssx][e/ssxs]... (ss enc(X))) with s=sigma1=b, x=sigma2
# the innermost piece is enc(X) = [xb/b] X -- under restart this diverges when X contains b
for Xs in ["b", "ab", "aab"]:
    try:
        restart("xb", "b", Xs, cap=500)
        print("   enc^m(%r) terminated (unexpected)" % Xs)
    except Diverge:
        print("   enc^m(%r) DIVERGES  -> paper's tail/head/eq/if cannot be inlined" % Xs)

print("=== (c) baseline doubling [aa/a] is injective on len<=8 ===")
seen = {}
inj = True
for s in all_strings("ab", 8):
    t = subst("aa", "a", s)
    if t in seen:
        inj = False
        print("   collision", repr(seen[t]), repr(s), "->", repr(t))
    seen[t] = s
print("   injective:", inj, "(and it grows: |t| = |s| + #a)")

print("=== (d) deletion nodes are always total?  [e/B]^m for |B|<=4 ===")
ok = True
for B in all_patterns("ab", 1, 4):
    for s in all_strings("ab", 10):
        try:
            restart("", B, s, cap=4000)
        except Diverge:
            ok = False
            print("   deletion diverges:", repr(B), repr(s))
print("   all deletion nodes total on tested domain:", ok)

print("=== (e) border decoding [e/xb^2]^m on benc images (black-box enc) ===")
def encb(s):
    return subst("xb", "b", s)
def bencb(s):
    return "xbb" + encb(s) + "xbb"
okk = True
for s in all_strings("abx", 5):
    bs = bencb(s)
    r, _ = restart("", "xbb", bs, cap=1000)
    if r != encb(s):
        okk = False
        print("   border decode fails", repr(s))
print("   [e/xb^2]^m strips both borders of benc(X):", "CONFIRMED" if okk else "REFUTED")

"""Exp 11: head/tail under restart with enc/dec as black-box oracles.

tail(X) = dec( [e/bb][e/bbx][e/bbxb] (prod_{i=3..N} [e/b b s_i]) (bb enc(X)) )
head(X) = dec( [e/enc(tail(X)) bb] (enc(X) bb) )
All passes are DELETIONS (total); each pattern contains bb, images contain none,
so every pass deletes exactly one occurrence and never rescans effectively.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

# alphabet: s1='a' (b), s2='b' (x), others 'c','d'; N=4
B, X = 'a', 'b'
OTHER = "cd"


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def tail(Xs):
    T = B + B + enc(Xs)
    for c in OTHER:                      # [e/bb s_i], i = 3..N
        T, _ = restart("", B + B + c, T, cap=5000)
    T, _ = restart("", B + B + X + B, T, cap=5000)     # [e/bbxb]
    T, _ = restart("", B + B + X, T, cap=5000)          # [e/bbx]
    T, _ = restart("", B + B, T, cap=5000)              # [e/bb]
    return dec(T)


def head(Xs):
    t = tail(Xs)
    T = enc(Xs) + B + B
    T, _ = restart("", enc(t) + B + B, T, cap=5000)
    return dec(T)


bad_t = bad_h = 0
n = 0
for Xs in all_strings("abcd", 5):
    n += 1
    want = Xs[1:] if Xs else ""
    if tail(Xs) != want:
        bad_t += 1
        if bad_t <= 5:
            print("   tail fail:", repr(Xs), repr(tail(Xs)), "want", repr(want))
    wanth = Xs[0] if Xs else ""
    if head(Xs) != wanth:
        bad_h += 1
        if bad_h <= 5:
            print("   head fail:", repr(Xs), repr(head(Xs)), "want", repr(wanth))
print("tail under restart (enc/dec oracle): %d instances, %d wrong" % (n, bad_t))
print("head under restart (enc/dec oracle): %d instances, %d wrong" % (n, bad_h))

# steps used per pass: confirm single-deletion claim
S = B + B + enc("abc" + B + X + "d")
steps = []
T = S
for c in OTHER + "":
    pass
T = S
total_steps = 0
for pat in [B + B + 'c', B + B + 'd', B + B + X + B, B + B + X, B + B]:
    T, st = restart("", pat, T, cap=5000)
    total_steps += st
print("tail passes on X='abc%sd': total deletion steps = %d (expect 1: only the head marker)" % (X, total_steps))

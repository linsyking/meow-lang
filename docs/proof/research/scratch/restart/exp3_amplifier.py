"""Exp 3 (v3): amplifier [baa/ab]^m -- formula check and growth. Bounded for speed.

THEORY: rule ab -> baa preserves v(s) (a=+1, b=x2, left-to-right from 0)
  == sum over a's of 2^(#b's to their right), and preserves #b.
  Each step increases #a by exactly 1, and #a(s) <= v(s). Hence termination and
      [baa/ab]^m (S) = b^(#b(S)) a^(v(S)).
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *


def v(S, base=2):
    val = 0
    for c in S:
        if c == 'a':
            val += 1
        else:
            val *= base
    return val


def nb(S):
    return S.count('b')


print("=== amplifier formula, ALL binary strings len<=10 ===", flush=True)
bad = 0
for S in all_strings("ab", 10):
    r, st = restart("baa", "ab", S, cap=10 ** 7)
    expect = "b" * nb(S) + "a" * v(S)
    if r != expect:
        bad += 1
        print("MISMATCH", repr(S), repr(r), repr(expect))
print("mismatches:", bad, flush=True)

print("=== base-k variants [b a^k / ab]^m, k=3..6, all strings len<=7 ===", flush=True)
for k in range(3, 7):
    A = "b" + "a" * k
    bad = 0
    for S in all_strings("ab", 7):
        r, st = restart(A, "ab", S, cap=10 ** 7)
        expect = "b" * nb(S) + "a" * v(S, k)
        if r != expect:
            bad += 1
            print("  MISMATCH k=%d %r -> %r want %r" % (k, S, r, expect))
    print("  k=%d: mismatches=%d" % (k, bad), flush=True)

print("=== growth on 'a b^(n-1)': out-len should be 2^(n-1)+n-1 ===", flush=True)
for n in range(1, 13):
    S = "a" + "b" * (n - 1)
    r, st = restart("baa", "ab", S, cap=10 ** 7)
    print("  n=%2d in-len=%2d steps=%5d out-len=%5d  predicted=%d" %
          (n, len(S), st, len(r), 2 ** (n - 1) + (n - 1)), flush=True)

print("=== TOWER pipeline node1=[baa/ab], node2=[ab/aa], node3=[baa/ab] ===", flush=True)
for n in range(1, 7):
    S = "a" + "b" * (n - 1)
    t1, s1 = restart("baa", "ab", S, cap=10 ** 7)
    t2, s2 = restart("ab", "aa", t1, cap=10 ** 7)
    t3, s3 = restart("baa", "ab", t2, cap=10 ** 7)
    print("  n=%d |S|=%d -> |t1|=%d -> |t2|=%d -> |t3|=%d" %
          (n, len(S), len(t1), len(t2), len(t3)), flush=True)

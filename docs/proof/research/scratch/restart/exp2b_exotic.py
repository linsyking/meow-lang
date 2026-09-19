"""Exp 2b: the exotic divergent rules with B not substring of A.
 - find minimal diverging input and trace the trajectory
 - extend search to |A|<=6, |B|<=3 (and |B|=4,|A|<=5) to find the family
 - check whether the growth accelerates (steps per added char)
 - check strategy sensitivity: for leftmost-total growing rules, does the
   rightmost strategy diverge somewhere? (system non-termination vs leftmost)
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

SIG2 = "ab"

EXOTIC = [("aabb", "ba"), ("abba", "bab"), ("baab", "aba"), ("bbaa", "ab")]


def trace(A, B, C, n=25, maxlen=400):
    s = C
    print("  trace [%s/%s] %r:" % (A, B, C))
    for k in range(n):
        i = s.find(B)
        if i < 0:
            print("    halt after %d steps: %r" % (k, s))
            return
        if len(s) > maxlen:
            print("    ... (len %d, %d steps, still growing)" % (len(s), k))
            return
        print("    %-3d len=%-3d %r" % (k, len(s), s))
        s = s[:i] + A + s[i + len(B):]


for (A, B) in EXOTIC:
    # minimal diverging input (by length, then lex) among all strings up to len 9
    best = None
    for C in all_strings(SIG2, 9):
        try:
            restart(A, B, C, cap=2500)
        except Diverge:
            if best is None or (len(C), C) < (len(best), best):
                best = C
    print("[%s/%s]^m minimal diverging input: %r" % (A, B, best))
    trace(A, B, best, n=18, maxlen=120)
    print()

# extended search for the family
print("=== extended family search |A|<=6, |B|<=3 ===")
strs = list(all_strings(SIG2, 9))
exotic = []
for A in all_patterns(SIG2, 0, 6):
    for B in all_patterns(SIG2, 1, 3):
        if B in A:
            continue
        if len(A) < len(B):
            continue
        ok = True
        for C in strs:
            try:
                restart(A, B, C, cap=2500)
            except Diverge:
                ok = False
                break
        if not ok:
            exotic.append((A, B))
print("divergent, B not in A, |A|<=6,|B|<=3 :", len(exotic))
for (A, B) in exotic:
    print("   ", repr(A), repr(B))

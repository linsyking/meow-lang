"""Exp 10b: rep_n construction under restart vs baseline (which is proven correct in
the Lean development), on hypothesis-(H)-respecting patterns.

(H): |X_i| = 1 or X_i does not end with the escape char x.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

B, X = 'a', 'b'   # b, x of the encoding


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def repC(S, pairs, engine):
    T = enc(S)
    for i, (Xi, Yi) in enumerate(pairs, start=1):
        mi = X + B * (i + 1)
        mnext = X + B * (i + 2)
        t = engine(mi, enc(Xi), T, cap=20000)[0]
        T = engine(enc(Xi) + B, mnext, t, cap=20000)[0]
    for i, (Xi, Yi) in reversed(list(enumerate(pairs, start=1))):
        mi = X + B * (i + 1)
        T = engine(enc(Yi), mi, T, cap=20000)[0]
    return dec(T)


def respects_H(pairs):
    for (Xi, Yi) in pairs:
        if len(Xi) >= 2 and Xi.endswith(X):
            return False
    return True


def baseline(A, Bp, C, cap=None):
    return (subst(A, Bp, C), 0)


print("rep_n: restart-construction vs baseline-construction, (H)-respecting patterns")
n = ok = 0
bad = []
for S in list(all_strings("abcd", 4)):
    for X1 in all_patterns("abcd", 1, 2):
        for X2 in all_patterns("abcd", 1, 2):
            pairs = [(X1, "cd"), (X2, "dcd")]
            if not respects_H(pairs):
                continue
            n += 1
            try:
                a = repC(S, pairs, baseline)
                r = repC(S, pairs, restart)
            except Diverge:
                r = "DIV"
            if r != a:
                ok = ok
                bad.append((S, pairs, a, r))
                if len(bad) > 4:
                    break
    if len(bad) > 4:
        break
print("   tested %d instances; restart==baseline on %d; failures: %d" % (n, n - len(bad), len(bad)))
for b in bad[:5]:
    print("      ", b)

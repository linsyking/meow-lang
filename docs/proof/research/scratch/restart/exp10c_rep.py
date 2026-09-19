"""Exp 10c: rep_n under restart vs baseline, with the strengthened hypothesis.

Failure found in 10b: the renaming pass [m_i / enc(X_i)]^m DIVERGES whenever
enc(X_i) occurs inside the marker m_i = x b^{i+1} (then m_i contains the pattern,
so every replacement re-seeds it).  enc-images inside x b^{i+1} are exactly
enc(w) for w in {x, b, bb, ..., b^i} (single x, or pure runs of the escaped char).
So we strengthen (H) by (H'):  X_i notin {x, b, b^2, ..., b^i}.

Also check the repair pass [enc(X_i) b / m_{i+1}]^m for the analogous condition.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

B, X = 'a', 'b'


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def repC(S, pairs, engine):
    T = enc(S)
    for i, (Xi, Yi) in enumerate(pairs, start=1):
        mi = X + B * (i + 1)
        mnext = X + B * (i + 2)
        t = engine(mi, enc(Xi), T, cap=30000)[0]
        T = engine(enc(Xi) + B, mnext, t, cap=30000)[0]
    for i, (Xi, Yi) in reversed(list(enumerate(pairs, start=1))):
        mi = X + B * (i + 1)
        T = engine(enc(Yi), mi, T, cap=30000)[0]
    return dec(T)


def respects_H(pairs):
    return all(len(Xi) == 1 or not Xi.endswith(X) for (Xi, Yi) in pairs)


def respects_Hp(pairs):
    # (H'): X_i not in {x, b, b^2, ..., b^i}; also repair-pass safety:
    # enc(X_i) b must not occur inside m_{i+1} = x b^{i+2}
    for i, (Xi, Yi) in enumerate(pairs, start=1):
        for k in range(0, i + 1):
            if Xi == X or Xi == B * k:
                return False
        # repair pass pattern enc(Xi)+B inside m_{i+2}:
        if (enc(Xi) + B) in (X + B * (i + 2)):
            return False
    return True


def baseline(A, Bp, C, cap=None):
    return (subst(A, Bp, C), 0)


print("=== rep_2: (H) only ===")
n = badn = 0
bad = []
for S in list(all_strings("abcd", 3)):
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
                badn += 1
                bad.append((S, X1, X2, a, r))
print("   tested %d, failures %d" % (n, badn))
for b in bad[:3]:
    print("      ", b)

print("=== rep_2: (H) + (H') ===")
n = badn = 0
bad = []
for S in list(all_strings("abcd", 4)):
    for X1 in all_patterns("abcd", 1, 2):
        for X2 in all_patterns("abcd", 1, 3):
            pairs = [(X1, "cd"), (X2, "dcd")]
            if not (respects_H(pairs) and respects_Hp(pairs)):
                continue
            n += 1
            try:
                a = repC(S, pairs, baseline)
                r = repC(S, pairs, restart)
            except Diverge:
                r = "DIV"
            if r != a:
                badn += 1
                bad.append((S, X1, X2, a, r))
print("   tested %d, failures %d" % (n, badn))
for b in bad[:5]:
    print("      ", b)

print("=== rep_1 and rep_3 with (H)+(H') ===")
for npairs in [1, 3]:
    n = badn = 0
    for S in list(all_strings("abcd", 3)):
        for X1 in all_patterns("abcd", 1, 2):
            for X2 in all_patterns("abcd", 1, 2):
                for X3 in (all_patterns("abcd", 1, 2) if npairs == 3 else ["c"]):
                    pairs = [(X1, "cd"), (X2, "dcd"), (X3, "cdc")]
                    pairs = pairs[:npairs]
                    if not (respects_H(pairs) and respects_Hp(pairs)):
                        continue
                    n += 1
                    try:
                        a = repC(S, pairs, baseline)
                        r = repC(S, pairs, restart)
                    except Diverge:
                        r = "DIV"
                    if r != a:
                        badn += 1
                        if badn < 4:
                            print("      fail:", S, pairs, a, r)
    print("   rep_%d: tested %d, failures %d" % (npairs, n, badn))

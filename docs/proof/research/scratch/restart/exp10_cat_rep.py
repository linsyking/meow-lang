"""Exp 10: paper's cat (and rep_n spot checks) under restart with enc/dec as black boxes.

cat(X,Y) = dec([enc(X)/xb^2][enc(Y)/xb^3](xb^2 xb^3)).
Under restart each node's baseline output is pattern-free (markers contain bb,
images do not), so by the Exact Agreement theorem restart == baseline per node.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

# alphabet: b = 'a', x = 'b'; other chars 'c','d' available
B, X = 'a', 'b'


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def cat_restart(Xs, Ys):
    m2, m3 = X + B + B, X + B + B + B
    t0 = m2 + m3
    t1, _ = restart(enc(Ys), m3, t0, cap=5000)
    t2, _ = restart(enc(Xs), m2, t1, cap=5000)
    return dec(t2)


bad = []
n = 0
for Xs in all_strings("abcd", 3):
    for Ys in all_strings("abcd", 3):
        n += 1
        r = cat_restart(Xs, Ys)
        if r != Xs + Ys:
            bad.append((Xs, Ys, r))
print("cat under restart (enc black box): %d instances, %d wrong" % (n, len(bad)))
for b in bad[:5]:
    print("   ", b)

print()
print("=== rep_2 spot check under restart (freezing semantics vs construction) ===")


def rep_ref(S, pairs):
    """freezing semantics of Definition (rep)"""
    n = len(S)
    frozen = [False] * n
    text = list(S)
    for (pat, rep) in pairs:
        i = 0
        while i <= len(text) - len(pat):
            if all(not frozen[i + k] and text[i + k] == pat[k] for k in range(len(pat))):
                for k in range(len(pat)):
                    frozen[i + k] = True
                # placeholder replace: mark and continue after
                for k in range(len(pat)):
                    text[i + k] = None if False else text[i + k]
                # freeze positions, continue scanning after the match
                i += len(pat)
            else:
                i += 1
    # second pass: build output
    out = []
    i = 0
    marks = [False] * len(S)
    # redo freezing cleanly
    frozen = [False] * n
    for (pat, rep) in pairs:
        i = 0
        while i <= n - len(pat):
            if all(not frozen[i + k] and S[i + k] == pat[k] for k in range(len(pat))):
                for k in range(len(pat)):
                    frozen[i + k] = True
                i += len(pat)
            else:
                i += 1
    # replace each maximal frozen run per round
    out = []
    i = 0
    while i < n:
        if frozen[i]:
            # find which round froze this run: rounds processed in order; a frozen
            # run of length |pat| belongs to the earliest round that matched here
            for (pat, rep) in pairs:
                if i + len(pat) <= n and all(S[i + k] == pat[k] for k in range(len(pat))):
                    out.append(rep)
                    i += len(pat)
                    break
            else:
                out.append(S[i])
                i += 1
        else:
            out.append(S[i])
            i += 1
    return "".join(out)


def repC(S, pairs):
    """the paper's construction, with restart nodes and black-box enc/dec"""
    E_S = enc(S)
    T = E_S
    # renaming + repair passes, i = 1..n
    for i, (Xi, Yi) in enumerate(pairs, start=1):
        mi = X + B * (i + 1)
        mnext = X + B * (i + 2)
        t, _ = restart(mi, enc(Xi), T, cap=5000)
        T, _ = restart(enc(Xi) + B, mnext, t, cap=5000)
    # instantiation passes i = n..1
    for i, (Xi, Yi) in reversed(list(enumerate(pairs, start=1))):
        mi = X + B * (i + 1)
        T, _ = restart(enc(Yi), mi, T, cap=5000)
    return dec(T)


tests = [("", ("a", "ba")), ("aba", ("a", "ba")), ("aabba", ("ab", "c")),
         ("abcabc", ("bc", "x")), ("aaa", ("aa", "b"))]
ok = True
for (S, pair) in tests:
    pairs = [pair]
    a = rep_ref(S, pairs)
    b = repC(S, pairs)
    print("   S=%r pairs=%r  freezing=%r  construction(restart)=%r %s" %
          (S, pair, a, b, "OK" if a == b else "DIFFER"))
    if a != b:
        ok = False
print("   (informal check; freezing reference implemented naively)")

"""Exp 6: toolkit under restart.

 - eq:  the paper's construction [bot/benc(X)][top/benc(Y)] benc(X) is CORRECT
        under restart provided benc is available (borders make patterns longer
        than the replacement, so no re-trigger).  Verify with baseline enc as a
        black box (enc = [xb/b] baseline).
 - if:  the paper's construction DIVERGES when X contains top; a
        deletion-based redesign works under restart (given enc/dec).
 - sort/collapse/spread identities; commutation of collapse nodes.
 - spread round trip:  [b/xb]^m o [bxb/bb]^m = id on xb-free strings.
 - collapse vs iterated baseline halving (bounded pipelines can't collapse).
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *
import itertools

SIG = "abcd"          # b='a', x='b', top='c', bot='d'
B, X, TOP, BOT = 'a', 'b', 'c', 'd'


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def benc(s):
    return X + B + B + enc(s) + X + B + B


print("=== sanity: baseline enc/dec round trip ===", flush=True)
assert all(dec(enc(s)) == s for s in all_strings("abcd", 6))
print("   ok", flush=True)

print("=== eq under restart (paper construction, enc as black box) ===", flush=True)
bad = []
for Xs in all_strings("abcd", 4):
    for Ys in all_strings("abcd", 4):
        bx, by = benc(Xs), benc(Ys)
        try:
            t, _ = restart(TOP, by, bx, cap=3000)
            r, _ = restart(BOT, bx, t, cap=3000)
        except Diverge:
            r = "DIV"
        want = TOP if Xs == Ys else BOT
        if r != want:
            bad.append((Xs, Ys, r))
print("   mismatches: %d of %d" % (len(bad), 25 * 25), flush=True)
for b in bad[:5]:
    print("      ", b)

print("=== if under restart: paper's construction ===", flush=True)
print("   if(C,X,Y) = dec([enc(Y)/bb][enc(X)/top][bb/bot]C), rightmost first", flush=True)
div = 0
bad = []
n = 0
for C in [TOP, BOT]:
    for Xs in all_strings("abcd", 3):
        for Ys in all_strings("abcd", 2):
            n += 1
            try:
                t1, _ = restart(B + B, BOT, C, cap=200)
                t2, _ = restart(enc(Xs), TOP, t1, cap=200)
                t3, _ = restart(enc(Ys), B + B, t2, cap=200)
                r = dec(t3)
            except Diverge:
                r = "DIV"
                div += 1
            want = Xs if C == TOP else Ys
            if r != want:
                bad.append((C, Xs, Ys, r))
print("   of %d instances: %d diverged, %d wrong (want X if C=top else Y)" % (n, div, len(bad)))
for b in bad[:5]:
    print("      ", b)

print("=== if under restart: deletion-based redesign ===", flush=True)
print("   S = enc(X) m C enc(Y) m ;  nodes: [e/enc(X) m bot] , [e/m top enc(Y) m] , [e/m], dec", flush=True)
M = X + B + B  # marker xbb (never inside enc images)


def ifrestart(C, Xs, Ys):
    S = enc(Xs) + M + C + enc(Ys) + M
    t1, _ = restart("", enc(Xs) + M + BOT, S, cap=3000)     # delete X-part if C=bot
    t2, _ = restart("", M + TOP + enc(Ys) + M, t1, cap=3000)  # delete Y-part if C=top
    t3, _ = restart("", M, t2, cap=3000)                     # delete leftover marker
    return dec(t3)


bad = []
n = 0
for C in [TOP, BOT]:
    for Xs in all_strings("abcd", 3):
        for Ys in all_strings("abcd", 3):
            n += 1
            r = ifrestart(C, Xs, Ys)
            want = Xs if C == TOP else Ys
            if r != want:
                bad.append((C, Xs, Ys, r, want))
print("   of %d instances: %d wrong" % (n, len(bad)))
for b in bad[:5]:
    print("      ", b)

print("=== sort / collapse / spread identities ===", flush=True)
ok1 = all(restart("ba", "ab", s, cap=5000)[0] == "b" * s.count('b') + "a" * s.count('a')
          for s in all_strings("ab", 9))
print("   [ba/ab]^m = sort (b* a*)            :", "CONFIRMED" if ok1 else "REFUTED")
ok2 = all(restart("ab", "ba", s, cap=5000)[0] == "a" * s.count('a') + "b" * s.count('b')
          for s in all_strings("ab", 9))
print("   [ab/ba]^m = reverse sort (a* b*)     :", "CONFIRMED" if ok2 else "REFUTED")


def collapse_runs(s, ch):
    return restart(ch, ch + ch, s, cap=5000)[0]


import re
ok3 = True
for s in all_strings("ab", 8):
    c = collapse_runs(collapse_runs(s, 'a'), 'b')
    if re.sub(r'(.)\1+', r'\1', s) != c:
        ok3 = False
        print("      collapse mismatch", repr(s), repr(c))
print("   [a/aa]^m then [b/bb]^m = run-collapse:", "CONFIRMED" if ok3 else "REFUTED")

ok4 = all(collapse_runs(collapse_runs(s, 'a'), 'b') == collapse_runs(collapse_runs(s, 'b'), 'a')
          for s in all_strings("ab", 8))
print("   the two collapse nodes commute      :", "CONFIRMED" if ok4 else "REFUTED")

print("=== spread round trip: [b/xb]^m o [bxb/bb]^m = id on xb-free strings ===", flush=True)
ok5 = True
for s in all_strings("ab", 8):
    if "ab" in s:   # pattern is x b = 'b','a' in this alphabet? use explicit chars
        continue
ok5 = True
# explicit: alphabet {a,b}: use spread [bxb/bb] with x='a', b='b': pattern 'bb'->'bab'
for s in all_strings("ab", 8):
    if 'a' + 'b' in s:  # x followed by b: 'ab'
        continue
    t1, _ = restart("bab", "bb", s, cap=3000)   # spread b-runs: bb -> b a b
    t2, _ = restart("b", "ab", t1, cap=3000)    # unspread: ab -> b
    if t2 != s:
        ok5 = False
        print("      round-trip failure", repr(s), repr(t1), repr(t2))
print("   on ab-free inputs:                   :", "CONFIRMED" if ok5 else "REFUTED")

print("=== collapse vs iterated baseline halving ===", flush=True)
for k in [1, 2, 3]:
    worst = 0
    for s in all_strings("ab", 10):
        t = s
        for _ in range(k):
            t = subst("a", "aa", t)
        if t != re.sub(r'(.)\1+', r'\1', s):
            worst = max(worst, len(s))
    print("   k=%d baseline [a/aa] passes collapse all inputs of length <= %d" % (k, worst - 1))
print("   (restart collapses ALL lengths in one node)")

"""Exp 7: growth of total restart nodes; strategy sensitivity; misc verifications.

 (a) For every total rule (|A|,|B|<=3 over {a,b}), measure max output length and
     max steps as a function of input length; classify: bounded, linear,
     polynomial (deg>=2), exponential-looking.
 (b) Strategy sensitivity: for leftmost-total rules, try the rightmost strategy;
     does it diverge somewhere? (then system non-terminating but leftmost total)
 (c) The prompt's example: [ab/b]^m "b" diverges.
 (d) collapse vs k baseline halvings: k passes collapse exactly runs <= 2^k.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *
import re

SIG = "ab"


def restart_rightmost(A, B, C, cap=200000):
    """rightmost strategy: repeatedly replace the RIGHTMOST occurrence."""
    s = C
    steps = 0
    while True:
        i = s.rfind(B)
        if i < 0:
            return s, steps
        s = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap:
            raise Diverge()


print("=== (c) [ab/b]^m 'b' ===")
try:
    restart("ab", "b", "b", cap=3000)
    print("   terminated (unexpected)")
except Diverge:
    print("   DIVERGES as expected (b in 'ab': pattern occurs in replacement).")
print("   trajectory:", end=" ")
s = "b"
for _ in range(8):
    i = s.find("b")
    s = s[:i] + "ab" + s[i + 1:]
    print(repr(s), end=" ")
print("...")

print()
print("=== (d) collapse vs k baseline halvings ===")
for k in [1, 2, 3, 4]:
    minfail = None
    for n in range(1, 40):
        s = "a" * n
        t = s
        for _ in range(k):
            t = subst("a", "aa", t)
        if t != "a":
            minfail = n
            break
    print("   k=%d: smallest a-run not collapsed: %s (= 2^k+1 expected: %d)" %
          (k, minfail, 2 ** k + 1))

print()
print("=== (a) growth of total rules (|A|,|B|<=3) ===")
strs_by_len = {L: list(all_strings(SIG, L)) for L in range(0, 12)}
NODES = [(A, B) for A in all_patterns(SIG, 0, 3) for B in all_patterns(SIG, 1, 3)]
rows = []
for (A, B) in NODES:
    ok = True
    maxlen = {}
    maxsteps = {}
    for L in range(0, 12):
        ml = ms = 0
        for s in strs_by_len[L]:
            try:
                r, st = restart(A, B, s, cap=6000)
            except Diverge:
                ok = False
                break
            ml = max(ml, len(r))
            ms = max(ms, st)
        if not ok:
            break
        maxlen[L] = ml
        maxsteps[L] = ms
    if not ok:
        continue  # non-total beyond some length
    rows.append((A, B, maxlen, maxsteps))


def classify(maxlen):
    """classify growth of max output length vs input length"""
    Ls = sorted(maxlen)
    if Ls[-1] < 5:
        return "tiny"
    a, b = maxlen[Ls[0]], maxlen[Ls[-1]]
    n = Ls[-1]
    if a == b:
        return "const"
    # check linear, quadratic, cubic, exponential by fitting ratios
    def err(deg):
        return sum(abs(maxlen[L] - max(1, (maxlen[1] if 1 in maxlen else 1)) * (max(L, 1) ** deg / max(1, 1))) for L in Ls)
    # simple: compare growth from L to L+1
    d1 = [maxlen[L + 1] - maxlen[L] for L in Ls[:-1]]
    if all(x == d1[0] for x in d1) and d1[0] > 0:
        return "linear"
    # exponential test: doubling of increments
    if maxlen[Ls[-1]] > 4 * maxlen[max(0, Ls[-1] - 4)] and maxlen[Ls[-1]] > 100:
        return "exponential-ish"
    return "poly?"


from collections import Counter
cnt = Counter()
exponential_rules = []
linear_rules = []
for (A, B, maxlen, maxsteps) in rows:
    c = classify(maxlen)
    cnt[c] += 1
    if c == "exponential-ish":
        exponential_rules.append((A, B, maxlen))
    if c == "linear":
        linear_rules.append((A, B, maxlen, maxsteps))
print("   total rules:", len(rows))
print("   growth classes:", dict(cnt))
print("   exponential-looking rules (A,B, maxlen dict):")
for r in exponential_rules:
    print("      ", r)
print("   max steps among linear rules (A, B, maxlen, maxsteps):")
for r in linear_rules[:8]:
    print("      ", r)
best = max(rows, key=lambda r: r[3][max(r[3])])
print("   rule with the largest step count:", repr(best[0]), repr(best[1]), best[3])

print()
print("=== (b) strategy sensitivity: leftmost-total but rightmost diverges? ===")
found = []
for (A, B) in NODES:
    # leftmost total on len<=10?
    lt = True
    for s in all_strings(SIG, 10):
        try:
            restart(A, B, s, cap=4000)
        except Diverge:
            lt = False
            break
    if not lt:
        continue
    for s in all_strings(SIG, 10):
        try:
            restart_rightmost(A, B, s, cap=4000)
        except Diverge:
            found.append((A, B, s))
            break
print("   leftmost-total rules where RIGHTMOST diverges on some input len<=10:", len(found))
for f in found[:10]:
    print("      ", repr(f[0]), repr(f[1]), "input", repr(f[2]))

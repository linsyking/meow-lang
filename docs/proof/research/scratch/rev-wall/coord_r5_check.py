#!/usr/bin/env python3
# Coordinator round-5 (rev-wall) verification battery. < 30 s.
# Fresh encodings: the fired-set counterexample probe, the resumption
# property, E1/E2, the bonus construction, the mod-3 tables, the L_m
# tightness runs.
import sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-32s got %r want %r' % (name, got, want))
    return ok

def fired_junctions(pat, w):
    """greedy leftmost-disjoint windows of pat in w; junction indices"""
    out, i = [], 0
    while True:
        j = w.find(pat, i)
        if j < 0: break
        out.append(w[:j].count('b'))       # junction index of the b inside
        i = j + len(pat)
    return out

def is_suffix(fired, nb):
    s = set(fired)
    if not s: return True
    m = min(s)
    return s == set(range(m, nb))

# ---- 1. my counterexample: TWO-FLANK single-b patterns can gap -------
print('1. two-flank single-b fired sets (the lemma-(i) probe)')
for k, pat, want in [(4, 'a' * 3 + 'b' + 'a' * 9, [1, 3]),
                     (4, 'a' * 1 + 'b' + 'a' * 3, [0, 2, 3]),
                     (5, 'a' * 3 + 'b' + 'a' * 9, [1, 3, 4])]:
    w = dk(k)
    f = fired_junctions(pat, w)
    check('fired(%s) k=%d' % (pat[:8], k), f, want)
    print('   fired=%s is_suffix=%s (contains suffix: %s)'
          % (f, is_suffix(f, k), set(range(min(f), k)) <= set(f) if f else True))
# and the campaign evaluator agrees on the outputs (direct sweep)
# recompute expected output by direct sweep
def sweep(pat, rep, w):
    out, i = [], 0
    while True:
        j = w.find(pat, i)
        if j < 0:
            out.append(w[i:]); break
        out.append(w[i:j]); out.append(rep)
        i = j + len(pat)
    return ''.join(out)
for k, pat in [(4, 'a' * 3 + 'b' + 'a' * 9), (4, 'a' * 1 + 'b' + 'a' * 3)]:
    w = dk(k)
    got = ev(S(K(''), K(pat), X), w)
    check('ev==sweep k=%d' % k, got, sweep(pat, '', w))
print('   (sweep cross-check done)')
# one-flank patterns: suffixes ALWAYS (their A1 class, re-verified)
bad = 0
for k in (2, 3, 4, 5):
    w = dk(k)
    for i in range(0, 41):
        if not is_suffix(fired_junctions('a' * i + 'b', w), k): bad += 1
        if not is_suffix(fired_junctions('b' + 'a' * i, w), k): bad += 1
check('one-flank non-suffix count', bad, 0)
print('   one-flank suffix property: 4 k-values x 41 x 2, 0 non-suffix')
# skip-after-bite structure: every skipped junction in [min(f), k-1]
# immediately follows a firing (the bite zeroed its left run below i)
bad = 0
for k in (3, 4, 5):
    w = dk(k)
    for i in range(0, 10):
        for j in range(0, 28):
            f = fired_junctions('a' * i + 'b' + 'a' * j, w)
            s = set(f)
            for sig in range(min(f) if f else k, k):
                if sig not in s and (sig - 1) not in s:
                    bad += 1          # skip NOT preceded by a firing
check('skip-after-bite violations', bad, 0)
print('   skip-after-bite structure: 3 k-values x 10 x 28, 0 violations')
# consequence (the Step-4 use): no single-b pass deletes exactly a
# proper prefix {0..m-1}
bad = 0
for k in (3, 4, 5):
    w = dk(k)
    for i in range(0, 10):
        for j in range(0, 28):
            f = set(fired_junctions('a' * i + 'b' + 'a' * j, w))
            for m in range(1, k):
                if f == set(range(m)): bad += 1
            if f == set(range(k)) and k < 3: bad += 0
check('clean-prefix deletions', bad, 0)
print('   no clean proper-prefix deletion: 0 over all probes')

# ---- 2. E1/E2 (part E, fresh encodings) -------------------------------
print('2. E1/E2 at k=2')
w2 = dk(2)
E1 = S(K('a' * 9 + 'b' + 'a' * 3 + 'b'),
       K('a' + 'b' + 'a' * 3 + 'b' + 'a' * 8), X)
check('E1 rev', ev(E1, w2), w2[::-1])
E2 = S(K('a' * 9 + 'b'), K('a' + 'b'), X)
v = ev(E2, w2)
check('E2 runs', [len(r) for r in v.split('b')], [9, 11, 9])

# ---- 3. the bonus: [eps/b][aa/aaa]X = a^{3^k} (part F) -----------------
print('3. bonus construction')
Eend = S(K(''), K('b'), S(K('aa'), K('aaa'), X))
for k in range(1, 7):
    check('end k=%d' % k, ev(Eend, dk(k)), 'a' * 3 ** k)

# ---- 4. mod-3 tables (part D) ------------------------------------------
print('4. mod-3 lemma')
for k in (2, 3, 4, 5):
    tops = [sum(B ** s for s in range(k - t, k + 1)) % 3
            for t in range(k)]          # t = 0..k-1 (0-indexed plants)
    bots = [sum(B ** s for s in range(0, sig + 1)) % 3
            for sig in range(k)]
    check('k=%d tops' % k, tops, [0] * k)
    check('k=%d bots' % k, bots, [1] * k)

# ---- 5. the L_m tightness runs (report R5.2) ---------------------------
print('5. L_m anchored runs (engine, k=4)')
mrg = S(K(''), K('b'), X)
def del_last(E):
    return S(K(''), C(K('b'), C(mrg, K('a'))), C(C(E, mrg), K('a')))
def del_first(E):
    return S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), E))
want = [(1, 120), (4, 117), (13, 108), (40, 81)]
for m in range(4):
    E = X
    for t in range(m):          E = del_first(E)
    for t in range(3 - m, 0, -1): E = del_last(E)
    Lm = C(E, K('a'))  # L_m is the del-chain scrutinee (per report B3)
    v = ev(E, dk(4))
    runs = [len(r) for r in v.split('b')]
    check('L_m m=%d' % m, (runs[0], runs[-1]), want[m])

print('FAILS:', fails)

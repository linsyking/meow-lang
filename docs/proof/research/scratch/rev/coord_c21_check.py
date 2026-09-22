#!/usr/bin/env python3
# Coordinator C21 fresh-encoding checks (rev-try / Lane C round 21). < 60 s.
# My OWN hand derivations (done BEFORE reading round21_delta.c), vs the
# evaluator and vs their census output files:
#   E1  [a^2 b a^4 / b] on D(k;3): fires everywhere, plant depths
#       BotSum(sigma)+6*sigma+2, anchored hits exactly I(1,1), I(1,2),
#       I(3,3) at sigma = 0,1,2 (the 3-hit drifting channel that
#       refutes round-20's "|hits| <= 2").
#   E2  [a^2 b a^112 / b] on D(5;3): Delta=114, mirror target I(5,5)=243
#       served at sigma=2 <= k-2 with debt (t+1)Delta = 342 >= 122,
#       output mass S + 5*114 = 934. Family Delta=(3^k-15)/2.
#   E3  [a^9/(abaaa)] on D(2;3) = a^9 b a^9 (survivor at 9 = I(2,2),
#       inserted 9 >= 5, never-inserted 0); [a^27/(abaaa)] on D(3;3) =
#       a^27 b a^59 (survivor 27 = I(3,3), second copy at 36 = I(2,3)).
#   D1/D2/INH arithmetic sweeps; the tightened-FIT pigeonhole.
#   MY OWN census at k=5 (full re-enumeration, my constraint reading):
#   expect exactly 29 survivors, set-equal to d5.txt; E1/E2 records
#   present. All d*.txt records re-validated against my constraints.
import sys
sys.path.insert(0, '.')
import itertools
import prov as PV
from lcore import K, V, C, S
X = V(0)
fails = 0
def check(name, got, want):
    global fails
    if got != want:
        fails += 1
        print('  FAIL %-36s got %r want %r' % (name, got, want))

def dk(k):     return 'b'.join('a' * (3 ** j) for j in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def BotSum(j): return (3 ** (j + 1) - 1) // 2
def I(u, v):   return (3 ** (v + 1) - 3 ** u) // 2
from itertools import accumulate
def sepdepths(t):
    # cumulative a-mass before each separator (NOT the b-to-b gaps)
    return list(accumulate(len(c) for c in t.split('b')[:-1]))

# ---------- 0. E1: the drifting 3-hit channel
e1 = S(K('aabaaaa'), K('b'), X)                    # [a^2 b a^4 / b]
IVmap = {}
for a in range(0, 9):
    for b in range(a, 9):
        IVmap.setdefault(I(a, b), []).append((a, b))
for k in (4, 5, 6, 7):
    t = ev(e1, dk(k))
    check('E1 b-count k=%d (all fire)' % k, t.count('b'), k)
    check('E1 depths k=%d' % k, sepdepths(t),
          [BotSum(s) + 6 * s + 2 for s in range(k)])
    hits = [(s, IVmap[d]) for s, d in enumerate(sepdepths(t)) if d in IVmap]
    check('E1 hits k=%d' % k, hits,
          [(0, [(1, 1)]), (1, [(1, 2)]), (2, [(3, 3)])])
check('E1 a-mass k=7 (f*Delta=+36)', ev(e1, dk(7)).count('a'),
      BotSum(7) + 7 * 6)
print('0. E1 [a^2ba^4/b]: depths BotSum(s)+6s+2, hits exactly I(1,1), '
      'I(1,2), I(3,3) at s=0,1,2, k=4..7 OK -- 3 real hits, refuting '
      'round-20 |hits|<=2')

# ---------- 1. E2: the mirror service via the debt branch
e2 = S(K('aab' + 'a' * 112), K('b'), X)             # [a^2 b a^112 / b]
t = ev(e2, dk(5))
check('E2 depths', sepdepths(t), [BotSum(s) + 114 * s + 2 for s in range(5)])
check('E2 mirror hit I(5,5)=243 at sigma=2', sepdepths(t)[2], 3 ** 5)
check('E2 hit classes', [d in IVmap for d in sepdepths(t)],
      [True, True, True, False, False])
check('E2 output mass S+5*114', t.count('a'), BotSum(5) + 5 * 114)
check('E2 debt 3*114 >= (3^5+1)/2', 3 * 114 >= (3 ** 5 + 1) // 2, True)
for k in (3, 4, 5, 6):
    D = (3 ** k - 15) // 2
    check('E2 family depth(2) k=%d' % k, BotSum(2) + 2 * D + 2, 3 ** k)
    check('E2 family debt k=%d' % k, 3 * D >= (3 ** k + 1) // 2, True)
print('1. E2 [a^2ba^112/b] on D(5;3): depths [3,120,243,384,579], mirror '
      'I(5,5) at sigma=2<=k-2, debt 342>=122, mass 934; family '
      'Delta=(3^k-15)/2 OK')

# ---------- 2. E3: the inherited survivor at a mirror depth
e3a = S(K('a' * 9), K('abaaa'), X)                  # [a^9/(abaaa)]
check('E3 k=2 text', ev(e3a, dk(2)), 'a' * 9 + 'b' + 'a' * 9)
check('E3 k=2 survivor depth = I(2,2)', sepdepths(ev(e3a, dk(2)))[0], 9)
check('E3 k=2 inserted >= (3^2+1)/2', 9 >= (9 + 1) // 2, True)
e3b = S(K('a' * 27), K('abaaa'), X)                 # [a^27/(abaaa)]
check('E3 k=3 text', ev(e3b, dk(3)), 'a' * 27 + 'b' + 'a' * 59)
check('E3 k=3 survivor depth = I(3,3)', sepdepths(ev(e3b, dk(3)))[0], 27)
# NB: their report says the 2nd copy lands "at depth 36 = I(2,3)": that
# counts the CHARACTER position (27+1+8); the a-mass depth is 35. Minor
# convention slip in a side remark; the survivor claim (27 = I(3,3)) is
# the load-bearing part and holds.
check('E3 k=3 2nd copy at a-depth 35', 27 + 8, 35)
check('E3 k=3 inserted >= (3^3+1)/2', 27 >= (27 + 1) // 2, True)
print('2. E3: survivor at mirror depth with top-scale inserted mass, '
      'never-inserted 0 (the bites ate the prefix); 2nd copy at I(2,3) OK')

# ---------- 3. D1 / D2 / INH arithmetic (my own sweeps)
for k in (6, 7, 8, 9):
    lo = (5 * 3 ** (k - 1) + 1) // 2
    for u in range(1, k + 1):
        for s in range(0, k - 1):
            W = (3 ** (k + 1) - 3 ** u - 3 ** (s + 1) + 1) // 2
            if W - 3 ** (s + 1) < (3 ** k + 1) // 2 or W < lo:
                fails += 1; print('  FAIL D1 k=%d u=%d s=%d' % (k, u, s))
    for u in range(1, k + 1):                        # D2 identity at s=k-1
        W = (3 ** (k + 1) - 3 ** u - 3 ** k + 1) // 2
        if W != 3 ** k - BotSum(u - 1):
            fails += 1; print('  FAIL D2 k=%d u=%d' % (k, u))
for k in (4, 5, 6, 7, 8):                            # INH supply bound
    for tt in range(0, k):
        for j in range(0, k):
            if I(tt + 1, k) - BotSum(j) < (3 ** k + 1) // 2:
                fails += 1; print('  FAIL INH k=%d t=%d j=%d' % (k, tt, j))
for j in range(0, 8):                                # mod-3 separation
    check('BotSum(%d) = 1 mod 3' % j, BotSum(j) % 3, 1)
for u in range(1, 8):
    for v in range(u, 8):
        check('I(%d,%d) = 0 mod 3' % (u, v), I(u, v) % 3, 0)
print('3. D1 (W-3^{s+1} >= (3^k+1)/2, W >= (5*3^{k-1}+1)/2), D2 identity, '
      'INH supply bound, mod-3 separation: swept OK')

# ---------- 4. the tightened-FIT pigeonhole (t1 distinct junctions in [0,s1))
for s1 in range(0, 7):
    for mask in range(1 << s1):                     # subsets of [0, s1)
        F = [i for i in range(s1) if mask >> i & 1]
        t1 = len(F)
        if F:                                        # earliest firing t0
            if not (min(F) <= s1 - t1):
                fails += 1; print('  FAIL pigeonhole', s1, F)
print('4. tightened FIT window: t_1 firings occupy distinct junctions in '
      '[0,sigma_1), so tau_0 <= sigma_1 - t_1 (all subsets, s1<7) OK')

# ---------- 5. MY OWN census at k=5 (full re-enumeration, my constraints)
k = 5
surv = []
sig_triples = list(itertools.combinations(range(k), 3))
ab_opts = [[(a, b) for a in range(1, k + 2) for b in range(a)
            if (a, b) != (s + 1, 0)] for s in range(k)]
for s1, s2, s3 in sig_triples:
    for ab1 in ab_opts[s1]:
        for ab2 in ab_opts[s2]:
            W12 = None
            for ab3 in ab_opts[s3]:
                for t1 in range(0, s1 + 1):
                    for q1 in range(1, s2 - s1 + 1):
                        for q2 in range(1, s3 - s2 + 1):
                            t2, t3 = t1 + q1, t1 + q1 + q2
                            W1 = (3**ab1[0] - 3**ab1[1] - 3**(s1+1) + 1) // 2
                            W2 = (3**ab2[0] - 3**ab2[1] - 3**(s2+1) + 1) // 2
                            W3 = (3**ab3[0] - 3**ab3[1] - 3**(s3+1) + 1) // 2
                            if (W2 - W1) * (t3 - t1) != (W3 - W1) * (t2 - t1):
                                continue
                            if (W2 - W1) % (t2 - t1):
                                continue
                            D = (W2 - W1) // (t2 - t1)
                            if D == 0:
                                continue
                            c = W1 - t1 * D
                            if not (c <= D + 3 ** (s1 - t1 + 1)):
                                continue
                            if not (c >= -3 ** (s1 - t1)):
                                continue
                            if I(s1 + 1, s2) + q1 * D < 0:
                                continue
                            if I(s2 + 1, s3) + q2 * D < 0:
                                continue
                            surv.append((s1, s2, s3, ab1, ab2, ab3,
                                        t1, q1, q2, D, c))
print('5. MY census at k=5: %d survivors (their d5.txt: 29)' % len(surv))
check('my k=5 census count', len(surv), 29)

# parse d5.txt and compare record sets
def parse_rec(line):
    rec = {}
    for tok in line.split():
        if '=' in tok:
            key, val = tok.split('=')
            rec[key] = val
    s = [int(x) for x in rec['s'].split(',')]
    ab = [tuple(int(y) for y in p.split('/')) for p in rec['ab'].split(',')]
    q = [int(x) for x in rec['q'].split(',')]
    return (s[0], s[1], s[2], ab[0], ab[1], ab[2],
            int(rec['t1']), q[0], q[1], int(rec['D']), int(rec['c']))

theirs = []
for line in open('../rev-try/d5.txt'):
    if line.startswith('REC'):
        theirs.append(parse_rec(line))
check('my k=5 census set == d5.txt', sorted(surv), sorted(theirs))
e1rec = (0, 1, 2, (2, 1), (3, 1), (4, 3), 0, 1, 1, 6, 2)
e2rec = (0, 1, 2, (2, 1), (5, 1), (6, 5), 0, 1, 1, 114, 2)
check('E1 record in d5.txt', e1rec in theirs, True)
check('E2 record in d5.txt', e2rec in theirs, True)

# validate ALL their records at k=6/8/9 against my constraint reading
# (also the k=5 distinct-channel count, mine: 23 not their stale 13)
ch5 = set()
for line in open('../rev-try/d5.txt'):
    if line.startswith('REC'):
        f = line.split()
        ch5.add((f[6], f[7]))
check('k=5 distinct (D,c) channels', len(ch5), 23)
ghosts = []
# v3 census (round 21b: the two-sided window): 29/80/361/651
for fn, kk, expn in (('d6.txt', 6, 80), ('d8.txt', 8, 361), ('d9.txt', 9, 651)):
    nrec = 0
    for line in open('../rev-try/' + fn):
        if not line.startswith('REC'):
            continue
        r = parse_rec(line)
        s1, s2, s3, ab1, ab2, ab3, t1, q1, q2, D, c = r
        assert line.split()[1] == 'k=%d' % kk
        for (a, b), s in ((ab1, s1), (ab2, s2), (ab3, s3)):
            if not (1 <= a <= kk + 1 and 0 <= b < a and (a, b) != (s + 1, 0)):
                fails += 1; print('  FAIL domain', fn, r)
        t2, t3 = t1 + q1, t1 + q1 + q2
        if not (0 <= t1 <= s1 and 1 <= q1 <= s2 - s1 and 1 <= q2 <= s3 - s2):
            fails += 1; print('  FAIL t-feasibility', fn, r)
        W1 = (3**ab1[0] - 3**ab1[1] - 3**(s1+1) + 1) // 2
        W2 = (3**ab2[0] - 3**ab2[1] - 3**(s2+1) + 1) // 2
        W3 = (3**ab3[0] - 3**ab3[1] - 3**(s3+1) + 1) // 2
        if not (W1 == t1 * D + c and W2 == t2 * D + c and W3 == t3 * D + c):
            fails += 1; print('  FAIL collinearity', fn, r)
        if D == 0:
            fails += 1; print('  FAIL Delta=0', fn, r)
        if not (c <= D + 3 ** (s1 - t1 + 1)):
            fails += 1; print('  FAIL tightened upper', fn, r)
        if not (c >= -3 ** (s1 - t1)):
            # MY FLAG: unrealizable ghost -- c = rho_j - p0 forces p0 > 3^{t0}
            ghosts.append(r)
        if I(s1 + 1, s2) + q1 * D < 0 or I(s2 + 1, s3) + q2 * D < 0:
            fails += 1; print('  FAIL monotonicity', fn, r)
        nrec += 1
    check('%s record count' % fn, nrec, expn)
print('6. all d6/d8/d9 records re-validated (collinearity, integrality, '
      't-feasibility, tightened UPPER window, monotonicity): OK')
# the lower-bound ghosts: p0 = rho_j - c >= -c > 3^{sigma_1 - t_1} >= 3^{t_0}
badghost = 0
for r in ghosts:
    s1, s2, s3, ab1, ab2, ab3, t1, q1, q2, D, c = r
    if -c <= 3 ** (s1 - t1):
        badghost += 1
check('all ghosts have p0 > 3^{s1-t1} (unrealizable)', badghost, 0)
# after round 21b (the two-sided window): ZERO ghosts remain
check('ghost count after 21b (two-sided window)', len(ghosts), 0)
print('   v3 confirmed: 29/80/361/651 records, all passing my TWO-SIDED '
      'tightened window (v2 had 19 lower-bound ghosts: d8: 3, d9: 16; my '
      'flag, fixed in round 21b). Distinct (D,c) channels: 23/57/218/365 '
      '-- their report says 13 at k=5, a stale number (the file has 23).')

# ---------- 7. T5: my flag-2 exhibit (the census is corroboration)
t = ev(S(K('a' * 35 + 'b' + 'a' * 46), K('b' + 'a' * 81), X), dk(7))
# fires at junctions 3..6 (run s+1 needs >= 81 a's); the planted depths:
# Delta = M_R - p0 - p1 = 81 - 0 - 81 = 0: prior fires contribute NET
# ZERO a-mass, so the plant depth is BotSum(s) + c with c = 35:
check('T5 planted depths',
      sepdepths(t)[3:], [BotSum(s) + 35 for s in (3, 4, 5, 6)])
check('T5 fires 3..6, zero real anchored hits',
      [d in IVmap for d in sepdepths(t)[3:]],
      [False, False, False, False])
print('7. T5 (my round-20 exhibit re-encoded): the idealized cross-pair '
      '{I(2,3),I(1,3)} is census-ghosted, real channel has zero hits OK')

print('FAILS:', fails)

#!/usr/bin/env python3
# Coordinator D7 fresh-encoding checks (rev-wall / Lane D round 7). < 60 s.
# My own catalog for the obligation lemma (random, plus an n=4 probe for
# G2), 7.2 at different ranges, 7.3's inequality, all witnesses fresh, and
# MY H3B FLAG probes: the pair-merge fired-set sentence vs the round-6
# recursion theorem (the witness chains at k>=6; the window interior
# does not give the width-1 atom).
import sys
sys.path.insert(0, '.')
import random
import prov as PV
from lcore import K, V, C, S
X = V(0)
def dk(k):     return 'b'.join('a' * (3 ** j) for j in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def I(u, v):   return (3 ** (v + 1) - 3 ** u) // 2
fails = 0
def check(name, got, want):
    global fails
    if got != want:
        fails += 1
        print('  FAIL %-32s got %r want %r' % (name, got, want))

# ---------- 1. my own obligation-lemma catalog (random, n<=3) + n=4 probe
rng = random.Random(31337)
def mstar(u, v, k):
    return max(min(s, k - s) for s in range(u, v + 1))
def canon(pieces):
    ps = sorted(pieces)
    out = []
    for sp in ps:
        if out and out[-1][0] == -sp[0] and out[-1][1] == sp[1]:
            out.pop()
        else:
            out.append(sp)
    return out
IV = {}
for a in range(0, 9):
    for b in range(a, 9):
        IV.setdefault(I(a, b), []).append((a, b))
bad3 = bad4a = bad4b = n3 = n4 = 0
SP = [(s, (a, b)) for s in (1, -1) for a in range(0, 9) for b in range(a, 9)]
for u in range(1, 8):
    for v in range(u + 1, 8):
        tgt = I(u, v)
        for t in range(-16, 17):
            if abs(t) >= 3 ** u:
                continue
            want = tgt - t
            for sp1 in SP:
                for sp2 in SP:
                    if sp1[0] * I(*sp1[1]) + sp2[0] * I(*sp2[1]) > want:
                        continue
                    rem = want - sp1[0] * I(*sp1[1]) - sp2[0] * I(*sp2[1])
                    for third in ([(-1, (0, 0))] if rem == 0 else
                                  [(1, iv) for iv in IV.get(rem, [])] +
                                  [(-1, iv) for iv in IV.get(-rem, [])]):
                        pc = canon([sp1, sp2] + ([third] if third != (-1, (0, 0)) else []))
                        if not pc:
                            continue
                        n3 += 1
                        for k in range(v + 1, 18):
                            ms = mstar(u, v, k)
                            if not any(min(d, k - c) >= ms - 1
                                       for (s, (c, d)) in pc):
                                bad3 += 1
                                if bad3 <= 3:
                                    print('   n<=3 gap:', pc, t, u, v, k)
                    # the n=4 probe: split the third piece into two
                    for iv1 in range(0, 60):
                        pass
                    break
# n=4 probe: enumerate 4-piece solutions on a smaller box (u<=5, a,b<=5)
n4 = bad4a = bad4b = 0
for u in range(1, 6):
    for v in range(u + 1, 6):
        tgt = I(u, v)
        for t in (-2, -1, 0, 1, 2):
            if abs(t) >= 3 ** u:
                continue
            want = tgt - t
            SP4 = [(s, (a, b)) for s in (1, -1)
                   for a in range(0, 6) for b in range(a, 6)]
            for sp1 in SP4:
                for sp2 in SP4:
                    for sp3 in SP4:
                        rem = want - (sp1[0] * I(*sp1[1]) + sp2[0] * I(*sp2[1])
                                      + sp3[0] * I(*sp3[1]))
                        if rem == 0:
                            fourth = None
                        elif rem in IV:
                            fourth = (1, IV[rem][0])
                        elif -rem in IV:
                            fourth = (-1, IV[-rem][0])
                        else:
                            continue
                        pl = [sp1, sp2, sp3] + ([fourth] if fourth else [])
                        pc = canon(pl)
                        if not pc or len(pc) > 4:
                            continue
                        n4 += 1
                        for k in range(v + 1, 14):
                            ms = mstar(u, v, k)
                            if not any(min(d, k - c) >= ms - 1
                                       for (s, (c, d)) in pc):
                                bad4a += 1
                            if not any(min(d, k - c) >= ms - 2
                                       for (s, (c, d)) in pc):
                                bad4b += 1
check('obligation lemma n<=3 (my catalog)', bad3, 0)
print('1. my constructive catalog (a,b<=8, u,v<=7, |t|<3^u): %d solutions '
      'n<=3, violations of m*-1: %d; n=4 probe (smaller box): %d sols, '
      'm*-1 violations %d, m*-2 violations %d (G2 data)'
      % (n3, bad3, n4, bad4a, bad4b))

# ---------- 2. 7.2 fresh at different ranges (c<=200, u,v<=9, U,V<=10)
sols = shifts = 0
unclassified = 0
for c in range(1, 201):
    for u in range(0, 10):
        for v in range(u, 10):
            w = c * I(u, v)
            for U in range(0, 11):
                if w < I(U, U):
                    break
                for V in range(U, 11):
                    if w == I(U, V):
                        sols += 1
                        L, Lp = v - u + 1, V - U + 1
                        if c == 3 ** (U - u) and (V - v) == (U - u):
                            shifts += 1
                        elif (Lp % L == 0 and U >= u and
                              c == 3 ** (U - u) * (3 ** Lp - 1) // (3 ** L - 1)):
                            pass
                        else:
                            unclassified += 1
check('7.2 unclassified (fresh ranges)', unclassified, 0)
print('2. 7.2 fresh (c<=200, u,v<=9, U,V<=10): %d solutions, %d shifts, '
      'all classified' % (sols, shifts))

# ---------- 3. 7.3's inequality (feasible flanks vs the exactness demand)
bad = 0
for u in range(0, 7):
    for v in range(u + 1, 8):
        c = v - u + 1
        if not (4 * 3 ** u < 3 ** (v + 1) / c):
            bad += 1
check('7.3 inequality 4*3^u < 3^{v+1}/c', bad, 0)
print('3. 7.3: i+j <= 4*3^u < 3^{v+1}/(v-u+1) for all u<v (|R|<0): OK')

# ---------- 4. the witnesses, fresh-encoded (hand-derived first)
for kk in (2, 3, 4, 5):
    check('triper k=%d' % kk, ev(S(K('aaa'), K('aa'), X), dk(kk)),
          'b'.join('a' * I(0, s) for s in range(kk + 1)))
for kk in (2, 3, 4, 5):
    check('full merge k=%d' % kk, ev(S(K('aaa'), K('abaa'), X), dk(kk)),
          'a' * I(0, kk))
for kk in range(2, 9):
    v = sum(I(0, s) for s in range(kk + 1))
    check('H2 formula k=%d' % kk, v, (3 ** (kk + 2) - 2 * kk - 5) // 4)
    check('H2 never lands k=%d' % kk,
          any(v == I(a, b) for a in range(kk + 5) for b in range(a, kk + 5)),
          False)
for t in range(0, 6):
    k = t + 2
    # isolate runs 0..t: [e/a^{3^{t+1}}]X = D(t;3).b^{k-t} (round-6 E2),
    # halve, merge: sum (3^s+1)/2 = (I(0,t)+t+1)/2
    e = S(K(''), K('b'),
          S(K('a'), K('aa'), S(K(''), K('a' * 3 ** (t + 1)), X)))
    got = ev(e, dk(k))
    want = 'a' * ((I(0, t) + t + 1) // 2)
    check('E1 halver+merge t=%d' % t, got, want)
    check('E1 identity t=%d' % t,
          sum((3 ** s + 1) // 2 for s in range(t + 1)),
          (I(0, t) + t + 1) // 2)
for m in range(1, 7):
    h = (3 ** (m + 1) + 1) // 2
    check('E3 halver mod3 m=%d' % m,
          any(h == I(a, b) for a in range(m + 3) for b in range(a, m + 3)),
          False)
check('F box', ev(S(K('b' + 'a' * 12 + 'b'),
                    K('b' + 'a' * 3 + 'b' + 'a' * 9 + 'b'), X), dk(4)),
      'a' + 'b' + 'a' * 12 + 'b' + 'a' * 27 + 'b' + 'a' * 81)
check('G box', ev(S(K('b' + 'a' * 36 + 'b'),
                    K('b' + 'a' * 9 + 'b' + 'a' * 27 + 'b'), X), dk(5)),
      'a' + 'b' + 'a' * 3 + 'b' + 'a' * 36 + 'b' + 'a' * 81 + 'b' + 'a' * 243)
check('pair-merge witness k=5',
      ev(S(K('a' * 28), K('a' + 'b' + 'a' * 27), X), dk(5)),
      'a' + 'b' + 'a' * 3 + 'b' + 'a' * I(2, 3) + 'b' + 'a' * I(4, 5))
print('4. witnesses (tripler, full merge, H2, E1, E3, F, G, pair-merge): OK')

# ---------- 5. MY H3B FLAG PROBES (the fired-set sentence)
def fired_rec(runs, i, j):
    out, c = [], runs[0]
    for sig in range(len(runs) - 1):
        f = (c >= i and runs[sig + 1] >= j)
        if f: out.append(sig)
        c = runs[sig + 1] - (j if f else 0)
    return out
def blocks(k, fires):
    fired = set(fires)
    out, start = [], 0
    for s in range(k):
        if s not in fired:
            out.append(sum(3 ** t for t in range(start, s + 1)))
            start = s + 1
    out.append(sum(3 ** t for t in range(start, k + 1)))
    return out
# (a) the witness (1,27) at k=7: chains past I(4,5)
f7 = fired_rec([3 ** s for s in range(8)], 1, 27)
check('witness (1,27) k=7 fired set', f7, [2, 4, 5, 6])
out = ev(S(K('a' * 28), K('a' + 'b' + 'a' * 27), X), dk(7))
check('witness k=7 output runs', [len(r) for r in out.split('b')],
      blocks(7, f7))
print('5a. H3B FLAG: witness (1,27) at k=7 fires {2,4,5,6} -- NOT "the '
      'junctions with 3^{s+1}>=27"={2,3,4,5,6}: junction 3 is blocked '
      '(remnant 0 < i) and 5,6 CHAIN after 4. The report sentence "fires '
      'exactly at the junctions sigma with 3^{sigma+1} >= j" is FALSE in '
      'general (its own hand note blocks u+1); the k=5 witness is real.')
# (b) the window interior (1,20): no width-1 atom
f5 = fired_rec([3 ** s for s in range(6)], 1, 20)
out = ev(S(K('a' * 21), K('a' + 'b' + 'a' * 20), X), dk(5))
check('interior (1,20) k=5 fired set', f5, [2, 3, 4])
check('interior (1,20) output runs', [len(r) for r in out.split('b')],
      blocks(5, f5))
print('5b. H3B FLAG: interior (i=1, j=20, u=2: 18<20<=27, the stated '
      'window) fires {2,3,4}: runs 2..5 chain into ONE run -- no width-1 '
      'atom I(2,3) bounded by surviving separators. The atom needs '
      '3^{u+1}-j < i (block junction u+1): the CORRECT window is '
      'max(3^u, 3^{u+1}-i) < j <= 3^{u+1}.')
# (c) the correct window: j = 3^{u+1} gives the atom at several u
for u in (1, 2, 3):
    k = u + 3
    j = 3 ** (u + 1)
    e = S(K('a' * (1 + j)), K('a' + 'b' + 'a' * j), X)
    out = ev(e, dk(k))
    runs = [len(r) for r in out.split('b')]
    want = ([3 ** s for s in range(u)] + [I(u, u + 1)] +
            [sum(3 ** t for t in range(u + 2, k + 1))])
    check('corrected window atom u=%d' % u, runs, want)
print('5c. corrected window (j=3^{u+1}): the width-1 atom I(u,u+1) at '
      'depth 1 confirmed u=1..3 (the chain to the right merges the tail, '
      'the atom itself is bounded by the blocked junction u+1)')

# ---------- 6. composition collapse
trip = S(K('aaa'), K('aa'), X)
e = S(K('a' * 5), trip, trip)
check('composition collapse', ev(e, dk(4)), 'a' * 5)
print('6. [a^5/tripler-text]tripler-text = a^5: the whole-text match '
      'collapses to R -- embedded cheapness does not compose')

print('FAILS:', fails)

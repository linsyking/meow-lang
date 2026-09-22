#!/usr/bin/env python3
"""ROUND 21 battery: the Delta!=0 multi-hit closure + the inherited
loophole (Lemma INH).  All claims hand-derived first (see
ROUND21_REPORT.md); this battery only falsifies/illustrates.

T5  coordinator flag-2 exhibit: P = b.a^81, R = a^35.b.a^46 on D(7;3):
    real channel c=35, Delta=0, fires 3..6, ZERO real anchored hits,
    idealized hit set {sigma=0: I(2,3), sigma=1: I(1,3)} = a cross-pair
    census-ghosted at s0=0 (35 > 3): the census is corroboration, not
    coverage (the hand kill at the REAL firing is the coverage).

T6a EXHIBIT E1 (a real drifting 3-hit channel): [a^2 b a^4 / b] on
    D(k;3), k=4..7: fires everywhere (p0=p1=0, t_sigma=sigma),
    Delta=6, c=2; plant depths BotSum(sigma)+6*sigma+2; anchored hits
    EXACTLY I(1,1), I(1,2), I(3,3) at sigma=0,1,2 (no more).

T6b EXHIBIT E2 (mirror service via the debt branch): [a^2 b a^112 / b]
    on D(5;3): Delta=114, c=2; anchored hits I(1,1), I(1,4) at sigma
    0,1 and I(5,5)=3^5 at sigma=2 — a MIRROR target served at
    sigma=2 <= k-2, with drift debt (t+1)*Delta = 3*114 = 342 >=
    (3^5+1)/2 = 122 (Lemma D1's debt branch), and output mass
    S + 5*114 = 364+570 = 934 (Lemma MR's bookkeeping).

T6c Lemma D1 arithmetic: for all u<=k, sigma<=k-2:
    W(u,sigma) - 3^{sigma+1} >= (3^k+1)/2 where
    W = (3^{k+1}-3^u-3^{sigma+1}+1)/2  (so FIT at the firing forces
    (t+1)Delta >= (3^k+1)/2, Delta>0).

T6d census claims on the C enumeration outputs d6/d8/d9.txt (program
    round21_delta.c, cross-validated against an independent Python
    re-implementation at k=6, record sets identical):
    (i) D1: every mirror-top hit (a=k+1) is at sigma=k-1 (window) or
        has Delta>0 and (t+1)*Delta >= (3^k+1)/2 (debt);
    (ii) max real hits per channel (DP over firing sets) <= 4;
    (iii) Delta<0 records: no mirror-top hit at sigma <= k-2.

T7  Lemma INH: (a) the supply bound arithmetic: I(t+1,k) - BotSum(j)
    >= (3^k+1)/2 for all t<=k-1, j<=k-1; (b) mod-3: BotSum(j) is never
    an interval sum congruent to 0 mod 3 (no Delta=0 survivor at any
    mirror depth); (c) EXHIBIT E3: [a^9 / (a b aaa)] on D(2;3): the
    ORIGINAL separator 1 survives at depth BotSum(1)+1*Delta =
    4+5 = 9 = I(2,2), a mirror target, with 9 of inserted mass before
    it (>= (3^2+1)/2 = 5) and 0 uninserted (bites ate the prefix);
    same at k=3 with R=a^27: survivor at 27 = I(3,3), inserted 27
    (>= 14).  The survivors-at-mirror-depths loophole is real but
    priced: the inserted mass is exact top-scale supply.
"""
import os
import re
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))

import prov as PV
from lcore import K, V, C, S

X = V(0)
val = lambda e, w: PV.content(PV.lden(e, (PV.lab_input(w),)))


def sup3(k):
    return 'b'.join('a' * (3 ** j) for j in range(k + 1))


BS = lambda t: (3 ** (t + 1) - 1) // 2
IV = lambda u, v: (3 ** (v + 1) - 3 ** u) // 2


def sep_depths(s):
    d, acc = [], 0
    for part in s.split('b'):
        acc += len(part)
        d.append(acc)
    return d[:-1]  # depths of the separators


def predict(p0, p1, M, k):
    """Lemma M: firing set, full output, event list (round 20)."""
    Phi = []
    for s in range(k):
        beta = 1 if (s >= 1 and (s - 1) in Phi) else 0
        if 3 ** s - beta * p1 >= p0 and 3 ** (s + 1) >= p1:
            Phi.append(s)
    PhiS = set(Phi)
    MR = sum(M)
    Rstr = 'b'.join('a' * m for m in M)
    L = [3 ** j - (p1 if (j - 1) in PhiS else 0) -
         (p0 if j in PhiS else 0) for j in range(k + 1)]
    parts, events, acc = [], [], 0
    for j in range(k + 1):
        parts.append('a' * L[j]); acc += L[j]
        if j < k:
            if j in PhiS:
                pre = 0
                for t in range(len(M) - 1):
                    pre += M[t]
                    events.append((acc + pre, 'planted', j, t))
                acc += MR; parts.append(Rstr)
            else:
                events.append((acc, 'inherited', j, None)); parts.append('b')
    return ''.join(parts), events, Phi


def iv_class(d, k, s):
    """The unique interval-sum representation of depth d at firing s
    (None if not an interval sum or inherited)."""
    for a in range(1, k + 2):
        for b in range(a):
            if IV(b, a - 1) == d and (a, b) != (s + 1, 0):
                return (a, b)
    return None


print('T5 coordinator flag-2 exhibit: P=b.a^81, R=a^35.b.a^46 on D(7;3)')
ok = True
w = sup3(7)
Pv, Rv = 'b' + 'a' * 81, 'a' * 35 + 'b' + 'a' * 46
out = val(S(K(Rv), K(Pv), X), w)
pred, events, Phi = predict(0, 81, (35, 46), 7)
ok &= (out == pred)
plants = [e for e in events if e[1] == 'planted']
realhits = [e for e in plants if iv_class(e[0], 7, e[2]) is not None]
ideal = [(s, iv_class(BS(s) + 35, 7, s)) for s in range(7)
         if iv_class(BS(s) + 35, 7, s) is not None]
ok &= (Phi == [3, 4, 5, 6]) and len(realhits) == 0
ok &= (ideal == [(0, (4, 2)), (1, (4, 1))])  # targets I(2,3), I(1,3)
print('  firing set', Phi, ' real anchored hits:', len(realhits),
      ' idealized hits:', ideal)
print('T5 real channel with zero real hits whose IDEALIZATION is a '
      'cross-pair (35 > 3^{0+1} = 3 census-ghosts it):',
      'VERIFIED' if ok else 'ANOMALY')

print('T6a EXHIBIT E1: [a^2 b a^4 / b] on D(k;3), k=4..7 (Delta=6, c=2)')
ok = True
for k in range(4, 8):
    w = sup3(k)
    out = val(S(K('a' * 2 + 'b' + 'a' * 4), K('b'), X), w)
    pred, events, Phi = predict(0, 0, (2, 4), k)
    ok &= (out == pred) and (Phi == list(range(k)))
    hits = []
    for e in events:
        if e[1] == 'planted':
            d = e[0]
            rep = iv_class(d, k, e[2])
            if rep:
                hits.append((e[2], rep, d))
    want = [(0, (2, 1), 3), (1, (3, 1), 12), (2, (4, 3), 27)]
    ok &= (hits == want)
print('  anchored hits exactly (sigma, target I(b,a-1), depth) =',
      want, 'at every k=4..7:',
      'VERIFIED' if ok else 'ANOMALY')

print('T6b EXHIBIT E2: [a^2 b a^112 / b] on D(5;3) (Delta=114, c=2)')
ok = True
k = 5
w = sup3(k)
out = val(S(K('a' * 2 + 'b' + 'a' * 112), K('b'), X), w)
pred, events, Phi = predict(0, 0, (2, 112), k)
ok &= (out == pred) and (Phi == list(range(k)))
hits = []
for e in events:
    if e[1] == 'planted':
        rep = iv_class(e[0], k, e[2])
        if rep:
            hits.append((e[2], rep, e[0]))
want = [(0, (2, 1), 3), (1, (5, 1), 120), (2, (6, 5), 243)]
ok &= (hits == want)
# mirror check: I(5,5) = 3^5 = 243 served at sigma=2 <= k-2 = 3
ok &= (IV(5, 5) == 243) and (2 <= k - 2)
debt = 3 * 114
ok &= (debt >= (3 ** k + 1) // 2) and (debt == 342)
outmass = sum(1 for ch in out if ch == 'a')
ok &= (outmass == BS(5) + 5 * 114 == 364 + 570)
print('  hits:', hits, ' mirror I(5,5)=243 at sigma=2; debt (t+1)*D=',
      debt, '>= (3^5+1)/2 =', (3 ** k + 1) // 2,
      '; output mass', outmass, '= S + 5*114')
print('T6b the debt branch of Lemma D1 + the MR mass bookkeeping:',
      'VERIFIED' if ok else 'ANOMALY')

print('T6c Lemma D1 arithmetic: W(u,sigma) - 3^{sigma+1} >= (3^k+1)/2')
ok = True
for k in (6, 7, 8, 9):
    for u in range(1, k + 1):
        for s in range(k - 1):
            W = (3 ** (k + 1) - 3 ** u - 3 ** (s + 1) + 1) // 2
            if W - 3 ** (s + 1) < (3 ** k + 1) // 2:
                ok = False
                print('  D1 arithmetic violation', k, u, s)
print('T6c for all u<=k, sigma<=k-2 (k=6..9):',
      'VERIFIED' if ok else 'ANOMALY')

print('T6d census claims (C enumeration outputs, cross-validated at k=6)')
ok = True


def parse(fn):
    recs = []
    for line in open(fn):
        m = re.match(r'REC k=(\d+) s=(\d+),(\d+),(\d+) ab=(\d+)/(\d+),'
                     r'(\d+)/(\d+),(\d+)/(\d+) q=(-?\d+),(-?\d+) '
                     r't1=(\d+) D=(-?\d+) c=(-?\d+)', line)
        if m:
            g = list(map(int, m.groups()))
            recs.append(dict(k=g[0], s=(g[1], g[2], g[3]),
                             ab=[(g[4], g[5]), (g[6], g[7]), (g[8], g[9])],
                             q=(g[10], g[11]), t1=g[12], D=g[13], c=g[14]))
    return recs


for fn in ('d6.txt', 'd8.txt', 'd9.txt'):
    fn = os.path.join(HERE, fn)
    recs = parse(fn)
    k = recs[0]['k']
    for r in recs:
        t = [r['t1'], r['t1'] + r['q'][0], r['t1'] + r['q'][0] + r['q'][1]]
        for i, (a, b) in enumerate(r['ab']):
            if a == k + 1:  # mirror-top target
                sm, tm = r['s'][i], t[i]
                if not (sm == k - 1 or (r['D'] > 0 and
                        (tm + 1) * r['D'] >= (3 ** k + 1) // 2)):
                    ok = False
                    print('  D1 census violation', fn, r)
                if r['D'] < 0 and sm <= k - 2:
                    ok = False
                    print('  D<0 early-mirror violation', fn, r)
    # max real hits per channel via firing-set DP
    ch = {}
    for r in recs:
        ch.setdefault((r['D'], r['c']), r)
    for (D, c) in ch:
        hit = set()
        for a in range(1, k + 2):
            for b in range(a):
                for s in range(k):
                    if (a, b) == (s + 1, 0):
                        continue
                    num = (3 ** a - 3 ** b - 3 ** (s + 1) + 1) // 2 - c
                    if num % D == 0:
                        tt = num // D
                        if 0 <= tt <= s:
                            hit.add((s, tt))
        f = [[0] * (k + 1) for _ in range(k + 1)]
        for s in range(k - 1, -1, -1):
            for t in range(s + 1):
                nf = f[s + 1][t]
                h = 1 if (s, t) in hit else 0
                fb = (f[s + 1][t + 1] + h) if t + 1 <= s + 1 else h
                f[s][t] = max(nf, fb)
        if f[0][0] > 4:
            ok = False
            print('  hit-count violation', fn, D, c, f[0][0])
    print('  %s: %d records, %d channels: D1 holds, D<0 has no '
          'early mirror, max real hits <= 4' % (fn, len(recs), len(ch)))
print('T6d census D1/no-early-negative-mirror/hit-count<=4:',
      'VERIFIED' if ok else 'ANOMALY')

print('T7 Lemma INH: the supply bound + mod-3 + exhibits')
ok = True
for k in (5, 6, 7, 8):
    for t in range(k):
        for j in range(k):
            if IV(t + 1, k) - BS(j) < (3 ** k + 1) // 2:
                ok = False
                print('  INH bound violation', k, t, j)
# mod-3: no Delta=0 survivor at a mirror depth
for k in (5, 6, 7, 8):
    for j in range(k):
        for t in range(k):
            if BS(j) % 3 != 1 or IV(t + 1, k) % 3 != 0:
                ok = False
            if BS(j) == IV(t + 1, k):
                ok = False
                print('  mod-3 violation', k, j, t)
print('  (a) I(t+1,k)-BotSum(j) >= (3^k+1)/2 and (b) mod-3 separation:',
      'VERIFIED' if ok else 'ANOMALY')
# E3: the survivor at a mirror depth
ok = True
for k, Rm in ((2, 9), (3, 27)):
    w = sup3(k)
    out = val(S(K('a' * Rm), K('a' + 'b' + 'a' * 3), X), w)
    pred, events, Phi = predict(1, 3, (Rm,), k)
    ok &= (out == pred) and (Phi == ([0] if k == 2 else [0, 2]))
    inh = [e for e in events if e[1] == 'inherited']
    # survivor 1 at depth BotSum(1) + 1*Delta, Delta = Rm - 1 - 3
    d1 = BS(1) + (Rm - 1 - 3)
    ok &= (inh[0][0] == d1) and (d1 == IV(k, k))
    inserted = Rm
    ok &= (inserted >= (3 ** k + 1) // 2)
    ok &= (sum(1 for ch in out if ch == 'a') == BS(k) + len(Phi) * (Rm - 4))
    print('  k=%d: output=%s survivor1 depth=%d=I(%d,%d) (mirror), '
          'inserted mass %d >= (3^k+1)/2 = %d' %
          (k, out[:20] + ('...' if len(out) > 20 else ''), inh[0][0],
           k, k, inserted, (3 ** k + 1) // 2))
print('T7 the inherited-at-mirror-depth survivor with top-scale '
      'inserted mass (Lemma INH exhibit):',
      'VERIFIED' if ok else 'ANOMALY')

print('ROUND 21 MACHINE VERDICT: see per-test lines above '
      '(T5 coverage note; T6a/b drifting-channel and debt exhibits; '
      'T6c/d Lemma D1 + census; T7 Lemma INH)')

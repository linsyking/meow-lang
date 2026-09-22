#!/usr/bin/env python3
# Coordinator D8 fresh-encoding checks (rev-wall / Lane D round 8). < 60 s.
# My OWN hand derivations (before reading g1g2_check.py), vs the evaluator
# and my own enumerations:
#   0.  the H3b window: my own 351-case sweep (u=1..3, i<=3, j<=3^{u+1}):
#       my fired_rec (the round-6 recursion theorem) predicts the
#       evaluator's pair-merge output EXACTLY; window
#       max(3^u, 3^{u+1}-i) < j <= 3^{u+1} (with i <= 3^u) iff
#       fire_u & !fire_{u-1} & !fire_{u+1} iff the atom I(u,u+1) appears.
#   1.  MY strata catalog (F1 q*3^e, F2 I(a,b), F3 G(r,T,m); 3 pieces;
#       |bite| <= 18; targets 3 <= u < v <= 6): the collected identity
#       Sum mu_d 3^d = 0; the top-defect inequality; the gap bound
#       3^g <= M_below; the deficit bound max Omega >= m*-1-floor(log_3 M).
#   2.  G2: MY exhaustive interval probe (a,b <= 3, u < v <= 3, |t| < 3^u,
#       multiplicity <= 7): the m*-1 violations by n EXACTLY the witness
#       7*I(0,1)+8 = I(2,3) (double 2-scale carry, M=20); the mass form
#       0 violations; n <= 6 never violates (the concentration argument).
#   3.  the exhibits' arithmetic + digit masses (M = 6/28/20); the F3 -> 7.2
#       coordination; Lane B's v_b instance; the C=2 closing arithmetic.
import sys
sys.path.insert(0, '.')
import bisect
from functools import lru_cache
import prov as PV
from lcore import K, V, C, S
X = V(0)
fails = 0
def check(name, got, want):
    global fails
    if got != want:
        fails += 1
        print('  FAIL %-40s got %r want %r' % (name, got, want))
def dk(k):     return 'b'.join('a' * (3 ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def I(u, v):   return (3 ** (v + 1) - 3 ** u) // 2
def mstar(u, v, k):
    return max(min(s, k - s) for s in range(u, v + 1))
def flog3(M):
    s, m = 0, 3
    while m <= M: m *= 3; s += 1
    return s
def tdigits(t):
    d = {}
    if t == 0: return d
    sgn, n, e = (1 if t > 0 else -1), abs(t), 0
    while n:
        if n % 3: d[e] = sgn * (n % 3)
        n //= 3; e += 1
    return d

# ---------- 0. the H3b window (my 351-case sweep)
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
ncase = nwin = 0
for u in (1, 2, 3):
    k = u + 4
    runs = [3 ** s for s in range(k + 1)]
    for i in range(1, min(3, 3 ** u) + 1):
        for j in range(1, 3 ** (u + 1) + 1):
            fires = fired_rec(runs, i, j)
            out = ev(S(K('a' * (i + j)), K('a' * i + 'b' + 'a' * j), X), dk(k))
            check('recursion->evaluator u=%d i=%d j=%d' % (u, i, j),
                  [len(r) for r in out.split('b')], blocks(k, fires))
            win = (i <= 3 ** u and max(3 ** u, 3 ** (u + 1) - i)
                   < j <= 3 ** (u + 1))
            cond = (u in fires and (u - 1) not in fires and (u + 1) not in fires)
            atom = (I(u, u + 1) in blocks(k, fires))
            if not (win == cond == atom):
                fails += 1
                print('  FAIL window u=%d i=%d j=%d: %s %s %s'
                      % (u, i, j, win, cond, atom))
            ncase += 1
            nwin += win
check('witness (1,27) k=7 fires', fired_rec([3 ** s for s in range(8)], 1, 27),
      [2, 4, 5, 6])
print('0. H3b: my recursion theorem predicts the evaluator on all %d cases; '
      'window <==> (fire_u & !fire_{u-1} & !fire_{u+1}) <==> atom I(u,u+1): '
      'EXACT (%d window hits)' % (ncase, nwin))

# ---------- 1. MY strata catalog (F1/F2/F3, 3 pieces, |bite| <= 18)
def G(r, T, m): return sum(3 ** (m - i * T) for i in range(r))
F1 = [(q * 3 ** e, ((e, q),)) for q in (1, 2, 4) for e in range(0, 6)]
F2 = [(I(a, b), tuple((s, 1) for s in range(a, b + 1))) for a in range(0, 6)
      for b in range(a, 6)]
F3 = [(G(r, T, m), tuple((m - i * T, 1) for i in range(r)))
      for r in (1, 2, 3) for T in (1, 2) for m in range(0, 6)
      if m - (r - 1) * T >= 0]
PIECES = F1 + F2 + F3
svals = sorted(set(p[0] for p in PIECES if p[0] > 0))
vmap = {}
for val, dg in PIECES:
    if val > 0: vmap.setdefault(val, []).append(dg)
targets = [(u, v) for u in range(3, 7) for v in range(u + 1, 7)]
nsol = viol_id = viol_td = viol_gap = viol_def = 0
for (u, v) in targets:
    tgt = I(u, v)
    for s1 in (1, -1):
        for s2 in (1, -1):
            for i1 in range(len(svals)):
                v1 = svals[i1]
                for v2 in svals[i1:]:
                    rem = tgt - (s1 * v1 + s2 * v2)
                    for s3 in (1, -1):
                        t3 = s3 * rem
                        lo = bisect.bisect_left(svals, t3 - 18)
                        hi = bisect.bisect_right(svals, t3 + 18)
                        for idx in range(lo, hi):
                            val3 = svals[idx]
                            t = tgt - (s1 * v1 + s2 * v2 + s3 * val3)
                            if abs(t) > 18: continue
                            for dg1 in vmap[v1]:
                                for dg2 in vmap[v2]:
                                    for dg3 in vmap[val3]:
                                        mu = {}
                                        for d, q in dg1: mu[d] = mu.get(d, 0) + s1 * q
                                        for d, q in dg2: mu[d] = mu.get(d, 0) + s2 * q
                                        for d, q in dg3: mu[d] = mu.get(d, 0) + s3 * q
                                        for d, q in tdigits(t).items(): mu[d] = mu.get(d, 0) + q
                                        for d in range(u, v + 1): mu[d] = mu.get(d, 0) - 1
                                        mu = {d: q for d, q in mu.items() if q}
                                        nsol += 1
                                        if sum(q * 3 ** d for d, q in mu.items()) != 0:
                                            viol_id += 1
                                        if not mu: continue
                                        dstar = max(mu)
                                        lhs = abs(mu[dstar]) * 3 ** dstar
                                        rhs = sum(abs(mu[d]) * 3 ** d
                                                  for d in mu if d < dstar)
                                        if lhs > rhs: viol_td += 1
                                        below = sorted(d for d in mu if d < dstar)
                                        if below and 3 ** (dstar - below[-1]) > \
                                           sum(abs(mu[d]) for d in below):
                                            viol_gap += 1
                                        M = sum(abs(q) for q in mu.values())
                                        for kk in range(v + 1, 16):
                                            ms = mstar(u, v, kk)
                                            best = max(min(max(d for d, q in dg), kk - min(d for d, q in dg))
                                                       for dg in (dg1, dg2, dg3))
                                            if best < ms - 1 - flog3(M):
                                                viol_def += 1
                                                if viol_def <= 3:
                                                    print('   def viol', u, v, t, M, ms, best)
print('1. MY strata catalog: %d digit-assignments; identity violations %d, '
      'top-defect %d, gap-bound %d, deficit-bound %d'
      % (nsol, viol_id, viol_td, viol_gap, viol_def))
check('strata catalog: collected identity', viol_id, 0)
check('strata catalog: top-defect inequality', viol_td, 0)
check('strata catalog: gap bound 3^g <= M_below', viol_gap, 0)
check('strata catalog: deficit bound (mass form)', viol_def, 0)

# ---------- 2. G2: MY exhaustive interval probe (multiplicity <= 7)
TYP = [(s, a, b, s * I(a, b)) for s in (1, -1)
       for a in range(4) for b in range(a, 4)]
TYP.sort(key=lambda x: -abs(x[3]))
N = len(TYP)
mx = [0] * (N + 1)
for i in range(N - 1, -1, -1):
    mx[i] = max(mx[i + 1], abs(TYP[i][3]))
@lru_cache(maxsize=None)
def reach(i, slots, R):
    if R == 0: return True
    if i == N or slots == 0: return False
    v = TYP[i][3]
    for c in range(0, slots + 1):
        r = R - c * v
        if abs(r) <= (slots - c) * mx[i + 1] and reach(i + 1, slots - c, r):
            return True
    return False
sols = []
CUR = (0, 0, 0)
def enum(i, slots, R, counts):
    if i == N:
        if R == 0: sols.append((tuple(counts),) + CUR)
        return
    v = TYP[i][3]
    for c in range(0, slots + 1):
        r = R - c * v
        if abs(r) <= (slots - c) * mx[i + 1] and reach(i + 1, slots - c, r):
            counts.append(c); enum(i + 1, slots - c, r, counts); counts.pop()
for (u, v) in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
    for t in range(-(3 ** u - 1), 3 ** u):
        CUR = (u, v, t)
        enum(0, 7, I(u, v) - t, [])
print('2. my exhaustive probe: %d multiset solutions (their B(i): 52959; '
      'mine is a SUPERSET -- no +/--canonicalization, netting pairs kept; '
      'the unique m*-1 violator is the same either way)' % len(sols))
viol_by_n = {}
mass_viol = 0
for counts, u, v, t in sols:
    n = sum(counts)
    mu = {}
    pieces = []
    for c, (s, a, b, val) in zip(counts, TYP):
        if c:
            pieces.append((a, b))
            for d in range(a, b + 1): mu[d] = mu.get(d, 0) + s * c
    for d, q in tdigits(t).items(): mu[d] = mu.get(d, 0) + q
    for d in range(u, v + 1): mu[d] = mu.get(d, 0) - 1
    M = sum(abs(q) for q in mu.values())
    anyviol = False
    for kk in range(v + 1, 16):
        ms = mstar(u, v, kk)
        best = max(min(b, kk - a) for (a, b) in pieces)
        if best < ms - 1:
            anyviol = True
            if best < ms - 1 - flog3(M):
                mass_viol += 1
    if anyviol:
        viol_by_n[n] = viol_by_n.get(n, 0) + 1
        if sum(viol_by_n.values()) <= 3:
            print('   m*-1 violation: n=%d target I(%d,%d) t=%d M=%d '
                  'pieces=%s' % (n, u, v, t, M, sorted(set(pieces))))
check('m*-1 violations by n = exactly the n=7 witness', viol_by_n, {7: 1})
check('the mass form: 0 violations', mass_viol, 0)
check('n <= 6 never violates (concentration 6+2 < 9)',
      any(k <= 6 for k in viol_by_n), False)

# ---------- 3. the exhibits, the F3 -> 7.2 coordination, C=2
check('3*I(0,1) = I(1,2)', 3 * I(0, 1), I(1, 2))
check('9*I(1,3) = I(3,5)', 9 * I(1, 3), I(3, 5))
check('7*I(0,1)+8 = I(2,3)', 7 * I(0, 1) + 8, I(2, 3))
def mass(pieces, t, u, v):
    mu = {}
    for (mult, a, b) in pieces:
        for d in range(a, b + 1): mu[d] = mu.get(d, 0) + mult
    for d, q in tdigits(t).items(): mu[d] = mu.get(d, 0) + q
    for d in range(u, v + 1): mu[d] = mu.get(d, 0) - 1
    return sum(abs(q) for q in mu.values())
check('M(3 I(0,1) -> I(1,2)) = 6', mass([(3, 0, 1)], 0, 1, 2), 6)
check('M(9 I(1,3) -> I(3,5)) = 28', mass([(9, 1, 3)], 0, 3, 5), 28)
check('M(7 I(0,1)+8 -> I(2,3)) = 20', mass([(7, 0, 1)], 8, 2, 3), 20)
check('deficit 1 = floor(log_3 6)', flog3(6), 1)
check('deficit 2 = floor(log_3 20)', flog3(20), 2)
for r in (2, 3, 4):
    for T in (1, 2, 3):
        c = (3 ** (r * T) - 1) // (3 ** T - 1)
        check('G(r=%d,T=%d) = 3^.. * c' % (r, T),
              G(r, T, (r - 1) * T), c)
        for uu in (0, 2, 5):
            check('c*I(u,u+T-1) = I(u,u+rT-1)', c * I(uu, uu + T - 1),
                  I(uu, uu + r * T - 1))
for m in (1, 2, 3, 4):                       # Lane B's mod2 v_b family
    check('v_b family (9^m-1)/8 * I(0,1) = I(0,2m-1)',
          ((9 ** m - 1) // 8) * I(0, 1), I(0, 2 * m - 1))
for ms in range(2, 40):                      # the C=2 closing arithmetic
    if not (1 + (ms - 1) / 2 >= ms / 2):
        fails += 1; print('  FAIL C=2 at m*=%d' % ms)
print('3. exhibits M = 6/28/20 with deficits = floor(log_3 M); F3 -> 7.2 '
      'length-divisibility (c = (3^{rT}-1)/(3^T-1), incl. Lane B v_b); '
      'C=2 closes: OK')

print('FAILS:', fails)

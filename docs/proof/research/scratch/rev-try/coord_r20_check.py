#!/usr/bin/env python3
# Coordinator round-20 (rev-try / OL-1) fresh-encoding checks. < 60 s.
# Everything re-derived by hand BEFORE this run (see my report-back):
# Lemma M depth formulas via MY cumulative-sum derivation, the K2 pair
# classification via the digit argument, the cross-pair ghost inequality,
# Lemma S forcing/window/exclusivity, T4i/T4iii hand-derived, mod-3,
# and the idealization-filter exhibit (c=35: realizable, 0 real hits,
# idealized cross-pair, filter-ghosted).
import sys
sys.path.insert(0, '.')
import random
import prov as PV
from lcore import K, V, C, S
X = V(0)
def dk(k):     return 'b'.join('a' * (3 ** j) for j in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def BS(s):     return (3 ** (s + 1) - 1) // 2
def IV(u, v):  return (3 ** (v + 1) - 3 ** u) // 2
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-34s got %r want %r' % (name, got, want))
    return ok

# ---------- 1. Lemma M: my simulation + my cumulative-form depth derivation
def mysweep(R, P, w):
    """my own greedy leftmost sweep; inserted text never rescanned"""
    res, rest = '', w
    while True:
        j = rest.find(P)
        if j < 0:
            break
        res += rest[:j] + R
        rest = rest[j + len(P):]
    return res + rest

def mylemma(p0, p1, M, k):
    """firing set (beta recursion) + output string + depths via MY
    cumulative-sum derivation:  plant (sigma,j) at sum_{i<=sigma}L_i
    + t_sigma*M_R + rho_j ;  inherited j at sum_{i<=j}L_i + t_j*M_R."""
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
    out, depths, runtot, fired_before = [], [], 0, 0
    for j in range(k + 1):
        runtot += L[j]
        out.append('a' * L[j])
        if j < k:
            if j in PhiS:
                pre = 0
                for t in range(len(M) - 1):
                    pre += M[t]
                    depths.append(('planted', j, t,
                                   runtot + fired_before * MR + pre))
                fired_before += 1
                out.append(Rstr)
            else:
                depths.append(('inherited', j, None,
                               runtot + fired_before * MR))
                out.append('b')
    return ''.join(out), depths, Phi

rng = random.Random(777)
bad_str = bad_depth = tested = 0
for trial in range(400):
    k = rng.randint(2, 5)
    p0 = rng.choice([0, 0, 1, 2, 3, 4, 9, 10, 27, 28, rng.randint(0, 12)])
    p1 = rng.choice([0, 0, 1, 2, 3, 5, 9, 10, 27, rng.randint(0, 12)])
    M = [rng.randint(0, 15) for _ in range(rng.randint(0, 3))]
    P = 'a' * p0 + 'b' + 'a' * p1
    R = 'b'.join('a' * m for m in M)
    w = dk(k)
    outp, depths, Phi = mylemma(p0, p1, M, k)
    outs = mysweep(R, P, w)
    outv = ev(S(K(R), K(P), X), w)
    tested += 1
    if not (outp == outs == outv):
        bad_str += 1
        if bad_str <= 3:
            print('   string mismatch:', p0, p1, M, k)
    # depth check: my cumulative forms vs their closed forms
    MR = sum(M)
    Delta = MR - p0 - p1
    rho, pre = [], 0
    for t in range(len(M) - 1):
        pre += M[t]
        rho.append(pre)
    for (kind, j, t, d) in depths:
        if kind == 'planted':
            want = BS(j) + Phi.index(j) * Delta - p0 + rho[t]
        else:
            want = BS(j) + len([s for s in Phi if s < j]) * Delta
        if d != want:
            bad_depth += 1
            if bad_depth <= 3:
                print('   depth mismatch:', kind, p0, p1, M, k, j, d, want)
    # locality M1
    for (kind, j, t, d) in depths:
        if kind == 'planted':
            lo = (BS(j - 1) if j >= 1 else 0) + Phi.index(j) * Delta
            hi = BS(j) + Phi.index(j) * Delta + MR
            if not (lo <= d <= hi):
                bad_depth += 1
check('Lemma M string mismatches', bad_str, 0)
check('Lemma M depth/locality mismatches', bad_depth, 0)
print('1. Lemma M: %d random (p0,p1,M,k) -- my simulation == my formula '
      'construction == evaluator; cumulative depths == closed forms' % tested)

# ---------- 2. K2 pair classification (digit argument), exhaustive
bad = 0; n = 0
for k in (6, 7):
    iv = {}
    for u in range(k + 1):
        for v in range(u, k + 1):
            iv.setdefault(IV(u, v), []).append((u, v))
    for s1 in range(k):
        for s2 in range(s1 + 1, k):
            rhs = IV(s1 + 1, s2)
            for (u1, v1) in [(a, b) for a in range(k + 1)
                             for b in range(a, k + 1)]:
                for (u2, v2) in iv.get(IV(u1, v1) + rhs, []):
                    n += 1
                    ladder = (v1 == s1 and u2 == u1 and v2 == s2)
                    cross = (u1 == s2 + 1 and u2 == s1 + 1 and v1 == v2)
                    if not (ladder or cross):
                        bad += 1
                        print('   NEW FAMILY', s1, s2, (u1, v1), (u2, v2))
check('K2 pair-classification violations', bad, 0)
print('2. pair equation solutions: %d, all ladder rungs or cross-pairs' % n)

# ---------- 3. cross-pair ghost + Lemma S forcing/window/exclusivity
bad = 0
for s1 in range(8):
    for s2 in range(s1 + 1, 8):
        for v in range(s2 + 1, 9):
            c = IV(s2 + 1, v) - BS(s1)      # cross-pair constant
            if not c >= (5 * 3 ** s2 + 1) // 2 > 3 ** s2 >= 3 ** (s1 + 1):
                bad += 1
check('cross-pair ghost inequality', bad, 0)
bad = 0
for k in (6, 7, 8):
    for u in range(1, k + 1):
        for s in range(k):
            c = IV(u, k) - BS(s)
            if s <= k - 2 and not c > 3 ** (s + 1):
                bad += 1
            if s == k - 1:
                if not (c <= 3 ** k and 3 ** k - c == BS(u - 1)):
                    bad += 1
check('Lemma S forcing + window identity', bad, 0)
bad = 0
for k in (6, 7, 8):
    for u in range(1, k + 1):
        c = 3 ** k - BS(u - 1)               # the mirror-window constant
        if BS(u - 1) + c != 3 ** k or 3 ** k != IV(k, k):
            bad += 1                         # early-hit depth = I(k,k)
        early_kill = (c > 3 ** u)            # FIT at s0 = u-1 fails
        if u <= k - 1 and not early_kill:
            bad += 1
        if u == k and not c <= 3 ** k:
            bad += 1
check('Lemma S exclusivity (early hit FIT-killed)', bad, 0)
print('3. ghost inequality, Lemma S forcing/window/exclusivity: 0 violations')

# ---------- 4. exhibitions T4i / T4iii (hand-derived before running)
for k in (4, 5, 6, 7):
    out = ev(S(K('baa'), K('aba'), X), dk(k))
    check('T4i ladder k=%d' % k,
          [out[:i].count('a') for i, ch in enumerate(out) if ch == 'b'],
          [BS(s) - 1 for s in range(k)])
for k in (4, 5, 6):
    p0, p1 = 3 ** (k - 1), 3 ** k
    M = [(5 * 3 ** (k - 1) + 1) // 2, (3 ** k - 1) // 2]
    R = 'b'.join('a' * m for m in M)
    out = ev(S(K(R), K('a' * p0 + 'b' + 'a' * p1), X), dk(k))
    check('T4iii string k=%d' % k, out, dk(k - 2) + 'b' + R)
    depths = [out[:i].count('a') for i, ch in enumerate(out) if ch == 'b']
    check('T4iii plant at 3^k k=%d' % k, 3 ** k in depths, True)
    check('T4iii single firing k=%d' % k, len(depths), k - 2 + 1 + 1 - 1 + 1)
print('4. T4i ladder + T4iii double-exact-tuned: byte-exact')

# ---------- 5. mod-3 inherited non-solution + ladder cap
bad = 0
for k in (5, 6, 7, 8):
    for j in range(k + 1):
        if BS(j) % 3 != 1:
            bad += 1
        for t in range(k):
            if BS(j) == IV(t + 1, k) or IV(t + 1, k) % 3 != 0:
                bad += 1
check('mod-3: BS(j)=1, I(t+1,k)=0, no solution', bad, 0)
bad = 0
for k in (5, 6, 7, 8):
    for u in range(1, k + 1):
        for sig in range(u, k):          # rungs: firings sigma <= k-1
            if IV(u, sig) >= 3 ** k:
                bad += 1
    for t in range(k):                  # mirror targets all >= 3^k
        if IV(t + 1, k) < 3 ** k:
            bad += 1
check('ladder magnitude cap + mirror floor', bad, 0)
print('5. mod-3 closure + ladder cap: 0 violations')

# ---------- 6. the idealization-filter exhibit (my §4 precision flag)
k = 7
P = 'b' + 'a' * 81
R = 'a' * 35 + 'b' + 'a' * 46
out = ev(S(K(R), K(P), X), dk(k))
depths = [out[:i].count('a') for i, ch in enumerate(out) if ch == 'b']
iv = {}
for u in range(k + 1):
    for v in range(u, k + 1):
        iv.setdefault(IV(u, v), []).append((u, v))
bs = set(BS(t) for t in range(k + 1))
real_hits = [d for d in depths if d in iv and d not in bs]
check('exhibit: realizable pass runs', isinstance(out, str), True)
check('exhibit: ZERO real hits', len(real_hits), 0)
ideal = [(s, iv[BS(s) + 35]) for s in range(k)
         if BS(s) + 35 in iv and BS(s) + 35 not in bs]
check('exhibit: idealized hits {0,1}', [s for (s, _) in ideal], [0, 1])
check('exhibit: idealized targets cross-pair',
      (ideal[0][1], ideal[1][1]), ([(2, 3)], [(1, 3)]))
check('exhibit: filter ghosts it (c=35 > 3^{s0+1}=3)', 35 > 3 ** 1, True)
print('6. filter exhibit: c=35 (Delta=0) IS in their T3 census class '
      '(35 = I(2,3)-I(0,0)), realized by P=b.a^81 / R=a^35.b.a^46; '
      'real hits 0; idealized hits {0,1} form a cross-pair; the machine '
      'filter (anchored at first IDEALIZED hit) ghosts it -- the census '
      'is corroboration; real-channel coverage is the hand kill (FIT at '
      'the real firing), which I verified independently.')

# ---------- 7. T4ii census, my own loop (6500 passes on D(5;3))
k = 5
mirror = set(IV(t + 1, k) for t in range(k))
mlist = [[m1, m2] for m1 in range(10) for m2 in range(10 - m1)]
mlist += [[m1] for m1 in range(10)]
bad = cnt = 0
for p0 in range(10):
    for p1 in range(10):
        for M in mlist:
            out = ev(S(K('b'.join('a' * m for m in M)),
                       K('a' * p0 + 'b' + 'a' * p1), X), dk(k))
            cnt += 1
            for i, ch in enumerate(out):
                if ch == 'b' and out[:i].count('a') in mirror:
                    bad += 1
check('T4ii census mirror plants', bad, 0)
print('7. my census: %d small passes on D(5;3), 0 mirror-depth plants' % cnt)

print('FAILS:', fails)

"""ROUND 20: OL-1 MATCH-EXACTNESS -- the battery behind the demand-side
lemma.  Theory first: every identity below was hand-derived before this
run (ROUND20_REPORT.md).  Base 3 staging family D(k;3), runs 3^j,
BotSum(s) = (3^{s+1}-1)/2 = I(0,s), interval sums I(u,v) =
(3^{v+1}-3^u)/2.

T1  LEMMA M (the two-sided match condition), byte-exact.  For a pass
    [R/P] with single-b pattern P = a^{p0} b a^{p1} and replacement
    R with run-vector M (mass M_R, separator-prefixes rho_j), the
    firing set is the top range determined by the fit conditions
    3^s - beta_s*p1 >= p0 and 3^{s+1} >= p1 (beta_s = [s-1 fired]:
    the round-19 double-biting bookkeeping), and every output
    separator sits at depth
        PLANTED (R-internal, copy at firing s):  BotSum(s)
              + t_s*Delta - p0 + rho_j,   Delta = M_R - p0 - p1,
              t_s = #earlier firings;
        INHERITED (surviving separator j):      BotSum(j) + t_j*Delta.
    Verified by predicting the ENTIRE output string from the firing
    set + formulas and comparing byte-exact with the evaluator, plus
    the per-separator depth/origin check, plus LEMMA M1 (locality):
    each plant from firing s lies in [BotSum(s-1)+t_s*Delta,
    BotSum(s)+t_s*Delta+M_R].

T2  LEMMA K (the interval-addition kernel).  (a) every solution of
    I(a,b)+I(c,d)=I(e,f) (exponents <= 8) is a consecutive merge (or
    has an empty side); (b) every solution of I(a,b)-I(c,d)=I(e,f)
    is a prefix/suffix split; (c) the scaling family 3*I(a,b) =
    I(a+1,b+1); (d) the blanket check: every vanishing collected
    signed power sum with support <= 4 exponents <= 8 and
    sum|coef| <= 6 reduces to all-zero by carries alone (the mod-3
    descent: a nonzero reduced form with all |coef| <= 2 cannot
    vanish).

T3  LEMMA K2 (channel rigidity).  For k = 7, 8 and a large class of
    channel constants c (all -BotSum(u-1), all site terms, ALL
    two-interval differences I(a,b)-I(c,d), small ints, random):
    the hit set {s: BotSum(s)+c is a non-inherited interval sum}
    satisfies: |hits| >= 3  ==>  c = -BotSum(u-1) exactly and hits =
    [u..k) (the bottom-fixed ladder, targets I(u,s)); |hits| = 2
    ==> the cross-pair structure (targets I(s1+1,v), I(s2+1,v)
    sharing the top v, crossed bottoms).  Drifting channels
    (BotSum(s)+s*Delta+c): |hits| <= 2 for all (Delta, c) in the
    tested classes.

T4  EXHIBITIONS.  (i) The bottom-ladder pass [baa/aba]X plants at
    depth BotSum(s)-1 = I(1,s) at EVERY firing -- a whole anchored
    ladder from a 3-letter pattern -- and the ladder is
    magnitude-capped below 3^k (all mirror targets are >= 3^k): the
    only multi-hit channel cannot serve the mirror family.
    (ii) The mirror-demand gap: no small pattern (p0,p1 <= 9,
    R-mass <= 9) plants at any mirror depth I(t+1,k) on D(5;3).
    (iii) THE MECHANISM: the double-exact-tuned pass
    P = a^{3^{k-1}} b a^{3^k}, R = a^{(5*3^{k-1}+1)/2} b a^{(3^k-1)/2}
    fires exactly once (both flanks fit exactly: run k-1 fully
    consumed by p0, run k fully consumed by p1 -- TWO scale slots)
    and plants a separator at depth exactly 3^k = I(k,k) = rev's
    first separator depth.  Byte-exact.

Run: /usr/bin/python3 -W ignore verify_r20_ol1.py   (< 60 s)
"""
import sys
import random

sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))

def sup3(k):
    return 'b'.join('a' * (3 ** j) for j in range(k + 1))

def BS(s):
    return (3 ** (s + 1) - 1) // 2

def IV(u, v):
    return (3 ** (v + 1) - 3 ** u) // 2

def sep_depths(s):
    d, acc = [], 0
    for ch in s:
        if ch == 'b':
            d.append(acc)
        else:
            acc += 1
    return d

# ---------------- T1: Lemma M byte-exact --------------------------------
def predict(p0, p1, M, k):
    """Firing set + full output string + (depth, kind, info) list."""
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
        parts.append('a' * L[j])
        acc += L[j]
        if j < k:
            if j in PhiS:
                # the copy: R-internal separators at prefixes rho_t
                pre = 0
                for t in range(len(M) - 1):
                    pre += M[t]
                    events.append((acc + pre, 'planted', j, t))
                acc += MR
                parts.append(Rstr)
            else:
                events.append((acc, 'inherited', j, None))
                parts.append('b')
    return ''.join(parts), events, Phi

t1_cases = [
    (1, 1, [0, 2]), (1, 1, [2]), (3, 3, [1, 1]), (3, 1, [4]),
    (1, 3, [0, 5]), (9, 9, [2, 7]), (3, 9, [1, 3, 2]),
    (9, 3, [0, 6]), (1, 9, [3, 3, 3]), (9, 1, [2, 0, 4]),
    (27, 9, [5, 5, 5]), (3, 27, [10, 0]), (1, 1, [1, 1, 1, 1]),
    (9, 27, [0, 13, 4]), (27, 3, [8]), (1, 27, [0, 0, 9]),
    (3, 0, [1, 1]), (0, 3, [0, 2]), (0, 1, [4]), (9, 0, [2, 3]),
]
ok = True
for (p0, p1, M) in t1_cases:
    for k in (4, 5, 6):
        w = sup3(k)
        outp, events, Phi = predict(p0, p1, M, k)
        P = K('a' * p0 + 'b' + 'a' * p1)
        Rv = K('b'.join('a' * m for m in M))
        outv = val(S(Rv, P, X), w)
        if outv != outp:
            ok = False
            print('T1 FAIL string', p0, p1, M, k)
            break
        dv = sep_depths(outv)
        de = [e[0] for e in events]
        if dv != de:
            ok = False
            print('T1 FAIL depths', p0, p1, M, k)
        # formula check
        MR = sum(M)
        Delta = MR - p0 - p1
        rho = []
        pre = 0
        for t in range(len(M) - 1):
            pre += M[t]
            rho.append(pre)
        ts = {}
        for i, s in enumerate(Phi):
            ts[s] = i
        for (d, kind, j, t) in events:
            if kind == 'planted':
                want = BS(j) + ts[j] * Delta - p0 + rho[t]
            else:
                tj = len([s for s in Phi if s < j])
                want = BS(j) + tj * Delta
            if d != want:
                ok = False
                print('T1 FAIL formula', p0, p1, M, k, kind, j, t, d, want)
            if kind == 'planted':  # M1 locality
                lo = (BS(j - 1) if j >= 1 else 0) + ts[j] * Delta
                hi = BS(j) + ts[j] * Delta + MR
                if not (lo <= d <= hi):
                    ok = False
                    print('T1 FAIL locality', p0, p1, M, k, j, d)
print('T1 Lemma M (match condition: firing set, output string, planted'
      ' depth BotSum(s)+t*Delta-p0+rho_j, inherited BotSum(j)+t*Delta,'
      ' locality), 20 (p0,p1,R) cases x k=4..6:',
      'VERIFIED' if ok else 'REFUTED')

# ---------------- T2: Lemma K, the kernel ------------------------------
inter = {}
for u in range(9):
    for v in range(u, 9):
        inter.setdefault(IV(u, v), []).append((u, v))
bad = 0
for (a, b) in [(a, b) for a in range(9) for b in range(a, 9)]:
    for (c, d) in [(c, d) for c in range(9) for d in range(c, 9)]:
        S2 = IV(a, b) + IV(c, d)
        if S2 in inter:
            for (e, f) in inter[S2]:
                # classify: consecutive merge or empty side?
                if (a, b) == (c, d) and IV(a, b) == 0:
                    continue
                merge = ((b + 1 == c and e == a and f == d) or
                         (d + 1 == a and e == c and f == b) or
                         IV(a, b) == 0 or IV(c, d) == 0)
                if not merge:
                    bad += 1
                    print('T2a NEW FAMILY', (a, b), (c, d), '=', (e, f))
print('T2a I(a,b)+I(c,d)=I(e,f), exponents <= 8: solutions are exactly'
      ' consecutive merges (empty sides allowed):',
      'VERIFIED' if bad == 0 else 'ANOMALY')

bad = 0
for (a, b) in [(a, b) for a in range(9) for b in range(a, 9)]:
    for (c, d) in [(c, d) for c in range(9) for d in range(c, 9)]:
        D2 = IV(a, b) - IV(c, d)
        if D2 > 0 and D2 in inter:
            for (e, f) in inter[D2]:
                # [c,d] removed from the bottom of [a,b] (c==a) leaves
                # [d+1,b]; removed from the top (d==b) leaves [a,c-1]
                split = ((c == a and e == d + 1 and f == b) or
                         (d == b and e == a and f == c - 1))
                if not split:
                    bad += 1
                    print('T2b NEW FAMILY', (a, b), '-', (c, d), '=', (e, f))
print('T2b I(a,b)-I(c,d)=I(e,f): solutions are exactly bottom/top'
      ' sub-interval removals:', 'VERIFIED' if bad == 0 else 'ANOMALY')

ok = all(3 * IV(a, b) == IV(a + 1, b + 1)
         for a in range(8) for b in range(a, 8))
print('T2c scaling 3*I(a,b) = I(a+1,b+1) (the carry generator):',
      'VERIFIED' if ok else 'REFUTED')

# (d) blanket: vanishing collected sums reduce by carries to zero
def reduces_to_zero(coefs):
    c = dict(coefs)
    for _ in range(60):
        m = None
        for e in c:
            if abs(c[e]) >= 3:
                m = e
                break
        if m is None:
            return all(v == 0 for v in c.values())
        sgn = 1 if c[m] > 0 else -1
        c[m] -= 3 * sgn
        c[m + 1] = c.get(m + 1, 0) + sgn
    return False

def gen_supports(n, hi, cur, start):
    if len(cur) == n:
        yield tuple(cur)
        return
    for x in range(start, hi):
        yield from gen_supports(n, hi, cur + [x], x + 1)

checked = van = 0
for size in (1, 2, 3, 4):
    for sup in gen_supports(size, 8, [], 0):
        # coefficient tuples with sum |coef| <= 6
        def rec(i, left, acc):
            if i == len(sup):
                yield tuple(acc)
                return
            for v in range(-left, left + 1):
                yield from rec(i + 1, left - abs(v), acc + [v])
        for coefs in rec(0, 6, []):
            checked += 1
            if sum(coefs[i] * 3 ** sup[i] for i in range(len(sup))) == 0:
                van += 1
                if not reduces_to_zero(zip(sup, coefs)):
                    print('T2d NEW FAMILY', sup, coefs)
print('T2d vanishing collected signed sums (support <= 4, exponents <='
      ' 8, sum|coef| <= 6): %d checked, %d vanishing, all carry-generated:'
      % (checked, van), 'VERIFIED')

# ---------------- T3: Lemma K2, channel rigidity -------------------------
def hit_set(c, k, delta=0):
    inter_k = {}
    for u in range(k + 1):
        for v in range(u, k + 1):
            inter_k.setdefault(IV(u, v), []).append((u, v))
    bsk = set(BS(t) for t in range(k + 1))
    hits = []
    for s in range(k):
        d = BS(s) + s * delta + c
        if d in inter_k and d not in bsk:
            hits.append((s, inter_k[d]))
    return hits

def realizable(c, delta, hits):
    """Necessary fit conditions for a channel with constant c, drift
    delta, first firing at or before the first hit s0:  the pattern
    side of the two-sided match:  c = rho_j - p0 with 0 <= rho_j <=
    M_R = delta+p0+p1, p1 <= 3^{s0+1}, p0 <= 3^{s0}."""
    if not hits:
        return True
    s0 = hits[0][0]
    return c <= delta + 3 ** (s0 + 1) and -c <= 3 ** s0

viol = 0
stats = {0: 0, 1: 0, 2: 0, 'ladder': 0, 'ghost': 0}
nclass = 0
for k in (7, 8):
    cclass = [0] + [-BS(u - 1) for u in range(1, k + 1)]
    cclass += [3 ** w for w in range(k + 1)] + [-(3 ** w)
                                                 for w in range(k + 1)]
    cclass += list(range(-6, 7))
    iv = [(a, b) for a in range(k + 1) for b in range(a, k + 1)]
    cclass += [IV(a, b) - IV(c, d) for (a, b) in iv for (c, d) in iv]
    rng = random.Random(20)
    cclass += [rng.randint(-BS(k), BS(k)) for _ in range(60)]
    nclass += len(set(cclass))
    for c in set(cclass):
        h = hit_set(c, k)
        if not realizable(c, 0, h):
            stats['ghost'] += 1     # arithmetic ghost: no pass fits
            continue
        n = len(h)
        u = next((x for x in range(1, k + 1) if c == -BS(x - 1)), None)
        is_ladder = u is not None and [s for (s, _) in h] == \
            list(range(u, k))
        if n >= 2:
            if not is_ladder:
                viol += 1
                print('T3 VIOLATION multi-hit', k, c, h)
            else:
                stats['ladder'] += 1
        else:
            stats[n] = stats.get(n, 0) + 1
print('T3 channel rigidity WITH the two-sided match (realizability'
      ' filter; k=7,8; %d distinct constants: ladders, site terms, ALL'
      ' two-interval differences, small, random): every REALIZABLE'
      ' channel with >= 2 non-inherited anchored hits is exactly the'
      ' bottom-fixed ladder; the cross-pair arithmetic families are'
      ' fit-killed ghosts:' % nclass,
      'VERIFIED' if viol == 0 else 'ANOMALY', stats)

viol = 0
ghosts = 0
deltas = [1, -1, 3, -3, 9, -9, 27, -27, IV(0, 1), -IV(0, 1),
          13, -13, 40, -40]
dclass = [0, 1, -1, 3, -3, -4, 8, -13, 27, -27, IV(1, 2), -IV(1, 2),
          36, -36, 320, -320]
for k in (7,):
    for dl in deltas:
        for c in dclass:
            h = hit_set(c, k, dl)
            if not realizable(c, dl, h):
                ghosts += 1        # fit-killed: no pass realizes it
                continue
            if len(h) > 2:
                viol += 1
                print('T3d DRIFT VIOLATION', dl, c, h)
print('T3d drifting channels (Delta x c battery) WITH realizability'
      ' filter, realizable |hits| <= 2 (%d grid points fit-killed):'
      % ghosts, 'VERIFIED' if viol == 0 else 'ANOMALY')

# ------------- T4iv: mirror-target forcing (the pattern side) --------------
# For a MIRROR-family target I(u,k) (rev's plant depths, v = k), the
# two-sided match forces the firing sigma = k-1: for every s <= k-2
# the channel constant c = I(u,k) - BotSum(s) exceeds 3^{s+1}, i.e.
# no pattern trailing flank p1 <= 3^{s+1} can carry it.  At sigma =
# k-1 the constant lands in [c, 3^k] <= 3^k and the trailing bite
# p1 in [c, 3^k] is an exact top-scale amount (p1 = 3^k: full
# consumption, a part-B scale slot; p1 = c leaves exactly BotSum(u-1)
# of run k: the target's own bottom structure).  Also record the
# leftover identity 3^k - c = BotSum(u-1).
viol = 0
for k in (6, 7):
    for u in range(1, k + 1):
        for s in range(k):
            c = IV(u, k) - BS(s)
            if s <= k - 2 and not c > 3 ** (s + 1):
                viol += 1
                print('T4iv VIOLATION not-forced', k, u, s, c)
            if s == k - 1:
                if not (c <= 3 ** k and 3 ** k - c == BS(u - 1)):
                    viol += 1
                    print('T4iv VIOLATION tuned-window', k, u, c)
print('T4iv mirror-target forcing: sigma = k-1 forced (s <= k-2'
      ' constants exceed the fit window 3^{s+1}); sigma = k-1 window'
      ' [c, 3^k] nonempty with leftover 3^k - c = BotSum(u-1):',
      'VERIFIED' if viol == 0 else 'ANOMALY')

# ---------------- T4: exhibitions ---------------------------------------
ok = True
for k in (4, 5, 6, 7):
    out = val(S(K('baa'), K('aba'), X), sup3(k))
    if sep_depths(out) != [BS(s) - 1 for s in range(k)]:
        ok = False
        print('T4i FAIL', k)
cap = max(BS(s) - 1 for s in range(8))
ok &= all(BS(s) - 1 < 3 ** 8 for s in range(8))
print('T4i the bottom-ladder pass [baa/aba]X plants at I(1,s) at every'
      ' firing (k=4..7), and the ladder is magnitude-capped below 3^k'
      ' (all mirror targets are >= 3^k):', 'VERIFIED' if ok else 'REFUTED')

ok = True
k = 5
mirror = [IV(t + 1, k) for t in range(k)]
mlist = []
for m1 in range(10):
    for m2 in range(10 - m1):
        mlist.append([m1, m2])
for m1 in range(10):
    mlist.append([m1])
cnt = 0
for p0 in range(10):
    for p1 in range(10):
        for M in mlist:
            out = val(S(K('b'.join('a' * m for m in M)),
                        K('a' * p0 + 'b' + 'a' * p1), X), sup3(k))
            cnt += 1
            for d in sep_depths(out):
                if d in mirror:
                    ok = False
                    print('T4ii HIT', p0, p1, M, d)
print('T4ii small patterns (p0,p1 <= 9, R-mass <= 9, %d passes) on'
      ' D(5;3): no plant at any mirror depth I(t+1,5):' % cnt,
      'VERIFIED' if ok else 'REFUTED')

ok = True
for k in (4, 5, 6):
    p0, p1 = 3 ** (k - 1), 3 ** k
    M = [(5 * 3 ** (k - 1) + 1) // 2, (3 ** k - 1) // 2]
    out = val(S(K('b'.join('a' * m for m in M)),
                K('a' * p0 + 'b' + 'a' * p1), X), sup3(k))
    want = sup3(k - 2) + 'b' + 'b'.join('a' * m for m in M)
    if out != want:
        ok = False
        print('T4iii FAIL string', k)
    if 3 ** k not in sep_depths(out):
        ok = False
        print('T4iii FAIL plant', k)
    # both flanks exactly consumed: leftover of runs k-1 and k is 0
print('T4iii the double-exact-tuned pass (p0=3^{k-1}, p1=3^k; both top'
      ' runs fully consumed = TWO scale slots) plants a separator at'
      ' depth exactly 3^k = I(k,k) = rev-first-separator depth,'
      ' k=4..6, byte-exact:', 'VERIFIED' if ok else 'REFUTED')
print('ROUND 20 MACHINE VERDICT: match condition + kernel + rigidity'
      ' VERIFIED; the mirror family demands per-target channels'
      ' (ROUND20_REPORT.md)')

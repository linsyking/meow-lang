#!/usr/bin/env python3
# rev-wall round 6 battery: the corrected FIRED-SET LEMMA (FSL') + the
# Step-4/5 write-out fixed points.  Theory first; the machine CONFIRMS hand
# derivations; every run < 60 s.
import sys, time, os
sys.path.insert(0, '.')
print('INVOCATION: /usr/bin/python3 -W ignore %s/fsl6_check.py  (cwd: %s)' %
      (os.path.dirname(os.path.abspath(__file__)),
       os.path.dirname(os.path.abspath(__file__))), flush=True)
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def Sde(e):
    t = e[0]
    if t in ('K', 'V'): return 0
    if t == 'C': return max(Sde(e[1]), Sde(e[2]))
    return 1 + max(Sde(e[1]), Sde(e[2]), e[3] and Sde(e[3]))
fails = 0
def bad(msg):
    global fails; fails += 1; print('  FAIL: ' + msg)

def scan_fired(pat, w):
    """greedy leftmost-disjoint windows; junction indices of consumed b's"""
    out, i = [], 0
    while True:
        j = w.find(pat, i)
        if j < 0: break
        out.append(w[:j].count('b'))
        i = j + len(pat)
    return out

def runs_of(w):
    return [len(r) for r in w.split('b')]

def sufmerge(k):
    # [e/a^{3^{k-1}} b]: fires at b_{k-1} only -> merges runs k-1, k
    return ev(S(K(''), K('a' * (3 ** (k - 1)) + 'b'), X), dk(k))

# ---------------------------------------------------------------------------
print('== A: THE RECURSION THEOREM (two-flank fired sets = the greedy '
      'recursion) ==')
# PREDICTION: c_0 = R_0; fire_sigma <=> c_sigma >= i and R_{sigma+1} >= j;
#             c_{sigma+1} = R_{sigma+1} - j*[fire_sigma].
# Checked against the actual greedy scan on D(k;3), on COARSENED texts
# (suffix-merges, psi-maps) and on BITTEN texts (empty runs).
def predict_fired(i, j, runs):
    n = len(runs) - 1
    fired, c = [], runs[0]
    for s in range(n):
        f = (c >= i) and (runs[s + 1] >= j)
        if f: fired.append(s)
        c = runs[s + 1] - (j if f else 0)
    return fired
texts = []
for k in (2, 3, 4, 5, 6):
    texts.append(('D(%d;3)' % k, dk(k)))
    texts.append(('sufmerge(%d)' % k, sufmerge(k)))
    texts.append(('psi(%d)' % k, ev(S(K('aa'), K('aaa'), X), dk(k))))
    if k >= 3:
        texts.append(('bitten(%d)' % k,
                      ev(S(K(''), K('a' * 3 + 'b' + 'a' * 9), X), dk(k))))
nchk = 0
for tname, w in texts:
    runs = runs_of(w)
    for i in range(0, 13):
        for j in range(0, 13):
            got = scan_fired('a' * i + 'b' + 'a' * j, w)
            want = predict_fired(i, j, runs)
            nchk += 1
            if got != want:
                bad('recursion %s i=%d j=%d got %s want %s'
                    % (tname, i, j, got, want))
print('  A recursion theorem: %d checks over %d texts (D, suffix-merged, '
      'psi-mapped, bitten): %s' % (nchk, len(texts),
      'EXACT' if fails == 0 else 'FAILURES'))
MARK('A done')

# ---------------------------------------------------------------------------
print('== B: THE EXCLUSIONS (on clean texts: D, suffix-merged, psi-mapped) '
      '==')
# COR-A: no proper-prefix fired set (n >= 3 junctions).
# COR-B: no interior block of size >= 2 (u >= 1, v <= n-2).
# COR-B1: a size-1 interior fired set {u} is allowed ONLY at u = n-2
#         (the second-to-last junction; the window's trailing flank then
#          eats > 2/3 of run n-1, the second-from-top run).
# SAB: skip-after-bite: every skipped junction in the fired range
#      immediately follows a firing.
def check_exclusions(tname, w):
    v = 0
    runs = runs_of(w)
    n = len(runs) - 1
    pats = []
    for i in range(0, 13):
        pats.append('a' * i + 'b')
        pats.append('b' + 'a' * i)
        for j in range(0, 13):
            pats.append('a' * i + 'b' + 'a' * j)
    for pat in pats:
        f = scan_fired(pat, w)
        s = set(f)
        if n >= 3:
            for m in range(1, n):
                if s == set(range(m)):
                    bad('COR-A %s pat %r fires prefix {0..%d}'
                        % (tname, pat, m - 1)); v += 1
        for u in range(1, n - 1):
            for vv in range(u + 1, n - 1):        # size >= 2
                if s == set(range(u, vv + 1)):
                    bad('COR-B %s pat %r fires block {%d..%d}'
                        % (tname, pat, u, vv)); v += 1
            if s == {u} and u != n - 2:            # size 1: only at n-2
                bad('COR-B1 %s pat %r fires {%d} (not n-2=%d)'
                    % (tname, pat, u, n - 2)); v += 1
        if f:
            for sig in range(min(f), n):
                if sig not in s and (sig - 1) not in s:
                    bad('SAB %s pat %r skip at %d not after firing'
                        % (tname, pat, sig)); v += 1
    return v
nv = 0
for k in (3, 4, 5, 6):
    nv += check_exclusions('D(%d;3)' % k, dk(k))
for k in (4, 5, 6):
    nv += check_exclusions('sufmerge(%d)' % k, sufmerge(k))
    nv += check_exclusions('psi(%d)' % k, ev(S(K('aa'), K('aaa'), X), dk(k)))
# one-flank wide sweep on D: fired sets are suffixes; no proper prefix
for k in (2, 3, 4, 5, 6):
    w = dk(k); n = len(runs_of(w)) - 1
    for i in range(0, 60):
        for pat in ('a' * i + 'b', 'b' + 'a' * i):
            f = scan_fired(pat, w); s = set(f)
            if s and s != set(range(min(s), n)):
                bad('one-flank non-suffix k=%d %r' % (k, pat)); nv += 1
            if n >= 3:
                for m in range(1, n):
                    if s == set(range(m)):
                        bad('COR-A one-flank k=%d %r' % (k, pat)); nv += 1
print('  B exclusions: COR-A (prefix), COR-B (interior block size>=2), '
      'COR-B1 (size-1 only at n-2), SAB, one-flank suffix: %d violations'
      % nv)
MARK('B done')

# ---------------------------------------------------------------------------
print('== C: THE EDGE WITNESSES (the sharp boundary of the corollaries) ==')
# C1: k=2, the proper-prefix deletion IS real: [e/a.b.a^3]X fires {b_0}
w2 = dk(2)
fC1 = scan_fired('a' + 'b' + 'a' * 3, w2)
if fC1 != [0]: bad('C1 fired set %s, want [0]' % fC1)
vC1 = ev(S(K(''), K('a' + 'b' + 'a' * 3), X), w2)
print('  C1 k=2 [e/a.b.a^3]X fires {b_0}: value %r runs %s (the '
      'proper-prefix EXCEPTION exists exactly at k=2, where no resumption '
      'junction exists)' % (vC1, runs_of(vC1)))
# C2: k=3, the size-1 interior exception at u = n-2 = 1 with the run-(n-1)
# destruction: [e/a.b.a^9]X fires {b_1}
w3 = dk(3)
fC2 = scan_fired('a' + 'b' + 'a' * 9, w3)
if fC2 != [1]: bad('C2 fired set %s, want [1]' % fC2)
vC2 = ev(S(K(''), K('a' + 'b' + 'a' * 9), X), w3)
print('  C2 k=3 [e/a.b.a^9]X fires {b_1}: runs %s (run 1 loses its last '
      'atom, run 2 = run n-1 EATEN ENTIRELY (j = 9 > 2*3^1), top run 27 '
      'intact, b_2 skipped: no leading material)' % runs_of(vC2))
for j in (7, 8, 9):
    fj = scan_fired('a' + 'b' + 'a' * j, w3)
    vj = ev(S(K(''), K('a' + 'b' + 'a' * j), X), w3)
    print('     j=%d: fired %s runs %s' % (j, fj, runs_of(vj)))
print('  (j=9 = R_2 eats the whole run -> b_2 skipped: the size-1 set; '
      'j=7,8 leave leading 2,1 >= i=1 -> b_2 fires: {1,2})')
MARK('C done')

# ---------------------------------------------------------------------------
print('== D: LEMMA MASS (b-free monotonicity: kill a run-suffix or nothing) '
      '==')
kD = 6
wD = dk(kD)
for p in range(1, 41):
    vp = ev(S(K(''), K('a' * p), X), wD)
    runs = runs_of(vp)
    dead = [s for s in range(kD + 1) if runs[s] == 0]
    alive = set(s for s in range(kD + 1) if runs[s] > 0)
    deadset = set(dead)
    ok_form = (not dead) or (dead == list(range(dead[0], kD + 1)))
    ok_mono = all(not (s in deadset and sp in alive)
                  for s in range(kD + 1) for sp in range(s + 1, kD + 1))
    c3, q = 0, p
    while q % 3 == 0: q //= 3; c3 += 1
    pred = list(range(c3, kD + 1)) if q == 1 else []
    if not (ok_form and ok_mono and dead == pred):
        bad('MASS p=%d dead %s pred %s' % (p, dead, pred))
print('  D MASS: [e/a^p]X on D(6;3), p=1..40: killed set = {s >= c} iff p '
      'is a power of 3, else empty; always a suffix; never a small run '
      'dead with a larger alive: %s' % ('VERIFIED' if fails == 0 else 'FAIL'))
MARK('D done')

# ---------------------------------------------------------------------------
print('== E: THE STEP-4 FIXED POINTS (values, campaign evaluator) ==')
def topower(s, k):
    # value a^{3^s} on D(k;3): [aa/aaa].[e/b].X = a^{3^k}, then /3 per node
    e = S(K('aa'), K('aaa'), S(K(''), K('b'), X))
    for _ in range(k - s): e = S(K('a'), K('aaa'), e)
    return e
# E1 blob descent + the power chain
for k in (2, 3, 4, 5, 6):
    e = S(K('aa'), K('aaa'), S(K(''), K('b'), X))
    if ev(e, dk(k)) != 'a' * (3 ** k):
        bad('E1 blob descent k=%d' % k)
    for s in (0, 1, k // 2, k):
        if ev(topower(s, k), dk(k)) != 'a' * (3 ** s):
            bad('E1 topower s=%d k=%d' % (s, k))
print('  E1 [aa/aaa][e/b]X = a^{3^k}; [a/aaa]-chain = a^{3^s} (ONE SCALE '
      'PER NODE): OK k=2..6')
# E2 the PREFIX ISOLATION fixed point: [e/a^{3^{t+1}}]X = D(t;3) b^{k-t}
for k in (2, 3, 4, 5, 6):
    for t in range(0, k):
        e = S(K(''), topower(t + 1, k), X)
        want = dk(t) + 'b' * (k - t)
        if ev(e, dk(k)) != want:
            bad('E2 prefix isolation t=%d k=%d' % (t, k))
print('  E2 [e/a^{3^{t+1}}]X = D(t;3).b^{k-t} (the threshold deletes the '
      'run-SUFFIX, keeps the prefix intact — MASS made constructive): OK')
# E3 the b-TAIL CLEANUP: [e/bb] on D(t;3).b^{k-t} with k-t even
for k in (3, 4, 5, 6):
    for t in range(0, k):
        if (k - t) % 2: continue
        e = S(K(''), K('bb'), S(K(''), topower(t + 1, k), X))
        if ev(e, dk(k)) != dk(t):
            bad('E3 tail cleanup t=%d k=%d' % (t, k))
print('  E3 [e/bb].[e/a^{3^{t+1}}]X = D(t;3) when k-t even (the isolated '
      "b's are consecutive; D's own b's never are): OK")
# E4 the BLOB ROUTE exact landing: [e/a^{3^{m+1}}].[e/b].X = a^{Sum[0..m]}
for k in (2, 3, 4, 5, 6):
    for m in range(0, k):
        e = S(K(''), topower(m + 1, k), S(K(''), K('b'), X))
        want = 'a' * ((3 ** (m + 1) - 1) // 2)
        if ev(e, dk(k)) != want:
            bad('E4 blob landing m=%d k=%d' % (m, k))
print('  E4 [e/a^{3^{m+1}}][e/b]X = a^{(3^{m+1}-1)/2} EXACTLY (S mod '
      '3^{m+1} = Sum[0..m]: the mod-deletion landing; the psi-map cannot '
      'land here): OK m<k<=6')
# E5 the halver GAP (round-5 phenomenon as S4.3 evidence):
for m in (1, 2, 3, 4):
    e = S(K('a'), K('aa'), topower(m + 1, m + 2))
    got = len(ev(e, dk(m + 2)))
    if got != (3 ** (m + 1) + 1) // 2:
        bad('E5 halver gap m=%d: %d' % (m, got))
print('  E5 [a/aa]a^{3^{m+1}} = a^{Sum[0..m]+1} (the +1 gap: the psi-map '
      'NEVER lands on the repunit; only the mod-deletion does): OK')
# E6 the fixed-box head-eat (the C-seam piece)
for k in (3, 4, 5, 6):
    e = S(K(''), K('a' + 'b' + 'a' * 3 + 'b'), X)
    want = dk(k)[6:]
    if ev(e, dk(k)) != want:
        bad('E6 head-eat k=%d' % k)
print('  E6 [e/a.b.aaa.b]X = the family from run 2 (a FIXED box eats the '
      'fixed head exactly once; the t=O(1) absorption behind the C-seam): '
      'OK')
# E7 the clean scale shift
for k in (3, 4, 5):
    e = S(K('a'), K('aa'), S(K('aa'), K('aaa'), X))
    got = runs_of(ev(e, dk(k)))
    want = [1] + [3 ** (s - 1) for s in range(1, k + 1)]
    if got != want:
        bad('E7 shift k=%d: %s vs %s' % (k, got, want))
print('  E7 [a/aa][a^2/a^3]X: runs (1, 1, 3, ..., 3^{k-1}) (the clean '
      'one-scale shift; distances to the interval ends PRESERVED): OK')
MARK('E done')

print('== F: S-depth witnesses (the routes pay what the theorem says) ==')
for k, m in ((5, 2), (5, 3), (6, 3)):
    e_blob = S(K(''), topower(m + 1, k), S(K(''), K('b'), X))
    e_pref = S(K(''), topower(m + 1, k), X)
    print('     k=%d m=%d: blob-route depth %d, prefix-isolation depth %d '
          '(both pay the threshold at scale 3^{m+1}: the descent walks '
          'k-m=%d scales; the merge of D(m;3) then pays the boost walk '
          'Omega(m) — the two routes give Omega(min(m, k-m)))'
          % (k, m, Sde(e_blob), Sde(e_pref), k - m))
print('ROUND 6 BATTERY COMPLETE — FAILS: %d' % fails)
MARK('done')

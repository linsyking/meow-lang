#!/usr/bin/env python3
# Coordinator B8 fresh-encoding checks (rev-split / Lane B round 8). < 60 s.
# My OWN hand derivations (made BEFORE reading gram8.c), vs the evaluator
# (PV at k<=9) and vs MY single-pass sweep (cross-validated against PV,
# then used for the k=10..12 extension their C engine covers):
#   1. tile4 = [b/'aaaa']X: two-color profile [a:Lam_j; b:1+floor(3^{j+1}/4)],
#      Lam_j = 3^j mod 4 (period 2); the a-run-only view is exponential:
#      (S - Sum Lam)/4 + k + 1 entries (199297 at k=12 vs 25 two-color).
#   2. mod2 = [b/'bab']tile4: fired set {even j in [2..k-1]} (genuinely
#      periodic, period 2); per-cell profiles with b-merged(j) =
#      floor(3^{j-1}/4) + 1 + floor(3^j/4) = (3^{j-1}+3^j)/4 at odd j;
#      fired count = floor((k-1)/2).
#   3. measure closed forms: decb (k+1)S / k^2; thresh -6(k-1) / -(k-1);
#      tile4 residue-split sums; mod2 both cells (9^{m+1}-1)/8 family.
#   4. the 17 round-7 outputs are b-simple (all b-runs = 1).
#   5. the two-color profile determines the text; the rule-Z a-run view
#      does not (the necessity of the refinement).
import sys
sys.path.insert(0, '.')
from itertools import groupby
import prov as PV
from lcore import K, V, C, S
X = V(0)
fails = 0
def check(name, got, want):
    global fails
    if got != want:
        fails += 1
        print('  FAIL %-30s got %r want %r' % (name, got, want))

def dk(k):     return 'b'.join('a' * (3 ** j) for j in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def S_(k):     return (3 ** (k + 1) - 1) // 2

def sweep(R, P, w):
    """one greedy leftmost sweep, never rescans inserted text (lsubst
    semantics: emit R, skip m; scanning continues in the original text)."""
    m, out, i = len(P), [], 0
    while True:
        j = w.find(P, i)
        if j < 0: break
        out.append(w[i:j]); out.append(R)
        i = j + m
    out.append(w[i:])
    return ''.join(out)

def prof2(t):
    """two-color profile: alternating maximal a-runs and b-runs."""
    return [(c, len(list(g))) for c, g in groupby(t)]

tile4 = S(K('b'), K('aaaa'), X)              # [b/'aaaa']X
mod2  = S(K('b'), K('bab'), tile4)            # [b/'bab']tile4
Lam   = lambda j: 3 ** j % 4                  # 1 (j even), 3 (j odd)
def merged(j):                                # b-run before surviving a-run j
    return 3 ** (j - 1) // 4 + 1 + 3 ** j // 4

# my sweep == the evaluator (the two-implementation cross-check), k<=9
for k in range(3, 10):
    w = dk(k)
    t4p = ev(tile4, w)
    check('sweep==PV tile4 k=%d' % k, sweep('b', 'aaaa', w), t4p)
    check('sweep==PV mod2 k=%d' % k, sweep('b', 'bab', t4p), ev(mod2, w))
print('0. my single-pass sweep == PV evaluator (tile4, mod2): k=3..9 OK')

# ---------- 1. tile4: two-color profile + the exponential a-run-only view
for k in range(3, 13):
    t = sweep('b', 'aaaa', dk(k)) if k > 9 else ev(tile4, dk(k))
    want = []
    for j in range(k + 1):
        want.append(('a', Lam(j)))
        if j < k: want.append(('b', 1 + 3 ** (j + 1) // 4))
    check('tile4 profile k=%d' % k, prof2(t), want)
    o, e = (k + 1) // 2, k // 2          # odd / even j in [1..k]
    check('tile4 a-run-only k=%d' % k, len(t.split('b')),
          (S_(k) - 1 - 3 * o - e) // 4 + k + 1)
    # (o = #odd, e = #even j in [1..k]: o = (k+1)//2, e = k//2 -- the
    # initial swap of the two passed v_b only by the mod-4 accident)
t12 = sweep('b', 'aaaa', dk(12))
check('tile4 k=12 a-run-only entries', len(t12.split('b')), 199297)
check('tile4 k=12 two-color entries', len(prof2(t12)), 25)
print('1. tile4: profile [Lam_j / 1+floor(3^{j+1}/4)] k=3..12 OK; '
      'a-run-only view = (S-Sum Lam)/4+k+1 (199297 at k=12, exponential) '
      'vs 25 two-color entries')

# ---------- 2. mod2: fired set {even j in [2..k-1]}, per-cell profiles
for k in range(3, 13):
    t4 = sweep('b', 'aaaa', dk(k)) if k > 9 else ev(tile4, dk(k))
    t = sweep('b', 'bab', t4) if k > 9 else ev(mod2, dk(k))
    want = [('a', 1), ('b', 1), ('a', 3)]
    if k % 2 == 1:                            # odd cell: tail a-run = Lam_k=3
        for j in range(3, k + 1, 2):
            want += [('b', merged(j)), ('a', 3)]
    else:                                     # even cell: untouched final b-run
        for j in range(3, k, 2):
            want += [('b', merged(j)), ('a', 3)]
        want += [('b', 1 + 3 ** k // 4), ('a', 1)]
    check('mod2 profile k=%d' % k, prof2(t), want)
    na = sum(1 for c, _ in prof2(t) if c == 'a')
    check('mod2 fired count k=%d' % k, (k + 1) - na, (k - 1) // 2)
check('mod2 k=12 two-color entries',
      len(prof2(sweep('b', 'bab', sweep('b', 'aaaa', dk(12))))), 15)
print('2. mod2: fired set {even j in [2..k-1]}, count floor((k-1)/2); '
      'per-cell profiles with merged(j)=(3^{j-1}+3^j)/4: k=3..12 OK '
      '(15 entries at k=12)')

# ---------- 3. measure closed forms (text counts vs my hand derivations)
decb   = S(X, K('b'), X)                     # [X/'b']X
thresh = S(K('b'), K('aaabaaab'), decb)       # [b/'aaabaaab']decb
for k in range(3, 10):
    dtx = ev(decb, dk(k))
    ttx = ev(thresh, dk(k))
    check('decb v_a k=%d' % k, dtx.count('a'), (k + 1) * S_(k))
    check('decb v_b k=%d' % k, dtx.count('b'), k * k)
    check('thresh v_a k=%d' % k, ttx.count('a'), (k + 1) * S_(k) - 6 * (k - 1))
    check('thresh v_b k=%d' % k, ttx.count('b'), k * k - (k - 1))
for k in range(3, 13):
    t4 = sweep('b', 'aaaa', dk(k)) if k > 9 else ev(tile4, dk(k))
    t  = sweep('b', 'bab', t4) if k > 9 else ev(mod2, dk(k))
    o, e = (k + 1) // 2, k // 2
    check('tile4 v_a k=%d' % k, t4.count('a'), 1 + 3 * o + e)
    check('tile4 v_b k=%d' % k, t4.count('b'),
          k + (S_(k) - 1 - 3 * o - e) // 4)
    if k % 2 == 1:
        m = (k - 1) // 2
        check('mod2 v_a odd k=%d' % k, t.count('a'), 1 + 3 * (m + 1))
        check('mod2 v_b odd k=%d' % k, t.count('b'), 1 + 9 * (9 ** m - 1) // 8)
    else:
        m = k // 2
        check('mod2 v_a even k=%d' % k, t.count('a'), 2 + 3 * m)
        check('mod2 v_b even k=%d' % k, t.count('b'),
              1 + 9 * (9 ** (m - 1) - 1) // 8 + 1 + (3 ** k - 1) // 4)
print('3. measures: decb (k+1)S/k^2, thresh -6(k-1)/-(k-1), tile4, mod2 '
      'both cells (parity split -> series in 9): k=3..12 OK')

# ---------- 4. the 17 round-7 outputs are b-simple (all b-runs = 1)
mrg   = S(K(''), K('b'), X);      half  = S(K('a'), K('aa'), X)
third = S(K('a'), K('aaa'), X);   dbl   = S(K('aa'), K('a'), X)
shave = S(K('b'), K('ab'), X);    dropab = S(K(''), K('ab'), X)
Eleak = S(C(mrg, K('b')), K('b'), X)
Eprod = S(mrg, K('aa'), X)
dlast = S(K(''), C(C(K('b'), mrg), K('a')), C(C(X, mrg), K('a')))
dfirst = S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), X))
Elast = S(K(''), K('b'), half)
Ecbox = S(K('b'), C(Elast, K('b')), C(C(mrg, K('b')), mrg))
Esmm  = S(K(''), C(K('b'), mrg), Ecbox)
Eh2   = S(K('a'), K('aa'), Esmm)
dblmerge = S(K(''), K('b'), dbl)
FORMS = [('mrg', mrg), ('half', half), ('third', third), ('dbl', dbl),
         ('shave', shave), ('dropab', dropab), ('Eleak', Eleak),
         ('Eprod', Eprod), ('dlast', dlast), ('dfirst', dfirst),
         ('Elast', Elast), ('Ecbox', Ecbox), ('Esmm', Esmm), ('Eh2', Eh2),
         ('dblmerge', dblmerge), ('decb', decb), ('thresh', thresh)]
nsimple = 0
for k in (3, 4, 5, 6, 7):
    for name, e in FORMS:
        t = ev(e, dk(k))
        if any(n != 1 for c, n in prof2(t) if c == 'b'):
            fails += 1; print('  FAIL b-simple %s k=%d' % (name, k))
        nsimple += 1
print('4. the 17 round-7 outputs b-simple (every b-run = 1): '
      '%d evaluations OK -- the a-run-only view sufficed there' % nsimple)

# ---------- 5. faithfulness: two-color profile <-> text; rule-Z is not injective
import random
rng = random.Random(271828)
def rebuild(prof): return ''.join(c * n for c, n in prof)
def aview_z(t): return [len(r) for r in t.split('b') if r]
for _ in range(300):
    t = ''.join(rng.choice('ab') for _ in range(rng.randint(1, 24)))
    if rebuild(prof2(t)) != t:
        fails += 1; print('  FAIL profile round-trip on %r' % t)
check('rule-Z not injective', aview_z('ab') == aview_z('abb'), True)
check('rule-Z not injective 2', aview_z('aabab') == aview_z('aababb'), True)
print('5. two-color profile determines the text (300 round-trips OK); '
      'rule-Z a-run view does not (exhibits ab/abb, aabab/aababb)')

print('FAILS:', fails)

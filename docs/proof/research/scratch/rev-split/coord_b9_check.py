#!/usr/bin/env python3
# Coordinator B9 fresh-encoding checks (rev-split / Lane B round 9). < 60 s.
# My OWN hand derivations (before reading gram9.c / tl_witness.c):
#   1. the replication chain: decb = [x/b]x has k^2+1 a-runs; decb^2 =
#      [decb/b]decb has k^4+1; decb^3 has k^8+1 (the a-run recursion
#      A' = A + B(R_w - 2)); the decb^2 k=3 VALUE TABLE (my full hand
#      derivation): head 4 = 2+2; sites 3,9 x27; junctions 31 = 27+3+1,
#      37 = 27+9+1 x9; seams 59 = 54+3+2, 65 = 54+9+2 x3; junction
#      seams 87 = 54+31+2, 93 = 54+37+2; end 108 = 54+54 -- 82 runs.
#      C-R9-1 (the exponent = the additive nesting depth Delta_V, not
#      the tree height) and C-R9-2 (the ambient-index anchoring).
#   2. tile7 = [b/a^7]X: Lambda_j = 3^j mod 7 (cycle 1,3,2,6,4,5;
#      period ord_7(3) = 6); profile [a:Lambda_j; b:1+floor(3^{j+1}/7)].
#   3. mod7 = [b/'bab']tile7: fired set {j: 6|j} cap [1..k-1]; the
#      SURVIVING family = the complement class j !~ 0 (mod 6) -- the
#      Boolean-closure mask; merged b-runs before j ~ 1 (mod 6);
#      #fired = floor((k-1)/6); the 417 = 104+1+312 at k=13.
#   4. the C-R9-3 closing arithmetic.
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
        print('  FAIL %-40s got %r want %r' % (name, got, want))
def dk(k):     return 'b'.join('a' * (3 ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def runs(t):   return [len(r) for r in t.split('b')]
def S_(k):     return (3 ** (k + 1) - 1) // 2

def sweep(R, P, w):
    m, out, i = len(P), [], 0
    while True:
        j = w.find(P, i)
        if j < 0: break
        out.append(w[i:j]); out.append(R)
        i = j + m
    out.append(w[i:])
    return ''.join(out)
def prof2(t): return [(c, len(list(g))) for c, g in groupby(t)]

# ---------- 1. the replication chain + the decb^2 value table
decb = S(X, K('b'), X)                       # [x/b]x
decb2 = S(decb, K('b'), decb)                 # [decb/b]decb
decb3 = S(decb2, K('b'), decb2)               # [decb^2/b]decb^2
for k in (3, 4, 5, 6):
    check('decb a-runs k=%d (k^2+1)' % k, len(runs(ev(decb, dk(k)))), k * k + 1)
    check('decb b-count k=%d (k^2)' % k, ev(decb, dk(k)).count('b'), k * k)
for k in (3, 4, 5, 6):
    check('decb^2 a-runs k=%d (k^4+1)' % k, len(runs(ev(decb2, dk(k)))),
          k ** 4 + 1)
    # the a-run recursion A' = A + B(R_w - 2)
    A, B, Rw = k * k + 1, k * k, k * k + 1
    check('recursion A+B(Rw-2) k=%d' % k, A + B * (Rw - 2), k ** 4 + 1)
check('decb^3 a-runs k=3 (k^8+1)', len(runs(ev(decb3, dk(3)))), 3 ** 8 + 1)
# my hand-derived decb^2 k=3 value table (multiset)
t = ev(decb2, dk(3))
mine = sorted([4] + [3] * 27 + [9] * 27 + [31] * 9 + [37] * 9 +
              [59] * 3 + [65] * 3 + [87, 93, 108])
check('decb^2 k=3 VALUE TABLE (82 runs)', sorted(runs(t)), mine)
check('decb^2 k=3 two-color entries', len(prof2(t)), 2 * 3 ** 4 + 1)
print('1. replication chain k^2+1 -> k^4+1 -> k^8+1 (the recursion A+B(Rw-2)); '
      'the decb^2 k=3 value table matches my full hand derivation '
      '(head 4=2+2, 31=27+3+1, 59=54+3+2, 87=54+31+2, 108=54+54)')

# ---------- 2. tile7 = [b/a^7]X
Lam7 = lambda j: 3 ** j % 7
for k in range(3, 14):
    w = dk(k)
    t = sweep('b', 'a' * 7, w)
    want = []
    for j in range(k + 1):
        want.append(('a', Lam7(j)))
        if j < k: want.append(('b', 1 + 3 ** (j + 1) // 7))
    check('tile7 profile k=%d' % k, prof2(t), want)
    check('tile7 a-run-only k=%d' % k, len(t.split('b')),
          (S_(k) - sum(Lam7(j) for j in range(k + 1))) // 7 + k + 1)
print('2. tile7: Lambda_j = 3^j mod 7 (period 6 = ord_7(3)), profile '
      '[Lambda_j / 1+floor(3^{j+1}/7)] k=3..13 OK; the a-run-only view is '
      'again exponential ((S-Sum Lambda)/7+k+1)')

# ---------- 3. mod7 = [b/'bab']tile7 (the complement-class mask)
for k in range(3, 14):
    t7 = sweep('b', 'a' * 7, dk(k))
    t = sweep('b', 'bab', t7)
    fired = [j for j in range(1, k) if j % 6 == 0]
    check('mod7 fired count k=%d' % k, len(fired), (k - 1) // 6)
    # my predicted profile: surviving a-runs = j not in fired (all j in
    # [0..k]); the b-run before surviving a-run j is merged iff j-1 fired
    want = []
    for j in range(k + 1):
        want.append(('a', Lam7(j)))
        if j < k:
            if j + 1 <= k - 1 and (j + 1) - 1 in fired:
                pass
    # build directly: walk surviving a-runs; b between j and j+1 merges
    # iff a-run j+1 was deleted (fired) -- i.e. the b-run following a
    # deleted run joins its neighbors via the inserted 'b'
    want = []
    j = 0
    while j <= k:
        want.append(('a', Lam7(j)))
        # the b-run after a-run j: separator + the next run's head-block,
        # minus bite adjustments if a-run j+1 fired (then a-run j+1 is
        # deleted and the b's merge with the following separator block)
        if j == k: break
        if j + 1 in fired:
            # a-run j+1 deleted: merged b-run = (b-run after j, tail) + 1
            # + (b-run after j+1, head); a-run j+2's entry comes next
            bm = 3 ** (j + 1) // 7 + 1 + 3 ** (j + 2) // 7
            want.append(('b', bm))
            j += 2
        else:
            want.append(('b', 1 + 3 ** (j + 1) // 7))
            j += 1
    check('mod7 profile k=%d' % k, prof2(t), want)
# the k=13 spot values (their head) and the merged 417
t13 = sweep('b', 'bab', sweep('b', 'a' * 7, dk(13)))
p13 = prof2(t13)
check('mod7 k=13 head', [n for _, n in p13[:13]],
      [1, 1, 3, 2, 2, 4, 6, 12, 4, 35, 5, 417, 3])
check('mod7 k=13 fired set {6,12}',
      [j for j in range(1, 13) if j % 6 == 0], [6, 12])
print('3. mod7: fired set {j: 6|j} cap [1..k-1], #fired = floor((k-1)/6); '
      'the surviving family = the COMPLEMENT class (the Boolean-closure '
      'mask); merged b before j ~ 1 (mod 6): k=3..13 OK (417 = 104+1+312 '
      'at k=13, two full mask periods)')

# ---------- 4. the C-R9-3 closing arithmetic
for F in range(1, 30):
    Ssz = F + 3
    if Ssz * Ssz - F * F < 6 * F + 9:
        fails += 1; print('  FAIL C-R9-3 closing at |F|=%d' % F)
print('4. C-R9-3 closing arithmetic (|S| >= |F|+3 => |S|^2-|F|^2 >= 6|F|+9): OK')

print('FAILS:', fails)

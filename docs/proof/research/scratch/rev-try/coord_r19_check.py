#!/usr/bin/env python3
# Coordinator round-19 fresh-encoding checks (rev-try, B=2 family). < 30 s.
# Independent verification of the new tools, the corrected closed forms,
# the round trips, and the mirror identity, with the campaign evaluator.
import sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0)
def ev(e, w): return PV.content(PV.lden(e, (PV.lab_input(w),)))
def wk(k):  return 'b'.join('a' * (2 ** m) for m in range(k + 1))
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-30s got %r want %r' % (name, got, want))
    return ok

# building blocks (record-verified)
mrg   = S(K(''), K('b'), X)                     # a^S
Elast = S(K(''), K('b'), S(K('a'), K('aa'), X)) # a^{2^k}
Esmm  = S(K(''), C(K('b'), mrg), S(K('b'), C(Elast, K('b')),
                                    C(mrg, C(K('b'), mrg))))
Eh2   = S(K('a'), K('aa'), Esmm)                # a^{2^{k-1}}
Eh4   = S(K('a'), K('aa'), Eh2)                 # a^{2^{k-2}}
Eleak = S(C(mrg, K('b')), K('b'), X)            # runs S+2^j
Eleakm = S(C(K('b'), mrg), K('b'), X)           # mirror
halver = S(K('a'), K('aa'), X)
doubler = S(K('aa'), K('a'), X)

# 1. halver self-similarity: [a/aa]X = 'ab' . w^{k-1}
for k in range(1, 9):
    check('halver k=%d' % k, ev(halver, wk(k)), 'ab' + wk(k - 1))
print('1. halver self-similarity: done')

# 2. STEPDOWN = [eps/(b.E_last)]X = w^{k-1}; chains via E_h2/E_h4
stepdown  = S(K(''), C(K('b'), Elast), X)
stepdown2 = S(K(''), C(K('b'), Eh2), stepdown)
stepdown3 = S(K(''), C(K('b'), Eh4), stepdown2)
for k in range(1, 9):
    check('stepdown k=%d' % k, ev(stepdown, wk(k)), wk(k - 1))
for k in range(2, 9):
    check('stepdown2 k=%d' % k, ev(stepdown2, wk(k)), wk(k - 2))
for k in range(3, 9):
    check('stepdown3 k=%d' % k, ev(stepdown3, wk(k)), wk(k - 3))
print('2. stepdown + chains: done')

# 3. JUMPDOWN(i) = [eps/(a^{2^i} b a^{2^i})]X -> runs (2^0..2^{i-1}, T)
#    T = 2^{k+1} - 2^i - (k-i)*2^{i+1}  (Lane C's corrected form)
for i in (0, 1, 2, 3):
    pat = C(C(K('a' * 2 ** i), K('b')), K('a' * 2 ** i))
    jd = S(K(''), pat, X)
    for k in range(i + 1, 11):
        v = ev(jd, wk(k))
        head = [2 ** j for j in range(i)]
        T = 2 ** (k + 1) - 2 ** i - (k - i) * 2 ** (i + 1)
        want = ('b'.join('a' * g for g in head) + ('b' if head else '')
                + 'a' * T)
        if not check('jumpdown i=%d k=%d' % (i, k), v, want):
            print('     T used =', T)
print('3. jumpdown corrected closed form: done')

# 4. SCALER = [E_last / a]X: every gap scaled by 2^k
scaler = S(Elast, K('a'), X)
for k in range(0, 8):
    v = ev(scaler, wk(k))
    want = 'b'.join('a' * (2 ** j * 2 ** k) for j in range(k + 1))
    check('scaler k=%d' % k, v, want)
print('4. scaler: done')

# 5. DIVIDER = [a / E_h2]X: gaps >= 2^{k-1} divided by 2^{k-1}
divider = S(K('a'), Eh2, X)
for k in range(1, 11):
    v = ev(divider, wk(k))
    g = [2 ** j for j in range(k + 1)]
    want = 'b'.join('a' * (x // 2 ** (k - 1) if x >= 2 ** (k - 1) else x)
                    for x in g)
    check('divider k=%d' % k, v, want)
print('5. divider: done')

# 6. LADDER = [b/ab][aa/a]X = gaps (1,3,7,...,2^k-1,2^{k+1})
ladder = S(K('b'), K('ab'), doubler)
for k in range(0, 9):
    v = ev(ladder, wk(k))
    g = [2 ** j - 1 for j in range(1, k + 1)] + [2 ** (k + 1)]
    want = 'b'.join('a' * x for x in g)
    check('ladder k=%d' % k, v, want)
# bonus identity: halver(ladder) = w^k
for k in range(0, 9):
    check('halver-ladder k=%d' % k, ev(S(K('a'), K('aa'), ladder),
                                       wk(k)), wk(k))
print('6. ladder + bonus identity: done')

# 7. +/-S round trips: [eps/mrg]E_leak = w^k and mirror too
for k in range(1, 9):
    check('leak-rt k=%d' % k, ev(S(K(''), mrg, Eleak), wk(k)), wk(k))
    check('leakm-rt k=%d' % k, ev(S(K(''), mrg, Eleakm), wk(k)), wk(k))
print('7. +/-S round trips: done')

# 8. recursion: doubler(rev(w^{k-1})) + 'ba' = rev(w^k);
#    halver(rev(w^k)) = rev(w^{k-1}) + 'ba'
for k in range(1, 9):
    rprev = wk(k - 1)[::-1]
    d = ev(doubler, rprev)  # doubler applied to the string rev(w^{k-1})
    check('rec-fwd k=%d' % k, d + 'ba', wk(k)[::-1])
    rk = ev(halver, wk(k)[::-1])
    check('rec-bwd k=%d' % k, rk, rprev + 'ba')
print('8. recursion facts: done')

# 9. plant-depth mirror: rev's separator j right-depth 2^{k-j}-1 equals
#    w's separator k-1-j left-depth; LEFT-depth of w sep m = 2^{m+1}-1
for k in range(1, 10):
    w = wk(k)
    ld = []
    a = 0
    for ch in w:
        if ch == 'a': a += 1
        else: ld.append(a)
    r = w[::-1]
    S_ = w.count('a')
    rd = []                      # RIGHT-depths of rev's separators
    a = 0
    for ch in r:
        if ch == 'a': a += 1
        else: rd.append(S_ - a)
    check('mirror k=%d' % k, rd, ld[::-1])
    check('ld k=%d' % k, ld, [2 ** (m + 1) - 1 for m in range(k)])
print('9. plant-depth mirror (order-reversing): done')

# 10. rotation threshold: rev(w^k) is a rotation of w^k iff k <= 2
for k in range(0, 6):
    w = wk(k); r = w[::-1]
    rots = {w[i:] + w[:i] for i in range(len(w))}
    check('rotation k=%d' % k, r in rots, k <= 2)
print('10. rotation threshold: done')

print('FAILS:', fails)

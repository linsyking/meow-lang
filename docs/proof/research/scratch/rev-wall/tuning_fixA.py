#!/usr/bin/env python3
# rev-wall round 3, corrected part A (the earlier A1-A6 used wrong hand forms;
# the machine falsified them -- see tuning.log).  Invocation:
#   /usr/bin/python3 -W ignore tuning_fixA.py     (cwd: rev-wall/)
import sys, time
sys.path.insert(0, '.')
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S

X = V(0)
def ev(e, w):
    return PV.content(PV.lden(e, (PV.lab_input(w),)))
def w2k(k):   return 'b'.join('a' * (2 ** m) for m in range(k + 1))
def dk(k, B): return 'b'.join('a' * (B ** m) for m in range(k + 1))
def acount(v): return v.count('a')

half  = S(K('a'), K('aa'), X)                 # [a/aa]X   (b-bearing per-run halver)
E_last = S(K(''), K('b'), half)               # [e/b][a/aa]X = a^{Sum ceil(r_i/2)}
mrg   = S(K(''), K('b'), X)                   # [e/b]X = a^S
dbl   = S(K('aa'), K('a'), X)                 # [aa/a]X (b-bearing doubler)
E_dbl2 = S(K(''), K('b'), dbl)                # [e/b][aa/a]X
del_last = S(K(''), C(C(K('b'), mrg), K('a')), C(C(X, mrg), K('a')))
E_cbox = S(K('b'), C(E_last, K('b')), C(C(mrg, K('b')), mrg))  # [b/(E_last.b)](mrg.b.mrg)
E_smm  = S(K(''), C(K('b'), mrg), E_cbox)     # [e/(b.mrg)]E_cbox
E_h2   = S(K('a'), K('aa'), E_smm)            # [a/aa]E_smm

print('== A (corrected): the B=2 telescoping degeneracy ==')
bad = 0
for k in range(1, 13):
    if ev(E_last, w2k(k)) != 'a' * (2 ** k): bad += 1; print('  A1 FAIL k=%d' % k)
print('  A1 [e/b][a/aa]X = a^{2^k}: the LAST RUN as a b-free value on w^(k)')
print('     12 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 11):
    if k == 1: want = 'a' * (2 ** 0 + 2 ** 1)
    else:      want = 'b'.join('a' * (2 ** m) for m in range(k - 1)) + 'b' + 'a' * (2 ** (k - 1) + 2 ** k)
    if ev(del_last, w2k(k)) != want: bad += 1; print('  A2 FAIL k=%d' % k)
print('  A2 del_last = runs 0..k-2, then glued run 2^{k-1}+2^k (last b consumed)')
print('     10 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 12):
    S_ = 2 ** (k + 1) - 1
    if ev(E_cbox, w2k(k)) != 'a' * (2 ** k - 1) + 'b' + 'a' * S_: bad += 1; print('  A3 FAIL k=%d' % k)
print('  A3 [b/(E_last.b)](mrg.b.mrg) = a^{2^k-1} b a^S (sum-minus-max as HEAD run)')
print('     11 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 12):
    if ev(E_smm, w2k(k)) != 'a' * (2 ** k - 1): bad += 1; print('  A4 FAIL k=%d' % k)
print('  A4 [e/(b.mrg)]E_cbox = a^{2^k-1}: B-FREE SUM-MINUS-MAX')
print('     11 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 12):
    if ev(E_h2, w2k(k)) != 'a' * (2 ** (k - 1)): bad += 1; print('  A5 FAIL k=%d' % k)
print('  A5 [a/aa]E_smm = a^{2^{k-1}}: the 2nd-from-top run, b-free (fixed offset)')
print('     11 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 11):
    if ev(E_dbl2, w2k(k)) != 'a' * (2 ** (k + 2) - 2): bad += 1; print('  A6 FAIL k=%d' % k)
print('  A6 [e/b][aa/a]X = a^{2^{k+2}-2}: tweak at depth k+2, b-free')
print('     10 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
MARK('A done')

print('== A7 (corrected, a-counts): contrast on B=3 -- supply values stay in gaps ==')
B = 3
def dist_to_powers(n, B):
    if n <= 0: return 10 ** 9, -1
    j = 0
    while B ** (j + 1) <= n: j += 1
    return min(n - B ** j, B ** (j + 1) - n), j
minrel = 1.0; minat = None
for k in range(1, 9):
    w = dk(k, B)
    row = []
    for (nm, e) in [('E_last', E_last), ('E_smm', E_smm), ('E_h2', E_h2)]:
        a = acount(ev(e, w))
        d, j = dist_to_powers(a, B)
        rel = d / max(1, a)
        if k >= 3 and rel < minrel: minrel, minat = rel, (nm, k)
        row.append('%s a=%d (dist %d to 3^%d)' % (nm, a, d, j))
    print('  k=%d: %s' % (k, '; '.join(row)))
print('  min relative power-distance for k>=3: %.3f at %s' % (minrel, minat))
print('  (B=2 gives distance 0 -- the telescoping; B=3 stays bounded away)')
MARK('A7 done')

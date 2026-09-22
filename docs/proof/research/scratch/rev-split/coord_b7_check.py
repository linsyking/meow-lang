#!/usr/bin/env python3
# Coordinator B7 fresh-encoding checks (rev-split / Lane B round 7). < 30 s.
# My OWN hand-derived run sequences for the round-7 grammars (derived
# BEFORE reading gram7.c's forms, then cross-checked against it),
# compared against prov.py -- independent of their C engine.
import sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0)
def dk(k):     return 'b'.join('a' * (3 ** j) for j in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def runs(t):   return [len(r) for r in t.split('b')] if t else []
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-26s first diff:' % name, end=' ')
        for i, (g, w) in enumerate(zip(got + [None] * 99, want + [None] * 99)):
            if g != w:
                print('run %d: got %s want %s (lens %d/%d)'
                      % (i, g, w, len(got), len(want)))
                break

mrg   = S(K(''), K('b'), X)
half  = S(K('a'), K('aa'), X)
third = S(K('a'), K('aaa'), X)
dbl   = S(K('aa'), K('a'), X)
shave = S(K('b'), K('ab'), X)
decb  = S(X, K('b'), X)                       # [X/'b']X
thresh = S(K('b'), K('aaabaaab'), decb)       # [b/'aaabaaab']decb

def S_(k): return (3 ** (k + 1) - 1) // 2

for k in (3, 4, 5, 6, 7):
    w = dk(k); Stot = S_(k)
    # -- the six core forms (my independent derivations) --
    check('mrg k=%d' % k,       runs(ev(mrg, w)), [Stot])
    check('half k=%d' % k,      runs(ev(half, w)), [(3 ** j + 1) // 2 for j in range(k + 1)])
    check('third k=%d' % k,     runs(ev(third, w)), [1] + [3 ** (j - 1) for j in range(1, k + 1)])
    check('dbl k=%d' % k,       runs(ev(dbl, w)), [2 * 3 ** j for j in range(k + 1)])
    check('shave k=%d' % k,     runs(ev(shave, w)), [3 ** j - 1 for j in range(k)] + [3 ** k])
    check('dropab k=%d' % k,    runs(ev(S(K(''), K('ab'), X), w)), [Stot - k])
    check('Eleak k=%d' % k,     runs(ev(S(C(mrg, K('b')), K('b'), X), w)),
          [Stot + 3 ** j for j in range(k)] + [3 ** k])
    check('Eprod k=%d' % k,     runs(ev(S(mrg, K('aa'), X), w)),
          [1] + [1 + ((3 ** j - 1) // 2) * Stot for j in range(1, k + 1)])
    check('dlast k=%d' % k,     runs(ev(S(K(''), C(C(K('b'), mrg), K('a')),
                                           C(C(X, mrg), K('a'))), w)),
          [3 ** j for j in range(k - 1)] + [3 ** (k - 1) + 3 ** k])
    check('dfirst k=%d' % k,    runs(ev(S(K(''), C(C(K('a'), mrg), K('b')),
                                           C(C(K('a'), mrg), X)), w)),
          [4] + [3 ** j for j in range(2, k + 1)])
    Elast = S(K(''), K('b'), half)
    check('Elast k=%d' % k,     runs(ev(Elast, w)), [(Stot + k + 1) // 2])
    Ecbox = S(K('b'), C(Elast, K('b')), C(C(mrg, K('b')), mrg))
    check('Ecbox k=%d' % k,     runs(ev(Ecbox, w)), [(Stot - k - 1) // 2, Stot])
    Esmm  = S(K(''), C(K('b'), mrg), Ecbox)
    check('Esmm k=%d' % k,      runs(ev(Esmm, w)), [(Stot - k - 1) // 2])
    L = (Stot - k - 1) // 2
    check('Eh2 k=%d' % k,       runs(ev(S(K('a'), K('aa'), Esmm), w)), [(L + 1) // 2])
    check('dblmerge k=%d' % k,  runs(ev(S(K(''), K('b'), dbl), w)), [2 * Stot])
    # -- decb: MY sequence (junctions = my corrected formula) --
    mine = [2]
    for c in range(k - 1):
        mine += [3 ** j for j in range(1, k)] + [3 ** k + 3 ** (c + 1) + 1]
    mine += [3 ** j for j in range(1, k)] + [2 * 3 ** k]
    check('decb k=%d' % k, runs(ev(decb, w)), mine)
    check('decb count k=%d' % k, len(runs(ev(decb, w))), k * k + 1)
    # -- thresh: MY sequence (k-1 firings, J_c all bitten, 3^1 masked) --
    mine = [2]
    mine += [3 ** j for j in range(1, k)] + [3 ** k + 1]           # copy 0
    for c in range(1, k - 1):
        mine += [3 ** j for j in range(2, k)] + [3 ** k + 3 ** (c + 1) - 2]
    mine += [3 ** j for j in range(2, k)] + [2 * 3 ** k]          # copy k-1
    check('thresh k=%d' % k, runs(ev(thresh, w)), mine)
    check('thresh count k=%d' % k, len(runs(ev(thresh, w))), k * k - k + 2)

print('FAILS:', fails)

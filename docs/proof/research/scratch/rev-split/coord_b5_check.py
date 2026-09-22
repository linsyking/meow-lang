#!/usr/bin/env python3
# Coordinator B5 fresh-encoding checks (rev-split). < 10 s.
# Verifies the round's two corrections and the battery's key closed forms
# with the campaign evaluator, independent of ledger3.c.
import sys
sys.path.insert(0, '.')
sys.path.insert(0, '../rev-wall')
import prov as PV
from lcore import K, V, C, S
X = V(0)
def ev(e, w): return PV.content(PV.lden(e, (PV.lab_input(w),)))
def dk(k, B=3): return 'b'.join('a' * (B ** m) for m in range(k + 1))
def Sm(k, B=3): return (B ** (k + 1) - 1) // (B - 1)

fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok: fails += 1
    print('  %-34s %-6s got %-22s want %s'
          % (name, 'OK' if ok else 'FAIL', got, want))

# --- C1 witness: E_last on B=3 = (S+k+1)/2 ---
print('C1: E_last = [eps/b][a/aa]X on D(k;3) = a^{(S+k+1)/2}')
halver = S(K('a'), K('aa'), X)
Elast = S(K(''), K('b'), halver)
for k in range(1, 9):
    v = ev(Elast, dk(k))
    want = 'a' * ((Sm(k) + k + 1) // 2)
    check('k=%d' % k, v, want)

# --- the B=2 non-dyadic stratum: [a/'aaa']X runs ---
print("B=2 stratum: [a/'aaa']X runs (2^j+2)/3 [j even], (2^j+4)/3 [j odd]")
Eaaa = S(K('a'), K('aaa'), X)
for j in range(0, 13):
    w = 'a' * (2 ** j)
    v = ev(Eaaa, w)
    want = 'a' * ((2 ** j + (2 if j % 2 == 0 else 4)) // 3)
    check('j=%d' % j, v, want)

# --- BA correction witness: E_prod last run on B=3 = 1 + floor(3^k/2)*S ---
print('BA fix: E_prod = [mrg/aa]X on D(k;3), last run 1+floor(3^k/2)*S')
mrg3 = S(K(''), K('b'), X)
Eprod = S(mrg3, K('aa'), X)
for k in range(1, 7):
    v = ev(Eprod, dk(k))
    runs = [len(r) for r in v.split('b')]
    check('k=%d last' % k, runs[-1], 1 + (3 ** k // 2) * Sm(k))
    check('k=%d j=%d interior' % (k, k - 1), runs[-2],
          Sm(k) * (3 ** (k - 1) - 1) // 2 + 1)

# --- E_cbox / E_smm on B=3: (S-k-1)/2 family ---
print('E_cbox/E_smm on D(k;3)')
Elast_len = lambda k: (Sm(k) + k + 1) // 2
def build_cbox(k):
    Eb = K('a' * Elast_len(k))          # E_last's value as a constant stand-in?
    # no: rebuild the honest expression (E_last depends on k only through X)
    patt = C(Elast, K('b'))
    return S(K('b'), patt, C(mrg3, C(K('b'), mrg3)))
# NOTE: build_cbox embeds Elast itself (k-independent expression): correct.
for k in range(1, 7):
    cbox = S(K('b'), C(Elast, K('b')), C(mrg3, C(K('b'), mrg3)))
    v = ev(cbox, dk(k))
    want = 'a' * ((Sm(k) - k - 1) // 2) + 'b' + 'a' * Sm(k)
    check('k=%d cbox' % k, v, want)
    smm = S(K(''), C(K('b'), mrg3), cbox)
    check('k=%d smm' % k, ev(smm, dk(k)), 'a' * ((Sm(k) - k - 1) // 2))

# --- B=2 classification: E_last B=2 = (S+1)/2 = 2^k ---
print('B=2: E_last on D(k;2) = a^{2^k} (S+1)/2')
for k in range(0, 9):
    check('k=%d' % k, ev(Elast, dk(k, 2)), 'a' * (2 ** k))

print('FAILS:', fails)

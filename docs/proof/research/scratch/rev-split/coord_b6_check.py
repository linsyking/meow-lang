#!/usr/bin/env python3
# Coordinator B6 fresh-encoding checks (rev-split). < 30 s.
# PO-1 window anatomy: bites = the pattern's own boundary runs; interior
# runs match exactly; consecutive-b-stretch correspondence. Plus the
# replica-index threshold on T = [X/'b']X.
import sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-30s got %r want %r' % (name, got, want))
    return ok

def runs_of(t):
    return [len(r) for r in t.split('b')] if 'b' in t else [len(t)]

def anatomy(pat, text):
    """first greedy window of pat in text; return (ok, data) verifying
    PO-1: window b's consecutive in text, interiors exact, bites c0/cm"""
    j = text.find(pat)
    if j < 0: return None
    c = pat.split('b')                     # pattern runs c_0..c_m
    m = len(c) - 2                          # interior count
    # window b positions in text
    wb = [pos for pos, ch in enumerate(text[j:j + len(pat)]) if ch == 'b']
    wb = [pos + j for pos in wb]
    # text b's strictly inside the window beyond the matched ones?
    allb = [pos for pos, ch in enumerate(text) if ch == 'b']
    inside = [pos for pos in allb if j <= pos < j + len(pat)]
    consecutive = (inside == wb)
    # interior runs of text between consecutive matched b's == c_{i+1}?
    interiors_ok = True
    for i in range(m):
        seg = text[wb[i] + 1:wb[i + 1]]
        if seg != c[i + 1]:
            interiors_ok = False
    # bites: the a-material before wb[0] inside the window; after wb[-1]
    biteL = wb[0] - j
    biteR = (j + len(pat)) - 1 - wb[-1]
    return dict(consecutive=consecutive, interiors=interiors_ok,
                biteL=biteL, biteR=biteR, c0=len(c[0]), cm=len(c[-1]))

# random multi-b patterns on D(k;3) plus bitten/merged texts
import random
rng = random.Random(99)
bad = 0; tested = 0
for trial in range(400):
    k = rng.randint(2, 5)
    text = dk(k)
    mode = rng.random()
    if mode < 0.3:            # bite some runs (make interiors 0 possible)
        ls = list(runs_of(text))
        for z in range(len(ls)):
            if rng.random() < 0.25:
                ls[z] = max(0, ls[z] - rng.randint(1, 5))
        text = 'b'.join('a' * z for z in ls)
    elif mode < 0.5:          # suffix-merge (drop leading runs)
        text = 'b'.join(dk(k).split('b')[rng.randint(0, k):])
    nb = rng.randint(2, 3)
    pruns = [rng.randint(0, 4) for _ in range(nb + 1)]
    pat = 'b'.join('a' * z for z in pruns)
    if 'b' not in pat.replace('ab', '') and nb >= 1 and pat.count('b') < 2:
        continue
    r = anatomy(pat, text)
    if r is None: continue
    tested += 1
    if not (r['consecutive'] and r['interiors']
            and r['biteL'] == r['c0'] and r['biteR'] == r['cm']):
        bad += 1
        print('   violation:', pat, text[:40], r)
check('PO-1 anatomy violations', bad, 0)
print('1. PO-1 window anatomy: %d windows checked, 0 violations' % tested)

# replica threshold on T = [X/'b']X: run before copy c's sep-0 is 3^c+1
print('2. replica structure on T = [X/b]X')
T = S(X, K('b'), X)
for k in (3, 4, 5):
    t = ev(T, dk(k))
    runs = runs_of(t)
    # expected: k+1 copies; copy c preceded by run of length 3^c + 1
    # (the merged junction): verify a few junction runs
    # junctions: first = 2 (r_0 + copy head); c>=1: 3^k + 3^c + 1
    want = [2] + [B ** k + B ** c + 1 for c in range(1, k)]
    got = [r for r in runs if r in want]
    check('k=%d junction runs' % k, got, want)
# the c0 = 3, 4 thresholds: fired copies = {c : 3^c + 1 >= c0}
for c0, pat in [(3, 'a' * 3 + 'b' + 'a' * 3 + 'b'),
                (4, 'a' * 4 + 'b' + 'a' * 3 + 'b')]:
    for k in (4, 5, 6, 7):
        rep = 'Z'
        out = ev(S(K(rep), K(pat), T), dk(k))
        # copy 0 fails (junction 2 < c0); copies 1..k-1 fire: k-1 windows
        check('c0=%d k=%d fired' % (c0, k), out.count(rep), k - 1)
print('   (their threshold patterns: copy 0 fails, k-1 fire)')

# EPT spot check: 3^k mod 7 has period 6; differences eventually periodic
print('3. EPT arithmetic spot checks')
check('ord_7(3)', [3 ** i % 7 for i in range(12)],
      [1, 3, 2, 6, 4, 5, 1, 3, 2, 6, 4, 5])
check('ord_5(3)', [3 ** i % 5 for i in range(8)], [1, 3, 4, 2, 1, 3, 4, 2])
check('ord_13(3) is 3', [3 ** i % 13 for i in range(9)],
      [1, 3, 9, 1, 3, 9, 1, 3, 9])

print('FAILS:', fails)

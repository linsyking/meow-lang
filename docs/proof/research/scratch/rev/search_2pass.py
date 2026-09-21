"""EXHAUSTIVE 2-pass search over the full library pass space: the maximum
LDS at mult=1 (Conjecture B) and the maximum LDS/mult (Conjecture A).

A 2-pass pipeline [R2/P2][R1/P1]X with all four parts from the library is a
depth-2 expression; this is an exhaustive coverage statement for that
fragment (beyond the paper's depth-3 constant-pattern search: here patterns
and replacements are VARIABLE, including the anchored right-end family).
"""
import sys
import time

import lcore as L
from lcore import battery
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN
rng_fixed = 20260921

LIB_P = dict(RL.PATTERNS)
LIB_R = dict(RL.REPLACEMENTS)
LIB_R['XX'] = lambda: L.C(L.V(0), L.V(0))
LIB_R['XaX'] = lambda: L.C(L.C(L.V(0), L.K('a')), L.V(0))

WS = [''.join(__import__('random').Random(99).choice('ab') for _ in range(n))
      for n in (14, 16)] + ['a' * 8 + 'b' * 8, 'ab' * 8, 'aab' * 6,
                            'aaaaabbbbbaaaaabbbbb', 'b' + 'a' * 11]
Ws = battery(5) + WS

PVals, RVals = {}, {}
for p, b in LIB_P.items():
    ast = b()
    PVals[p] = {}
    for w in Ws:
        try:
            PVals[p][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            PVals[p][w] = None
for r, b in LIB_R.items():
    ast = b()
    RVals[r] = {}
    for w in Ws:
        try:
            RVals[r][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            RVals[r][w] = None

# only total-nonempty patterns (on the whole battery)
PN = [p for p in PVals if all(PVals[p][w] is not None and PVals[p][w]
                              for w in Ws)]
RN = list(RVals)
print(f'patterns {len(PN)}, replacements {len(RN)} -> '
      f'{len(PN)*len(RN)} passes, {len(PN)**2 * len(RN)**2} 2-pass pipelines',
      flush=True)

bestB = (0, None)     # (LDS@mult1, pipeline)
bestR = (0.0, None)  # (LDS/mult, pipeline)
t0 = time.time()
n_checked = 0
n_valid = 0
for p1 in PN:
    for r1 in RN:
        # first pass outputs per w (cached per (p1,r1))
        T1 = {}
        ok = True
        for w in Ws:
            B, A = PVals[p1][w], RVals[r1][w]
            if B is None or not B or A is None:
                ok = False
                break
            T = PV.lsubst(A, B, PV.lab_input(w))
            if len(T) > 600:
                ok = False
                break
            T1[w] = T
        if not ok:
            continue
        for p2 in PN:
            for r2 in RN:
                n_checked += 1
                mB = mD = mM = 0
                mr = 0.0
                good = True
                for w in Ws:
                    B, A = PVals[p2][w], RVals[r2][w]
                    if B is None or not B or A is None:
                        good = False
                        break
                    T = PV.lsubst(A, B, T1[w])
                    if len(T) > 600:
                        good = False
                        break
                    pr = PV.labels(T)
                    if not pr:
                        continue
                    d, m = PV.lds(pr), PV.mult(pr)
                    mD, mM = max(mD, d), max(mM, m)
                    if m:
                        mr = max(mr, d / m)
                    if m == 1:
                        mB = max(mB, d)
                if not good:
                    continue
                n_valid += 1
                if mB > bestB[0]:
                    bestB = (mB, (p1, r1, p2, r2))
                    print(f'  new best LDS@mult1 = {mB}: {(p1, r1, p2, r2)} '
                          f'({time.time()-t0:.0f}s)', flush=True)
                if mr > bestR[0]:
                    bestR = (mr, (p1, r1, p2, r2))
print(f'exhaustive 2-pass: {n_checked} pipelines enumerated, '
      f'{n_valid} fully valid ({time.time()-t0:.0f}s)')
print(f'MAX LDS@mult1  = {bestB[0]}  at {bestB[1]}')
print(f'MAX LDS/mult   = {bestR[0]:.2f}  at {bestR[1]}')

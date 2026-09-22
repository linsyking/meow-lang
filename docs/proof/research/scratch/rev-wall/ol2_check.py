#!/usr/bin/env python3
# rev-wall round 5 (OL-2 + D1'' completion) battery.
# Invocation: /usr/bin/python3 -W ignore ol2_check.py   (cwd: rev-wall/)
# Theory first; the machine CONFIRMS hand derivations.  All parts < 60 s.
import sys, time, random, os
sys.path.insert(0, '.')
print('INVOCATION: /usr/bin/python3 -W ignore %s/ol2_check.py  (cwd: %s)' %
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
    return 1 + max(Sde(e[1]), Sde(e[2]), Sde(e[3]))

def fired_junctions(ptext, ftext):
    """greedy leftmost disjoint matches of ptext in ftext; return the
    ABSOLUTE indices (in ftext) of the b's consumed, and the match count."""
    js, i, n, t = [], 0, len(ftext), 0
    while i < n:
        j = ftext.find(ptext, i)
        if j < 0: break
        js += [j + m for m, ch in enumerate(ptext) if ch == 'b']
        t += 1; i = j + len(ptext)
    return js, t

def junction_b_indices(ftext):
    return [m for m, ch in enumerate(ftext) if ch == 'b']

def is_suffix(fired, allb):
    """fired (a set of junction positions) is a suffix of allb's order"""
    fs = set(fired)
    idx = [i for i, b in enumerate(allb) if b in fs]
    return len(idx) == len(fs) and (not idx or idx == list(range(idx[0], len(allb))))

print('== A: THE FIRED-SET LEMMA on D(4;3) (selectivity: suffix / all / '
      'one-exact) ==')
MARK('start')
w = dk(4)
allb = junction_b_indices(w)
viol_suffix = viol_single = nchk = 0
# A1: single-b patterns a^i b and b a^j (constants): fired sets are
# suffixes (or all, or empty)
for i in range(0, 41):
    for pat in ('a' * i + 'b', 'b' + 'a' * i):
        js, t = fired_junctions(pat, w)
        nchk += 1
        if not is_suffix(js, allb):
            viol_suffix += 1
            print('  A1 NON-SUFFIX: pat=%r fired=%s' % (pat[-8:], js))
print('  A1 single-b patterns (i=0..40, both orientations): %d checks, '
      '%d non-suffix' % (nchk, viol_suffix))
# A2: multi-b patterns a^i b a^j b a^i2 (positive interior j): at most ONE
# firing on the distinct-run text (SD); the firing's window spans a
# contiguous junction block whose interior runs match the pattern's
# interior EXACTLY; the block is pinned by the interior value j (a fixed
# offset when j is a power, no firing when not a run length)
def windows(ptext, ftext):
    ws, i, n = [], 0, len(ftext)
    while i < n:
        j = ftext.find(ptext, i)
        if j < 0: break
        ws.append(j); i = j + len(ptext)
    return ws
nchk = viol = exact_ok = fired1 = 0
pows = set(1 * B ** s for s in range(0, 6))
# j = 0 gives a 'bb' interior: cannot fire (D(k;3) has no 'bb' — runs
# between junctions are positive), which is claim (iii)
js_range = sorted(set([0] + list(pows) + [2, 4, 5, 10, 12, 26, 28]))
runlens = {len(z) for z in w.split('b')}          # {1,3,9,27,81}
for i in range(0, 10):
    for j in js_range:
        for i2 in range(0, 10):
            pat = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * i2
            ws = windows(pat, w)
            nchk += 1
            if len(ws) > 1:
                viol += 1
                print('  A2 MULTI-FIRING: %r -> %d windows' % (pat, len(ws)))
            elif len(ws) == 1:
                fired1 += 1
                # interior-exactness: the pattern's interior run j must be a
                # genuine run length, and the fired junction's block is the
                # unique one pinned by it
                if j not in runlens:
                    viol += 1
                    print('  A2 NON-RUN interior fired: %r' % pat)
                else:
                    # the window must sit with its interior on that run
                    ok = (w[ws[0] + i + 1: ws[0] + i + 1 + j] == 'a' * j
                          and w[ws[0] + i + 1 + j] == 'b')
                    if not ok:
                        viol += 1
                        print('  A2 INTERIOR MISALIGNED: %r' % pat)
                    else:
                        exact_ok += 1
print('  A2 multi-b patterns (i,i2<=9, j in %s): %d checks, %d violations,'
      ' %d firings (all single-window, interior-exact)'
      % (js_range, nchk, viol, fired1))
print('  A: FIRED-SET LEMMA:', 'VERIFIED' if (viol_suffix + viol) == 0
      else 'REFUTED')
MARK('A done')

print('== B: interior BLOCK deletion is not one pass; the staged walk ==')
# B1: no single-b pattern's fired set is a strict-interior block
# {b_u..b_v} with 1 <= u and v <= k-2 (size >= 2): suffixes only.
# (k = 4 junctions b_0..b_3: interior blocks must have v <= 2.)
blocks = [(u, v) for u in range(1, 3) for v in range(u, 3)]
hit = 0
for i in range(0, 122):
    for pat in ('a' * i + 'b', 'b' + 'a' * i):
        js, _ = fired_junctions(pat, w)
        fs = set(js)
        for (u, v) in blocks:
            want = set(allb[u:v + 1])
            if fs == want and len(want) >= 2:
                hit += 1
                print('  B1 ONE-PASS INTERIOR-BLOCK HIT: pat %r fires '
                      '{%d..%d}' % (pat[-8:], u, v))
print('  B1 interior-block-by-one-pass search (i=0..121 both orientations, '
      'strict-interior blocks size>=2): %d hits' % hit)
# B2: the staged suffix-deletion to reach the interior block {b_1,b_2}
# while keeping b_0,b_3,b_4: the staging EATS the preceding run (of size
# = the threshold) at every step — it cannot spare the tail's structure:
E_stage = S(K(''), K('a' * 27 + 'b'), X)     # fires at b_4 only (prec>=27)
v1 = ev(E_stage, w)
print('  B2 staging step 1 [e/a^27.b]X: runs %s (run 3 = 27 EATEN + b_4 '
      'deleted: the threshold always eats its preceding run)'
      % [len(z) for z in v1.split('b')])
E_stage2 = S(K(''), K('a' * 9 + 'b'), E_stage)   # now fires at b_3
v2 = ev(E_stage2, w)
print('  B2 staging step 2 [e/a^9.b]: runs %s (run 2 = 9 EATEN + b_3 '
      'deleted — suffix staging consumes the tail; interior blocks need '
      'the boost walk or the two-sided box)' % [len(z) for z in v2.split('b')])
# B3: the engine's del-chain walk (round-4 part C): L_m chain lengths
def build(letters):
    k = len(letters); seps = sorted(set(letters))
    mrg = X
    for s in seps: mrg = S(K(''), K(s), mrg)
    def del_last(E, s):
        return S(K(''), C(K(s), C(mrg, K('a'))), C(C(E, mrg), K('a')))
    def del_first(E, s):
        return S(K(''), C(C(K('a'), mrg), K(s)), C(C(K('a'), mrg), E))
    Ds = []
    for m in range(k):
        E = X
        for t in range(m):      E = del_first(E, letters[t])
        for t in range(k - 1, m, -1): E = del_last(E, letters[t])
        Ds.append(S(K(letters[m]), E, C(C(mrg, K(letters[m])), mrg)))
    return Ds, mrg
Ds, mrg = build(['b'] * 4)
print('  B3 the box patterns L_m: value runs (prefix_m, suffix_m) and '
      'S-depth:')
for m in range(4):
    Lv = ev(Ds[m][2], w)
    print('     L_%d: runs %s  S-depth %d' %
          (m, [len(z) for z in Lv.split('b')], Sde(Ds[m][2])))
MARK('B done')

print('== C: the threshold-supply walk (psi-chain scale descent) ==')
# [a/aaa] chain off mrg: values at descending scales, ~one scale per node
chain = [mrg]
for j in range(6):
    chain.append(S(K('a'), K('aaa'), chain[-1]))
k = 5
w5 = dk(5)
print('  k=5, S=%d; the [a/aaa]-chain values and their scale-distance '
      'from the top power 3^5=243:' % ((3 ** 6 - 1) // 2))
import math
for j, e in enumerate(chain):
    v = ev(e, w5)
    L = v.count('a')
    d = math.log(243 / L, 3) if L else float('inf')
    print('     depth %d: value a^%d  (scale-distance %.2f)' % (j, L, d))
print('  (each step multiplies by ~1/3: the threshold at scale-distance '
      'delta needs depth ~delta; no jump)')
# the exact-power check: does any chain value EQUAL a power? (the gaps)
pows = set(3 ** s for s in range(0, 7))
hits = [(j, len(ev(e, w5))) for j, e in enumerate(chain)
        if len(ev(e, w5)) in pows]
print('  chain values that are exact powers: %s (expect: none — the gap '
      'phenomenon)' % (hits or 'none'))
MARK('C done')

print('== D: the T1-trace arithmetic (mod-3 lemma) ==')
k = 4
tops = [sum(3 ** s for s in range(k - t, k + 1)) for t in range(k)]
bots = [sum(3 ** s for s in range(0, sigma + 1)) for sigma in range(k)]
print('  TopSum(t) (output plant a-masses): %s  (mod 3: %s)'
      % (tops, [t % 3 for t in tops]))
print('  BotSum(sigma) (input b a-masses):  %s  (mod 3: %s)'
      % (bots, [b % 3 for b in bots]))
print('  intersection:', sorted(set(tops) & set(bots)) or 'EMPTY',
      '-> every surviving input b at a plant position is DISPLACED '
      '(Delta != 0)')
MARK('D done')

print('== E: D1\'\'-strong directed attempts at k=2 (the selectivity wall) ==')
w2 = dk(2)
# E1: the single-splice: unique long pattern keeps only run 2's last atom
E1 = S(K('a' * 9 + 'b' + 'a' * 3 + 'b'), K('a' + 'b' + 'a' * 3 + 'b' + 'a' * 8), X)
v1 = ev(E1, w2)
print('  E1 [a^9 b a^3 b / a b a^3 b a^8]X = %r  rev? %s'
      % (v1, v1 == w2[::-1]))
# E2: the double-firing damage: [a^9 b / a b]X
E2 = S(K('a' * 9 + 'b'), K('a' + 'b'), X)
v2 = ev(E2, w2)
print('  E2 [a^9 b / a b]X = %r (double firing: the second window at b_1 '
      'eats run 1\'s last atom and glues: runs %s)'
      % (v2, [len(z) for z in v2.split('b')]))
# E3: every short selector a^i b fires at a suffix of the junctions
sels = {}
allb2 = junction_b_indices(w2)
for i in range(0, 10):
    js, t = fired_junctions('a' * i + 'b', w2)
    sels[i] = [allb2.index(j) for j in sorted(js)]   # junction INDICES
print('  E3 selectors a^i b on D(2;3) (junction indices fired):', sels)
print('  (fired sets are suffixes {1} or {0,1} or {}: b_0 cannot be '
      'selected alone without eating run 1 — the wall behind the '
      'failed multi-label constructions)')
MARK('E done')

print('== F: the END-anchored contrast — [e/b][aa/aaa]X = a^{3^k} (depth 2) ==')
# psi-map: run u -> r*floor(u/p) + (u mod p) with r=2, p=3: run j>=1 maps
# 3^j -> 2*3^{j-1} exactly (powers of 3 are 0 mod 3); run 0 (a^1) is
# untouched; the [e/b] merge then sums 1 + sum_{j>=1} 2*3^{j-1} = 3^k
# EXACTLY: the TOP input run, extracted at S-depth 2.  The end of OL-2's
# range is free; the Omega(min(m,k-m)) floor is interior-only.
okF = 0
Ef = S(K(''), K('b'), S(K('aa'), K('aaa'), X))
Einner = S(K('aa'), K('aaa'), X)
for kf in range(1, 7):
    wf = dk(kf)
    vf = ev(Ef, wf)
    runs = [len(z) for z in ev(Einner, wf).split('b')]
    good = (vf == 'a' * (3 ** kf)
            and runs == [1] + [2 * 3 ** (j - 1) for j in range(1, kf + 1)])
    okF += good
    print('     k=%d: inner runs %s -> merged a^%d (want 3^k = %d): %s'
          % (kf, runs, len(vf), 3 ** kf, 'OK' if good else 'FAIL'))
print('  F TOP-RUN EXTRACTION AT DEPTH 2:',
      'VERIFIED (%d/6)' % okF if okF == 6 else 'REFUTED (%d/6)' % okF)
print('  (end-anchored single-run values cost O(1); contrast the interior '
      'anchored sums: the Omega(min(m, k-m)) walk)')
print('ROUND 5 BATTERY COMPLETE')

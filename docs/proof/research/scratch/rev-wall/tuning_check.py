#!/usr/bin/env python3
# rev-wall round 3 (TUNING LEMMA) battery.
# Invocation: /usr/bin/python3 -W ignore tuning_check.py   (cwd: rev-wall/)
# All parts < 60 s total; the machine CONFIRMS hand derivations.
import sys, time, random
sys.path.insert(0, '.')
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S, pp

X = V(0)
def ev(e, w):
    return PV.content(PV.lden(e, (PV.lab_input(w),)))
def w2k(k):    return 'b'.join('a' * (2 ** m) for m in range(k + 1))
def dk(k, B):  return 'b'.join('a' * (B ** m) for m in range(k + 1))

half  = S(K('a'), K('aa'), X)                        # [a/aa]X  = ceiling halver
mrg   = S(K(''), K('b'), X)                          # [e/b]X   = a^S
dbl   = S(K('aa'), K('a'), X)                        # [aa/a]X  = doubler
del_last = S(K(''), C(C(K('b'), mrg), K('a')), C(C(X, mrg), K('a')))
# complement box with the halver as pattern lead: [b/(half.b)](mrg.b.mrg)
E_cbox = S(K('b'), C(half, K('b')), C(C(mrg, K('b')), mrg))
# b-free sum-minus-max: [e/(b.mrg)]E_cbox
E_smm  = S(K(''), C(K('b'), mrg), E_cbox)
# halving chain off sum-minus-max: [a/aa]E_smm
E_h2   = S(K('a'), K('aa'), E_smm)

print('== A: the B=2 telescoping degeneracy (hand-derived this round) ==')
MARK('start')
bad = 0
for k in range(1, 13):
    if ev(half, w2k(k)) != 'a' * (2 ** k): bad += 1; print('  A1 FAIL k=%d' % k)
print('  A1 [a/aa]X = a^{2^k}: the LAST RUN as a b-free value (telescoping)')
print('     12 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 11):
    want = 'b'.join('a' * (2 ** m) for m in range(k)) + 'b' + 'a' * (2 ** (k - 1) + 2 ** k) \
           if k >= 1 else None
    # hand form: runs 0..k-1 with separators, then glued run 2^{k-1}+2^k (last b deleted)
    want = 'b'.join('a' * (2 ** m) for m in range(k)) + 'b' + 'a' * (2 ** (k - 1) + 2 ** k)
    if ev(del_last, w2k(k)) != want: bad += 1; print('  A2 FAIL k=%d' % k)
print('  A2 del_last = runs 0..k-1, then glued run 2^{k-1}+2^k (Lane C L3)')
print('     10 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 13):
    S_ = 2 ** (k + 1) - 1
    if ev(E_cbox, w2k(k)) != 'a' * (2 ** k - 1) + 'b' + 'a' * S_:
        bad += 1; print('  A3 FAIL k=%d' % k)
print('  A3 [b/(half.b)](mrg.b.mrg) = a^{2^k-1} b a^S (sum-minus-max as HEAD)')
print('     12 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 13):
    if ev(E_smm, w2k(k)) != 'a' * (2 ** k - 1): bad += 1; print('  A4 FAIL k=%d' % k)
print('  A4 [e/(b.mrg)]E_cbox = a^{2^k-1}: B-FREE SUM-MINUS-MAX')
print('     12 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 13):
    if ev(E_h2, w2k(k)) != 'a' * (2 ** (k - 1)): bad += 1; print('  A5 FAIL k=%d' % k)
print('  A5 [a/aa]E_smm = a^{2^{k-1}}: the 2nd-from-top run, b-free (fixed offset)')
print('     12 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
bad = 0
for k in range(1, 11):
    if ev(dbl, w2k(k)) != 'a' * (2 ** (k + 2) - 2): bad += 1; print('  A6 FAIL k=%d' % k)
print('  A6 [aa/a]X = a^{2^{k+2}-2}: tweak at depth k+2')
print('     10 checks, %d failures -> %s' % (bad, 'VERIFIED' if bad == 0 else 'REFUTED'))
MARK('A done')

print('== A7: contrast on B=3 (the supply class stays in the gaps) ==')
B = 3
def runs(v):
    out, cur = [], 0
    for c in v:
        if c == 'a': cur += 1
        else: out.append(cur); cur = 0
    out.append(cur); return out
def dist_to_powers(n, B):
    if n <= 0: return 10 ** 9
    j = 0
    while B ** (j + 1) <= n: j += 1
    return min(n - B ** j, B ** (j + 1) - n)
worst = 1.0
for k in range(1, 9):
    w = dk(k, B)
    for (nm, e) in [('halver', half), ('E_smm', E_smm), ('E_h2', E_h2)]:
        try: v = len(ev(e, w))
        except PV.Undefined: continue
        d = dist_to_powers(v, B)
        worst = min(worst, d / max(1, v))
        print('  k=%d %-7s len=%d  dist to nearest power=%d' % (k, nm, v, d))
print('  -> min relative distance to any 3^j: %.3f (B=2 gives 0: the telescoping)' % worst)
MARK('A7 done')

print('== B: the dec-refutation class (recorded per charter) ==')
def dec(rs):
    best = [0] * len(rs)
    for i in range(len(rs)):
        best[i] = 1
        for j in range(i):
            if rs[j] > rs[i] and best[j] + 1 > best[i]: best[i] = best[j] + 1
    return max(best) if best else 0
for (nm, e) in [('[X/a]X', S(X, K('a'), X)), ("[X/'b']X", S(X, K('b'), X))]:
    row = []
    for k in range(1, 7):
        v = ev(e, w2k(k))
        row.append((dec(runs(v)), len(v)))
    print('  %-8s (dec, |out|) at k=1..6: %s' % (nm, row))
MARK('B done')

print('== C: tuned-bite dichotomy on D(k;3), k=2..5 (random depth-<=3 battery) ==')
class Bail(Exception): pass
def my_eval_bites(e, w, log):
    t = e[0]
    if t == 'K': return e[1]
    if t == 'V': return w
    if t == 'C':
        return my_eval_bites(e[1], w, log) + my_eval_bites(e[2], w, log)
    if t == 'S':
        R, P, F = (my_eval_bites(x, w, log) for x in (e[1], e[2], e[3]))
        if P == '': raise PV.Undefined
        if max(len(R), len(P), len(F)) > 20000: raise Bail
        out, i, n = [], 0, len(F)
        while i < n:
            j = F.find(P, i)
            if j < 0:
                out.append(F[i:]); break
            out.append(F[i:j]); out.append(R)
            p0 = len(P) - len(P.lstrip('a'))
            pbe = len(P) - len(P.rstrip('a'))
            if p0 > 0:
                s = j - 1
                while s >= 0 and F[s] == 'a': s -= 1
                log.append((Lleft := (j - 1 - s), p0))
            if pbe > 0:
                r = j + len(P)
                s = r
                while s < n and F[s] == 'a': s += 1
                log.append((s - r, pbe))
            i = j + len(P)
        return ''.join(out)
    raise ValueError(t)

def classify(p, S_, B):
    if any(abs(p - B ** j) <= 8 for j in range(0, 20)): return 'tweak'
    for m in range(-3, 2):
        if abs(p - B ** m * S_) <= 8: return 'affine(a=B^%d)' % m
    for u in range(0, 8):
        for v in range(u, 9):
            if abs(p - sum(B ** i for i in range(u, v + 1))) <= 8:
                return 'interval[%d..%d]' % (u, v)
    return 'other'

CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb', 'bab']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

rng = random.Random(20260922)
nexpr = nok = 0
events = {}
midviol = 0
while nexpr < 300:
    e = rand_expr(rng, 3); nexpr += 1
    log = []
    try:
        for k in (2, 3, 4, 5):
            my_eval_bites(e, dk(k, B), log)
        v1 = ev(e, dk(4, B)); l2 = []
        v2 = my_eval_bites(e, dk(4, B), l2)
        if v1 != v2: continue
    except (PV.Undefined, Bail):
        continue
    nok += 1
    for k in (2, 3, 4, 5):
        S_ = sum(B ** m for m in range(k + 1))
        for (L, p) in log:
            surv = L - p
            if p > 8 and any(abs(surv - B ** j) <= 8 for j in range(0, k + 3)):
                cls = classify(p, S_, B)
                events[cls] = events.get(cls, 0) + 1
                if cls.startswith('interval['):
                    u = int(cls[9:cls.index('..')])
                    v = int(cls[cls.index('..') + 2:-1])
                    if u >= 1 and v <= k - 1: midviol += 1
print('  %d expressions instrumented (matches campaign evaluator)' % nok)
print('  exactness-event bite classification (survivor within 8 of a power):')
for (cls, cnt) in sorted(events.items(), key=lambda x: -x[1]):
    print('    %-16s %d' % (cls, cnt))
print('  MIDDLE-INTERVAL bites at exactness events (u>=1, v<=k-1): %d' % midviol)
MARK('C done')

print('== D: structured uniform-rev-on-B=2 attempts (hand-motivated, expected fail) ==')
cands = []
cands.append(('h.b.(E_smm-ish tail)', C(C(half, K('b')), E_smm)))
cands.append(('complement-box head', E_cbox))
pol = S(C(mrg, K('b')), K('aa'), mrg)
cands.append(('E_poll-style+b', S(K('b'), K('aab'), pol)))
cands.append(('block-swap analog', S(S(K(''), K('a'), X), C(X, K('b')), C(C(X, mrg), K('a')))))
for (nm, e) in cands:
    res = []
    for k in (2, 3, 4):
        want = 'b'.join('a' * (2 ** m) for m in range(k, -1, -1))
        try: got = ev(e, w2k(k))
        except PV.Undefined: got = None
        res.append(got == want)
    print('  %-22s reverses w^(k) for k=2,3,4: %s' % (nm, res))
MARK('D done')

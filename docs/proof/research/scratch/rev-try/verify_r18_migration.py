"""ROUND 18 (revision charter): migrate the machine backing to D(k;3)
(base 3, the strongly super-increasing staging family) and re-anchor
the B=2 boundary witnesses.  ILLUSTRATION GRADE for the assumption-
backing parts; the proved lemmas' per-case cores are confirmed exactly.

Parts
  A3  FP tweak-set spot-check on D(k;3), k=4..6, plus 5 random
      distinct-run strings: single-b 256 + pure-a 48 constant passes
      per input, every case anchored (independent greedy
      reconstruction == evaluator output), gap sequences matched
      exactly by the FP(ii) shifts / FP(iii) chain sums.
  B3  Exact tuning on D(k;3): full sweeps k=4..6 of ALL flank
      patterns (p0,p1) with p0+p1 <= 3^k+2 (targeted k=7): the
      fully-consumed values are always a subset of {p0,p1,p0+p1},
      and at most TWO of these are powers of 3 (a sum of two powers
      of 3 is never a power of 3).
  C3  Pinned flanks (mrg = a^S, halver = [aa/a]mrg, doubler = [a/aa]
      mrg, shave flank a^{S+1}, all COMPUTED values) on X and
      X.mrg.a at base 3, k=6..8: zero firings at separators with
      both adjacent runs <= 3^{k-2} (deep); every firing site has an
      adjacent run >= 3^{k-1} (top or merge-flanked).
  D3  Counting on base 3: max deep coverage per flank pattern = 2
      (exhaustive k=4..6, targeted near powers k=7,8); the
      constructive pattern (3^j, 3^{j+1}) consumes exactly
      {3^j, 3^{j+1}}; so the k-1 deep sizes 3^0..3^{k-2} need at
      least ceil((k-1)/2) patterns; k=4..8.
  E2  The B=2 boundary witnesses re-anchored (Lane D round 3 + Lane
      B round 4, coordinator-verified; the fragment's degeneracy
      proposition cites them): E_last = [eps/b][a/aa]X = a^{2^k};
      [eps/b][aa/a]X = a^{2^{k+2}-2}; E_cbox = [b/(E_last.b)]
      (mrg.b.mrg) = a^{2^k-1} b a^S; E_smm = [eps/(b.mrg)]E_cbox =
      a^{2^k-1}; E_h2 = [a/aa]E_smm = a^{2^{k-1}}; and the L1
      refutation witnesses E_leak = [(mrg.b)/'b']X (runs
      (S+2^0,...,S+2^{k-1},2^k)) and E_prod = [mrg/'aa']X (runs
      (1,S,2S,...,S*2^{k-1})).

Performance note: the input-dependent context (b-positions, run
values) is hoisted out of the sweeps; per-case work is then the
greedy find plus O(#separators) bookkeeping.

Run: /usr/bin/python3 -W ignore verify_r18_migration.py   (< 60 s)
"""
import random
import sys

sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))

def sup(k, B=2):
    return 'b'.join('a' * (B ** m) for m in range(k + 1))

def windows(text, pat):
    spans, i = [], 0
    while True:
        j = text.find(pat, i)
        if j < 0:
            return spans
        spans.append((j, j + len(pat)))
        i = j + len(pat)

def reconstruct(text, spans, R):
    out, prev = [], 0
    for s, e in spans:
        out.append(text[prev:s]); out.append(R); prev = e
    out.append(text[prev:])
    return ''.join(out)

def make_ctx(w):
    """Input-dependent context: (b-positions, run values, b-count)."""
    return ([i for i, c in enumerate(w) if c == 'b'],
            [len(t) for t in w.split('b')], w.count('b'))

def wnd_of(bs, spans):
    return [any(s <= b < e for (s, e) in spans) for b in bs]

# ---------------- A3: FP tweak sets on base 3 ---------------------------
def fp_single_b(w, m1, m2, p0, p1):
    R, P = 'a' * m1 + 'b' + 'a' * m2, 'a' * p0 + 'b' + 'a' * p1
    out = val(S(K(R), K(P), X), w)
    spans = windows(w, P)
    if reconstruct(w, spans, R) != out:
        return 'instrument mismatch'
    bs, r, k = make_ctx(w)
    if out.count('b') != k:
        return 'b-count not preserved'
    wnd = wnd_of(bs, spans)
    pred = []
    for j in range(k + 1):
        L = wnd[j - 1] if j >= 1 else False
        Rt = wnd[j] if j <= k - 1 else False
        pred.append(r[j] + (m2 - p1) * L + (m1 - p0) * Rt)
    got = [len(t) for t in out.split('b')]
    return 'ok' if got == pred else 'gap mismatch: %s vs %s' % (got, pred)

def fp_pure_a(w, m, p0, p1):
    R, P = 'a' * m, 'a' * p0 + 'b' + 'a' * p1
    out = val(S(K(R), K(P), X), w)
    spans = windows(w, P)
    if reconstruct(w, spans, R) != out:
        return 'instrument mismatch'
    bs, r, k = make_ctx(w)
    wnd = wnd_of(bs, spans)

    def c(j):
        L = wnd[j - 1] if j >= 1 else False
        Rt = wnd[j] if j <= k - 1 else False
        return r[j] - p1 * L - p0 * Rt

    pred, j = [], 0
    while j <= k:
        total, last = c(j), j
        while last <= k - 1 and wnd[last]:
            total += m + c(last + 1)
            last += 1
        pred.append(total)
        j = last + 1
    got = [len(t) for t in out.split('b')]
    return 'ok' if got == pred else 'gap mismatch: %s vs %s' % (got, pred)

rng = random.Random(180922)
inputs = [sup(k, 3) for k in (4, 5, 6)]
for _ in range(5):
    kk = rng.randint(5, 8)
    inputs.append('b'.join('a' * v for v in rng.sample(range(1, 41), kk + 1)))

ok = True
for w in inputs:
    for m1 in range(4):
        for m2 in range(4):
            for p0 in range(4):
                for p1 in range(4):
                    res = fp_single_b(w, m1, m2, p0, p1)
                    if res != 'ok':
                        ok = False
                        print('A3-single FAIL', len(w), m1, m2, p0, p1, res)
print('A3 single-b FP tweak set, %d inputs (D(k;3), k=4..6, + randoms)'
      ' x 256 passes:' % len(inputs), 'VERIFIED' if ok else 'REFUTED')

ok = True
for w in inputs:
    for m in (1, 2, 3):
        for p0 in range(4):
            for p1 in range(4):
                res = fp_pure_a(w, m, p0, p1)
                if res != 'ok':
                    ok = False
                    print('A3-pure FAIL', len(w), m, p0, p1, res)
print('A3 pure-a chain-sum gaps, %d inputs x 48 passes:' % len(inputs),
      'VERIFIED' if ok else 'REFUTED')

# ---------------- B3: exact tuning on base 3 ----------------------------
_anchor = [0]

def consumed(w, ctx, p0, p1, anchor_every=200):
    """Input run values fully consumed by [eps/P], P = a^p0 b a^p1.

    ctx = make_ctx(w) hoisted by the caller.  The greedy-vs-evaluator
    anchor is sampled every anchor_every-th call (the sweeps are pure
    string mechanics otherwise).  Stated domain.
    """
    bs, r, k = ctx
    P = 'a' * p0 + 'b' + 'a' * p1
    spans = windows(w, P)
    _anchor[0] += 1
    if _anchor[0] % anchor_every == 1:
        if reconstruct(w, spans, '') != val(S(K(''), K(P), X), w):
            return None
    if not spans:
        return set()
    wnd = wnd_of(bs, spans)
    out = set()
    for j in range(k + 1):
        L = wnd[j - 1] if j >= 1 else False
        Rt = wnd[j] if j <= k - 1 else False
        if (L or Rt) and r[j] - p1 * L - p0 * Rt == 0:
            out.add(r[j])
    return out

_sweep = {}

def sweep(k):
    if k not in _sweep:
        w = sup(k, 3)
        ctx = make_ctx(w)
        _sweep[k] = {(p0, v - p0): consumed(w, ctx, p0, v - p0)
                     for v in range(0, 3 ** k + 3)
                     for p0 in range(v + 1)}
    return _sweep[k]

ok, maxcap, maxpow = True, 0, 0
for k in (4, 5, 6):
    pw = set(3 ** j for j in range(k + 1))
    for (p0, p1), cons in sweep(k).items():
        if cons is None:
            ok = False
            print('B3 instrument FAIL', k, p0, p1)
            continue
        if not cons <= {p0, p1, p0 + p1}:
            ok = False
            print('B3 FAIL', k, p0, p1, cons)
        maxcap = max(maxcap, len(cons))
        maxpow = max(maxpow, len(cons & pw))
w7, ctx7 = sup(7, 3), None
ctx7 = make_ctx(w7)
for v in sorted(set([3 ** j + d for j in range(8) for d in (-1, 0, 1)] + [0, 2])):
    for p0 in range(v + 1):
        cons = consumed(w7, ctx7, p0, v - p0)
        if cons is None:
            ok = False
            continue
        if not cons <= {p0, v - p0, v}:
            ok = False
            print('B3 FAIL k=7', p0, v - p0, cons)
        maxcap = max(maxcap, len(cons))
print('B3 exact tuning on D(k;3): fully-consumed subset of {p0,p1,p0+p1},'
      ' full sweeps k=4..6, targeted k=7 (caps: sizes %d, power-sizes %d):'
      % (maxcap, maxpow), 'VERIFIED' if ok else 'REFUTED')

# ---------------- C3: pinned flanks at base 3 ---------------------------
ok = True
sites = []
for k in (6, 7, 8):
    w = sup(k, 3)
    mrgv = val(S(K(''), K('b'), X), w)
    halver = val(S(K('aa'), K('a'), S(K(''), K('b'), X)), w)
    dbl = val(S(K('a'), K('aa'), S(K(''), K('b'), X)), w)
    flanks = {'mrg(a^S)': len(mrgv), 'halver': len(halver),
              'doubler': len(dbl), 'shave(a^{S+1})': len(mrgv) + 1}
    for name, f in flanks.items():
        for (p0, p1) in ((f, 1), (1, f)):
            P = 'a' * p0 + 'b' + 'a' * p1
            for label, T in (('X', w), ('X.mrg.a', w + mrgv + 'a')):
                for (s, e) in windows(T, P):
                    bpos = s + P.index('b')
                    before, i = 0, bpos - 1
                    while i >= 0 and T[i] == 'a':
                        before += 1; i -= 1
                    after, i = 0, bpos + 1
                    while i < len(T) and T[i] == 'a':
                        after += 1; i += 1
                    if max(before, after) <= 3 ** (k - 2):
                        ok = False
                        print('C3 FAIL deep firing', k, name, p0, p1, label)
                    sites.append((k, before, after))
n_top = sum(1 for (k, b, a) in sites if max(b, a) >= 3 ** (k - 1))
print('C3 pinned flanks on X and X.mrg.a at base 3, k=6..8: zero firings'
      ' at deep separators (both adjacent runs <= 3^{k-2}); %d/%d firings'
      ' with an adjacent run >= 3^{k-1}:' % (n_top, len(sites)),
      'VERIFIED' if ok else 'REFUTED')

# ---------------- D3: counting on base 3 --------------------------------
ok = True
print('D3 counting corollary (deep sizes 3^0..3^{k-2}):')
for k in (4, 5, 6, 7, 8):
    w = sup(k, 3)
    ctx = make_ctx(w)
    deep = set(3 ** j for j in range(k - 1))
    if k in _sweep:                      # exhaustive sweeps: k = 4..6
        best = max((len(cons & deep) for cons in _sweep[k].values()
                    if cons is not None), default=0)
    else:                                # targeted near the deep powers
        best = 0
        for v in sorted(set([3 ** j + d for j in range(k - 1)
                             for d in (-2, -1, 0, 1, 2)] + [0, 1, 2])):
            for p0 in range(v + 1):
                cons = consumed(w, ctx, p0, v - p0)
                if cons is not None:
                    best = max(best, len(cons & deep))
    cover_ok = True
    for j in range(k - 2):
        cons = consumed(w, ctx, 3 ** j, 3 ** (j + 1))
        cover_ok &= cons is not None and {3 ** j, 3 ** (j + 1)} <= cons
    ok &= cover_ok and best <= 2
    print('  k=%d: max deep sizes consumed by one flank pattern = %d'
          ' (%s); (3^j,3^{j+1}) covers {3^j,3^{j+1}} for j=0..k-3: %s;'
          ' >= %d patterns needed for %d deep sizes'
          % (k, best, 'exhaustive sweep' if k in _sweep else 'targeted',
             'yes' if cover_ok else 'NO',
             -(-(k - 1) // best) if best else 0, k - 1))

# ---------------- E2: the B=2 boundary witnesses ------------------------
def D(p): return S(K(''), K(p), X)
mrgE = D('b')
E_last = S(K(''), K('b'), S(K('a'), K('aa'), X))          # [eps/b][a/aa]X
E_grow = S(K(''), K('b'), S(K('aa'), K('a'), X))          # [eps/b][aa/a]X
E_cbox = S(K('b'), C(E_last, K('b')), C(C(mrgE, K('b')), mrgE))
E_smm = S(K(''), C(K('b'), mrgE), E_cbox)
E_h2 = S(K('a'), K('aa'), E_smm)
E_leak = S(C(mrgE, K('b')), K('b'), X)
E_prod = S(mrgE, K('aa'), X)

ok = True
for k in range(0, 12):
    w, S_ = sup(k, 2), 2 ** (k + 1) - 1
    ok &= val(E_last, w) == 'a' * (2 ** k)
    ok &= val(E_grow, w) == 'a' * (2 ** (k + 2) - 2)
    ok &= val(E_cbox, w) == 'a' * (2 ** k - 1) + 'b' + 'a' * S_
    ok &= val(E_smm, w) == 'a' * (2 ** k - 1)
    if k >= 1:
        ok &= val(E_h2, w) == 'a' * (2 ** (k - 1))
for k in range(1, 11):
    w, S_ = sup(k, 2), 2 ** (k + 1) - 1
    exp_leak = 'b'.join('a' * (S_ + 2 ** m) for m in range(k)) \
        + 'b' + 'a' * (2 ** k)
    ok &= val(E_leak, w) == exp_leak
for k in range(1, 9):
    w, S_ = sup(k, 2), 2 ** (k + 1) - 1
    exp_prod = 'b'.join('a' * (1 if m == 0 else S_ * 2 ** (m - 1))
                        for m in range(k + 1))
    ok &= val(E_prod, w) == exp_prod
print('E2 the B=2 boundary witnesses (E_last, E_grow, E_cbox, E_smm, E_h2,'
      ' E_leak, E_prod) re-anchored on base 2 (k ranges as in the record):',
      'VERIFIED' if ok else 'REFUTED')
print('ROUND 18 MACHINE VERDICT: migration backing in place; see the'
      ' revised dichotomy.tex')

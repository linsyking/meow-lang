"""ROUND 17 (write-up charter, part b): the tuning-lemma machine
illustration + FP tweak-set spot-checks feeding rev-try/dichotomy.tex.

ILLUSTRATION GRADE throughout: Lane B owns the pinned schema's sharp
form, Lane D owns the tuning lemma's proof attempt.  This battery
confirms the hand derivations behind the fragment on the stated
domains; it proves nothing about all expressions.

Parts
  A  FP tweak-set spot-check (extends the coordinator's [bab/aa]X):
     single-b replacements R = a^m1 b a^m2 and flank patterns
     P = a^p0 b a^p1 (constants m1,m2,p0,p1 <= 3) on distinct-run
     inputs (super-increasing w^(k), k=4..6, plus 5 random
     distinct-run strings): the output's gap sequence is EXACTLY
     r_j + sigma_j, sigma_j = (m2-p1)*L_j + (m1-p0)*R_j with
     L_j/R_j the windowing indicators of the adjacent separators
     (sigma_0, sigma_last single-bite: no L for the first gap, no R
     for the last), and the b-count is preserved.  Pure-a replacements
     R = a^m (m=1..3): gaps are chain sums  sum c + jm over maximal
     windowed-b chains.
  B  Exact tuning: on w^(k), k=4..6 (k=7 targeted near powers), EVERY
     flank pattern (p0,p1) with p0+p1 <= 2^k+2 fully consumes only
     runs whose value lies in {p0, p1, p0+p1}: a pass-fixed cap of
     3 sizes (2 on the powers themselves).
  C  Pinned flanks cannot reach deep separators: on X and on the
     merge-flanked X.mrg.a, the computed pinned flanks (mrg = a^S,
     halver = [aa/a]mrg = a^{2^k}, doubler = [a/aa]mrg, shave flank
     a^{S+1}) fire only at the top separator (adjacent run >=
     2^{k-1}); zero firings at deep separators (both adjacent runs
     <= 2^{k-2}).  k = 6..8.
  D  The counting corollary, illustrated: max deep coverage per flank
     pattern is 2 (on powers), the constructive cover (2^j,2^j)
     achieves {2^j, 2^{j+1}}, so consuming the deep sizes 2^0..2^{k-2}
     needs >= ceil((k-1)/2) patterns = Omega(k) pass nodes; assembled
     with Lemma SD (counting lane, PROVED there; re-illustrated on
     90 multi-interior patterns: all fire <= 1 on distinct-run
     scrutinees, while single-b controls fire up to k times).

Run: /usr/bin/python3 -W ignore verify_r17_tuning.py   (string ops, < 10 s)
"""
import random
import sys

sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))

# ---------------- instrument: the paper's greedy, re-derived ------------
def windows(text, pat):
    """Leftmost-first, non-overlapping occurrences (constant pattern)."""
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

def run_values(w):                 # a-run values (single-b separators)
    return [len(t) for t in w.split('b')]

def b_positions(w):
    return [i for i, c in enumerate(w) if c == 'b']

def sup(k):
    return 'b'.join('a' * (2 ** m) for m in range(k + 1))

def wnd_flags(w, spans):
    return [any(s <= b < e for (s, e) in spans) for b in b_positions(w)]

# ---------------- Part A: FP tweak-set spot-checks ----------------------
def fp_single_b(w, m1, m2, p0, p1):
    """Exact FP(b) check: out gaps == r_j + sigma_j, sigma in the 4-set."""
    R, P = 'a' * m1 + 'b' + 'a' * m2, 'a' * p0 + 'b' + 'a' * p1
    out = val(S(K(R), K(P), X), w)
    spans = windows(w, P)
    if reconstruct(w, spans, R) != out:
        return 'instrument mismatch'
    r, k = run_values(w), w.count('b')
    if out.count('b') != k:
        return 'b-count not preserved'
    wnd = wnd_flags(w, spans)
    pred = []
    for j in range(k + 1):
        L = wnd[j - 1] if j >= 1 else False
        Rt = wnd[j] if j <= k - 1 else False
        pred.append(r[j] + (m2 - p1) * L + (m1 - p0) * Rt)
    got = [len(t) for t in out.split('b')]
    return 'ok' if got == pred else 'gap mismatch: %s vs %s' % (got, pred)

def fp_pure_a(w, m, p0, p1):
    """FP(c) check: gaps are chain sums over maximal windowed-b chains."""
    R, P = 'a' * m, 'a' * p0 + 'b' + 'a' * p1
    out = val(S(K(R), K(P), X), w)
    spans = windows(w, P)
    if reconstruct(w, spans, R) != out:
        return 'instrument mismatch'
    r, k = run_values(w), w.count('b')
    wnd = wnd_flags(w, spans)

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

rng = random.Random(170922)
inputs = [sup(k) for k in (4, 5, 6)]
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
                        print('A-single FAIL', len(w), m1, m2, p0, p1, res)
print('A single-b FP tweak set {0,-p0+m1,-p1+m2,-p0-p1+m1+m2},'
      ' %d inputs x 256 constant passes:' % len(inputs),
      'VERIFIED' if ok else 'REFUTED')

ok = True
for w in inputs:
    for m in (1, 2, 3):
        for p0 in range(4):
            for p1 in range(4):
                res = fp_pure_a(w, m, p0, p1)
                if res != 'ok':
                    ok = False
                    print('A-pure FAIL', len(w), m, p0, p1, res)
print('A pure-a chain-sum gaps, %d inputs x 48 passes:' % len(inputs),
      'VERIFIED' if ok else 'REFUTED')

# ---------------- Part B: exact tuning ----------------------------------
_anchor_calls = [0]

def consumed(w, p0, p1, anchor_every=50):
    """Input run values fully consumed by [eps/P], P = a^p0 b a^p1.

    The greedy-vs-evaluator instrument anchor (reconstruction equals
    the evaluator's output) is sampled every anchor_every-th call --
    the sweeps are pure string mechanics otherwise.  Stated domain.
    """
    P = 'a' * p0 + 'b' + 'a' * p1
    spans = windows(w, P)
    _anchor_calls[0] += 1
    if _anchor_calls[0] % anchor_every == 1:
        if reconstruct(w, spans, '') != val(S(K(''), K(P), X), w):
            return None                  # instrument mismatch
    r, k = run_values(w), w.count('b')
    wnd = wnd_flags(w, spans)
    out = set()
    for j in range(k + 1):
        L = wnd[j - 1] if j >= 1 else False
        Rt = wnd[j] if j <= k - 1 else False
        if (L or Rt) and r[j] - p1 * L - p0 * Rt == 0:
            out.add(r[j])
    return out

_sweep_cache = {}

def sweep(k):
    """consumed sets for all (p0,p1) with p0+p1 <= 2^k+2 on w^(k)."""
    if k not in _sweep_cache:
        w = sup(k)
        _sweep_cache[k] = {(p0, v - p0): consumed(w, p0, v - p0)
                           for v in range(0, 2 ** k + 3)
                           for p0 in range(v + 1)}
    return _sweep_cache[k]

ok, maxcap, maxpower = True, 0, 0
for k in (4, 5, 6):
    for (p0, p1), cons in sweep(k).items():
        if cons is None:
            ok = False
            print('B instrument FAIL', k, p0, p1)
            continue
        if not cons <= {p0, p1, p0 + p1}:
            ok = False
            print('B FAIL', k, p0, p1, cons)
        maxcap = max(maxcap, len(cons))
w = sup(7)
for v in sorted(set([2 ** j + d for j in range(8) for d in (-1, 0, 1)] +
                     [0, 2, 3])):
    if v < 0:
        continue
    for p0 in range(v + 1):
        p1 = v - p0
        cons = consumed(w, p0, p1)
        if cons is None:
            ok = False
            continue
        if not cons <= {p0, p1, p0 + p1}:
            ok = False
            print('B FAIL k=7', p0, p1, cons)
        maxcap = max(maxcap, len(cons))
for k in (4, 5, 6):
    pw = set(2 ** j for j in range(k + 1))
    for cons in sweep(k).values():
        if cons is not None:
            maxpower = max(maxpower, len(cons & pw))
print('B exact tuning: fully-consumed values subset of {p0,p1,p0+p1},'
      ' full sweeps k=4..6, targeted k=7 (cap over all sweeps: %d):'
      % maxcap, 'VERIFIED' if ok else 'REFUTED')

# ---------------- Part C: pinned flanks cannot reach deep --------------
ok = True
details = []
for k in (6, 7, 8):
    w = sup(k)
    mrgv = val(S(K(''), K('b'), X), w)
    halver = val(S(K('aa'), K('a'), S(K(''), K('b'), X)), w)
    dbl = val(S(K('a'), K('aa'), S(K(''), K('b'), X)), w)
    flanks = {'mrg(a^S)': len(mrgv), 'halver(a^{2^k})': len(halver),
              'doubler(a^{2S})': len(dbl), 'shave(a^{S+1})': len(mrgv) + 1}
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
                    if max(before, after) <= 2 ** (k - 2):
                        ok = False
                        print('C FAIL deep firing', k, name, p0, p1, label)
                    details.append((k, name, label, before, after))
deeppct = 100.0 * sum(1 for d in details if max(d[3], d[4]) >= 2 ** (d[0] - 1)) \
    / max(1, len(details))
print('C pinned flanks (mrg, halver, doubler, shave) on X and X.mrg.a,'
      ' k=6..8: zero firings at deep separators (both adjacent runs'
      ' <= 2^{k-2}); %d/%d firings at separators with an adjacent run'
      ' >= 2^{k-1}:'
      % (sum(1 for d in details if max(d[3], d[4]) >= 2 ** (d[0] - 1)),
         len(details)),
      'VERIFIED' if ok else 'REFUTED')

# ---------------- Part D: the Omega(k) counting, illustrated ------------
ok = True
print('D counting corollary (deep sizes 2^0..2^{k-2}):')
for k in (4, 5, 6, 7, 8):
    deep = set(2 ** j for j in range(k - 1))
    best = 0
    for cons in sweep(k).values():
        if cons is not None:
            best = max(best, len(cons & deep))
    cover_ok = True
    for j in range(k - 2):
        cons = sweep(k).get((2 ** j, 2 ** j))
        cover_ok &= cons is not None and {2 ** j, 2 ** (j + 1)} <= cons
    ok &= cover_ok and best <= 2
    print('  k=%d: max deep sizes consumed by one flank pattern = %d;'
          ' (2^j,2^j) covers {2^j,2^{j+1}} for j=0..k-3: %s;'
          ' >= %d patterns needed for %d deep sizes'
          % (k, best, 'yes' if cover_ok else 'NO',
             -(-(k - 1) // best) if best else 0, k - 1))

# SD re-illustration (proved by the counting lane; not a new claim)
ok = True
maxf = 0
for _ in range(60):
    x0, y, x2 = rng.randint(0, 4), rng.randint(1, 4), rng.randint(0, 4)
    P = 'a' * x0 + 'b' + 'a' * y + 'b' + 'a' * x2
    w = sup(rng.choice([5, 6, 7]))
    maxf = max(maxf, len(windows(w, P)))
    ok &= len(windows(w, P)) <= 1
for _ in range(30):
    x0, y1, y2, x3 = (rng.randint(0, 3), rng.randint(1, 3),
                      rng.randint(1, 3), rng.randint(0, 3))
    P = 'a' * x0 + 'b' + 'a' * y1 + 'b' + 'a' * y2 + 'b' + 'a' * x3
    w = sup(rng.choice([5, 6, 7]))
    maxf = max(maxf, len(windows(w, P)))
    ok &= len(windows(w, P)) <= 1
ctrl = 0
for k in (5, 6, 7):
    ctrl = max(ctrl, len(windows(sup(k), 'ab')))
print('D Lemma SD re-illustration: 90 multi-interior patterns on distinct-'
      'run scrutinees, max firings = %d (<= 1: %s); single-b control'
      " 'ab' fires up to %d times (the k-adaptive class)"
      % (maxf, 'VERIFIED' if ok else 'REFUTED', ctrl))
print('ROUND 17 MACHINE VERDICT: illustration-grade, see dichotomy.tex')

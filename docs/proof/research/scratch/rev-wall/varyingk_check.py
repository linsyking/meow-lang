"""rev-wall round 2: VARYING SEPARATOR COUNT checks (machine falsifies only).

A: independent greedy-semantics cross-check (my own S-evaluator vs the
   campaign's prov.py) -- the semantic basis of the SNF / uniform-interleave
   formalization.
B: two uniform-k constructions, hand-derived this round:
   B1  E_abk = [R/X](X.a) with R = [eps/a]X  computes rev on {a b^k : k >= 1}
   B2  E_ab  = [ba/ab]X (constant pattern)    computes rev on {(ab)^k : k>=1}
   B3  b^k -> b^k : identity (record, not obstructive)
   B4  a^i b a^i b a^i : palindrome profile, rev = identity (record)
C: dec-capacity probe: longest strictly-decreasing run-length subsequence
   of E(w) on the increasing diagonal D(k;B), k = 1..6 -- does ANY small
   expression have dec growing with k?  (If yes, my dec-program dies.)
D: extraction hunt: does any small E compute, on D(k;B), a value equal to
   the last run a^{r_k}, the b-free sum-minus-max a^{S-r_k}, w-minus-last-run,
   or any value whose HEAD run is a^{r_k}?  (Falsification of the
   last-run-extraction / arithmetic-split conjectures at small k.)
"""
import sys, random
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S, pp

X = V(0)
def ev(e, w):
    return PV.content(PV.lden(e, (PV.lab_input(w),)))

# ---------------------------------------------------------------- A
def my_eval(e, w):
    """Independent evaluator: greedy leftmost, never rescan inserted text."""
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return w
    if t == 'C':
        return my_eval(e[1], w) + my_eval(e[2], w)
    if t == 'S':
        R, P, F = my_eval(e[1], w), my_eval(e[2], w), my_eval(e[3], w)
        if P == '':
            raise PV.Undefined
        out, i, n = [], 0, len(F)
        while i < n:
            j = F.find(P, i)
            if j < 0:
                out.append(F[i:]); break
            out.append(F[i:j]); out.append(R)
            i = j + len(P)               # never rescan inserted text
        return ''.join(out)
    raise ValueError(t)

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
ag = am = 0
for _ in range(1500):
    e = rand_expr(rng, 3)
    w = ''.join(rng.choice('aabb') for _ in range(rng.randint(1, 14)))
    try:
        v1 = ev(e, w)
    except PV.Undefined:
        try:
            my_eval(e, w); print('A: definedness DISAGREEMENT'); am += 1
        except PV.Undefined:
            pass
        continue
    v2 = my_eval(e, w)
    ag += 1
    if v1 != v2:
        am += 1
        if am < 4: print('A MISMATCH', pp(e)[:80], repr(w), repr(v1), repr(v2))
print('A: %d agree, %d disagree -> %s' % (ag, am, 'VERIFIED' if am == 0 else 'REFUTED'))

# ---------------------------------------------------------------- B
print('== B: uniform-k diagonal constructions ==')
R_abk = S(K(''), K('a'), X)
E_abk = S(R_abk, X, C(X, K('a')))
bad = chk = 0
for k in range(1, 41):
    w = 'a' + 'b' * k
    got = ev(E_abk, w); want = 'b' * k + 'a'; chk += 1
    if got != want:
        bad += 1
        if bad < 4: print('  B1 MISMATCH k=%d got=%r want=%r' % (k, got, want))
print('  B1 a.b^k -> b^k.a : %d checks, %d mismatches -> %s'
      % (chk, bad, 'VERIFIED (CONSTRUCTION)' if bad == 0 else 'REFUTED'))

E_ab = S(K('ba'), K('ab'), X)
bad = chk = 0
for k in range(1, 41):
    w = 'ab' * k
    got = ev(E_ab, w); want = 'ba' * k; chk += 1
    if got != want:
        bad += 1
        if bad < 4: print('  B2 MISMATCH k=%d got=%r want=%r' % (k, got, want))
print('  B2 (ab)^k -> (ba)^k : %d checks, %d mismatches -> %s'
      % (chk, bad, 'VERIFIED (CONSTRUCTION)' if bad == 0 else 'REFUTED'))
for k in (3, 7):
    w = 'b' * k
    print('  B3 b^%d -> %r (identity computes rev)' % (k, w))
for i in (2, 5):
    w = 'a' * i + 'b' + 'a' * i + 'b' + 'a' * i
    print('  B4 a^%d b a^%d b a^%d palindrome: rev==input==%r'
          % (i, i, i, ev(X, w) == w))

# ---------------------------------------------------------------- C + D
B = 3
def D(k):
    return 'b'.join('a' * (B ** m) for m in range(k + 1))
def runs_of(v):
    out, cur = [], 0
    for c in v:
        if c == 'a': cur += 1
        else: out.append(cur); cur = 0
    out.append(cur)
    return out
def dec(rs):
    # longest strictly-decreasing subsequence of run lengths
    best = [0] * len(rs)
    for i in range(len(rs)):
        best[i] = 1
        for j in range(i):
            if rs[j] > rs[i] and best[j] + 1 > best[i]:
                best[i] = best[j] + 1
    return max(best) if best else 0

mrg = S(K(''), K('b'), X)
dbl = S(K('aa'), K('a'), X)
half = S(K('a'), K('aa'), X)
big = C(C(mrg, K('b')), mrg)
LIB = [('X', X), ('mrg', mrg), ('dbl', dbl), ('half', half), ('big', big),
       ('X.X', C(X, X)), ('ww2 C(mrg,mrg)', C(mrg, mrg))]
print('== C: dec-capacity on the increasing diagonal D(k;B=3)  [label fixed 2026-09-22; the code always used B=3] ==')
for (nm, e) in LIB:
    ds = []
    for k in range(1, 6):
        try:
            ds.append(dec(runs_of(ev(e, D(k)))))
        except PV.Undefined:
            ds.append(-1)
    print('  %-14s dec(k=1..5) = %s' % (nm, ds))
print('  sanity dec(rev(D(k))): %s (should be 2..6)'
      % [dec(list(reversed(runs_of(D(k))))) for k in range(1, 6)])

rng = random.Random(4242)
maxdec = {}
nex = nok = 0
hits = []
NTRY = 700
while nex < NTRY:
    e = rand_expr(rng, 3)
    nex += 1
    vals = []
    ok = True
    for k in range(1, 6):
        try:
            v = ev(e, D(k))
        except PV.Undefined:
            ok = False; break
        if len(v) > 600:             # explosive values: skip, keeps run < 60 s
            ok = False; break
        vals.append(v)
    if not ok or len(vals) < 4: continue
    nok += 1
    ks = list(range(1, 6))
    for k, v in zip(ks, vals):
        d = dec(runs_of(v))
        if d > maxdec.get(k, 0):
            maxdec[k] = d
        # D: extraction hits
        rs = runs_of(v)
        rk = B ** k; S_ = sum(B ** m for m in range(k + 1))
        if v == 'a' * rk:
            hits.append(('LAST RUN', k, pp(e)[:120]))
        if v == 'a' * (S_ - rk):
            hits.append(('SUM-MINUS-MAX', k, pp(e)[:120]))
        if rs and rs[0] == rk:
            hits.append(('HEAD = r_k', k, pp(e)[:120]))
        if v == D(k)[:len(D(k)) - rk] and len(v) == len(D(k)) - rk:
            hits.append(('W-MINUS-LAST-RUN', k, pp(e)[:120]))
print('  random sweep: %d tried, %d evaluated on all k=1..5' % (nex, nok))
print('  max dec by k: %s' % sorted(maxdec.items()))
print('  D extraction hits: %s' % (hits if hits else 'NONE'))

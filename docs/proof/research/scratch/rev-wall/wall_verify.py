"""rev-wall round 1: machine falsification battery (machine only falsifies).

A: the SIGN-GATE on F1 (hand-derived): E_asym computes a^f with
   f = 2(i+j) for i>j, i+j for i<=j -- a b-free value whose length is a
   piecewise function of s with a sign-gated jump.  Witnesses that the
   'piecewise' in Lemma S is essential and that sign-of-d is extractable
   as a gate (though not as a length).
B: W2 catalogue sanity (stock values, the lead-augmented w2).
C: run-level invariant falsification sweep on W2 (S-depth <= 3):
   D1  lead i-dominance    (lead i-slope >= j-slope and >= k-slope)
   D2  tail k-dominance
   P1  prefix-sum i-dominance at every run boundary
   P2  suffix-sum k-dominance
   VH  V_h / swapped-flank detection: two-b outputs with run-0 k-typed
       and run-2 i-typed (Lane C's sharp target, h folded into tolerance)
   P1f L-family (Lane C's transplant P1 = a^i b a^{j+k}): one-b, i-typed
       lead, (j+k)-typed tail
   P2f mirror family (P2 = a^{i+j} b a^k): one-b, (i+j)-typed lead,
       k-typed tail
   Slopes measured at step 3 over 9 along each axis at 5 base points
   (different bases sample different cells of the piece structure).
   Only clear violations outside residue jitter are counted (margin
   0.34 slope units; jitter of bounded-period sawtooths over 9 steps
   is < 0.12).
"""
import sys, random
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S, pp

X = V(0)
def valtry(e, w):
    try:
        return PV.content(PV.lden(e, (PV.lab_input(w),)))
    except PV.Undefined:
        return None

# ---------------------------------------------------------------- Part A
print('== A: the sign-gate E_asym on F1 ==')
merge = S(K(''), K('b'), X)                              # [eps/b]X
dbl   = S(K('aa'), K('a'), X)                            # [aa/a]X
diff  = S(K(''), merge, dbl)                             # [eps/merge]dbl
T     = C(X, diff)
Q     = C(K('b'), merge)                                 # b . a^s
E_asym = S(K(''), K('b'), S(K(''), Q, T))                # [eps/b][eps/Q]T
bad = checked = 0
for i in range(1, 26):
    for j in range(1, 26):
        w = 'a' * i + 'b' + 'a' * j
        v = valtry(E_asym, w); checked += 1
        want = 'a' * (2 * (i + j) if i > j else i + j)
        if v != want:
            bad += 1
            if bad < 6:
                print('  MISMATCH i=%d j=%d got=%r want=%r' % (i, j, v, want))
for _ in range(400):
    i = random.randint(1, 300); j = random.randint(1, 300)
    v = valtry(E_asym, 'a' * i + 'b' + 'a' * j); checked += 1
    want = 'a' * (2 * (i + j) if i > j else i + j)
    if v != want:
        bad += 1
print('  A: %d checks, %d mismatches -> %s' %
      (checked, bad, 'VERIFIED' if bad == 0 else 'REFUTED'))

# ---------------------------------------------------------------- Part B
print('== B: W2 catalogue sanity ==')
def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
merge2 = S(K(''), K('b'), X)
big2   = C(C(merge2, K('b')), merge2)
halfm  = S(K('a'), K('aa'), merge2)
for (name, e) in [('merge2', merge2), ('big2', big2), ('C(X,X)', C(X, X)),
                  ('halfm', halfm)]:
    print('  %-7s on (3,4,5): %r' % (name, valtry(e, w2(3, 4, 5))))
R_diag = C(C(halfm, K('b')), halfm)
print('  [R_diag/b]w2 on (3,4,5): %r' %
      valtry(S(R_diag, K('b'), X), w2(3, 4, 5)))

# ---------------------------------------------------------------- Part C
print('== C: run-level invariant falsification sweep on W2 ==')
def runs_of(v):
    out, cur = [], 0
    for c in v:
        if c == 'a': cur += 1
        else: out.append(cur); cur = 0
    out.append(cur)
    return out

BASES = [(5, 5, 5), (2, 8, 4), (8, 2, 4), (4, 4, 9), (9, 3, 2), (3, 9, 3)]
TS = [0, 3, 6, 9]
CAP = 300000

def runvec(e, i, j, k):
    v = valtry(e, w2(i, j, k))
    if v is None or len(v) > CAP:
        return None
    return runs_of(v)

def slopes_from(vals_at):
    """vals_at(t) for t in TS along one axis; returns slope or None"""
    try:
        col = [vals_at(t) for t in TS]
    except PV.Undefined:
        return None
    if any(c is None for c in col):
        return None
    return (col[3] - col[0]) / 9.0

def expr_slopes(e):
    """returns (nb, [per-run [(d_i,d_j,d_k) per base]]) or None"""
    cache = {}
    def rv(i, j, k):
        if (i, j, k) not in cache:
            cache[(i, j, k)] = runvec(e, i, j, k)
        return cache[(i, j, k)]
    for (i0, j0, k0) in BASES:
        for t in TS:
            if rv(i0 + t, j0, k0) is None or \
               rv(i0, j0 + t, k0) is None or rv(i0, j0, k0 + t) is None:
                return None
    nb = len(rv(*BASES[0])) - 1
    for (i0, j0, k0) in BASES:
        for t in TS:
            if len(rv(i0 + t, j0, k0)) - 1 != nb or \
               len(rv(i0, j0 + t, k0)) - 1 != nb or \
               len(rv(i0, j0, k0 + t)) - 1 != nb:
                return None
    out = []
    for u in range(nb + 1):
        per_base = []
        for (i0, j0, k0) in BASES:
            d_i = slopes_from(lambda t: rv(i0 + t, j0, k0)[u])
            d_j = slopes_from(lambda t: rv(i0, j0 + t, k0)[u])
            d_k = slopes_from(lambda t: rv(i0, j0, k0 + t)[u])
            per_base.append((d_i, d_j, d_k))
        out.append(per_base)
    return nb, out

CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb', 'baab', 'bab']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

MARGIN = 0.34
rng = random.Random(20260922)
n_expr = n_ok = 0
viol = {'D1': 0, 'D2': 0, 'P1': 0, 'P2': 0, 'VH': 0, 'P1f': 0, 'P2f': 0}
examples = []
NTRY = 1500
while n_expr < NTRY:
    e = rand_expr(rng, 3)
    n_expr += 1
    res = expr_slopes(e)
    if res is None:
        continue
    nb, sl = res
    n_ok += 1
    m = nb
    def flag(tag):
        viol[tag] += 1
        examples.append((tag, e))
    for (d_i, d_j, d_k) in sl[0]:
        if d_i < d_j - MARGIN or d_i < d_k - MARGIN:
            flag('D1'); break
    for (d_i, d_j, d_k) in sl[m]:
        if d_k < d_i - MARGIN or d_k < d_j - MARGIN:
            flag('D2'); break
    # prefix/suffix sums
    def rvec(i, j, k):
        return runvec(e, i, j, k)
    okp = True
    for u in range(m + 1):
        for (i0, j0, k0) in BASES:
            p_i = slopes_from(lambda t: sum(rvec(i0 + t, j0, k0)[:u + 1]))
            p_j = slopes_from(lambda t: sum(rvec(i0, j0 + t, k0)[:u + 1]))
            p_k = slopes_from(lambda t: sum(rvec(i0, j0, k0 + t)[:u + 1]))
            if p_i < p_j - MARGIN or p_i < p_k - MARGIN:
                flag('P1'); okp = False; break
            s_i = slopes_from(lambda t: sum(rvec(i0 + t, j0, k0)[u:]))
            s_j = slopes_from(lambda t: sum(rvec(i0, j0 + t, k0)[u:]))
            s_k = slopes_from(lambda t: sum(rvec(i0, j0, k0 + t)[u:]))
            if s_k < s_i - MARGIN or s_k < s_j - MARGIN:
                flag('P2'); okp = False; break
        if not okp:
            break
    # V_h: two-b, run0 k-typed, run2 i-typed (k,j,i)+slack on interior
    if m == 2:
        l0 = [(d_i, d_j, d_k) for (d_i, d_j, d_k) in sl[0]
              if abs(d_k - 1.0) <= MARGIN and abs(d_i) <= MARGIN
              and abs(d_j) <= MARGIN]
        t2 = [(d_i, d_j, d_k) for (d_i, d_j, d_k) in sl[2]
              if abs(d_i - 1.0) <= MARGIN and abs(d_k) <= MARGIN
              and abs(d_j) <= MARGIN]
        if l0 and t2:
            flag('VH')
    # P1f: one-b, i-typed lead, (j+k)-typed tail
    if m == 1:
        for (a_i, a_j, a_k) in sl[0]:
            if abs(a_i - 1.0) > MARGIN:
                break
        else:
            for (b_i, b_j, b_k) in sl[1]:
                if b_j + b_k - 2 * b_i > MARGIN:
                    flag('P1f'); break
        for (a_i, a_j, a_k) in sl[0]:
            if abs(a_i + a_j - 2.0) > 1.2 * MARGIN:
                break
        else:
            for (b_i, b_j, b_k) in sl[1]:
                if b_k - b_i > MARGIN and abs(b_i) <= MARGIN:
                    flag('P2f'); break
print('  expressions tried: %d, cleanly evaluated (fixed #b over probes): %d'
      % (n_expr, n_ok))
print('  violations:', viol)
seen = set()
for (tag, e) in examples[:15]:
    s = pp(e)
    if s in seen: continue
    seen.add(s)
    print('  %s: %s' % (tag, s[:160]))
print('  (margin %.2f slope units; only clear violations counted)' % MARGIN)

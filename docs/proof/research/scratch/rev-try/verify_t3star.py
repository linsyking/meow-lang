"""ROUND 15 (construction lane) — THEOREM T3* (rational correlations) and
Lemma-S stress tests (cross-lane note).

T3*: for all coprime c >= 0, d >= 1, rev is computable on
    F_{c,d} = {a^i b a^j b a^k : j = c(i+k)/d}   over Sigma = {a,b}
    (integrality of j forces d | i+k when gcd(c,d) = 1), by
    E_{c,d} = [ b . M . b  /  X ] . ( F . b . M . b . F )
    F = [a^d / a^{c+d}][eps/b]X ,  M = [a^c / a^{c+d}][eps/b]X
On F_{c,d}: S = i+j+k = (c+d)(i+k)/d, so F evaluates to
d*floor(S/(c+d)) + S mod (c+d) = d*(i+k)/d = i+k EXACTLY, and M to
c*(i+k)/d = j EXACTLY.  The pattern X = a^i b a^j b a^k (two b's,
interior j) fires once at the (b,b) pair of T = F.b.M.b.F (interior
match EXACT, flanks i+k with remnants (k, i)), and R = b.M.b supplies
the middle: output a^k b a^j b a^i = rev.
(c,d) = (m-1,1) is the integer m-family of verify_t2_corr.py.

Lemma-S stress tests (for Lane A, whose relayed lemma says: total
a-content of any constructible value on w2 is a piecewise function of
S = i+j+k alone):
  ST1: [merge/'bb'] . [b/a]X  has total S*floor((S+2)/2) ~ S^2/2:
       quadratic in S -> the AFFINE (diagonal) form is dead.
  ST2: [aa/a]X has total ceil(i/2)+ceil(j/2)+ceil(k/2), which is NOT a
       function of S alone (S=5: (2,2,1)->3 but (3,1,1)->4) -> the
       S-EXACT form needs a +O(1) jitter clause (or cells).
Run: /usr/bin/python3 -W ignore verify_t3star.py   (< 30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))

mrg = S(K(''), K('b'), X)                       # [eps/b]X = a^S

def E_cd(c, d):
    """F = [a^d/a^{c+d}]mrg, M = [a^c/a^{c+d}]mrg; E = [b.M.b/X](F.b.M.b.F)"""
    F = S(K('a' * d), K('a' * (c + d)), mrg)
    M = S(K('a' * c), K('a' * (c + d)), mrg)
    R = C(C(K('b'), M), K('b'))
    T = C(C(C(F, K('b')), M), C(K('b'), F))
    return S(R, X, T), F, M

def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k

print('=== T3* rational correlation family ===')
allok = True
cases = [(0, 1), (1, 1), (2, 1), (3, 1), (1, 2), (3, 2), (2, 3),
         (5, 2), (4, 3), (1, 3)]
for (c, d) in cases:
    E, F, M = E_cd(c, d)
    ok = True
    n = 0
    for t in range(0, 26):            # i+k = d*t, j = c*t
        for i in range(0, d * t + 1):
            k = d * t - i
            j = c * t
            w = w2(i, j, k)
            ok &= val(E, w) == w[::-1]
            n += 1
    rng = random.Random(hash((c, d)) & 0xffff)
    for _ in range(300):
        t = rng.randint(0, 120)
        i = rng.randint(0, d * t)
        k = d * t - i
        w = w2(i, c * t, k)
        ok &= val(E, w) == w[::-1]
    # intermediates
    for t in range(0, 10):
        for i in range(0, d * t + 1):
            k = d * t - i
            w = w2(i, c * t, k)
            ok &= val(F, w) == 'a' * (i + k)
            ok &= val(M, w) == 'a' * (c * t)
    print('  (c,d)=(%d,%d) family j=c(i+k)/d, %d grid + 300 random + '
          'intermediates:' % (c, d, n), 'VERIFIED' if ok else 'REFUTED')
    allok &= ok

# prov: never DB, injective
rng = random.Random(99)
ok = True
for (c, d) in [(1, 2), (3, 2)]:
    E, _, _ = E_cd(c, d)
    for _ in range(200):
        t = rng.randint(0, 60)
        i = rng.randint(0, d * t)
        w = w2(i, c * t, d * t - i)
        p = prv(E, w)
        ok &= p != tuple(range(len(w) - 1, -1, -1))
        ok &= len(set(p)) == len(p)
print('  T3* prov never DB + injective (200 random x2):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok
print('T3*:', 'ALL VERIFIED' if allok else 'REFUTED')

print('=== Lemma-S stress tests (cross-lane, same-letter w2) ===')
acnt = lambda s: s.count('a')

# ST1: quadratic-in-S a-count (kills affine diagonality).  [b/a]X = b^{S+2};
# [merge/'bb'] fires floor((S+2)/2) times, each inserting a^S; a trailing b
# survives iff S+2 odd.  a-count = S*floor((S+2)/2) in every case.
dbl_b = S(K('b'), K('a'), X)                       # [b/a]X: a's -> b's
quad = S(mrg, K('bb'), dbl_b)                      # [merge/'bb']...
ok = True
for (i, j, k) in [(2, 1, 3), (4, 0, 1), (1, 1, 1), (3, 2, 0), (5, 3, 2)]:
    Ssum = i + j + k
    out = val(quad, w2(i, j, k))
    ok &= acnt(out) == Ssum * ((Ssum + 2) // 2)
    ok &= (len(out) - acnt(out)) == (Ssum + 2) % 2   # leftover b iff odd
print('  ST1 [merge/bb].[b/a]X a-count = S*floor((S+2)/2) (quadratic):',
      'VERIFIED' if ok else 'REFUTED')

# ST2: ceil-halving a-count is NOT a function of S alone (kills S-exact)
half = S(K('a'), K('aa'), X)                       # [aa/a]X
ok = True
for (i, j, k), want in [((2, 2, 1), 3), ((3, 1, 1), 4),
                        ((4, 0, 0), 2), ((1, 1, 2), 3), ((0, 3, 1), 3)]:
    ok &= acnt(val(half, w2(i, j, k))) == want
a1 = acnt(val(half, w2(2, 2, 1)))     # S = 5
a2 = acnt(val(half, w2(3, 1, 1)))     # S = 5
print('  ST2 [aa/a]X a-counts (S=5: (2,2,1)->%d vs (3,1,1)->%d):'
      % (a1, a2), 'CONFIRMED (not an S-function)' if ok else 'REFUTED')
print('  -> Lemma S must be stated as f(S) + O(1) jitter (or on cells);')
print('     S-exact and affine forms are both refuted.')

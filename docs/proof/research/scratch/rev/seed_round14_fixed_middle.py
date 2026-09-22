"""SEED for round 14 (coordinator's construction, found during round-13
verification; machine-verified by me 2026-09-21 with prov.py/lcore).

THE FIXED-MIDDLE THEOREM (instances).  For a fixed middle string M and
c = c(M), the expression
    E_M = [a^c M^R a^c / w] . C(shave_M, M, shave_M)
computes rev on {a^i M a^k : i, k >= c}, where shave_M computes
a^{i+k-c} from w = a^i M a^k by junction-anchored deletion passes.
Round 13's E_swap is the degenerate case M = 'b', c = 0 (shave = merge).

Verified instances (grid 12x12/14x14 + 400 random to 200, prov.py):
  M='b'     c=0  shave=[e/b]                          (round 13)
  M='bab'   c=1  shave=[e/(ab)]                       2 separators
  M='baab'  c=2  shave=[e/(aab)]                       2 separators
  M='babab' c=1  shave=[e/(ab)]                       3 separators
  M='baac'  c=2  shave=[e/(aab)][e/(aac)]             mixed letters
  M='bb'    c=2  shave=[e/(ba)][e/(ab)]               adjacent seps
NOTE the M='bb' lesson (my own hand-derivation slip, caught by the
machine): [e/(ba)] consumes the b PLUS one right-flank a, so c = 2,
not 1.  Derive c(M) from the actual firing structure, never by eyeball.

Consequences (to be proved in round 14):
  1. The 13.7 wall is at VARYING interior runs, not at >= 2 separators
     as such: every fixed-interior family, at every separator count,
     falls to the same symmetrization engine.  13.7's statements about
     w2 (all of i,j,k varying) are unaffected -- this is a missed
     positive stratum, consistent with the caveat in 13.7.
  2. Calculus fact to prove (strengthens 13.2(i)): a b-free pattern
     with b-free replacement maps each run by psi(u) = r*floor(u/p)
     + (u mod p); psi(u) = u - c for all large u forces c = 0.  So a
     CONSTANT can never be shaved off a b-free run by b-free means --
     the shave fundamentally needs M's junction b's.
  3. Open reduction question: does rev on the ALL-VARYING two-b family
     {a^i b a^j b a^k} imply the split (middle-run isolation)?
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0); lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def D(p):            return S(K(''), K(p), X)          # [e/p]
def symm(sh, M, R):  return S(K(R), X, C(C(sh, K(M)), sh))

cases = [
    # (M, c, R, E)
    ('bab',   1, 'ababa',   symm(D('ab'),  'bab',   'ababa')),
    ('baab',  2, 'aabaabaa', symm(D('aab'), 'baab',  'aabaabaa')),
    ('babab', 1, 'abababa', symm(D('ab'),  'babab', 'abababa')),
    ('baac',  2, 'aacaabaa', symm(S(K(''), K('aab'), D('aac')),
                                 'baac',  'aacaabaa')),
    ('bb',    2, 'aabbaa',  symm(S(K(''), K('ba'), D('ab')),
                                 'bb',    'aabbaa')),
]
allok = okp = True
for (M, c, R, E) in cases:
    for i in range(c, c + 14):
        for k in range(c, c + 14):
            w = 'a' * i + M + 'a' * k
            allok &= val(E, w) == 'a' * k + M[::-1] + 'a' * i
    rng = random.Random(hash(M) & 0xffff)
    for _ in range(400):
        i, k = rng.randint(c, 200), rng.randint(c, 200)
        w = 'a' * i + M + 'a' * k
        allok &= val(E, w) == 'a' * k + M[::-1] + 'a' * i
    for _ in range(300):
        i, k = rng.randint(c, 60), rng.randint(c, 60)
        w = 'a' * i + M + 'a' * k
        p, n = prv(E, w), len(w)
        okp &= p != tuple(range(n - 1, -1, -1)) and len(set(p)) == len(p)
    print('M=%-6s c=%d: %s' % (M, c, 'VERIFIED' if allok else 'REFUTED'))
print('prov never DB, injective:', 'VERIFIED' if okp else 'REFUTED')
print('SEED:', 'ALL VERIFIED' if (allok and okp) else 'REFUTED')

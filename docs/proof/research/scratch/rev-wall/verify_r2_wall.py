"""Coordinator verification battery for rev-wall ROUND 2 (Lane D).

Fresh checks, my conventions (prov.py/lcore.py ground truth):

  1  Dissection replay: regenerate Lane D's part-C/D sweep (same seed
     4242, same rand_expr), find the k=2 SUM-MINUS-MAX hit(s), and
     evaluate them at k=1..6 -- is the hit a CONSTANT (coincidence)
     or genuine extraction (grows with k)?
  2  B1 fresh encoding (my hand derivation): E_abk = [R/X](X.a),
     R = [eps/a]X, computes rev on {a.b^k : k>=1}; k=0 must FAIL
     (pattern 'a' fires twice -> output eps).
  3  B2 fresh encoding: [ba/ab]X computes rev on {(ab)^k : k>=1};
     off-family honesty checks (NOT rev on near-miss strings).
  4  SNF on the CAMPAIGN evaluator: for random S(R,P,F) expressions,
     prov(E,w) must equal the greedy-interleave of F(w)'s remnants
     with R(w) at P(w)'s leftmost-disjoint positions -- the Sweep
     Normal Form checked DIRECTLY against the ground-truth
     evaluator, not just against Lane D's reimplementation.

Run: /usr/bin/python3 -W ignore verify_r2_wall.py   (~20 s)
"""
import sys, random
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S, pp

X = V(0)
def ev(e, w):
    return PV.content(PV.lden(e, (PV.lab_input(w),)))
def evtry(e, w):
    try:
        return ev(e, w)
    except PV.Undefined:
        return None

# ------------------------------------------------------------- 1
CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb', 'bab']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

B = 3
def D(k):
    return 'b'.join('a' * (B ** m) for m in range(k + 1))

print('1  dissection replay (Lane D sweep, seed 4242):')
rng = random.Random(4242)
nex = 0
hits2 = []
while nex < 700:
    e = rand_expr(rng, 3)
    nex += 1
    vals = []
    ok = True
    for k in range(1, 6):
        v = evtry(e, D(k))
        if v is None or len(v) > 600:
            ok = False; break
        vals.append(v)
    if not ok or len(vals) < 4:
        continue
    k = 2; v = vals[k - 1]
    rk = B ** k; S_ = sum(B ** m for m in range(k + 1))
    if v == 'a' * (S_ - rk):
        hits2.append(e)
print('   k=2 SUM-MINUS-MAX hits replayed: %d' % len(hits2))
allok = len(hits2) == 1
for e in hits2:
    row = []
    for k in range(1, 7):
        v = evtry(e, D(k))
        row.append(v if (v is not None and len(v) <= 40) else
                   ('len%d' % len(v) if v is not None else 'UND'))
    print('   values at k=1..6: %s' % row)
    # dissection: constant a^4 on k=2,3,4 (and beyond) = coincidence;
    # genuine extraction would equal a^{S-r_k} = a^{(3^k-1)/2} growth
    for k in (2, 3, 4, 5, 6):
        v = evtry(e, D(k))
        want = 'a' * (sum(B ** m for m in range(k + 1)) - B ** k)
        if v is not None and len(v) <= 600:
            allok &= (v == 'a' * 4)          # constant-coincidence claim
print('1  dissection (hits are constant, not extraction):',
      'VERIFIED' if allok else 'REFUTED')

# ------------------------------------------------------------- 2
R_abk = S(K(''), K('a'), X)                       # [eps/a]X
E_abk = S(R_abk, X, C(X, K('a')))                 # [R/X](X.a)
ok = True
for k in range(1, 61):
    w = 'a' + 'b' * k
    ok &= ev(E_abk, w) == 'b' * k + 'a'
# k=0 must FAIL (the only boundary miss, as reported)
w0 = 'a'
fails_at_0 = ev(E_abk, w0) != 'a'
print('2  B1 [R/X](X.a) on a.b^k (k=1..60) + fails at k=0:',
      'VERIFIED' if (ok and fails_at_0) else 'REFUTED')
allok &= ok and fails_at_0

# ------------------------------------------------------------- 3
E_ab = S(K('ba'), K('ab'), X)
ok = True
for k in range(1, 61):
    w = 'ab' * k
    ok &= ev(E_ab, w) == 'ba' * k
# honesty: near-family strings are NOT rev'd by it (domain precision)
off = []
for w in ['aba', 'aab', 'abba', 'ababa', 'aabb', 'bab']:
    if ev(E_ab, w) == w[::-1]:
        off.append(w)
print('3  B2 [ba/ab]X on (ab)^k (k=1..60), off-family not rev:',
      'VERIFIED' if (ok and not off) else 'REFUTED (rev at %s)' % off)
allok &= ok and not off

# ------------------------------------------------------------- 4
# SNF on the campaign evaluator: prov(S(R,P,F), w) == interleave of
# F(w) remnants with R(w) at P(w)'s greedy leftmost disjoint sites.
rng = random.Random(20260922)
n = agreed = 0
for _ in range(1200):
    e = S(rand_expr(rng, 2), rand_expr(rng, 2), rand_expr(rng, 2))
    w = ''.join(rng.choice('aabb') for _ in range(rng.randint(1, 12)))
    try:
        Rv = ev(e[1], w); Pv = ev(e[2], w); Fv = ev(e[3], w)
        if Pv == '':
            raise PV.Undefined
        got = ev(e, w)
    except PV.Undefined:
        continue
    # greedy leftmost disjoint packing of Pv in Fv
    out, i = [], 0
    while i < len(Fv):
        j = Fv.find(Pv, i)
        if j < 0:
            out.append(Fv[i:]); break
        out.append(Fv[i:j]); out.append(Rv)
        i = j + len(Pv)
    snf = ''.join(out)
    n += 1
    if snf == got:
        agreed += 1
    elif n - agreed < 4:
        print('   SNF MISMATCH', pp(e)[:70], repr(w), repr(got), repr(snf))
print('4  SNF vs campaign evaluator: %d/%d agree' % (agreed, n),
      '-> VERIFIED' if agreed == n else '-> REFUTED')
allok &= agreed == n

print()
print('COORDINATOR BATTERY (rev-wall round 2):',
      'ALL VERIFIED' if allok else 'REFUTED')
sys.exit(0 if allok else 1)

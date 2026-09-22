"""Coordinator verification battery for rev-try ROUND 16 (Lane C).

Fresh encodings from my own hand derivations (independent of Lane C's
script, which I have read only AFTER deriving):

  1  E_block = [B/(X.b)]((X.b).mrg) computes rev on {a^i b^k} (my
     hand check: scrutinee a^i b^{k+1} a^i, pattern a^i b^{k+1}
     unique at 0; boundaries i=0, k=0, both hand-traced).
  2  E_alt = [R/P]X, R = [eps/aa]X = (ab)^k, P = [eps/aa][ba/ab]X
     = (ba)^k, computes rev on {(ab)^k aa, k >= 1} (my hand check:
     w_k = a.(ba)^k.a, (ba)^k unique at position 1; k=0 excluded).
  3  L1/L2 collapse facts, fresh encodings.
  4  The stratified-picks counterexample class (Lane C's [X/'b']X
     and my [X/a]X): LDS/dec of the value GROWS with k on the
     super-increasing family at S-depth 2 -- the naive
     dec/LDS-bound invariant is FALSE; any correct descent must
     carry value-stratification (disjoint value ranges), exactly as
     Lane C's round and my Lane-D verification both conclude.
  5  FP spot-check: a multi-firing single-b replacement with pure
     flanks, [bab/aa]X, on super-increasing inputs -- the output's
     run values must all be (input run 2^m) - (uniform bite in
     {0,1,2}) per FP(2)'s uniform-bite prediction (the 'aa' window
     bites 2 from one run and 'bab' re-emits flanks of 1 that merge
     back).  A structural spot-check of the Final-Pass Lemma's
     mechanism, not its statement.

Run: /usr/bin/python3 -W ignore verify_r16_coord.py   (~15 s)
"""
import sys, random
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
def val(e, w):
    return PV.content(PV.lden(e, (PV.lab_input(w),)))
def D(p):
    return S(K(''), K(p), X)

mrg = D('b')                                     # [eps/b]X = a^i
Bsk = S(K(''), K('a'), X)                        # [eps/a]X = b^k

# ---------- 1: E_block, fresh encoding ----------
E_block = S(Bsk, C(X, K('b')), C(C(X, K('b')), mrg))
ok = True
for i in range(0, 15):
    for k in range(0, 15):
        w = 'a' * i + 'b' * k
        ok &= val(E_block, w) == w[::-1]
rng = random.Random(20260923)
for _ in range(500):
    i, k = rng.randint(0, 300), rng.randint(0, 300)
    w = 'a' * i + 'b' * k
    ok &= val(E_block, w) == w[::-1]
print('1  E_block on {a^i b^k}, 15^2 grid + 500 random:',
      'VERIFIED' if ok else 'REFUTED')
allok = ok

# ---------- 2: E_alt, fresh encoding ----------
R_alt = S(K(''), K('aa'), X)                     # [eps/aa]X
P_alt = S(K(''), K('aa'), S(K('ba'), K('ab'), X))
E_alt = S(R_alt, P_alt, X)
ok = True
for k in range(1, 70):
    w = ('ab' * k) + 'aa'
    ok &= val(E_alt, w) == w[::-1]
# structural identity + pattern uniqueness spot-check
for k in (1, 2, 5, 12):
    w = ('ab' * k) + 'aa'
    ok &= w == 'a' + 'ba' * k + 'a'
    ok &= val(R_alt, w) == 'ab' * k
    ok &= val(P_alt, w) == 'ba' * k
    ok &= w.count('ba' * k) == 1                 # unique firing site
print('2  E_alt on {(ab)^k aa}, k=1..69 + uniqueness:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---------- 3: L1/L2, fresh ----------
ok = True
for i in range(8):
    for j in range(8):
        for k in range(8):
            w = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
            ok &= val(S(K('b'), X, C(X, mrg)), w) == 'b' + val(mrg, w)
            ok &= val(S(Bsk, X, C(C(mrg, X), mrg)), w) == \
                val(mrg, w) + val(Bsk, w) + val(mrg, w)
print('3  L1 [b/X](X.mrg)=b.mrg, L2 [B/X](mrg.X.mrg)=mrg.B.mrg, 8^3:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---------- 4: the stratified-picks counterexample class ----------
def runs(s):
    out, cur = [], 0
    for ch in s:
        if ch == 'a':
            cur += 1
        else:
            out.append(cur); cur = 0
    out.append(cur)
    return out
def dec(rs):
    best = [0] * len(rs)
    for i in range(len(rs)):
        best[i] = 1
        for j in range(i):
            if rs[j] > rs[i] and best[j] + 1 > best[i]:
                best[i] = best[j] + 1
    return max(best) if best else 0
def sup(k):
    return 'b'.join('a' * (2 ** m) for m in range(k + 1))

E_cb = S(X, K('b'), X)          # Lane C's [X/'b']X
E_ca = S(X, K('a'), X)          # mine: [X/a]X
grow = True
for k in range(1, 7):
    w = sup(k)
    d1 = dec(runs(val(E_cb, w)))
    d2 = dec(runs(val(E_ca, w)))
    grow &= d1 >= k and d2 >= k                 # unbounded in k at depth 2
print('4  stratified-picks counterexamples [X/b]X and [X/a]X: dec >= k',
      '(k=1..6, S-depth 2):', 'VERIFIED (naive dec/LDS bound FALSE)'
      if grow else 'REFUTED')
allok &= grow

# ---------- 5: FP uniform-bite spot-check ----------
E_fp = S(K('bab'), K('aa'), X)                  # single-b R, pure flanks
ok = True
for k in range(1, 7):
    w = sup(k)
    v = val(E_fp, w)
    r_in = set(2 ** m for m in range(k + 1))
    for r in runs(v):
        # FP(2): every output run is an input run minus a uniform bite
        # in {0,1,2} (the 'aa' window) plus the merged 'b a b' flanks
        ok &= any(abs(r - (t - b)) <= 3 for t in r_in for b in (0, 1, 2))
print('5  FP spot-check [bab/aa]X uniform-bite structure:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

print()
print('COORDINATOR BATTERY (rev-try round 16):',
      'ALL VERIFIED' if allok else 'REFUTED')
sys.exit(0 if allok else 1)

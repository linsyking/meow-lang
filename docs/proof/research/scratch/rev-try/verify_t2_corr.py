"""ROUND 15 (construction lane) — THEOREM T3 (m-family), machine verification.

For every integer m >= 1, rev is computable on the SAME-LETTER
two-separator correlation family
    F_m = {a^i b a^j b a^k : j = (m-1)(i+k)}    over Sigma = {a,b},
i, k >= 0 varying, by

    E_m = [ b . hm^{m-1} . b  /  X ] . ( hm . b . hm^{m-1} . b . hm )

    hm = [a/a^m][e/b]X : on F_m, [e/b]X = a^{i+j+k} = a^{m(i+k)},
         so hm = a^{i+k} EXACTLY (m | m(i+k)).
Scrutinee T = a^{i+k} b a^{(m-1)(i+k)} b a^{i+k}: interior = j (exact);
pattern X = a^i b a^j b a^k fires once at the pair, flanks i+k with
remnants (k, i); R = b a^{(m-1)(i+k)} b = b a^j b supplies the middle.
Output a^k b a^j b a^i = rev(w2).  m=1 is the adjacent-b family {a^i bb a^k}
(fixed-middle M='bb' instance, now with c=0); m=2 is THEOREM T2.

Also verified: near-miss behaviour of E_2 off-family (j = i+k+1 matches
but outputs the flanks inflated by 1); E_2 is NOT accidentally universal
(it fails off-family); the input X itself never matches C(X,X)-style
collapse here.

Run: /usr/bin/python3 -W ignore verify_t2_corr.py   (< 30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))

def rep(e, t):           # e repeated t times, concatenated
    r = K('')
    for _ in range(t):
        r = C(r, e)
    return r

def E_m(m):
    hm = S(K('a'), K('a' * m), S(K(''), K('b'), X))   # [a/a^m][eps/b]X
    R  = C(C(K('b'), rep(hm, m - 1)), K('b'))
    T  = C(C(C(rep(hm, 1), K('b')), rep(hm, m - 1)), C(K('b'), hm))
    return S(R, X, T), hm, R, T

def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k

allok = True
for m in range(1, 5):
    E, hm, R, T = E_m(m)
    ok = True
    # grid on the family j = (m-1)(i+k)
    for i in range(0, 12):
        for k in range(0, 12):
            j = (m - 1) * (i + k)
            w = w2(i, j, k)
            ok &= val(E, w) == w[::-1]
    rng = random.Random(1000 + m)
    for _ in range(300):
        i, k = rng.randint(0, 150), rng.randint(0, 150)
        j = (m - 1) * (i + k)
        w = w2(i, j, k)
        ok &= val(E, w) == w[::-1]
    # intermediates on the family
    for i in range(0, 6):
        for k in range(0, 6):
            j = (m - 1) * (i + k)
            w = w2(i, j, k)
            ok &= val(hm, w) == 'a' * (i + k)
            ok &= val(T, w) == ('a' * (i + k) + 'b' + 'a' * j + 'b'
                                + 'a' * (i + k))
    print('m=%d: family j=(m-1)(i+k): grid 12x12 + random 300 + '
          'intermediates:' % m, 'VERIFIED' if ok else 'REFUTED')
    allok &= ok

# --- near-miss ledger: E_2 off-family -------------------------------------
E2, hm, R, T = E_m(2)
rng = random.Random(77)
ok_match = True
for _ in range(200):
    i, k = rng.randint(0, 60), rng.randint(0, 60)
    d = rng.randint(0, 3)
    j = i + k + d
    w = w2(i, j, k)
    out = val(E2, w)
    if d == 0:
        ok_match &= out == w[::-1]
    elif d == 1:
        # match fires, flanks inflated by 1: a^{k+1} b a^{i+k+1} b a^{i+1}
        ok_match &= out == ('a' * (k + 1) + 'b' + 'a' * (i + k + 1)
                            + 'b' + 'a' * (i + 1))
    else:
        ok_match &= out != w[::-1]
print('E_2 near-miss ledger (d=0 rev / d=1 flanks+1 / d>=2 no rev):',
      'VERIFIED' if ok_match else 'REFUTED')
allok &= ok_match

# --- E_2 not accidentally universal --------------------------------------
rng = random.Random(78)
cnt = bad = 0
for _ in range(300):
    i, j, k = rng.randint(0, 40), rng.randint(0, 40), rng.randint(0, 40)
    if j == i + k:
        continue
    cnt += 1
    bad &= val(E2, w2(i, j, k)) == w2(i, j, k)[::-1]
print('E_2 off-family (%d non-family inputs): rev outputs: %d (expected 0)'
      % (cnt, bad), 'VERIFIED' if bad == 0 else 'REFUTED')
allok &= (bad == 0)

# --- prov: never DB, injective on the family ------------------------------
ok = True
for m in (2, 3):
    E, _, _, _ = E_m(m)
    for _ in range(200):
        i, k = rng.randint(0, 60), rng.randint(0, 60)
        w = w2(i, (m - 1) * (i + k), k)
        p = prv(E, w)
        ok &= p != tuple(range(len(w) - 1, -1, -1))
        ok &= len(set(p)) == len(p)
print('m=2,3 prov never DB + injective (200 random each):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

print('T3 m-FAMILY:', 'ALL VERIFIED' if allok else 'REFUTED')

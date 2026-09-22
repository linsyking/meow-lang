"""ROUND 15 (construction lane) — THEOREM T1, machine verification.

rev is computable on the MIXED-LETTER two-separator family
    F_mix = {a^i b a^j c a^k : i, j, k >= 0}   over Sigma = {a, b, c},
with ALL of i, j, k VARYING, by

    E_mix = [b / mrg.b] . C( Cc , Bb )

    mrg = [e/c][e/b]X            = a^{i+j+k}
    Lb  = [e/c]X                  = a^i b a^{j+k}     (one-b projection)
    Lc  = [e/b]X                  = a^{i+j} c a^k      (one-c projection)
    Cc  = [c/Lc](mrg . c . mrg)   = a^k c a^{i+j}      (c-anchored box)
    Bb  = [b/Lb](mrg . b . mrg)   = a^{j+k} b a^i      (b-anchored box)
    T   = Cc . Bb = a^k c a^{i+2j+k} b a^i

Final pass: pattern mrg.b (one b, leading run i+j+k) fires once at T's
unique b, shaving a^{i+j+k} off the middle run a^{i+2j+k}, leaving a^j;
output a^k c a^j b a^i = rev(X).

Checks: content = rev on 11x11x11 grid (incl. all boundaries),
400 random (i,j,k) to 200, intermediate values on a grid, prov never DB
+ injective, laundered L_a.L_b.L_c.E_mix gives rev with prov == ().
Run: /usr/bin/python3 -W ignore verify_t1_mixed.py   (< 30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def D(p):            return S(K(''), K(p), X)          # [eps/p]X
def symm(sh, M, R):  return S(K(R), X, C(C(sh, K(M)), sh))

mrg = S(K(''), K('c'), D('b'))          # [eps/c][eps/b]X = a^{i+j+k}
Lb  = D('c')                            # [eps/c]X = a^i b a^{j+k}
Lc  = D('b')                            # [eps/b]X = a^{i+j} c a^k
Cc  = S(K('c'), Lc, C(C(mrg, K('c')), mrg))    # [c/Lc](mrg c mrg)
Bb  = S(K('b'), Lb, C(C(mrg, K('b')), mrg))    # [b/Lb](mrg b mrg)
T   = C(Cc, Bb)
E_mix = S(K('b'), C(mrg, K('b')), T)    # [b / mrg.b] (Cc . Bb)

def w3(i, j, k): return 'a' * i + 'b' + 'a' * j + 'c' + 'a' * k

# laundering L_sigma = [s/ss][ss/s]  (double then halve; rightmost first)
def L(s, E):
    return S(K(s), K(s * 2), S(K(s * 2), K(s), E))

allok = True
# --- part 1: grid incl. boundaries ---------------------------------------
for i in range(0, 11):
    for j in range(0, 11):
        for k in range(0, 11):
            w = w3(i, j, k)
            allok &= val(E_mix, w) == w[::-1]
print('T1 grid 11^3 (i,j,k in [0,10], boundaries incl.):',
      'VERIFIED' if allok else 'REFUTED')

# --- part 2: random ------------------------------------------------------
rng = random.Random(1509)
ok = True
for _ in range(400):
    i, j, k = rng.randint(0, 200), rng.randint(0, 200), rng.randint(0, 200)
    w = w3(i, j, k)
    ok &= val(E_mix, w) == w[::-1]
print('T1 random 400 to 200:', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 3: intermediate values (hand-proof steps) ----------------------
ok = True
for i in range(0, 8):
    for j in range(0, 8):
        for k in range(0, 8):
            w = w3(i, j, k)
            ok &= val(mrg, w) == 'a' * (i + j + k)
            ok &= val(Lb, w) == 'a' * i + 'b' + 'a' * (j + k)
            ok &= val(Lc, w) == 'a' * (i + j) + 'c' + 'a' * k
            ok &= val(Cc, w) == 'a' * k + 'c' + 'a' * (i + j)
            ok &= val(Bb, w) == 'a' * (j + k) + 'b' + 'a' * i
            ok &= val(T, w) == ('a' * k + 'c' + 'a' * (i + 2 * j + k)
                               + 'b' + 'a' * i)
            ok &= val(C(mrg, K('b')), w) == 'a' * (i + j + k) + 'b'
print('T1 intermediates mrg/Lb/Lc/Cc/Bb/T/mrg.b, 8^3 grid:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 4: prov never DB, injective -------------------------------------
ok = True
for _ in range(300):
    i, j, k = rng.randint(0, 60), rng.randint(0, 60), rng.randint(0, 60)
    w = w3(i, j, k)
    p = prv(E_mix, w)
    ok &= p != tuple(range(len(w) - 1, -1, -1))   # never DB
    ok &= len(set(p)) == len(p)                   # injective (mult 1)
print('T1 prov never DB + injective (300 random):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 5: laundered composition: rev with prov == () -------------------
El = L('a', L('b', L('c', E_mix)))
ok = True
for i in range(0, 7):
    for j in range(0, 7):
        for k in range(0, 7):
            w = w3(i, j, k)
            ok &= val(El, w) == w[::-1] and prv(El, w) == ()
for _ in range(100):
    i, j, k = rng.randint(0, 80), rng.randint(0, 80), rng.randint(0, 80)
    w = w3(i, j, k)
    ok &= val(El, w) == w[::-1] and prv(El, w) == ()
print('T1 laundered L_a.L_b.L_c.E_mix: rev with prov == ():',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

print('T1 THEOREM:', 'ALL VERIFIED' if allok else 'REFUTED')

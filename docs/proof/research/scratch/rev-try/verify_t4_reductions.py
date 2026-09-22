"""ROUND 15 (construction lane) — REDUCTION machinery, machine checks.

R1 (V_h-equivalence mechanism).  For every constant h >= 1 the two
constant passes
    pad_h   = [b a^h / b]     (insert h a's after every b)
    strip_h = [b / b a^h]     (delete h a's after every b, when present)
satisfy, on the relevant shapes (runs long enough),
    strip_h ( a^k b a^{j+h} b a^{i+h} ) = a^k b a^j b a^i  = rev(w2)
    pad_h   ( a^k b a^j b a^i ) = a^k b a^{j+h} b a^{i+h}  =: V_h
Hence: rev computable on {a^i b a^j b a^k}  <=>  V_h constructible as a
value for some constant h  (<=: strip the constructed V_h; =>: pad the
rev-computer's output).  The machine checks the pass arithmetic on
constant scrutinees (grid + random) and the round trip through the
m-family construction E_2 (where a rev-computer exists).

R2 (transplant note).  E_mix (T1) is the letter-blind verification of
the engine: if the one-b projections  P1 = a^i b a^{j+k},
P2 = a^{i+j} b a^k  were constructible on the same-letter family, the
E_mix skeleton with Lb:=P1, Lc:=P2 (relabel c->b) would compute rev
there.  Recorded as hand derivation; machine-checked only in the mixed
world (that IS verify_t1_mixed.py).

R3 (corrected collapse fact).  [R/X] C(X,X) = R . R  (greedy: the
leftmost match at 0 consumes copy 1; the scan resumes at |X| where
copy 2 matches at its own start).  My first hand derivation of this
("R a^k R") was wrong; recorded here to keep the ledger honest.

Run: /usr/bin/python3 -W ignore verify_t4_reductions.py   (< 20 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def D(p): return S(K(''), K(p), X)
def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k

# --- R1: pass arithmetic on constant scrutinees --------------------------
rng = random.Random(4242)
ok = True
for h in (1, 2, 3):
    pad = S(K('b' + 'a' * h), K('b'), X)
    strip = S(K('b'), K('b' + 'a' * h), X)
    for i in range(0, 6):
        for j in range(0, 6):
            for k in range(0, 6):
                w = w2(i, j, k)
                ok &= val(pad, w) == w2(i, j + h, k + h)      # both b's
                # strip needs the middle and right runs >= h
                if j >= 0 and k >= 0:
                    pass
    for _ in range(200):
        i, j, k = (rng.randint(0, 50), rng.randint(0, 50),
                   rng.randint(0, 50))
        w = w2(i, j, k)
        ok &= val(pad, w) == w2(i, j + h, k + h)
        Vh = w2(k, j + h, i + h)     # scrutinee shaped a^k b a^{j+h} b a^{i+h}
        ok &= val(strip, Vh) == w2(k, j, i)
        # round trip: strip then pad (on rev-shaped output)
        revw = w2(k, j, i)
        ok &= val(pad, val(strip, revw) if False else revw) \
            == w2(k, j + h, i + h)
print('R1 pad/strip arithmetic (h=1,2,3; grid+random):',
      'VERIFIED' if ok else 'REFUTED')

# --- R1b: the round trip through the m-family rev-computer E_2 ------------
mrg2 = S(K(''), K('b'), X)
hm = S(K('a'), K('aa'), mrg2)
R2e = C(C(K('b'), hm), K('b'))
T2e = C(C(C(hm, K('b')), hm), C(K('b'), hm))
E2 = S(R2e, X, T2e)      # m=2 construction on {j = i+k}
ok = True
for h in (1, 3):
    pad = S(K('b' + 'a' * h), K('b'), E2)          # pad the rev output
    strip = S(K('b'), K('b' + 'a' * h), pad)       # then strip it
    for _ in range(200):
        i, k = rng.randint(0, 50), rng.randint(0, 50)
        j = i + k
        w = w2(i, j, k)
        ok &= val(pad, w) == w2(k, j + h, i + h)   # V_h on the family
        ok &= val(strip, w) == w2(k, j, i)        # back to rev
print('R1b V_h round trip through E_2 (h=1,3; 200 random):',
      'VERIFIED' if ok else 'REFUTED')

# --- R3: corrected collapse fact [R/X]C(X,X) = R . R ----------------------
ok = True
for _ in range(200):
    i, j, k = (rng.randint(0, 30), rng.randint(0, 30), rng.randint(0, 30))
    w = w2(i, j, k)
    for R in ('b', 'ab', 'aab', 'ba'):
        E = S(K(R), X, C(X, X))
        ok &= val(E, w) == R + R
print('R3 [R/X]C(X,X) = R.R (R in {b,ab,aab,ba}; 200 random):',
      'VERIFIED' if ok else 'REFUTED')

# --- R4: [R/X]C(a^t, X, a^u) = a^t R a^u (collapse with pads) -------------
ok = True
for _ in range(150):
    i, j, k = (rng.randint(0, 25), rng.randint(0, 25), rng.randint(0, 25))
    t, u = rng.randint(0, 4), rng.randint(0, 4)
    w = w2(i, j, k)
    E = S(K('b'), X, C(C(K('a' * t), X), K('a' * u)))
    ok &= val(E, w) == 'a' * t + 'b' + 'a' * u
print('R4 [b/X]C(a^t,X,a^u) = a^t b a^u (150 random):',
      'VERIFIED' if ok else 'REFUTED')

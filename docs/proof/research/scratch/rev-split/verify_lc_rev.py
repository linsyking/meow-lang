"""rev-split ROUND 2 -- INDEPENDENT verification of Lane C's claimed
rev-on-W2 construction (merge-catalyzed selective deletion + transplant
skeleton), with my own evaluator (prov.py/lcore.py ground truth), plus
the consistency checks against Lemma S / Schema P that my charter needs:

  (a) E_rev == rev on W2 (grid incl. all-zero boundaries + random);
  (b) every intermediate's a-content is a function of S alone
      (Lemma S consistency -- the construction lives in the stratum
      where P4's degree form holds: affine runs, O(1) window counts);
  (c) the final pass is entry-(ii) class: computed adjacent-letter
      pattern (a^{S+1} b), O(1) firings under pinned comparisons.

Falsify/verify only.  < 30 s.
"""
import random, sys, time
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def D(p): return S(K(''), K(p), X)                  # [eps/p]X

mrg = D('b')                                         # a^S, S = i+j+k

# Lane C's expressions, rebuilt by me from the mechanism description
patP1 = C(K('b'), C(mrg, K('a')))                    # b . mrg . a
scrP1 = C(C(X, mrg), K('a'))                         # X . mrg . a
E_P1 = S(K(''), patP1, scrP1)

patP2 = C(C(K('a'), mrg), K('b'))                    # a . mrg . b
scrP2 = C(C(K('a'), mrg), X)                         # a . mrg . X
E_P2 = S(K(''), patP2, scrP2)

box_scr = C(C(mrg, K('b')), mrg)                     # mrg . b . mrg
Cc = S(K('b'), E_P2, box_scr)                        # [b/P2](mrg b mrg)
Bb = S(K('b'), E_P1, box_scr)                        # [b/P1](mrg b mrg)
T2 = C(C(Cc, K('a')), Bb)                            # Cc . a . Bb
patF = C(C(K('a'), mrg), K('b'))                     # a . mrg . b
E_rev = S(K('b'), patF, T2)                          # [b/(a.mrg.b)] T

def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k

t0 = time.time()
# (a) full grid incl. boundaries, then random
ok = True
for i in range(0, 11):
    for j in range(0, 11):
        for k in range(0, 11):
            ok &= val(E_rev, w2(i, j, k)) == w2(i, j, k)[::-1]
print('E_rev == rev, 11^3 grid incl. zero boundaries:',
      'VERIFIED' if ok else 'REFUTED')
rng = random.Random(424242)
ok2 = True
for _ in range(600):
    i, j, k = rng.randint(0, 250), rng.randint(0, 250), rng.randint(0, 250)
    ok2 &= val(E_rev, w2(i, j, k)) == w2(i, j, k)[::-1]
print('E_rev == rev, 600 random to 250:', 'VERIFIED' if ok2 else 'REFUTED')

# (b) intermediates + Lemma-S consistency (a-content a function of S)
ok3 = True
for i in range(0, 8):
    for j in range(0, 8):
        for k in range(0, 8):
            w = w2(i, j, k); S_ = i + j + k
            ok3 &= val(mrg, w) == 'a' * S_
            ok3 &= val(E_P1, w) == 'a' * i + 'b' + 'a' * (j + k)
            ok3 &= val(E_P2, w) == 'a' * (i + j) + 'b' + 'a' * k
            ok3 &= val(Cc, w) == 'a' * k + 'b' + 'a' * (i + j)
            ok3 &= val(Bb, w) == 'a' * (j + k) + 'b' + 'a' * i
            ok3 &= val(T2, w) == ('a' * k + 'b' + 'a' * (i + 2*j + k + 1)
                                  + 'b' + 'a' * i)
            # S-functional totals: P1,P2,Cc,Bb -> S ; T -> 2S+1 ; rev -> S
            for e, tot in ((E_P1, S_), (E_P2, S_), (Cc, S_), (Bb, S_),
                           (T2, 2*S_ + 1), (E_rev, S_)):
                v = val(e, w)
                ok3 &= sum(1 for ch in v if ch == 'a') == tot
print('intermediates + S-functional totals, 8^3 grid:',
      'VERIFIED' if ok3 else 'REFUTED')

# (c) run structure of E_rev's value: exactly 2 b's, three affine runs
#     (k, j, i) -- P4's degree form HOLDS on this stratum (no products).
ok4 = True
for _ in range(200):
    i, j, k = rng.randint(0, 80), rng.randint(0, 80), rng.randint(0, 80)
    v = val(E_rev, w2(i, j, k))
    parts = v.split('b')
    ok4 &= len(parts) == 3
    ok4 &= len(parts[0]) == k and len(parts[1]) == j and len(parts[2]) == i
print('E_rev run structure = (k, j, i) affine, 200 random:',
      'VERIFIED' if ok4 else 'REFUTED')
print('%.1fs' % (time.time() - t0))

"""ROUND 16 (unification charter): positives + lemma checks.

THE CHARTER QUESTION: one expression computing rev on ALL of {a,b}*
(varying separator count).  Pure-think pass (done first, see report)
concluded: IMPOSSIBLE - with a Dilworth/channel architecture.  This
script machine-verifies the ROUND'S POSITIVE BYPRODUCTS and the
mechanical lemmas the impossibility architecture rests on.

P1 (block-swap family FALLS - skeleton separation):
  w = a^i b^k,  rev(w) = b^k a^i.
  B   = [eps/a]X          = b^k   (pure-b skeleton, total, k-adaptive)
  mrg = [eps/b]X          = a^i
  E_block = [B / (X.b)] ((X.b).mrg):
  the scrutinee (X.b).mrg literally begins with the pattern value X.b
  (unique occurrence: the only a-block is the prefix), the single
  firing deletes it and emits B, leaving mrg:  out = b^k a^i = rev(w).
  All boundaries (i=0, k=0, both) hand-checked and in the grid.

P2 (heavy-tail alternating family FALLS - phase swap):
  w_k = (ab)^k aa = a.(ba)^k.a,  k >= 1;  rev(w_k) = a.(ab)^k.a.
  R = [eps/'aa']X                = (ab)^k   (unique trailing 'aa')
  P = [eps/'aa']([ba/'ab']X)      = (ba)^k
    ([ba/ab] is a CONSTANT local swap: fires at each 'ab', k firings,
    output (ba)^k.aa; the unique-ish 'aa' peel then yields (ba)^k -
    greedy fires at the boundary 'aa', leaving (ba)^{k-1}.ba = (ba)^k.)
  E_alt = [R/P]X: (ba)^k occurs in w_k only at position 1; the single
  firing gives out = a . (ab)^k . a = rev(w_k).  (k=0 is the empty-
  pattern edge; the claim is for k >= 1.)

L1 (collapse fact, load-bearing for the assembly lemma):
  [R/P](P.G) = R.G whenever P does not occur in G  (greedy fires at 0).
L2 (merge-framed replacement):
  [R/V](mrg.V.mrg) = mrg.R.mrg for one-b V (V occurs only at the merge
  flank junction).

L3 (assembly-lemma illustration on super-increasing inputs):
  w^(k) = a^{2^0} b a^{2^1} ... b a^{2^k}: every run value produced by
  a battery of computed values is either a tweak of a single input run
  or an affine function of S (the pinned-polynomial schema the
  impossibility needs from Lane B).  Illustrative, k <= 6.

Run: /usr/bin/python3 -W ignore verify_r16.py    (< 30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def D(p): return S(K(''), K(p), X)                    # [eps/p]X
mrg = D('b')                                          # a^S
B = S(K(''), K('a'), X)                               # [eps/a]X = b-skeleton

# ---------- P1: block swap -----------------------------------------------
E_block = S(B, C(X, K('b')), C(C(X, K('b')), mrg))     # [B/(X.b)]((X.b).mrg)
ok = True
for i in range(0, 13):
    for k in range(0, 13):
        w = 'a' * i + 'b' * k
        ok &= val(E_block, w) == w[::-1]
print('P1 block swap {a^i b^k}: grid 13^2 (boundaries incl.):',
      'VERIFIED' if ok else 'REFUTED')
rng = random.Random(160922)
ok = True
for _ in range(400):
    i, k = rng.randint(0, 200), rng.randint(0, 200)
    w = 'a' * i + 'b' * k
    ok &= val(E_block, w) == w[::-1]
print('P1 block swap: random 400 to 200:', 'VERIFIED' if ok else 'REFUTED')
ok = True
for i in range(0, 10):
    for k in range(0, 10):
        w = 'a' * i + 'b' * k
        ok &= val(mrg, w) == 'a' * i
        ok &= val(B, w) == 'b' * k
        ok &= val(C(X, K('b')), w) == w + 'b'
print('P1 intermediates B=b^k, mrg=a^i, X.b: 10^2 grid:',
      'VERIFIED' if ok else 'REFUTED')

# ---------- P2: heavy-tail alternating ------------------------------------
R_alt = S(K(''), K('aa'), X)                          # [eps/aa]X
P_alt = S(K(''), K('aa'), S(K('ba'), K('ab'), X))     # [eps/aa][ba/ab]X
E_alt = S(R_alt, P_alt, X)                             # [R/P]X
ok = True
for k in range(1, 45):
    w = ('ab' * k) + 'aa'
    ok &= val(E_alt, w) == w[::-1]
print('P2 alternating {(ab)^k aa}, k=1..44:', 'VERIFIED' if ok else 'REFUTED')
ok = True
for k in range(1, 15):
    w = ('ab' * k) + 'aa'
    ok &= val(R_alt, w) == 'ab' * k
    ok &= val(P_alt, w) == 'ba' * k
    ok &= w == 'a' + 'ba' * k + 'a'                   # structural identity
print('P2 intermediates R=(ab)^k, P=(ba)^k, k=1..14:',
      'VERIFIED' if ok else 'REFUTED')

# ---------- L1/L2: collapse facts -----------------------------------------
ok = True
for i in range(0, 7):
    for j in range(0, 7):
        for k in range(0, 7):
            w = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
            # L1: [b/X](X . mrg) = 'b' . mrg  (X occurs only at 0)
            ok &= val(S(K('b'), X, C(X, mrg)), w) == 'b' + val(mrg, w)
            # L2: [B/X](mrg . X . mrg) = mrg . B . mrg
            ok &= val(S(B, X, C(C(mrg, X), mrg)), w) == \
                val(mrg, w) + val(B, w) + val(mrg, w)
print('L1 [b/X](X.mrg)=b.mrg and L2 [B/X](mrg.X.mrg)=mrg.B.mrg, 7^3 W2 grid:',
      'VERIFIED' if ok else 'REFUTED')

# ---------- L3: schema illustration on super-increasing inputs ------------
def runs(s):
    out, cur = [], 0
    for ch in s:
        if ch == 'a':
            cur += 1
        else:
            out.append(cur); cur = 0
    out.append(cur)
    return out

def sup(k):
    return 'b'.join('a' * (2 ** m) for m in range(k + 1))

halver = S(K('aa'), K('a'), mrg)                        # [aa/a]mrg
dbl = S(K('a'), K('aa'), mrg)                           # [a/aa]mrg
del_last = S(K(''), C(K('b'), C(mrg, K('a'))), C(C(X, mrg), K('a')))
del_first = S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), X))
battery = [mrg, B, halver, dbl, del_last, del_first]
ok = True
for k in range(1, 7):
    w = sup(k)
    S_ = sum(2 ** m for m in range(k + 1))
    for e in battery:
        v = val(e, w)
        for r in runs(v):
            is_tweak = any(abs(r - 2 ** m) <= 8 for m in range(k + 1))
            is_pinned = any(abs(r - (alpha * S_ + beta)) <= 8
                            for alpha in (0, 1, 0.5, 0.25, 0.75, 1.5, 2)
                            for beta in (-2, -1, 0, 1, 2))
            ok &= is_tweak or is_pinned
print('L3 schema illustration (tweak-or-affine-in-S), k=1..6:',
      'VERIFIED' if ok else 'REFUTED')
print('ROUND 16 MACHINE VERDICT: see report for the impossibility architecture')

"""ROUND 15C (construction lane): THE MAIN CONSTRUCTION — rev on the
SAME-LETTER ALL-VARYING two-separator family W2 = {a^i b a^j b a^k :
i, j, k >= 0} over Sigma = {a, b}.  The campaign's positive endgame.

MECHANISM (merge-catalyzed selective deletion).  mrg = [eps/b]X = a^S
deletes BOTH separators (that is why the one-b projections were thought
unreachable).  But CONCATENATING mrg next to X gives ONE separator an
unbounded adjacent run, so a merge-flavored pattern fires there
UNCONDITIONALLY and at the other separator NEVER; the deletion
consumes exactly the merge and the natural glue is what remains:

    P1 = [eps / (b.mrg.a)] (X . mrg . a)      = a^i b a^{j+k}
      scrutinee a^i b a^j b a^{k+S+1}: pattern b.a^{S+1} fires only at
      b#2 (b#1's following run j <= S < S+1); window = b#2 + (S+1) a's;
      output a^i b a^j . a^{k} = a^i b a^{j+k}.
    P2 = [eps / (a.mrg.b)] (a . mrg . X)      = a^{i+j} b a^k
      scrutinee a^{S+1+i} b a^j b a^k: pattern a^{S+1}.b fires only at
      b#1 (b#2's preceding run j < S+1); output a^i . a^j b a^k.

Then the round-15 transplant skeleton (the E_mix engine, letter-blind):

    Cc  = [b / P2] (mrg . b . mrg)   = a^k b a^{i+j}
    Bb  = [b / P1] (mrg . b . mrg)   = a^{j+k} b a^i
    T   = Cc . a . Bb = a^k b a^{i+2j+k+1} b a^i
    E_rev = [b / (a.mrg.b)] T:
      pattern a^{S+1}.b fires only at T's second b (first b's preceding
      run k <= S < S+1; middle run i+2j+k+1 >= S+1 iff j >= 0), shaving
      exactly S+1 and leaving j:  output a^k b a^j b a^i = rev(X).
(The K('a') pad between Cc and Bb and the +1 in the final pattern are
paired: at j = 0 the middle run is exactly S+1, and at i = j = 0 the
first b's preceding run k must stay < S+1.)

Checks: content = rev on 11^3 grid (all boundaries), 600 random to 250,
intermediates P1/P2/Cc/Bb/T on grids, prov never DB + injective, and
the laundering composition L_a.L_b.E_rev: rev with prov == ().
Run: /usr/bin/python3 -W ignore verify_t5_rev.py   (< 30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def D(p): return S(K(''), K(p), X)                  # [eps/p]X

mrg = D('b')                                         # a^S,  S = i+j+k

# --- the one-b projections (L-family), merge-catalyzed --------------------
patP1 = C(K('b'), C(mrg, K('a')))                    # b . mrg . a
scrP1 = C(C(X, mrg), K('a'))                         # X . mrg . a
E_P1 = S(K(''), patP1, scrP1)                        # [eps/(b.mrg.a)](X.mrg.a)

patP2 = C(C(K('a'), mrg), K('b'))                    # a . mrg . b
scrP2 = C(C(K('a'), mrg), X)                         # a . mrg . X
E_P2 = S(K(''), patP2, scrP2)                        # [eps/(a.mrg.b)](a.mrg.X)

# --- transplant skeleton --------------------------------------------------
box_scr = C(C(mrg, K('b')), mrg)                     # mrg . b . mrg
Cc = S(K('b'), E_P2, box_scr)                        # [b/P2](mrg b mrg)
Bb = S(K('b'), E_P1, box_scr)                        # [b/P1](mrg b mrg)
T2 = C(C(Cc, K('a')), Bb)                            # Cc . a . Bb
patF = C(C(K('a'), mrg), K('b'))                     # a . mrg . b
E_rev = S(K('b'), patF, T2)                          # [b/(a.mrg.b)] T

def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k

def L(s, E):                                         # laundering
    return S(K(s), K(s * 2), S(K(s * 2), K(s), E))

allok = True
# --- part 1: full grid incl. all boundaries -------------------------------
for i in range(0, 11):
    for j in range(0, 11):
        for k in range(0, 11):
            w = w2(i, j, k)
            allok &= val(E_rev, w) == w[::-1]
print('REV grid 11^3 (i,j,k in [0,10], boundaries incl.):',
      'VERIFIED' if allok else 'REFUTED')

# --- part 2: random --------------------------------------------------------
rng = random.Random(150922)
ok = True
for _ in range(600):
    i, j, k = (rng.randint(0, 250), rng.randint(0, 250), rng.randint(0, 250))
    w = w2(i, j, k)
    ok &= val(E_rev, w) == w[::-1]
print('REV random 600 to 250:', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 3: intermediates (hand-proof steps) ------------------------------
ok = True
for i in range(0, 8):
    for j in range(0, 8):
        for k in range(0, 8):
            w = w2(i, j, k)
            S_ = i + j + k
            ok &= val(mrg, w) == 'a' * S_
            ok &= val(E_P1, w) == 'a' * i + 'b' + 'a' * (j + k)
            ok &= val(E_P2, w) == 'a' * (i + j) + 'b' + 'a' * k
            ok &= val(Cc, w) == 'a' * k + 'b' + 'a' * (i + j)
            ok &= val(Bb, w) == 'a' * (j + k) + 'b' + 'a' * i
            ok &= val(T2, w) == ('a' * k + 'b' + 'a' * (i + 2 * j + k + 1)
                                 + 'b' + 'a' * i)
            ok &= val(patF, w) == 'a' * (S_ + 1) + 'b'
print('intermediates mrg/P1/P2/Cc/Bb/T/pattern, 8^3 grid:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 4: prov never DB, injective -------------------------------------
ok = True
for _ in range(300):
    i, j, k = (rng.randint(0, 60), rng.randint(0, 60), rng.randint(0, 60))
    w = w2(i, j, k)
    p = prv(E_rev, w)
    ok &= p != tuple(range(len(w) - 1, -1, -1))      # never DB
    ok &= len(set(p)) == len(p)                       # injective
print('prov never DB + injective (300 random):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# --- part 5: laundered composition: rev with prov == () --------------------
El = L('a', L('b', E_rev))
ok = True
for i in range(0, 7):
    for j in range(0, 7):
        for k in range(0, 7):
            w = w2(i, j, k)
            ok &= val(El, w) == w[::-1] and prv(El, w) == ()
for _ in range(100):
    i, j, k = (rng.randint(0, 80), rng.randint(0, 80), rng.randint(0, 80))
    w = w2(i, j, k)
    ok &= val(El, w) == w[::-1] and prv(El, w) == ()
print('laundered L_a.L_b.E_rev: rev with prov == ():',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

print('E_rev THEOREM:', 'ALL VERIFIED' if allok else 'REFUTED')

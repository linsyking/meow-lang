"""ROUND 17 (coordinator) — THE SAME-LETTER WALL FALLS: my independent
verification battery for Lane C's round 15C (E_rev + the general engine)
and Lane B's round 2 (the P4 counterexample CH2).

Everything here is encoded FRESH from my own hand derivations (which
preceded reading either lane's scripts):

  E_rev = [b/(a.mrg.b)](Cc . a . Bb)   on W2 = {a^i b a^j b a^k : i,j,k >= 0}
    mrg = [eps/b]X = a^S
    P1  = [eps/(b.mrg.a)](X.mrg.a)  = a^i b a^{j+k}   (fires only at b#2:
          its following run k+S+1 >= S+1; b#1's is j <= S < S+1)
    P2  = [eps/(a.mrg.b)](a.mrg.X)  = a^{i+j} b a^k   (fires only at b#1)
    Cc  = [b/P2](mrg.b.mrg) = a^k b a^{i+j};  Bb = [b/P1](mrg.b.mrg)
          = a^{j+k} b a^i;  T2 = Cc.a.Bb = a^k b a^{S+1+j} b a^i; the final
          pattern a^{S+1}.b fires only at T2's second b (first's preceding
          run k <= S < S+1), shaving exactly S+1 and leaving j.

  General engine (my derivation, separators s_1..s_k, runs r_0..r_k):
    del_last(E,s) = [eps/(s.mrg.a)](E.mrg.a);  del_first(E,s) =
    [eps/(a.mrg.s)](a.mrg.E);  L_m = del_first^(m-1) del_last^(k-m) X =
    a^{r_0+..+r_{m-1}} s_m a^{r_m+..+r_k};  D_m = [s_m/L_m](mrg.s_m.mrg)
    = a^{r_m+..+r_k} s_m a^{r_0+..+r_{m-1}};  T' = D_k.a.D_{k-1}...a.D_1
    (inter-separator runs exactly S+1+r_{m-1}); one pass per distinct
    letter [s/(s.mrg.a)] fires at every separator except the last
    (following run r_0 <= S), eating exactly S+1 and leaving r_{m-1}.
    Output = a^{r_k} s_k a^{r_{k-1}} ... s_1 a^{r_0} = rev.

  CH2 (Lane B's P4 counterexample) = [merge/'bb'] . [bb/aa]X, merge =
  [eps/b]X: on the all-odd cell, output = a^{S(i+j-2)/2+1} b
  a^{S(k-1)/2+1} b a — the first run is INDECOMPOSABLE as A(i,j,k)+P(S)
  (its k-slope on the plane S=const is -S/2, unbounded).

Run: /usr/bin/python3 -W ignore verify_round17.py   (~25 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
rng = random.Random(20260923)
allok = True

# ---------- part A: E_rev, fresh encoding ----------
mrg = S(K(''), K('b'), X)                          # [eps/b]X = a^S
P1 = S(K(''), C(K('b'), C(mrg, K('a'))), C(C(X, mrg), K('a')))
P2 = S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), X))
Cc = S(K('b'), P2, C(C(mrg, K('b')), mrg))
Bb = S(K('b'), P1, C(C(mrg, K('b')), mrg))
T2 = C(C(Cc, K('a')), Bb)
E_rev = S(K('b'), C(C(K('a'), mrg), K('b')), T2)

def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
ok = True
for i in range(12):
    for j in range(12):
        for k in range(12):
            ok &= val(E_rev, w2(i, j, k)) == w2(i, j, k)[::-1]
for _ in range(500):
    i, j, k = rng.randint(0, 300), rng.randint(0, 300), rng.randint(0, 300)
    ok &= val(E_rev, w2(i, j, k)) == w2(i, j, k)[::-1]
# adversarial scales: one run tiny, one huge
for _ in range(300):
    t, u = rng.randint(0, 4), rng.randint(50, 200)
    for (i, j, k) in [(t, u, t), (u, t, t), (t, t, u), (u, u, t)]:
        ok &= val(E_rev, w2(i, j, k)) == w2(i, j, k)[::-1]
print('A  E_rev fresh encoding: 12^3 grid (boundaries incl.) + 500 random',
      '+ 300 adversarial scales:', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# intermediates
ok = True
for i in range(8):
    for j in range(8):
        for k in range(8):
            w = w2(i, j, k); s = i + j + k
            ok &= val(mrg, w) == 'a' * s
            ok &= val(P1, w) == 'a' * i + 'b' + 'a' * (j + k)
            ok &= val(P2, w) == 'a' * (i + j) + 'b' + 'a' * k
            ok &= val(Cc, w) == 'a' * k + 'b' + 'a' * (i + j)
            ok &= val(Bb, w) == 'a' * (j + k) + 'b' + 'a' * i
            ok &= val(T2, w) == 'a' * k + 'b' + 'a' * (i + 2 * j + k + 1) \
                + 'b' + 'a' * i
print('A2 intermediates mrg/P1/P2/Cc/Bb/T2, 8^3:', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# prov: never DB, injective
ok = True
for _ in range(300):
    w = w2(rng.randint(0, 80), rng.randint(0, 80), rng.randint(0, 80))
    p = prv(E_rev, w)
    ok &= p != tuple(range(len(w) - 1, -1, -1))
    ok &= len(set(p)) == len(p)
print('A3 prov never DB + injective (300):', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# laundering L_a.L_b.E_rev = rev with prov == ()
def L(s, E):
    return S(K(s), K(s * 2), S(K(s * 2), K(s), E))
El = L('a', L('b', E_rev))
ok = True
for i in range(7):
    for j in range(7):
        for k in range(7):
            w = w2(i, j, k)
            ok &= val(El, w) == w[::-1] and prv(El, w) == ()
for _ in range(100):
    w = w2(rng.randint(0, 100), rng.randint(0, 100), rng.randint(0, 100))
    ok &= val(El, w) == w[::-1] and prv(El, w) == ()
print('A4 laundered L_a.L_b.E_rev = rev, prov == ():',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---------- part B: V_0/V_1 constructible (prefix-dominance refuted) ------
V0 = E_rev                                        # value a^k b a^j b a^i
V1 = S(K('b' + 'a'), K('b'), E_rev)               # [b.a/b]E_rev = V_1
ok = True
for _ in range(200):
    i, j, k = rng.randint(0, 60), rng.randint(0, 60), rng.randint(0, 60)
    ok &= val(V0, w2(i, j, k)) == w2(k, j, i)          # V_0
    ok &= val(V1, w2(i, j, k)) == w2(k, j + 1, i + 1)  # V_1
print('B  V_0 = E_rev, V_1 = [b.a/b]E_rev (prefix-dominance refuted):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---------- part C: general engine, fresh encodings ----------
def del_last(E, s, m):
    return S(K(''), C(K(s), C(m, K('a'))), C(C(E, m), K('a')))
def del_first(E, s, m):
    return S(K(''), C(C(K('a'), m), K(s)), C(C(K('a'), m), E))

def gen_engine(word):
    """word = s_1..s_k; returns the engine for a^{r_0} s_1 ... s_k a^{r_k}."""
    k = len(word)
    m = X
    for s in reversed(word):                      # mrg = delete all
        m = S(K(''), K(s), m)
    def L_of(mm):                                 # keep separator #mm
        e = X
        for j in range(k, mm, -1):                # del_last s_k..s_{mm+1}
            e = del_last(e, word[j - 1], m)
        for j in range(1, mm):                    # del_first s_1..s_{mm-1}
            e = del_first(e, word[j - 1], m)
        return e
    D = [None] * (k + 1)
    for mm in range(1, k + 1):
        s = word[mm - 1]
        D[mm] = S(K(s), L_of(mm), C(C(m, K(s)), m))
    T = D[k]
    for mm in range(k - 1, 0, -1):                # D_k . a . D_{k-1} ... D_1
        T = C(C(T, K('a')), D[mm])
    for s in sorted(set(word)):                   # per-letter shaves
        T = S(K(s), C(K(s), C(m, K('a'))), T)
    return T

def wf(runs, word):
    out = []
    for t in range(len(word) + 1):
        out.append('a' * runs[t])
        if t < len(word):
            out.append(word[t])
    return ''.join(out)

# (separator letters must be distinct from the filler 'a' — the engine's
# hypothesis; a word containing 'a' as a separator is out of scope)
for word in ['b', 'bb', 'bbb', 'bbbb', 'cbb', 'bcb', 'bcc', 'cb', 'bc',
             'cbc', 'cbccb']:
    E = gen_engine(word)
    k = len(word)
    ok = True
    rng2 = random.Random(hash(word) & 0xffff)
    n = 0
    for runs in [tuple(rng2.randint(0, 5) for _ in range(k + 1))
                 for _ in range(600)] + \
               [tuple(rng2.randint(0, 40) for _ in range(k + 1))
                for _ in range(200)]:
        w = wf(runs, word)
        ok &= val(E, w) == w[::-1]
        n += 1
    print('C  engine[%s] (k=%d), %d cases:' % (word, k, n),
          'VERIFIED' if ok else 'REFUTED')
    allok &= ok

# ---------- part D: CH2, the P4 counterexample ----------
dbl = S(K('bb'), K('aa'), X)                        # [bb/aa]X
ch2 = S(mrg, K('bb'), dbl)                          # [merge/'bb'].dbl
ok = True
for i in range(1, 9, 2):
    for j in range(1, 9, 2):
        for k in range(1, 9, 2):
            w = w2(i, j, k); s = i + j + k
            want = ('a' * (s * (i + j - 2) // 2 + 1) + 'b' +
                    'a' * (s * (k - 1) // 2 + 1) + 'b' + 'a')
            ok &= val(ch2, w) == want
# general rule: per b-run L of [bb/aa]X -> (a^S)^{L//2} b^{L%2},
# with the a-leftovers (1 per odd original run) merging in
for _ in range(300):
    i, j, k = rng.randint(0, 40), rng.randint(0, 40), rng.randint(0, 40)
    w = w2(i, j, k); s = i + j + k
    mid = [S(K('bb'), K('aa'), X)]                 # placeholder, use ch2
    v = val(ch2, w)
    # indecomposable first run on all-odd cells
    if i % 2 and j % 2 and k % 2:
        ok &= v.split('b')[0].count('a') == s * (i + j - 2) // 2 + 1
print('D  CH2 [merge/bb].[bb/aa]X all-odd closed form (indec. run):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---------- part E: sizes (tree + DAG) ----------
def nodes(e, seen=None):
    if seen is None:
        seen = set()
    if id(e) in seen:
        return 0
    seen.add(id(e))
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + nodes(e[1], seen) + nodes(e[2], seen)
    return 1 + nodes(e[1], seen) + nodes(e[2], seen) + nodes(e[3], seen)
def snodes(e, seen=None):
    if seen is None:
        seen = set()
    if id(e) in seen:
        return 0
    seen.add(id(e))
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return snodes(e[1], seen) + snodes(e[2], seen)
    return 1 + snodes(e[1], seen) + snodes(e[2], seen) + snodes(e[3], seen)
def sdepth(e):
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return max(sdepth(e[1]), sdepth(e[2]))
    return 1 + max(sdepth(e[1]), sdepth(e[2]), sdepth(e[3]))
treeN = nodes(E_rev, set())  # full tree: visit-once counting
# DAG count (shared objects once) vs tree count (expand): report both
def tree_size(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + tree_size(e[1]) + tree_size(e[2])
    return 1 + tree_size(e[1]) + tree_size(e[2]) + tree_size(e[3])
def tree_s(e):
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return tree_s(e[1]) + tree_s(e[2])
    return 1 + tree_s(e[1]) + tree_s(e[2]) + tree_s(e[3])
print('E  E_rev sizes: DAG nodes %d, S-nodes %d | TREE nodes %d, S-nodes %d'
      ' | S-depth %d' % (nodes(E_rev), snodes(E_rev), tree_size(E_rev),
                         tree_s(E_rev), sdepth(E_rev)))
allok &= sdepth(E_rev) == 4

print()
print('ROUND 17 COORDINATOR BATTERY:', 'ALL VERIFIED' if allok else 'REFUTED')
sys.exit(0 if allok else 1)

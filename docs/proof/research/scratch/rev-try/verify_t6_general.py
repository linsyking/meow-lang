"""ROUND 15C-2: THE GENERAL ENGINE — rev on EVERY fixed separator structure
{a^{r_0} s_1 a^{r_1} s_2 ... s_k a^{r_k} : all r_m >= 0 varying}, over any
finite alphabet, for every fixed separator word (s_1..s_k), including
same-letter collisions at any multiplicity.

ENGINE (unifies round-14 complement engine k=1, 15B distinct-separator
engine, and this round's E_rev = the k=2 same-letter instance):

  mrg      = delete-all-separators (chained [eps/s_m]) = a^S.
  del-last(E,s)  = [eps/(s.mrg.a)] (E.mrg.a)     delete the LAST s:
     the concatenation boosts the last s's following run to rho+S+1, the
     pattern s.a^{S+1} fires there unconditionally and nowhere else (all
     other runs are contiguous sums <= S < S+1); it eats exactly the
     merge, gluing E's natural tail.
  del-first(E,s) = [eps/(a.mrg.s)] (a.mrg.E)     delete the FIRST s.
  L_m      = keep separator #m = del-first(.. letters before ..) then
     del-last(.. letters after ..); value a^{r_0+..+r_m} s_m a^{r_{m+1}+..+r_k}.
  D_m      = [s_m/L_m] (mrg.s_m.mrg)  complement box
             = a^{r_{m+1}+..+r_k} s_m a^{r_0+..+r_m}.
  T'       = D_{k-1} . a . D_{k-2} . a . ... . a . D_0
             = a^{r_k} s_{k-1} a^{S+1+r_{k-1}} ... a^{S+1+r_1} s_0 a^{r_0}.
  final    = one pass per distinct letter: [s/(s.mrg.a)]:
     fires at every s-position whose following run is >= S+1 — exactly
     all separators except the last (s_0, following r_0 <= S) — eating
     exactly S+1 and leaving r_m.  Output = rev(X).
The 'a' pads and the +1 are paired edge-guards: without them the last
separator fires when r_0 = S (all other runs 0) and eats the tail.

Cases verified: k=1 ['b'] (complement-engine cross-check), k=2 ['b','b']
(cross-check against the hand-built E_rev of verify_t5_rev.py), k=3
['b','b','b'], k=4 ['b','b','b','b'], mixed ['b','b','c'], ['b','c','b'],
['c','b'] (E_mix cross-check).  Grids incl. boundaries + randoms;
intermediates (L_m, D_m) on grids for k=3; prov never DB + injective and
the laundered rev for k=3 same-letter.  Run (< 50 s):
/usr/bin/python3 -W ignore verify_t6_general.py
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def L(s, E): return S(K(s), K(s * 2), S(K(s * 2), K(s), E))   # laundering

def build(letters):
    """letters: separator letters s_0..s_{k-1}; X = a^{r_0}s_0 a^{r_1}...s_{k-1}a^{r_k}."""
    k = len(letters)
    seps = sorted(set(letters))
    mrg = X
    for s in seps:
        mrg = S(K(''), K(s), mrg)                       # a^S
    def del_last(E, s):
        return S(K(''), C(K(s), C(mrg, K('a'))), C(C(E, mrg), K('a')))
    def del_first(E, s):
        return S(K(''), C(C(K('a'), mrg), K(s)), C(C(K('a'), mrg), E))
    Ls, Ds = [], []
    for m in range(k):
        E = X
        for t in range(m):                              # delete s_0..s_{m-1}
            E = del_first(E, letters[t])
        for t in range(k - 1, m, -1):                   # delete s_{k-1}..s_{m+1}
            E = del_last(E, letters[t])
        Ls.append(E)
        Ds.append(S(K(letters[m]), E, C(C(mrg, K(letters[m])), mrg)))
    T = Ds[k - 1]                                       # D_{k-1} . a . ... . D_0
    for m in range(k - 2, -1, -1):
        T = C(C(T, K('a')), Ds[m])
    Efull = T
    for s in seps:                                      # per-letter shaves
        Efull = S(K(s), C(K(s), C(mrg, K('a'))), Efull)
    return Efull, Ls, Ds, mrg

def mk(letters, runs):
    out = 'a' * runs[0]
    for s, r in zip(letters, runs[1:]):
        out += s + 'a' * r
    return out

def counts(e):
    """tuple AST -> (nodes, S-depth, AST depth in edges)"""
    t = e[0]
    if t in ('K', 'V'):
        return (1, 0, 0)
    if t == 'C':
        a, b = counts(e[1]), counts(e[2])
        return (1 + a[0] + b[0], max(a[1], b[1]), 1 + max(a[2], b[2]))
    if t == 'S':
        a, b, c = counts(e[1]), counts(e[2]), counts(e[3])
        return (1 + a[0] + b[0] + c[0], 1 + max(a[1], b[1], c[1]),
                1 + max(a[2], b[2], c[2]))
    raise ValueError

rng = random.Random(1509221)
allok = True

def check(name, letters, grid_n, nrand, maxr, also_inter=False):
    global allok
    E, Ls, Ds, mrg = build(letters)
    k = len(letters)
    ok = True
    for c in range(grid_n ** (k + 1)):
        runs = []
        t = c
        for _ in range(k + 1):
            runs.append(t % grid_n); t //= grid_n
        w = mk(letters, runs)
        ok &= val(E, w) == w[::-1]
    print(f'{name}: grid {grid_n}^{k+1} (boundaries incl.):',
          'VERIFIED' if ok else 'REFUTED')
    allok &= ok
    ok = True
    for _ in range(nrand):
        runs = [rng.randint(0, maxr) for _ in range(k + 1)]
        w = mk(letters, runs)
        ok &= val(E, w) == w[::-1]
    print(f'{name}: random {nrand} to {maxr}:',
          'VERIFIED' if ok else 'REFUTED')
    allok &= ok
    if also_inter:
        ok = True
        for c in range(4 ** (k + 1)):
            runs = []; t = c
            for _ in range(k + 1):
                runs.append(t % 4); t //= 4
            w = mk(letters, runs)
            ok &= val(mrg, w) == 'a' * sum(runs)
            for m in range(k):
                pre, suf = sum(runs[:m + 1]), sum(runs[m + 1:])
                ok &= val(Ls[m], w) == 'a' * pre + letters[m] + 'a' * suf
                ok &= val(Ds[m], w) == 'a' * suf + letters[m] + 'a' * pre
        print(f'{name}: intermediates mrg/L_m/D_m, 4^{k+1} grid:',
              'VERIFIED' if ok else 'REFUTED')
        allok &= ok
    return E

# k=1: the round-14 complement engine
check('k=1 same-letter [b]', ['b'], 9, 200, 120, also_inter=True)
# k=2: E_rev itself
E2, _, _, _ = build(['b', 'b'])
ok = True
for c in range(8 ** 3):
    i, j, k2 = c % 8, (c // 8) % 8, (c // 64) % 8
    w = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k2
    ok &= val(E2, w) == w[::-1]
print('k=2 same-letter [b,b]: grid 8^3 (boundaries incl.):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok
# k=3 same-letter, with intermediates + prov + laundering
E3 = check('k=3 same-letter [b,b,b]', ['b', 'b', 'b'], 5, 400, 80, also_inter=True)
ok = True
for _ in range(200):
    runs = [rng.randint(0, 40) for _ in range(4)]
    w = mk(['b', 'b', 'b'], runs)
    p = prv(E3, w)
    ok &= p != tuple(range(len(w) - 1, -1, -1)) and len(set(p)) == len(p)
print('k=3 prov never DB + injective (200 random):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok
El3 = L('a', L('b', E3))
ok = True
for c in range(5 ** 4):
    runs = []; t = c
    for _ in range(4):
        runs.append(t % 5); t //= 5
    w = mk(['b', 'b', 'b'], runs)
    ok &= val(El3, w) == w[::-1] and prv(El3, w) == ()
print('k=3 laundered L_a.L_b.E: rev with prov == ():',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok
# k=4 same-letter
check('k=4 same-letter [b,b,b,b]', ['b', 'b', 'b', 'b'], 4, 300, 50)
# mixed structures
check('mixed [b,b,c]', ['b', 'b', 'c'], 5, 400, 80, also_inter=True)
check('mixed [b,c,b]', ['b', 'c', 'b'], 5, 300, 80)
check('mixed [c,b] (E_mix cross-check)', ['c', 'b'], 7, 300, 100)

# size counts for the k=2 engine (= E_rev) and k=3
for nm, letters in (('k=2 (E_rev)', ['b', 'b']), ('k=3', ['b', 'b', 'b']),
                    ('k=4', ['b', 'b', 'b', 'b'])):
    E, _, _, _ = build(letters)
    n, sd, dd = counts(E)
    print(f'size {nm}: {n} nodes, S-depth {sd}, AST depth {dd} (edges)')
print('GENERAL ENGINE:', 'ALL VERIFIED' if allok else 'REFUTED')

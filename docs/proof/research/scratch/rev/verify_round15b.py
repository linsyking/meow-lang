"""ROUND 15B — the general distinct-separator theorem (coordinator's own
construction, machine verification).

For every k >= 1 and distinct separators s_1..s_k (over Sigma =
{a, s_1..s_k}), rev is computable on the ALL-VARYING family

    X = a^{r_0} s_1 a^{r_1} s_2 a^{r_1+1} ... s_k a^{r_k}

by    E_k = [s_1/(mrg.s_1)] . [s_2/(mrg.s_2)] ... [s_{k-1}/(mrg.s_{k-1})]
             . ( D_k . D_{k-1} ... D_1 )

    mrg = (delete all separators) X = a^S ,  S = r_0+...+r_k
    L_m = (delete all separators except s_m) X = a^{r_0+..+r_{m-1}} s_m a^{r_m+..+r_k}
    D_m = [s_m/L_m](mrg . s_m . mrg) = a^{r_m+..+r_k} s_m a^{r_0+..+r_{m-1}}
    (complement engine on the m-th projection; S-node children all
    evaluate at the ORIGINAL input)

Concatenation D_k..D_1 = a^{r_k} s_k a^{S+r_{k-1}} s_{k-1} ... a^{S+r_1}
s_1 a^{r_0}: each inter-separator run is S + r_m.  Shave pass
[s_m/(mrg.s_m)] fires once at the unique s_m, its leading run S fitting
the run before s_m (iff r_m >= 0), removing exactly S and leaving r_m.
Shaves run s_{k-1} first, ..., s_1 last; s_k needs no shave (its leading
run r_k is exact) and r_0 is exact as D_1's right flank.

Special cases: k=1 is the round-14 complement engine [s_1/X](mrg.s_1.mrg);
k=2 is Lane C's T1 (E_mix); this file verifies k=3 and k=4 (Lane C left
k>=3 OPEN, unclaimed).

Run: /usr/bin/python3 -W ignore verify_round15b.py  (~30 s)
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
rng = random.Random(20260923)
allok = True

def E_k(seps):
    """seps = 'bcd' (s_1..s_k); returns the construction for that k."""
    k = len(seps)
    other = lambda m: ''.join(s for j, s in enumerate(seps) if j != m)
    # mrg = delete all separators (rightmost-first chain = delete s_k..s_1)
    mrg = X
    for s in reversed(seps):
        mrg = S(K(''), K(s), mrg)
    D = []
    for m, s in enumerate(seps):
        L = X                                   # keep only s_m
        for t in reversed(other(m)):
            L = S(K(''), K(t), L)
        D.append(S(K(s), L, C(C(mrg, K(s)), mrg)))
    body = D[k - 1]
    for m in range(k - 2, -1, -1):              # D_k . D_{k-1} ... D_1
        body = C(body, D[m])
    for m in range(k - 2, -1, -1):              # shaves s_{k-1},...,s_1
        body = S(K(seps[m]), C(mrg, K(seps[m])), body)
    return body

def wk(runs, seps):
    """a^{r_0} s_1 a^{r_1} ... s_k a^{r_k}"""
    out = []
    for m in range(len(seps) + 1):
        out.append('a' * runs[m])
        if m < len(seps):
            out.append(seps[m])
    return ''.join(out)

# ---- k = 1: unification with the round-14 complement engine ---------------
E1 = E_k('b')
ok = True
for i in range(0, 13):
    for j in range(0, 13):
        w = wk((i, j), 'b')
        ok &= val(E1, w) == w[::-1]
print('k=1  (round-14 complement engine shape) 13x13:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- k = 2: unification with Lane C's E_mix --------------------------------
E2 = E_k('bc')
ok = True
for i in range(0, 10):
    for j in range(0, 10):
        for k2 in range(0, 10):
            w = wk((i, j, k2), 'bc')
            ok &= val(E2, w) == w[::-1]
print('k=2  (= T1 / E_mix shape) 10^3:', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- k = 3: the family Lane C left OPEN ------------------------------------
E3 = E_k('bcd')
ok = True
for r0 in range(0, 9):
    for r1 in range(0, 9):
        for r2 in range(0, 9):
            for r3 in range(0, 9):
                w = wk((r0, r1, r2, r3), 'bcd')
                ok &= val(E3, w) == w[::-1]
for _ in range(400):
    runs = tuple(rng.randint(0, 120) for _ in range(4))
    w = wk(runs, 'bcd')
    ok &= val(E3, w) == w[::-1]
print('k=3  {a^i b a^j c a^k d a^l} 9^4 grid + 400 random:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- k = 4 ------------------------------------------------------------------
E4 = E_k('bcde')
ok = True
for r0 in range(0, 7):
    for r1 in range(0, 7):
        for r2 in range(0, 7):
            for r3 in range(0, 7):
                for r4 in range(0, 7):
                    w = wk((r0, r1, r2, r3, r4), 'bcde')
                    ok &= val(E4, w) == w[::-1]
for _ in range(300):
    runs = tuple(rng.randint(0, 100) for _ in range(5))
    w = wk(runs, 'bcde')
    ok &= val(E4, w) == w[::-1]
print('k=4  {a^i b a^j c a^k d a^l e a^m} 7^5 grid + 300 random:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- size counts ------------------------------------------------------------
def nodes(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + nodes(e[1]) + nodes(e[2])
    return 1 + nodes(e[1]) + nodes(e[2]) + nodes(e[3])

def snodes(e):
    if e[0] in ('K', 'V'):
        return 0
    if e[0] == 'C':
        return snodes(e[1]) + snodes(e[2])
    return 1 + snodes(e[1]) + snodes(e[2]) + snodes(e[3])

def sdepth(e):
    if e[0] in ('K', 'V'):
        return 0
    if e[0] == 'C':
        return max(sdepth(e[1]), sdepth(e[2]))
    return 1 + max(sdepth(e[1]), sdepth(e[2]), sdepth(e[3]))

for name, e in [('E_1', E1), ('E_2', E2), ('E_3', E3), ('E_4', E4)]:
    print('     %s: tree nodes %d, S-nodes %d, S-depth %d'
          % (name, nodes(e), snodes(e), sdepth(e)))
allok &= (snodes(E2), nodes(E2)) == (15, 58)     # E_2 == E_mix counts

print()
print('ROUND-15B GENERAL DISTINCT-SEPARATOR THEOREM:',
      'ALL VERIFIED' if allok else 'REFUTED')
sys.exit(0 if allok else 1)

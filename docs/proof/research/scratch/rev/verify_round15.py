"""ROUND 15 (Lane C, rev-try) — COORDINATOR VERIFICATION BATTERY.

Independent re-verification of the round-15 claims, re-derived by hand by
the coordinator (fresh encodings typed from the coordinator's own hand
derivations, NOT copied from the agent's scripts), plus re-establishment of
the checks the agent's final scripts dropped when they were overwritten
(the logs record them but the delivered scripts no longer reproduce them):
the rev-slack calculus, the size counts, the A7-convergence, and the
slack-class closure.  Run from this dir: /usr/bin/python3 -W ignore
verify_round15.py   (~10 s)

Claims under test (Lane C's round-15 report):
  T1   E_mix computes rev on {a^i b a^j c a^k}, i,j,k all varying.
  T3*  E_{c,d} computes rev on {a^i b a^{c(i+k)/d} b a^k} for gcd(c,d)=1.
  R1   V_h-equivalence: pad/strip constant passes.
  R5'  rev-slack calculus, CORRECTED FORMS (the delivered log's formula
       [a^{d1+r0} b a^{r1+h-d1} / a^{r0} b a^{r1}] on slack text is a
       sign slip: it yields a^{k+2d1} b a^{j+2h} b a^{i+2d2}, not rev).
       The two correct directions, both verified here:
         PAD   [a^{r0+d1} b a^{r1+d2} / a^{r0} b a^{r1}] on rev
               -> a^{k+d1} b a^{j+h} b a^{i+d2}   (h = d1+d2)
         STRIP [a^{r0-d1} b a^{r1-d2} / a^{r0} b a^{r1}] on
               a^{k+d1} b a^{j+h} b a^{i+d2} -> rev
       with bounds r0 >= d1, r1 >= d2, k+d1 >= r0, j+h >= r1+r0, i+d2 >= r1.
  D    slack-class closure: a one-b constant pass maps the class
       {a^{k+d1} b a^{j+c} b a^{i+d2}} to itself (affine action on
       (d1, c, d2), independent of i,j,k).
  E    A7-convergence: [eps/(b.M.b)] w2 = a^{i+k} on F_{c,d}.
  F    size counts: E_mix tree (S-nodes, size, S-depth), E_{c,d} same.
  G    ST2 residue-cell refinement (coordinator's hand claim): on each
       mod-2 cell of (i,j,k) the halver [a/aa]X total is (S + #odd)/2 —
       an S-function PER CELL, so the landed per-piece Lemma S (with
       residue classes) survives ST2; only the residue-less S-exact
       reading dies.
"""
import random, sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))


def w3(i, j, k): return 'a' * i + 'b' + 'a' * j + 'c' + 'a' * k
def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
rng = random.Random(20260922)
allok = True

# ---- part A: E_mix, fresh encoding from the coordinator's derivation ----
# mrg = [eps/c][eps/b]X ; Lb = [eps/c]X ; Lc = [eps/b]X
# Cc = [c/Lc](mrg.c.mrg) ; Bb = [b/Lb](mrg.b.mrg) ; E_mix = [b/(mrg.b)](Cc.Bb)
D = lambda p: S(K(''), K(p), X)
mrg = S(K(''), K('c'), D('b'))
Lb, Lc = D('c'), D('b')
Cc = S(K('c'), Lc, C(C(mrg, K('c')), mrg))
Bb = S(K('b'), Lb, C(C(mrg, K('b')), mrg))
E_mix = S(K('b'), C(mrg, K('b')), C(Cc, Bb))
ok = True
for i in range(13):
    for j in range(13):
        for k in range(13):
            w = w3(i, j, k)
            ok &= val(E_mix, w) == w[::-1]
for _ in range(500):
    i, j, k = (rng.randint(0, 300), rng.randint(0, 300), rng.randint(0, 300))
    ok &= val(E_mix, w3(i, j, k)) == w3(i, j, k)[::-1]
print('A  E_mix fresh encoding, 13^3 grid + 500 random:',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- part B: E_{c,d} fresh encoding ----
mrgb = S(K(''), K('b'), X)                 # [eps/b]X = a^S
def E_cd(c, d):
    F = S(K('a' * d), K('a' * (c + d)), mrgb)
    M = S(K('a' * c), K('a' * (c + d)), mrgb)
    R = C(C(K('b'), M), K('b'))
    T = C(C(C(F, K('b')), M), C(K('b'), F))
    return S(R, X, T)
ok = True
for (c, d) in [(0, 1), (1, 1), (2, 1), (3, 1), (1, 2), (3, 2), (2, 3),
               (5, 2), (4, 3), (1, 3), (7, 3), (5, 6)]:
    E = E_cd(c, d)
    for t in range(0, 21):
        for i in range(0, d * t + 1):
            k = d * t - i
            ok &= val(E, w2(i, c * t, k)) == w2(i, c * t, k)[::-1]
    for _ in range(200):
        t = rng.randint(0, 150)
        i = rng.randint(0, d * t)
        ok &= val(E, w2(i, c * t, d * t - i)) == w2(i, c * t, d * t - i)[::-1]
print('B  E_{c,d} fresh encoding, 12 pairs (incl. 7/3, 5/6):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- part C: rev-slack calculus, corrected forms ----
ok = True
for _ in range(400):
    h = rng.randint(1, 4)
    d1 = rng.randint(0, h)
    d2 = h - d1
    r0 = rng.randint(d1, d1 + 3)
    r1 = rng.randint(d2, d2 + 3)
    # PAD runs on rev (first run k, middle j, right i): needs k >= r0,
    # j >= r1+r0, i >= r1.  STRIP runs on slack (runs k+d1, j+h, i+d2):
    # needs k+d1 >= r0, j+h >= r1+r0, i+d2 >= r1.  Both must hold.
    k = rng.randint(max(r0, r0 - d1), 60)
    j = rng.randint(max(r1 + r0, r1 + r0 - h), 60)
    i = rng.randint(max(r1, r1 - d2), 60)
    pad = S(K('a' * (r0 + d1) + 'b' + 'a' * (r1 + d2)),
            K('a' * r0 + 'b' + 'a' * r1), X)
    strip = S(K('a' * (r0 - d1) + 'b' + 'a' * (r1 - d2)),
             K('a' * r0 + 'b' + 'a' * r1), X)
    rev = w2(k, j, i)                        # a^k b a^j b a^i
    slack = w2(k + d1, j + h, i + d2)        # a^{k+d1} b a^{j+h} b a^{i+d2}
    ok &= val(pad, rev) == slack             # PAD: rev -> slack
    ok &= val(strip, slack) == rev            # STRIP: slack -> rev
print("C  rev-slack calculus PAD/STRIP (corrected signs, 400):",
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- part D: slack-class closure under one-b constant passes ----
ok = True
for _ in range(300):
    d1, c0, d2 = (rng.randint(0, 3), rng.randint(0, 4), rng.randint(0, 3))
    r0, r1 = rng.randint(0, 4), rng.randint(0, 4)
    x, y = rng.randint(0, 4), rng.randint(0, 4)
    # bounds so both sites fire: k+d1>=r0, j+c0>=r1 (then >=r0 after r1),
    # i+d2>=r1
    k = rng.randint(max(0, r0 - d1), 50)
    j = rng.randint(max(0, r1 + r0 - c0), 50)
    i = rng.randint(max(0, r1 - d2), 50)
    E = S(K('a' * x + 'b' + 'a' * y), K('a' * r0 + 'b' + 'a' * r1), X)
    out = val(E, w2(k + d1, j + c0, i + d2))
    # check: exactly two b's, and the offsets (out flanks minus k, j, i)
    # are constant across a second triple with the same constants
    parts = out.split('b')
    ok &= len(parts) == 3 and all(p == '' or set(p) == {'a'} for p in parts)
    K1, J1, I1 = (len(parts[0]), len(parts[1]), len(parts[2]))
    ok &= (K1 - k, J1 - j, I1 - i) == (d1 - r0 + x, c0 + x + y - r1 - r0,
                                       d2 + y - r1)
    # constancy: same pass, same (d1,c0,d2), different (k,j,i) -> same offsets
    k2 = k + rng.randint(1, 20)
    j2 = j + rng.randint(1, 20)
    i2 = i + rng.randint(1, 20)
    out2 = val(E, w2(k2 + d1, j2 + c0, i2 + d2))
    p2 = out2.split('b')
    ok &= (len(p2) == 3 and
           (len(p2[0]) - k2, len(p2[1]) - j2, len(p2[2]) - i2) ==
           (K1 - k, J1 - j, I1 - i))
print('D  slack-class closure, affine action on (d1,c,d2) (300):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- part E: A7-convergence ----
ok = True
for (c, d) in [(1, 1), (2, 1), (3, 2), (1, 3)]:
    M = S(K('a' * c), K('a' * (c + d)), mrgb)
    A7 = S(K(''), C(C(K('b'), M), K('b')), X)   # [eps/(b.M.b)]w2
    for _ in range(200):
        t = rng.randint(0, 100)
        i = rng.randint(0, d * t)
        ok &= val(A7, w2(i, c * t, d * t - i)) == 'a' * (i + d * t - i)
print('E  A7-convergence [eps/(b.M.b)]w2 = a^{i+k} (4 families x 200):',
      'VERIFIED' if ok else 'REFUTED')
allok &= ok

# ---- part F: size counts (tree counts, shared subtrees instantiated) ----
def nodes(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + nodes(e[1]) + nodes(e[2])
    if t == 'S':
        return 1 + nodes(e[1]) + nodes(e[2]) + nodes(e[3])
    raise ValueError(t)

def snodes(e):
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return snodes(e[1]) + snodes(e[2])
    if t == 'S':
        return 1 + snodes(e[1]) + snodes(e[2]) + snodes(e[3])
    raise ValueError(t)

def sdepth(e):
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return max(sdepth(e[1]), sdepth(e[2]))
    if t == 'S':
        return 1 + max(sdepth(e[1]), sdepth(e[2]), sdepth(e[3]))
    raise ValueError(t)

def depth(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + max(depth(e[1]), depth(e[2]))
    if t == 'S':
        return 1 + max(depth(e[1]), depth(e[2]), depth(e[3]))
    raise ValueError(t)

for name, e in [('E_mix', E_mix), ('E_{1,1}', E_cd(1, 1)),
                ('E_{2,1}', E_cd(2, 1)), ('E_{1,2}', E_cd(1, 2))]:
    print('F  %s: tree nodes %d, S-nodes %d, S-depth %d, AST depth %d '
          '(nodes) / %d (edges)'
          % (name, nodes(e), snodes(e), sdepth(e), depth(e), depth(e) - 1))
    if name == 'E_mix':
        allok &= (nodes(e), snodes(e), sdepth(e), depth(e) - 1) == \
            (58, 15, 4, 7)
    else:
        allok &= (nodes(e), snodes(e), sdepth(e), depth(e) - 1) == \
            (40, 9, 3, 6)

# ---- part G: ST2 residue-cell refinement ----
half = S(K('a'), K('aa'), X)
ok = True
for i in range(0, 7):
    for j in range(0, 7):
        for k in range(0, 7):
            w = w2(i, j, k)
            got = val(half, w).count('a')
            nodd = (i % 2) + (j % 2) + (k % 2)
            ok &= got == ((i + j + k) + nodd) // 2
            ok &= val(half, w) == ('a' * ((i + 1) // 2) + 'b' +
                                  'a' * ((j + 1) // 2) + 'b' +
                                  'a' * ((k + 1) // 2))
print('G  ST2 cells: halver total = (S+#odd)/2 per mod-2 cell; per-run '
      'ceil-halving (7^3):', 'VERIFIED' if ok else 'REFUTED')
allok &= ok

print()
print('ROUND-15 COORDINATOR BATTERY:', 'ALL VERIFIED' if allok else 'REFUTED')
sys.exit(0 if allok else 1)

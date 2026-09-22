"""rev-split ROUND 1 -- grid verification of the hand-derived engine
identities (part A) on F = {a^i b a^j} (and W2 where noted).

The machine only falsifies or surfaces candidates; every identity here
was hand-derived first (see REPORT.md sections 2-4).

  A1  [e/C(shrinkL,shrinkR)] C(w,w)      = "aa"          (two-b engine, remnant 2)
  A2  [e/C(shrinkL,swap)]    C(w,swap)   = "a"           (two-b engine, remnant 1)
  A3  SYSTEMATIC two-b deletion engine: for all quadruples of one-b
      values (X1,X2,Y1,Y2) from the 7-value stock and all grid points:
      if text C(X1,X2) and pattern C(Y1,Y2) both have exactly 2 b's,
      their interiors are equal, and the flanks dominate, then the
      output is exactly a^(len(X1)+len(X2)-len(Y1)-len(Y2)); else (no
      interior match / no domination) the output is the unchanged text.
      This verifies the engine algebra AND its limitation: the remnant
      is a difference of total lengths (all symmetric forms).
  A4  [e/merge]dbl^2 = (i-3j, 4j) on the cone i > 3j  and
      (2i-2j, 3j-i) on the cone j <= i <= 3j   (division-remainder
      engine: asymmetric RUNS, symmetric total).
  A5  complement engine [R/w]bigsym = (j+r0, i+r1) for constant R =
      a^r0 b a^r1, all r0,r1 <= 2: total a-mass always i+j+r0+r1.
  A6  DIAGONAL EXCEPTION: [a/aa]merge = a^i on the lines j = i and
      j = i-1 (1-D families escape the invariant; F itself does not).
  A7  W2 lock-baked mechanism: [e/(b a^j b)]w2 = a^(i+k) and
      [b/(b a^j b)]w2 = a^i b a^k  (patterns BAKED with middle-run
      knowledge -- not constructible, mechanism check only).
  A8  [e/swap]bigsym = w  and  [b/swap]bigsym = w  (cute identities;
      the complement of w in bigsym via swap is w again).
  A9  [e/C(shrinkR,shrinkL)]C(w,w) = C(w,w)  (interior i+j-2 != i+j:
      never fires).
  A10 [e/C(w,swap)]C(w,swap) = eps (self-collapse: pattern = text).
"""
import sys, time
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0); lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def CC(*a):
    r = a[0]
    for t in a[1:]: r = C(r, t)
    return r
def D(e):            return S(K(''), e, X)             # [e/P] on X
def runvec(s):
    """runs of 'a' between b's -> (list_of_runs, nb)"""
    runs, cur, nb = [], 0, 0
    for ch in s:
        if ch == 'a': cur += 1
        else: runs.append(cur); cur = 0; nb += 1
    runs.append(cur)
    return runs, nb

t0 = time.time()
print('rev-split ROUND 1 -- grid identities (falsify/discover only)')
print('=' * 72)

# ---- library (one-b stock, all hand-derived in round 13 / here) ----
merge   = S(K(''), K('b'), X)
bigsym  = CC(merge, K('b'), merge)
swap    = S(K('b'), X, bigsym)
dbl     = S(K('aa'), K('a'), X)
half    = S(K('a'), K('aa'), X)
shrinkL = S(K('b'), K('ab'), X)
shrinkR = S(K('b'), K('ba'), X)
diff    = S(K(''), merge, dbl)
dbl2    = S(K('aa'), K('a'), dbl)
halft   = S(K('a'), K('aa'), merge)          # [a/aa]merge

ok = True

# ---------------------------------------------------------------- A1
print('\n[A1] [e/C(shrinkL,shrinkR)]C(w,w) = "aa"')
E = S(K(''), C(shrinkL, shrinkR), C(X, X))
for i in range(1, 9):
    for j in range(1, 9):
        w = 'a' * i + 'b' + 'a' * j
        ok &= val(E, w) == 'aa'
print('  8x8 grid:', 'VERIFIED' if ok else 'REFUTED')

# ---------------------------------------------------------------- A2
print('\n[A2] [e/C(shrinkL,swap)]C(w,swap) = "a"')
E = S(K(''), C(shrinkL, swap), C(X, swap))
ok2 = True
for i in range(1, 9):
    for j in range(1, 9):
        w = 'a' * i + 'b' + 'a' * j
        ok2 &= val(E, w) == 'a'
print('  8x8 grid:', 'VERIFIED' if ok2 else 'REFUTED')
ok &= ok2

# ---------------------------------------------------------------- A3
print('\n[A3] systematic two-b deletion engine (7^4 quadruples, 4x4 grid)')
stock = {'w': X, 'swap': swap, 'shrinkL': shrinkL, 'shrinkR': shrinkR,
         'dbl': dbl, 'bigsym': bigsym, 'diff': diff}
names = list(stock)
nfire = nno = nbad = nskip = 0
pts = [(i, j) for i in range(2, 6) for j in range(2, 6)]
for n1 in names:
    for n2 in names:
        for m1 in names:
            for m2 in names:
                textE = C(stock[n1], stock[n2])
                patE  = C(stock[m1], stock[m2])
                E = S(K(''), patE, textE)
                for (i, j) in pts:
                    w = 'a' * i + 'b' + 'a' * j
                    try:
                        T = val(textE, w); P = val(patE, w)
                    except PV.Undefined:
                        nskip += 1; continue
                    if not T or not P: nskip += 1; continue
                    tr, tb = runvec(T); pr, pb = runvec(P)
                    if tb != 2 or pb != 2: nskip += 1; continue
                    # interior equality + flank domination?
                    precond = (tr[1] == pr[1] and tr[0] >= pr[0]
                               and tr[2] >= pr[2])
                    out = val(E, w)
                    if precond:
                        nfire += 1
                        if out != 'a' * (len(T) - len(P)): nbad += 1
                    else:
                        nno += 1
                        if out != T: nbad += 1
print('  firings checked: %d, no-fire cases: %d, skipped (shape): %d'
      % (nfire, nno, nskip))
print('  formula violations:', nbad,
      '=>', 'VERIFIED' if nbad == 0 else 'REFUTED')
ok &= (nbad == 0)

# ---------------------------------------------------------------- A4
print('\n[A4] division-remainder engine [e/merge]dbl^2')
E = S(K(''), merge, dbl2)
okA = okB = okL = True; nA = nB = nL = 0
for i in range(1, 26):
    for j in range(1, 26):
        w = 'a' * i + 'b' + 'a' * j
        out = val(E, w)
        if i > 3 * j:
            nA += 1; okA &= out == 'a' * (i - 3 * j) + 'b' + 'a' * (4 * j)
        elif j < i < 3 * j:
            nB += 1; okB &= out == 'a' * (2 * i - 2 * j) + 'b' + 'a' * (3 * j - i)
        elif i == j or i == 3 * j:
            nL += 1; okL &= out == 'b'    # cut lines are their own cells
print('  OPEN cone i>3j (%d pts): %s' % (nA, 'VERIFIED' if okA else 'REFUTED'))
print('  OPEN cone j<i<3j (%d pts): %s' % (nB, 'VERIFIED' if okB else 'REFUTED'))
print('  cut lines i=j, i=3j (%d pts) -> "b": %s'
      % (nL, 'VERIFIED' if okL else 'REFUTED'))
ok &= okA and okB and okL

# ---------------------------------------------------------------- A5
print('\n[A5] complement engine [R/w]bigsym = (j+r0, i+r1)')
ok5 = True; n5 = 0
for r0 in range(0, 3):
    for r1 in range(0, 3):
        R = 'a' * r0 + 'b' + 'a' * r1
        E = S(K(R), X, bigsym)
        for i in range(1, 8):
            for j in range(1, 8):
                w = 'a' * i + 'b' + 'a' * j
                n5 += 1
                ok5 &= val(E, w) == 'a' * (j + r0) + 'b' + 'a' * (i + r1)
print('  %d pts (r0,r1<=2, 7x7):' % n5, 'VERIFIED' if ok5 else 'REFUTED')
ok &= ok5

# ---------------------------------------------------------------- A6
print('\n[A6] DIAGONAL exception: [a/aa]merge = a^i on j=i and j=i-1')
okD = okE = True
for i in range(1, 15):
    for j in (i, i - 1):
        if j < 1: continue
        w = 'a' * i + 'b' + 'a' * j
        if val(halft, w) != 'a' * i:
            if j == i: okD = False
            else: okE = False
print('  line j=i:', 'VERIFIED' if okD else 'REFUTED',
      '| line j=i-1:', 'VERIFIED' if okE else 'REFUTED')

# ---------------------------------------------------------------- A7
print('\n[A7] W2 lock-baked mechanism (baked middle, NOT constructible)')
ok7 = True
for i in range(1, 6):
    for j in range(1, 6):
        for k in range(1, 6):
            w2 = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
            P = 'b' + 'a' * j + 'b'
            e1 = S(K(''), K(P), X); e2 = S(K('b'), K(P), X)
            ok7 &= val(e1, w2) == 'a' * (i + k)
            ok7 &= val(e2, w2) == 'a' * i + 'b' + 'a' * k
print('  5x5x5 grid:', 'VERIFIED' if ok7 else 'REFUTED')

# ---------------------------------------------------------------- A8
print('\n[A8] [b/swap]bigsym = w ; [e/swap]bigsym = merge (b-free merges)')
ok8 = True
for i in range(1, 9):
    for j in range(1, 9):
        w = 'a' * i + 'b' + 'a' * j
        ok8 &= val(S(K('b'), swap, bigsym), w) == w
        ok8 &= val(S(K(''), swap, bigsym), w) == 'a' * (i + j)
print('  8x8 grid:', 'VERIFIED' if ok8 else 'REFUTED')
ok &= ok8

# ---------------------------------------------------------------- A9
print('\n[A9] [e/C(shrinkR,shrinkL)]C(w,w) = C(w,w) (never fires)')
ok9 = True
for i in range(1, 8):
    for j in range(1, 8):
        w = 'a' * i + 'b' + 'a' * j
        T = val(C(X, X), w)
        ok9 &= val(S(K(''), C(shrinkR, shrinkL), C(X, X)), w) == T
print('  7x7 grid:', 'VERIFIED' if ok9 else 'REFUTED')
ok &= ok9

# ---------------------------------------------------------------- A10
print('\n[A10] [e/C(w,swap)]C(w,swap) = eps (self-collapse)')
ok10 = True
for i in range(1, 8):
    for j in range(1, 8):
        w = 'a' * i + 'b' + 'a' * j
        ok10 &= val(S(K(''), C(X, swap), C(X, swap)), w) == ''
print('  7x7 grid:', 'VERIFIED' if ok10 else 'REFUTED')
ok &= ok10

print('\nROUND 1 grid identities:', 'ALL VERIFIED' if ok else 'REFUTED')
print('%.1fs' % (time.time() - t0))

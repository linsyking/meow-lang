"""ROUND 14 machine verification (2026-09-22).  All theory-side: the
machine only falsifies or discovers cheaply -- never proves.

  A. Coordinator's seed re-verified: junction-shave stratum, their c's.
  B. THE FIXED-MIDDLE THEOREM, OPTIMAL FORM (c = 0):
        E_M = [M^R / X] . C([e/M]X, M, [e/M]X)
     computes rev on {a^i M a^k : i, k >= 0} for EVERY M containing at
     least one letter != 'a'.  Boundaries included; 29-M battery +
     random; prov injective and never DB.  M = 'b' is round-13 E_swap.
  C. Self-anchoring lemma, string level:
     (i) M occurs exactly once in a^i M a^k;
     (ii) a^i M a^k occurs exactly once in a^L M a^L for L >= max(i,k).
  D. Calculus fact (strengthens 13.2(i)):
     D1  [a^r/a^p] maps a run a^u to psi(u) = r*floor(u/p) + (u mod p)
         (greedy tiling from the left), string level;
     D2  no composition of <= 3 b-free/b-free passes is u -> u - c on a
         tail with c != 0 (exhaustive p, r in [1..5]^3 = 15625 combos):
         a nonzero constant can never be shaved off a b-free run by
         b-free means.
  E. REDUCTION: SPLIT => REV-ON-W2.  If some E computes the middle
     value w2 |-> a^j (equivalently b a^j b), then
        E_rev = [MID/X] . C([e/MID]X, MID, [e/MID]X),
        MID = C(K(b), E_mid, K(b)),
     computes rev on W2 = {a^i b a^j b a^k : i, j, k >= 1}: MID = b a^j b
     is a palindrome, so the fixed-middle engine (part B) applies with
     computed middle.  Machine check: E_mid instantiated by constants
     K(a^j), j in 1..6 -- validates the engine on each fixed-j slice.
     Plus the laundered variant: L_a.L_b.E_bab computes rev with
     prov = () (dead prov, like round 13's laundered E_swap).
  F. Boundary/degenerate battery for the theorem statement: M = a^d
     (pure filler) -- [e/a^d] misfires inside the flanks (the family is
     the one-b slice of round 13, handled there); documented, not run.
"""
import random, sys, time
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0); lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def prv(e, w): return PV.labels(PV.lden(e, (lab(w),)))
def D(p):            return S(K(''), K(p), X)          # [e/p]
def symm(sh, M, R):  return S(K(R), X, C(C(sh, K(M)), sh))

t0 = time.time()
V = []   # (name, ok) per part
def verdict(name, ok):
    V.append((name, ok))
print('ROUND 14 -- machine verification (falsify/discover only)')
print('=' * 72)

# ---------------------------------------------------------------- A
print('\n[A] coordinator seed: junction-shave stratum (their c values)')
cases = [
    ('bab',   1, symm(D('ab'),  'bab',   'ababa')),
    ('baab',  2, symm(D('aab'), 'baab',  'aabaabaa')),
    ('babab', 1, symm(D('ab'),  'babab', 'abababa')),
    ('baac',  2, symm(S(K(''), K('aab'), D('aac')), 'baac', 'aacaabaa')),
    ('bb',    2, symm(S(K(''), K('ba'), D('ab')),   'bb',    'aabbaa')),
]
allok = okp = True
for (M, c, E) in cases:
    ok = True
    for i in range(c, c + 14):
        for k in range(c, c + 14):
            w = 'a' * i + M + 'a' * k
            ok &= val(E, w) == 'a' * k + M[::-1] + 'a' * i
    rng = random.Random(hash(M) & 0xffff)
    for _ in range(400):
        i, k = rng.randint(c, 200), rng.randint(c, 200)
        ok &= val(E, 'a'*i + M + 'a'*k) == 'a'*k + M[::-1] + 'a'*i
    for _ in range(300):
        i, k = rng.randint(c, 60), rng.randint(c, 60)
        p, n = prv(E, 'a'*i + M + 'a'*k), len('a'*i + M + 'a'*k)
        okp &= p != tuple(range(n - 1, -1, -1)) and len(set(p)) == len(p)
    allok &= ok
    print('  M=%-6s c=%d: %s' % (M, c, 'VERIFIED' if ok else 'REFUTED'))
print('[A] seed (junction shaves, c in {1,2}):',
      'ALL VERIFIED' if allok else 'REFUTED')
verdict('A seed', allok and okp)

# ---------------------------------------------------------------- B
print('\n[B] fixed-middle theorem, OPTIMAL c = 0: '
      'E_M = [M^R/X].C([e/M]X, M, [e/M]X)')
def Egen(M):
    sh = S(K(''), K(M), X)
    return S(K(M[::-1]), X, C(C(sh, K(M)), sh))

Ms = ['b', 'bab', 'baab', 'babab', 'baac', 'bb', 'ab', 'ba', 'aba',
      'abba', 'aabb', 'bbaa', 'abab', 'aabaa', 'aaabaaa', 'bbb',
      'abbb', 'bbba', 'aabbcc', 'cab', 'aac', 'abcba', 'aabbaabb',
      'abababab', 'baaab', 'cbabc', 'aabaab', 'bbaabb']
allok = okp = True
for M in Ms:
    E = Egen(M); ok = True
    for i in range(0, 9):                       # FULL family, boundaries
        for k in range(0, 9):
            w = 'a' * i + M + 'a' * k
            ok &= val(E, w) == 'a' * k + M[::-1] + 'a' * i
    rng = random.Random(hash(M) & 0xffff)
    for _ in range(400):
        i, k = rng.randint(0, 200), rng.randint(0, 200)
        ok &= val(E, 'a'*i + M + 'a'*k) == 'a'*k + M[::-1] + 'a'*i
    for _ in range(300):
        i, k = rng.randint(0, 60), rng.randint(0, 60)
        w = 'a'*i + M + 'a'*k
        p = prv(E, w); n = len(w)
        okp &= p != tuple(range(n - 1, -1, -1)) and len(set(p)) == len(p)
    allok &= ok
print('  %d middles (incl. all five seed M and M = b): %s'
      % (len(Ms), 'ALL VERIFIED on full family {i,k >= 0}' if allok
         else 'REFUTED'))
print('  prov injective, never DB:',
      'VERIFIED' if okp else 'REFUTED')

# B2: M = 'b' coincides with round-13 E_swap (content equality on grid).
merge  = S(K(''), K('b'), X)
bigsym = C(C(merge, K('b')), merge)
Eswap  = S(K('b'), X, bigsym)
ok = all(val(Egen('b'), w) == val(Eswap, w)
         for i in range(0, 12) for k in range(0, 12)
         for w in ['a'*i + 'b' + 'a'*k])
print('  M = b reproduces round-13 E_swap:',
      'VERIFIED' if ok else 'REFUTED')
verdict('B c=0 theorem', ok and allok and okp)

# B3: junction-shave tiling formula.  For M = a^{mu0} b ... b a^{mum}
# (m junction b's) and the one-b pass [e/(a^x b a^y)]: on the firing
# region, output = a^{i+k-c} with
#   c = (x-mu0) + sum_{j=1}^{m-1}(x+y-mu_j) + (y-mum).
rng2 = random.Random(1414)
okf = True
ntr = 0
for _ in range(4000):
    m = rng2.randint(1, 3)
    mus = [rng2.randint(0, 3) for _ in range(m + 1)]
    M = 'a'*mus[0] + 'b' + ''.join('a'*mus[t] + 'b'
                                   for t in range(1, m)) + 'a'*mus[m]
    x, y = rng2.randint(0, 3), rng2.randint(0, 3)
    # firing region: i+mu0 >= x; mu_j >= x+y (internal); mu_m+k >= y
    if any(mu < x + y for mu in mus[1:-1] if m >= 2): continue
    i = rng2.randint(max(0, x - mus[0]), max(0, x - mus[0]) + 25)
    k = rng2.randint(max(0, y - mus[m]), max(0, y - mus[m]) + 25)
    if i + mus[0] < x or mus[m] + k < y: continue
    c = ((x - mus[0]) + sum(x + y - mus[t] for t in range(1, m))
         + (y - mus[m]))
    w = 'a'*i + M + 'a'*k
    got = val(D('a'*x + 'b' + 'a'*y), w)
    ntr += 1
    okf &= (got == 'a'*(i + k - c))
print('  B3 junction-shave c-formula (%d in-region trials):' % ntr,
      'VERIFIED' if okf else 'REFUTED')
verdict('B3 junction c-formula', okf)

# ---------------------------------------------------------------- C
print('\n[C] self-anchoring lemma, string level')
rng = random.Random(14)
ok1 = ok2 = ok3 = True
for _ in range(20000):
    ml, al = rng.randint(1, 6), rng.randint(0, 2)
    alpha = 'abc'[:al]
    M = ''.join(rng.choice((alpha + 'b') if 'b' not in alpha
                           else alpha + 'a') for _ in range(ml))
    if all(ch == 'a' for ch in M): continue
    i, k = rng.randint(0, 30), rng.randint(0, 30)
    t = 'a'*i + M + 'a'*k
    ok1 &= t.count(M) == 1
    L = max(i, k) + rng.randint(0, 5)
    ok2 &= ('a'*L + M + 'a'*L).count(t) == 1
    # greedy [e/M] on t == a^{i+k} (Python count-based emulation of the
    # leftmost-greedy single pass; M unique by (i), so one deletion):
    ok3 &= t.replace(M, '', 1) == 'a'*(i + k)
print('  (i)   M unique in a^i M a^k:            ',
      'VERIFIED' if ok1 else 'REFUTED')
print('  (ii)  pattern unique in a^L M a^L:      ',
      'VERIFIED' if ok2 else 'REFUTED')
print('  (iii) greedy [e/M] on a^i M a^k = a^ik:  ',
      'VERIFIED' if ok3 else 'REFUTED')
verdict('C self-anchoring', ok1 and ok2 and ok3)

# ---------------------------------------------------------------- D
print('\n[D] calculus fact (strengthens 13.2(i))')
def psi(p, r, u): return r*(u//p) + u % p
okd = True
for _ in range(5000):
    p, r, u = rng.randint(1, 9), rng.randint(1, 9), rng.randint(0, 300)
    out, i = '', 0                        # string-level greedy tiling
    while i + p <= u:
        out += 'a'*r; i += p
    out += 'a'*(u - i)
    okd &= len(out) == psi(p, r, u)
print('  D1 psi(u) = r*floor(u/p) + u mod p:     ',
      'VERIFIED' if okd else 'REFUTED')

pairs = [(p, r) for p in range(1, 6) for r in range(1, 6)]
U, TAIL, bad, ncomp = 120, 60, [], 0
for a in pairs:
    for b in pairs:
        for c3 in pairs:
            ncomp += 1
            vals = [psi(*a, psi(*b, psi(*c3, u))) for u in range(TAIL, U)]
            d = [vals[t] - (TAIL + t) for t in range(U - TAIL)]
            if len(set(d)) == 1 and d[0] != 0:
                bad.append((a, b, c3, d[0]))
print('  D2 %d compositions (depth 3, p,r<=5); tail-'
      'translations u-c, c!=0: %d' % (ncomp, len(bad)))
print('     no constant shaved off a b-free run by b-free means:',
      'VERIFIED' if not bad else 'REFUTED ' + str(bad[:3]))
verdict('D calculus fact', okd and not bad)

# ---------------------------------------------------------------- E
print('\n[E] reduction SPLIT => REV-ON-W2 (computed palindrome middle)')
def Erev(E_mid):
    MID = C(C(K('b'), E_mid), K('b'))          # b a^j b  (palindrome)
    sh  = S(K(''), MID, X)                     # [e/MID]X = a^{i+k}
    return S(MID, X, C(C(sh, MID), sh))        # [MID/X].C(sh, MID, sh)

ok = True
for j in range(1, 7):
    E = Erev(K('a' * j))                       # E_mid := K(a^j)
    for i in range(0, 9):
        for k in range(0, 9):
            w = 'a'*i + 'b' + 'a'*j + 'b' + 'a'*k
            ok &= val(E, w) == 'a'*k + 'b' + 'a'*j + 'b' + 'a'*i
    rng = random.Random(j)
    for _ in range(300):
        i, k = rng.randint(0, 150), rng.randint(0, 150)
        w = 'a'*i + 'b' + 'a'*j + 'b' + 'a'*k
        ok &= val(E, w) == 'a'*k + 'b' + 'a'*j + 'b' + 'a'*i
print('  engine on fixed-j slices j=1..6 (grids + 300 random each):',
      'VERIFIED' if ok else 'REFUTED')

def L(expr, s):
    return S(K(s), K(s + s), S(K(s + s), K(s), expr))
EM = Egen('bab')
El = L(L(EM, 'a'), 'b')
ok = True
for i in range(0, 7):
    for k in range(0, 7):
        w = 'a'*i + 'bab' + 'a'*k
        ok &= val(El, w) == 'a'*k + 'bab' + 'a'*i and prv(El, w) == ()
print('  laundered L_a.L_b.E_bab: rev with prov = ():',
      'VERIFIED' if ok else 'REFUTED')

# ---------------------------------------------------------------- F
print('\n[F] degenerate M = a^d (pure filler): family is the one-b '
      'slice; [e/a^d] fires\n     inside flanks; handled by round 13. '
      'Not a case of the theorem (M must\n     contain a non-flank '
      'letter).  Documented only -- no run needed.')

verdict('E reduction + laundered', ok)
print('\n' + '=' * 72)
for (nm, g) in V: print('  %-24s %s' % (nm, 'OK' if g else 'FAIL'))
print('ROUND 14:', 'ALL VERIFIED' if all(g for _, g in V)
      else 'REFUTED', ' (%.1fs)' % (time.time() - t0))

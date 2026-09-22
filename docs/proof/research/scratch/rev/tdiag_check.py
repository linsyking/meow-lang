"""T-DIAGONALITY machine spot-check (round 14, reduction analysis).

Claim under test (Lemma A' / total-type calculus, derived in the
reduction analysis; relayed to the parallel lanes): for every value V
constructible from X = w2 = a^i b a^j b a^k by passes/C/constants, the
TOTAL a-count of V is piecewise affine on finitely many
(full-dimensional) pieces, and on each piece its coefficient-triple is
DIAGONAL: N_V = Lambda*(i+j+k) + nu.  Consequences: (1) a b-free value
(single run) has diagonal type, so pure types -- a^j = (0,1,0), a^i,
a^k, a^{i+k} = (1,0,1) -- are NOT constructible (the split toll);
(2) one-b and two-b values may have non-diagonal RUNS but their totals
stay diagonal.

Method: for every [R/P]F over the 16-value library x 24-pool (the
round-14 sweep's S1 stratum), evaluate on the 4x4x4 grid, group points
by b-count, and on each b-stable group with >= 12 points that affinely
spans all three directions (rank filter -- degenerate groups such as
k = 1 slices have unidentified coefficients and are excluded) fit the
TOTAL a-count exactly as an affine function of (i,j,k) (integer Cramer
on up to 15 subsets of the first 6 points, exact Fraction verification
on the whole group).  Dead-pattern combos (P never fires on the grid)
are skipped -- they return F itself, whose total is checked whenever F
appears as a live combo's scrutinee.  Non-affine (piecewise) groups are
skipped and counted.  Falsification only -- the machine never proves.
"""
import itertools
from fractions import Fraction as F

def spass(s, pat, rep):
    if pat == '': return s
    out, i, n, m = [], 0, len(s), len(pat)
    while i < n:
        if s[i:i+m] == pat:
            out.append(rep); i += m
        else:
            out.append(s[i]); i += 1
    return ''.join(out)

def det4(m):
    # integer 4x4 determinant by cofactor expansion
    def det3(a):
        return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
                - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
                + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))
    t = 0
    for c in range(4):
        minor = [[m[r][cc] for cc in range(4) if cc != c]
                 for r in range(1, 4)]
        t += ((-1)**c) * m[0][c] * det3(minor)
    return t

def cramer(pts):
    A = [[p[0], p[1], p[2], 1] for p in pts]
    rhs = [p[3] for p in pts]
    D = det4(A)
    if D == 0: return None
    sol = []
    for c in range(4):
        Ac = [row[:] for row in A]
        for r in range(4): Ac[r][c] = rhs[r]
        sol.append(F(det4(Ac), D))
    return tuple(sol)

def fit_total(vals):
    """exact affine fit y = a*i + b*j + c*k + d on ALL points, or None"""
    head = vals[:6]
    for sel in itertools.islice(itertools.combinations(range(len(head)), 4),
                                 15):
        sol = cramer([head[t] for t in sel])
        if sol is None: continue
        a, b, c, d = sol
        if all(F(p[3]) == a*p[0] + b*p[1] + c*p[2] + d for p in vals):
            return sol
    return None

def rank3(pts):
    (i0, j0, k0) = pts[0]
    rows = [[p[0]-i0, p[1]-j0, p[2]-k0] for p in pts[1:]]
    r = 0
    for c in range(3):
        piv = next((t for t in range(len(rows))
                    if rows[t][c] != 0), None)
        if piv is None: continue
        r += 1
        pv = rows[piv][c]
        rows[piv] = [x/pv for x in rows[piv]]
        for t in range(len(rows)):
            if t != piv and rows[t][c] != 0:
                fac = rows[t][c]
                rows[t] = [x - fac*y for x, y in zip(rows[t], rows[piv])]
    return r == 3

names = ['w2','mrg','js1','js2','del1','dbl2','half2','onbA','onbB',
         'cw2','cws','big2','midb','sym3','sand','dupb']
consts = {'e':'','a':'a','b':'b','aa':'aa','ab':'ab','ba':'ba',
          'bb':'bb','aab':'aab'}

G = [(i, j, k) for i in range(1, 5) for j in range(1, 5)
     for k in range(1, 5)]

def libvals(i, j, k):
    w2 = 'a'*i + 'b' + 'a'*j + 'b' + 'a'*k
    mrg = spass(w2, 'b', '')
    js1 = spass(w2, 'ba', 'b')
    d = {'w2': w2, 'mrg': mrg, 'js1': js1,
         'js2': spass(w2, 'ab', 'b'), 'del1': spass(w2, 'ab', ''),
         'dbl2': spass(w2, 'a', 'aa'), 'half2': spass(w2, 'aa', 'a'),
         'onbA': spass(w2, 'aabaa', ''), 'onbB': spass(w2, 'baa', ''),
         'cw2': w2 + w2, 'cws': w2 + js1,
         'big2': mrg + 'b' + mrg, 'midb': 'b' + mrg + 'b',
         'sym3': mrg + 'b' + mrg + 'b' + mrg,
         'sand': mrg + 'b' + w2 + 'b' + mrg,
         'dupb': spass(w2, 'b', 'bab')}
    d.update(consts)
    return d

LIB = {g: libvals(*g) for g in G}
pool = names + list(consts)

nchecked = nviol = nskip = ndead = 0
worst = []
for Fn in names:
    for P in pool:
        if P == 'e': continue
        for R in pool:
            data = {}
            dead = True
            for g in G:
                d = LIB[g]
                out = spass(d[Fn], d[P], d[R])
                if out != d[Fn]: dead = False
                data.setdefault(out.count('b'), []).append((g, out))
            if dead: ndead += 1; continue       # P never fires -> F itself
            for nb, pts in data.items():
                if len(pts) < 12: nskip += 1; continue
                if not rank3([g for (g, o) in pts]):
                    nskip += 1; continue
                sol = fit_total([(g[0], g[1], g[2], o.count('a'))
                                 for (g, o) in pts])
                if sol is None: nskip += 1; continue
                nchecked += 1
                a, b, c, d = sol
                if not (a == b == c):
                    nviol += 1
                    if len(worst) < 6:
                        worst.append(('[%s/%s]%s' % (R, P, Fn), nb,
                                      [str(x) for x in (a, b, c)]))
print('region-stable affine groups checked: %d' % nchecked)
print('T-diagonality violations: %d' % nviol)
for w in worst: print('  VIOLATION:', w)
print('skipped groups (piecewise/thin/unfittable/small): %d' % nskip)
print('dead-pattern identity combos (P never fires): %d' % ndead)

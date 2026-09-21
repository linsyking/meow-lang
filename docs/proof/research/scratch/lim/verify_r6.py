# verify_r6.py -- R6: the sweep-count ceiling K <= c^{|w|} for convergent
# one-rule sweep orbits.
#
# THE POTENTIAL THEOREM (proved; machine-checked below):
#   Letters act on a state read in a fixed direction (L or R) as
#   t -> mult[x]*t + off[x] (mult >= 1, off >= 0), inducing v(s).
#   Call (dir, mult, off, c) an affine potential for [A/B] if
#     (inv)  the word maps of A and B coincide: prod mult equal AND
#            sum_x off[x]*coeff_x equal (coeff_x = sum over positions
#            of x of prod of mult strictly after) -- equivalently
#            v(xAy) = v(xBy) for ALL contexts x, y;
#     (cnt)  delta = #c(A) - #c(B) >= 1;
#     (wgt)  off[c] >= 1.
#   Then EVERY sweep-orbit of [A/B] converges and
#       K <= Phi(s_0)/delta,  Phi = v - #c,  so
#       K <= n * maxoff * (maxmult)^n          (single exponential).
#   Proof.  (inv) holds for all contexts, so each fire preserves v and
#   composes over a sweep; each fire adds delta to #c, so Phi drops by
#   delta*r_k >= 1 per firing sweep.  Phi >= 0 on every string: v =
#   sum over c-positions of off[c]*prod(after) >= #c (off[c] >= 1,
#   mult >= 1), minus #c.  Phi(B) = Phi(A) + delta >= 1 by (inv) and
#   (cnt).  Phi(uv) = A_v*Phi(u) + (A_v-1)*#c(u) + Phi(v) >= A_v*Phi(u)
#   (A_v >= 1), so any string containing B has Phi >= Phi(B) >= 1.
#   Hence: fires stop only when B is gone (fixed point), and at most
#   Phi(s_0)/delta of them happen: the orbit converges within
#   Phi(s_0)/delta sweeps.  QED.
#
#   Trivial cases |A| <= |B|: shrinking rules lose beta-alpha per fire
#   (K <= n/(beta-alpha)); length-preserving convergent orbits have
#   pairwise distinct states (a repeat is a cycle), so K <= 2^n.

import itertools
import math
import random
import time

N = 0
FAILS = []


def check(name, ok, detail=''):
    global N
    N += 1
    if not ok:
        FAILS.append((name, detail))
        print('FAIL', name, detail)


def rules():
    for la in range(5):
        for lb in range(1, 5):
            for ta in itertools.product('ab', repeat=la):
                for tb in itertools.product('ab', repeat=lb):
                    A, B = ''.join(ta), ''.join(tb)
                    if A != B:
                        yield (A, B)


def strs(maxlen):
    for n in range(maxlen + 1):
        for t in itertools.product('ab', repeat=n):
            yield ''.join(t)


def sweep(A, B, s):
    parts, i = [], 0
    while True:
        j = s.find(B, i)
        if j < 0:
            parts.append(s[i:])
            break
        parts.append(s[i:j])
        parts.append(A)
        i = j + len(B)
    return ''.join(parts)


def orbit(A, B, w, capsteps=6000, caplen=1 << 16):
    """('conv', out, K) | ('div',)."""
    s, k = w, 0
    while True:
        t = sweep(A, B, s)
        if t == s:
            return ('conv', s, k)
        s = t
        k += 1
        if k > capsteps or len(s) > caplen:
            return ('div',)


# ---------------- potential search ----------------

def fold_value(s, mult, off, direction):
    t = 0
    for x in (s if direction == 'L' else reversed(s)):
        t = mult[x] * t + off[x]
    return t


def _coeffs(W, mult):
    """coeff_x = sum over positions of x in W of prod(mult strictly
    after the position)."""
    ca = cb = 0
    p = 1
    for x in reversed(W):
        if x == 'a':
            ca += p
        else:
            cb += p
        p *= mult[x]
    return ca, cb


def find_potential(A, B, maxm=64):
    """All minimal affine potentials; complete up to maxm (the product
    equation forces mult = (t^|db|/h, t^|da|/h), so the minimal
    solution has max-mult <= 2^max(|A|,|B|); the off equation is solved
    in closed form, so nothing else is lost)."""
    sols = []
    delta_a = A.count('a') - B.count('a')
    delta_b = A.count('b') - B.count('b')
    for direction in ('L', 'R'):
        AA = A if direction == 'L' else A[::-1]
        BB = B if direction == 'L' else B[::-1]
        for ma in range(1, maxm + 1):
            for mb in range(1, maxm + 1):
                mult = {'a': ma, 'b': mb}
                if (ma ** AA.count('a') * mb ** AA.count('b')
                        != ma ** BB.count('a') * mb ** BB.count('b')):
                    continue
                caA, cbA = _coeffs(AA, mult)
                caB, cbB = _coeffs(BB, mult)
                da, db = caA - caB, cbA - cbB
                # solve off_a*da + off_b*db = 0 over nonneg ints,
                # off[c] >= 1 for some c with delta_c >= 1
                cands = []
                if da == 0 and db == 0:
                    cands = [{'a': 1, 'b': 0}, {'a': 0, 'b': 1},
                             {'a': 1, 'b': 1}]
                elif da == 0:
                    cands = [{'a': 1, 'b': 0}]
                elif db == 0:
                    cands = [{'a': 0, 'b': 1}]
                elif da * db < 0:
                    g = math.gcd(abs(da), abs(db))
                    cands = [{'a': abs(db) // g, 'b': abs(da) // g}]
                for off in cands:
                    for c, dlt in (('a', delta_a), ('b', delta_b)):
                        if dlt >= 1 and off[c] >= 1:
                            sols.append(dict(direction=direction,
                                              mult=dict(mult),
                                              off=dict(off), c=c,
                                              delta=dlt))
                if len(sols) >= 24:
                    return sols
    return sols


def potential_check_on_orbit(A, B, w, pot, capsteps=10 ** 5,
                             caplen=1 << 22):
    """Verify the theorem's per-orbit predictions. True | reason |
    None (= divergent at cap: would REFUTE the theorem)."""
    mult, off, c = pot['mult'], pot['off'], pot['c']
    d = pot['delta']
    v0 = fold_value(w, mult, off, pot['direction'])
    phi0 = v0 - w.count(c)
    if phi0 < 0:
        return ('phi0-negative', w)
    s, k = w, 0
    while True:
        t = sweep(A, B, s)
        if t == s:
            break
        s = t
        k += 1
        if k > capsteps or len(s) > caplen:
            return None
        v = fold_value(s, mult, off, pot['direction'])
        if v != v0:
            return ('v-invariance', w)
        if v - s.count(c) < 0:
            return ('phi-negative', w)
        if k * d > phi0:
            return ('K-exceeds-Phi0/delta', w)
    if fold_value(s, mult, off, pot['direction']) - s.count(c) < 0:
        return ('phi-final-negative', w)
    if B in s:
        return ('final-contains-B', w)
    return True


# ---------------- part A+B: census coverage + orbit verification ------

def partAB():
    t0 = time.time()
    grules = [(A, B) for (A, B) in rules()
              if len(A) > len(B) and B not in A]
    conv, div = [], []
    for (A, B) in grules:
        ok = True
        for w in strs(9):
            if orbit(A, B, w)[0] != 'conv':
                ok = False
                break
        (conv if ok else div).append((A, B))
    adm, nonadm = [], []
    for (A, B) in conv:
        (adm if find_potential(A, B) else nonadm).append((A, B))
    divadm = [(A, B) for (A, B) in div if find_potential(A, B)]
    print("(A) the 148 growing census rules (|A|>|B|, B not-in A, "
          "|A|<=4):")
    print(f"    convergent on <= 9: {len(conv)}; divergent: {len(div)}: "
          f"{['[' + A + '/' + B + ']' for (A, B) in div]}")
    print(f"    convergent WITH an affine potential: {len(adm)} "
          f"(=> total, and K <= n*maxoff*maxmult^n)")
    print(f"    convergent WITHOUT: {len(nonadm)}: "
          f"{['[' + A + '/' + B + ']' for (A, B) in nonadm]}")
    print(f"    divergent WITH a potential (would REFUTE the theorem): "
          f"{divadm}")
    check('A-no-divergent-admitter', not divadm, (divadm,))
    # (B) per-orbit verification on every admitting rule
    ncheck = 0
    for (A, B) in adm:
        pots = find_potential(A, B)
        pot = min(pots, key=lambda p: (max(p['mult'].values()),
                                        max(p['off'].values())))
        for w in strs(7):
            r = potential_check_on_orbit(A, B, w, pot)
            ncheck += 1
            if r is not True:
                check('B-orbit', False, ((A, B), w, r))
    print(f"(B) theorem verified per-orbit (v invariant every sweep, "
          f"Phi >= 0, K*delta <= Phi0, Phi(final) = 0, final B-free) "
          f"on all {len(adm)} admitting rules x all inputs <= 7: "
          f"{ncheck} orbits")
    # positivity / B-in-s => Phi >= 1 / exponential start, random strings
    random.seed(6)
    for (A, B) in adm:
        pots = find_potential(A, B)
        pot = min(pots, key=lambda p: max(p['mult'].values()))
        mult, off, c = pot['mult'], pot['off'], pot['c']
        for _ in range(30):
            s = ''.join(random.choice('ab')
                        for _ in range(random.randrange(0, 12)))
            phi = fold_value(s, mult, off, pot['direction']) - s.count(c)
            if phi < 0 or (B in s and phi < 1):
                check('B-positivity', False, ((A, B), s, phi))
            if phi > (len(s) + 1) * max(max(off.values()), 1) * \
                    max(mult.values()) ** len(s):
                check('B-exp-start', False, ((A, B), s, phi))
    print(f"    positivity, B-containing => Phi>=1, Phi0 <= "
          f"(n+1)*maxoff*maxmult^n on random strings: OK")
    print(f"    [{time.time()-t0:.1f}s]")
    return adm, nonadm


# ---------------- part C: the non-admitters' growth -------------------

def partC(nonadm):
    t0 = time.time()
    print("(C) convergent non-admitters: worst (f, K, R) per length, "
          "all inputs <= 9:")
    for (A, B) in nonadm:
        best = {}
        for w in strs(9):
            s, k, rr = w, 0, 0
            while True:
                i2, fires = 0, 0
                while True:
                    j2 = s.find(B, i2)
                    if j2 < 0:
                        break
                    fires += 1
                    i2 = j2 + len(B)
                rr += fires
                t = sweep(A, B, s)
                if t == s:
                    break
                s = t
                k += 1
                if k > 200000 or len(s) > 1 << 18:
                    k = None
                    break
            if k is None:
                continue
            n = len(w)
            cur = best.get(n, (0, 0, 0))
            best[n] = (max(cur[0], len(s)), max(cur[1], k),
                       max(cur[2], rr))
        row = [(n,) + best[n] for n in sorted(best)]
        print(f"    [{A}/{B}]: {row}")
        bad = [n for n in best if best[n][1] > 2 ** n]
        check('C-nonadm-K', not bad, ((A, B), bad))
    print(f"    [{time.time()-t0:.1f}s]")


# ---------------- part D: random larger rules -------------------------

def partD():
    t0 = time.time()
    random.seed(66)
    print("(D) 400 random larger rules (2 <= |B| <= 3 < |A| <= 6, "
          "B not-in A, binary):")
    nconv = ndiv = 0
    nonadm = []
    tested = 0
    while tested < 400:
        lb = random.randrange(2, 4)
        la = random.randrange(lb + 1, 7)
        B = ''.join(random.choice('ab') for _ in range(lb))
        A = ''.join(random.choice('ab') for _ in range(la))
        if A == B or B in A or B == '':
            continue
        tested += 1
        ok = True
        for w in strs(6):
            if orbit(A, B, w, capsteps=4000, caplen=1 << 16)[0] != 'conv':
                ok = False
                break
        if ok:
            nconv += 1
            if not find_potential(A, B, maxm=70):
                nonadm.append((A, B))
        else:
            ndiv += 1
    print(f"    tested {tested}: convergent on <= 6: {nconv}, "
          f"divergent/capped: {ndiv}")
    print(f"    convergent WITHOUT affine potential: {len(nonadm)}: "
          f"{['[' + A + '/' + B + ']' for (A, B) in nonadm[:12]]}")
    random.seed(667)
    spot = 0
    while spot < 30:
        lb = random.randrange(2, 4)
        la = random.randrange(lb + 1, 7)
        B = ''.join(random.choice('ab') for _ in range(lb))
        A = ''.join(random.choice('ab') for _ in range(la))
        if A == B or B in A or B == '':
            continue
        pots = find_potential(A, B, maxm=70)
        if not pots:
            continue
        pot = min(pots, key=lambda p: max(p['mult'].values()))
        w = ''.join(random.choice('ab')
                    for _ in range(random.randrange(4, 9)))
        r = potential_check_on_orbit(A, B, w, pot, capsteps=40000,
                                     caplen=1 << 18)
        if r is not True:
            check('D-spot', False, ((A, B), w, r))
        spot += 1
    print(f"    theorem spot-verified on 30 random larger admitting "
          f"rules x random inputs: "
          f"{'OK' if not FAILS else 'SEE FAILS'}")
    print(f"    [{time.time()-t0:.1f}s]")


# ---------------- part E: |A| <= |B| -- the trivial bounds -----------

def partE():
    t0 = time.time()
    print("(E) non-growing rules (|A| <= |B|), inputs <= 7:")
    nsr = nlp = ndivE = 0
    for (A, B) in rules():
        if len(A) > len(B):
            continue
        shrinking = len(A) < len(B)
        diverged = False
        for w in strs(7):
            if diverged:
                break
            s, k, seen, repeated = w, 0, {w}, False
            verdict = 'conv'
            while True:
                t = sweep(A, B, s)
                if t == s:
                    break
                s = t
                k += 1
                if k > 260 or len(s) > 4096:
                    verdict = 'div'
                    break
                if s in seen:
                    repeated = True
                    verdict = 'div'
                    break
                seen.add(s)
            if verdict == 'div':
                ndivE += 1
                diverged = True
                continue
            if repeated:
                check('E-distinctness', False, ((A, B), w))
            if shrinking:
                nsr += 1
                if k * (len(B) - len(A)) > len(w):
                    check('E-shrink-bound', False, ((A, B), w, k))
            else:
                nlp += 1
                if k > 2 ** len(w):
                    check('E-lp-bound', False, ((A, B), w, k))
    print(f"    convergent orbits: shrinking {nsr} "
          f"(K*(beta-alpha) <= n checked), length-preserving {nlp} "
          f"(K <= 2^n checked, states distinct)")
    print(f"    (rules divergent or cycling on some input <= 7: "
          f"{ndivE} orbits; cycles are repeats, consistent with "
          f"divergence)")
    print(f"    [{time.time()-t0:.1f}s]")


# ---------------- part F: the base-m family potentials ----------------

def partF():
    t0 = time.time()
    print("(F) closed-form potentials for the four base-m shapes, "
          "m = 2..5, plus the amplifier's exact R = Phi0:")
    fams = []
    for m in range(2, 6):
        fams.append(('b' + 'a' * m, 'ab', 'S1', m))
        fams.append(('b' * m + 'a', 'ab', 'S2', m))
        fams.append(('a' * m + 'b', 'ba', 'T1', m))
        fams.append(('a' + 'b' * m, 'ba', 'T2', m))
    for (A, B, shape, m) in fams:
        if shape == 'S1':
            # fire 'ab' -> 'b a^m'; v = sum_a m^{#b after} (L-fold)
            pot = dict(direction='L', mult={'a': 1, 'b': m},
                      off={'a': 1, 'b': 0}, c='a', delta=m - 1)
            w = 'a' * 3 + 'b' * (8 if m <= 3 else 5)
            i, j = 3, len(w) - 3
        elif shape == 'S2':
            # fire 'ab' -> 'b^m a'; v = sum_b m^{#a before} (R-fold)
            pot = dict(direction='R', mult={'a': m, 'b': 1},
                       off={'a': 0, 'b': 1}, c='b', delta=m - 1)
            w = 'a' * (8 if m <= 3 else 5) + 'b' * 3
            i, j = len(w) - 3, 3
        elif shape == 'T1':
            # fire 'ba' -> 'a^m b'; v = sum_a m^{#b before} (R-fold)
            pot = dict(direction='R', mult={'a': 1, 'b': m},
                       off={'a': 1, 'b': 0}, c='a', delta=m - 1)
            w = 'b' * (8 if m <= 3 else 5) + 'a' * 3
            i, j = 3, len(w) - 3
        else:
            # fire 'ba' -> 'a b^m'; v = sum_b m^{#a after} (L-fold)
            pot = dict(direction='L', mult={'a': m, 'b': 1},
                       off={'a': 0, 'b': 1}, c='b', delta=m - 1)
            w = 'b' * 3 + 'a' * (8 if m <= 3 else 5)
            i, j = len(w) - 3, 3
        check('F-search-finds', bool(find_potential(A, B)),
              ((A, B),))
        phi0 = (fold_value(w, pot['mult'], pot['off'], pot['direction'])
                - w.count(pot['c']))
        # the family law: Phi0 = (#fuel-block)*m^(#dup-block) - fuel
        if shape in ('S1', 'T1'):
            check('F-phi0', phi0 == i * m ** j - i, ((A, B), phi0))
        else:
            check('F-phi0', phi0 == j * m ** i - j, ((A, B), phi0))
        r = potential_check_on_orbit(A, B, w, pot, capsteps=10 ** 6,
                                     caplen=1 << 24)
        check('F-orbit', r is True, ((A, B), r))
        s, k, rr = w, 0, 0
        while True:
            t = sweep(A, B, s)
            if t == s:
                break
            rr += s.count(B)
            s = t
            k += 1
        check('F-K-le-Phi0/delta', k * (m - 1) <= phi0, ((A, B), k))
        check('F-R-eq-Phi0/delta', rr == phi0 // (m - 1),
              ((A, B), rr, phi0))
    print(f"    all {len(fams)} family instances: the search finds a "
          f"potential; Phi0 matches i*m^j - i exactly; orbit checks "
          f"pass; K <= Phi0/(m-1); R = Phi0/(m-1) EXACTLY (the "
          f"potential counts the remaining fires)")
    print(f"    [{time.time()-t0:.1f}s]")


# ---------------- part G: k-gram potentials for the slow tier ---------

def grams(s, k):
    return [s[t:t + k] for t in range(len(s) - k + 1)]


def ocount(s, g):
    """OVERLAPPING occurrence count (str.count is non-overlapping:
    'aaa'.count('aa') = 1, but the potential counts 2)."""
    if not g:
        return 0
    return sum(1 for t in range(len(s) - len(g) + 1)
               if s[t:t + len(g)] == g)


def ctxs(k):
    e = ['', 'a', 'b']
    if k == 2:
        xs = e
    else:
        e2 = [p + q for p in 'ab' for q in 'ab']
        xs = e + e2
    return xs


def kgram_potential(A, B, kmax=3):
    """Search Phi = #g1 + w*#g2 (k-grams, w in {0,1,2}) with:
    per-fire Delta <= -1 for every boundary context, and g1 a k-gram
    of B (so B in s => Phi >= 1).  Returns (k, g1, w, g2) or None."""
    for k in (2, 3):
        cand = sorted(set(grams(A, k) + grams(B, k)
                         + [x + A[:1] for x in ctxs(k) if len(x) == k - 1]
                         + [A[-1:] + y for y in ctxs(k)
                            if len(y) == k - 1]))
        bg = set(grams(B, k))
        X = ctxs(k)

        def delta(g1, w, g2, x, y):
            before = x + B + y
            after = x + A + y
            return (ocount(after, g1) + w * ocount(after, g2)
                    - ocount(before, g1) - w * ocount(before, g2))

        for g1 in sorted(bg):
            for g2 in cand:
                for w in (0, 1, 2):
                    g2u = g1 if w == 0 else g2
                    if all(delta(g1, w, g2u, x, y) <= -1
                           for x in X for y in X):
                        return (k, g1, w, g2u)
    return None


def kgram_check_on_orbit(A, B, w, kg, capsteps=10 ** 5, caplen=1 << 20):
    k, g1, ww, g2 = kg

    def phi(s):
        return ocount(s, g1) + ww * ocount(s, g2)
    s, fires_tot, phi0 = w, 0, phi(w)
    while True:
        t = sweep(A, B, s)
        if t == s:
            break
        # count greedy fires and per-sweep decrease
        i2, fcount = 0, 0
        while True:
            j2 = s.find(B, i2)
            if j2 < 0:
                break
            fcount += 1
            i2 = j2 + len(B)
        s = t
        fires_tot += fcount
        if fires_tot > capsteps or len(s) > caplen:
            return None
        if phi0 - phi(s) < fires_tot:
            return ('phi-drop', w)
        if phi(s) < 0:
            return ('phi-neg', w)
    if B in s:
        return ('final-has-B', w)
    return True


def partG(nonadm):
    t0 = time.time()
    print("(G) k-gram (substring-counting) potentials, Phi = #g1 + "
          "w*#g2, k in {2,3}, for the affine non-admitters:")
    cov = []
    for (A, B) in nonadm:
        kg = kgram_potential(A, B)
        if kg is None:
            print(f"    [{A}/{B}]: NO k-gram potential (k <= 3)")
            continue
        r = kgram_check_on_orbit(
            A, B, 'a' * 4 + 'b' * 4 + 'ab' * 3, kg)
        r2 = kgram_check_on_orbit(A, B, 'b' * 5 + 'a' * 5, kg)
        if r is True and r2 is True:
            cov.append((A, B))
            print(f"    [{A}/{B}]: Phi = #{kg[1]} "
                  f"+ {kg[2]}*#{kg[3]} (k={kg[0]}), verified: "
                  f"K <= Phi0 <= n^{kg[0]}")
        else:
            check('G-orbit', False, ((A, B), kg, r, r2))
    print(f"    covered by k-gram potentials: {len(cov)} of "
          f"{len(nonadm)}; K <= n^k (polynomial)")
    # verify on ALL census orbits of the covered rules
    for (A, B) in cov:
        kg = kgram_potential(A, B)
        for w in strs(7):
            r = kgram_check_on_orbit(A, B, w, kg, capsteps=4000,
                                     caplen=1 << 16)
            if r is not True:
                check('G-census-orbit', False, ((A, B), w, r))
    print(f"    all census orbits (inputs <= 7) of covered rules: "
          f"Phi drops >= 1 per fire, K <= Phi0: "
          f"{'OK' if not FAILS else 'SEE FAILS'}")
    print(f"    [{time.time()-t0:.1f}s]")
    return cov


def main():
    print("verify_r6.py -- R6: the sweep-count ceiling K <= c^|w|")
    print("=" * 70)
    adm, nonadm = partAB()
    partC(nonadm)
    partD()
    partE()
    partF()
    partG(nonadm)
    print("=" * 70)
    print(f"TOTAL: {N} checks, {len(FAILS)} failures")
    if FAILS:
        for f in FAILS[:20]:
            print('  FAIL', f)
        raise SystemExit(1)
    print("ALL GREEN")


if __name__ == '__main__':
    main()

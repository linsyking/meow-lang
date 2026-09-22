"""ROUND 12 spot-checks: the alphabet-scope theorem and its witnesses.

Part 1 -- the LAUNDERING identity (Theorem 12.2).  For each letter
    sigma, L_sigma = [sigma/sigmasigma][sigmasigma/sigma] (doubling then
    halving, rightmost applies first) is the IDENTITY on every text and
    kills every sigma-label; composing over the whole alphabet kills
    every label.  Checked: for random small E and random w over {a,b},
    content(L_a L_b E, w) == content(E, w) and labels(L_a L_b E, w)
    == ().

Part 2 -- the DEAD-PROV rev witnesses over the fixed alphabet {a,b}
    (Corollary 12.2b): rev computed on infinite families with prov ==
    () on every member:
      W1 = {b a^j}      E1  = C( La.[eps/b]X , b )
      W2 = {a^i b}      E2  = C( b , La.[eps/b]X )
      W3 = {(ab)^k}     E3  = [ba/ab]                (single pass!)
      W4(i) = {a^i b a^j : j >= 0} for FIXED i in {1,2,3}:
            E4  = C( La.[eps/a^i b]X , b , a^i )     (constant left run)
      and symmetrically W5(j) = {a^i b a^j : i >= 0} for fixed j;
      W6 = the REDUCTION construction of 12.3 with E_L = K(a^i):
            E6  = C( La.[eps/(E_L b)]X , b , La.E_L )  (laundered E_L).
    (W4/W5 show the two-sided one-b family is rev-computable with dead
    prov whenever ONE side is fixed; only when both i and j vary does
    the split problem remain.)

Part 3 -- the crux of the DB-forcing lemma (12.1): an output atom
    carrying a letter OUTSIDE the expression's constant alphabet is
    never a constant.  Checked: random E over constants {a,b}, random
    w over {c,d}: no output atom with char in {c,d} is unlabeled.  The
    lemma's implication itself -- rev-correct + distinct chars avoiding
    Gamma(E) forces prov = DB -- DOES fire on this domain, but only
    trivially: the rev-correct outputs that arise are on palindromes
    (rev = identity there, prov increasing, distinctness failing --
    the lemma's exact hypothesis) and on |w| <= 1 (where DB = (0,) =
    the identity prov, the lemma's conclusion).  Both behaviors are
    counted and reported.

Each part runs in well under 60 s.
Usage: /usr/bin/python3 -W ignore verify_round12.py [1|2|3|all]
"""
import itertools
import random
import sys

import prov as PV
from lcore import K, V, C, S


def lab(w):
    return PV.lab_input(w)


def L(expr, s):
    """L_s = [s/ss].[ss/s]  (doubling applies first)."""
    return S(K(s), K(s + s), S(K(s + s), K(s), expr))


def rand_expr(rng):
    """A random small expression; V(0) is the input."""
    kind = rng.randrange(6)
    if kind == 0:
        return S(K(''), K('ab'), V(0))
    if kind == 1:
        return S(V(0), K('b'), V(0))
    if kind == 2:
        return C(C(K('a'), V(0)), C(K('b'), V(0)))
    if kind == 3:
        return S(C(V(0), K('b')), K('b'), C(K('a'), V(0)))
    if kind == 4:
        return C(V(0), V(0))
    return S(K('bb'), K('b'), C(K('ab'), V(0)))


def part1():
    rng = random.Random(12)
    ok = bad = 0
    for _ in range(440000):
        n = rng.randint(1, 12)
        w = ''.join(rng.choice('ab') for _ in range(n))
        E = rand_expr(rng)
        try:
            vE = PV.lden(E, (lab(w),))
        except PV.Undefined:
            continue
        LE = L(L(E, 'a'), 'b')
        vL = PV.lden(LE, (lab(w),))
        if PV.content(vL) == PV.content(vE) and PV.labels(vL) == ():
            ok += 1
        else:
            bad += 1
            if bad <= 5:
                print('   FAIL:', w, PV.content(vE), PV.content(vL),
                      PV.labels(vL))
    print('PART 1 (laundering identity + dead prov): %d ok, %d bad' %
          (ok, bad))
    print('  verdict:', 'VERIFIED' if bad == 0 else 'REFUTED')
    return bad == 0


def part2():
    bad = []
    # W1: rev on {b a^j}
    e1 = C(L(S(K(''), K('b'), V(0)), 'a'), K('b'))
    for j in range(0, 11):
        w = 'b' + 'a' * j
        v = PV.lden(e1, (lab(w),))
        if PV.content(v) != 'a' * j + 'b' or PV.labels(v) != ():
            bad.append(('W1', w, PV.content(v), PV.labels(v)))
    # W2: rev on {a^i b}
    e2 = C(K('b'), L(S(K(''), K('b'), V(0)), 'a'))
    for i in range(0, 11):
        w = 'a' * i + 'b'
        v = PV.lden(e2, (lab(w),))
        if PV.content(v) != 'b' + 'a' * i or PV.labels(v) != ():
            bad.append(('W2', w, PV.content(v), PV.labels(v)))
    # W3: rev on {(ab)^k} -- single pass, all-constant replacement
    e3 = S(K('ba'), K('ab'), V(0))
    for k in range(1, 9):
        w = 'ab' * k
        v = PV.lden(e3, (lab(w),))
        if PV.content(v) != 'ba' * k or PV.labels(v) != ():
            bad.append(('W3', w, PV.content(v), PV.labels(v)))
    # W4: rev on {a^i b a^j : j >= 0} for FIXED i (constant left run)
    for i in (1, 2, 3):
        ei = C(C(L(S(K(''), K('a' * i + 'b'), V(0)), 'a'), K('b')),
               K('a' * i))
        for j in range(0, 9):
            w = 'a' * i + 'b' + 'a' * j
            v = PV.lden(ei, (lab(w),))
            if (PV.content(v) != 'a' * j + 'b' + 'a' * i
                    or PV.labels(v) != ()):
                bad.append(('W4', w, PV.content(v), PV.labels(v)))
    # W5: rev on {a^i b a^j : i >= 0} for FIXED j (constant right run)
    for j in (1, 2, 3):
        ej = C(C(K('a' * j), K('b')),
               L(S(K(''), K('b' + 'a' * j), V(0)), 'a'))
        for i in range(0, 9):
            w = 'a' * i + 'b' + 'a' * j
            v = PV.lden(ej, (lab(w),))
            if (PV.content(v) != 'a' * j + 'b' + 'a' * i
                    or PV.labels(v) != ()):
                bad.append(('W5', w, PV.content(v), PV.labels(v)))
    # W6: the REDUCTION construction of 12.3 with E_L = K(a^i) (the
    #     fixed-i left-run): E = C( La.[eps/(E_L b)]X , b , La.E_L )
    for i in (1, 2, 3):
        EL = K('a' * i)
        e6 = C(C(L(S(K(''), K('a' * i + 'b'), V(0)), 'a'), K('b')),
               L(EL, 'a'))
        for j in range(0, 9):
            w = 'a' * i + 'b' + 'a' * j
            v = PV.lden(e6, (lab(w),))
            if (PV.content(v) != 'a' * j + 'b' + 'a' * i
                    or PV.labels(v) != ()):
                bad.append(('W6', w, PV.content(v), PV.labels(v)))
    print('PART 2 (dead-prov rev witnesses): W1 11 inputs, W2 11, W3 8,'
          ' W4 3x9, W5 3x9, W6 3x9; failures: %d' % len(bad))
    for b in bad[:8]:
        print('   ', b)
    print('  verdict:', 'VERIFIED' if not bad else 'REFUTED')
    return not bad


def part3():
    rng = random.Random(121)
    checked = bad = 0
    fired = fired_distinct = fired_db = fired_n1 = 0
    examples = []
    for _ in range(200000):
        n = rng.randint(1, 8)
        w = ''.join(rng.choice('cd') for _ in range(n))
        E = rand_expr(rng)          # constants only from {a,b}
        try:
            v = PV.lden(E, (lab(w),))
        except PV.Undefined:
            continue
        for (c, l) in v:
            checked += 1
            if c in 'cd' and l is None:
                bad += 1
                if bad <= 5:
                    print('   FAIL: unlabeled non-Gamma atom', c, 'w=', w)
        # the antecedent of the forcing lemma (content = rev(w)):
        if PV.content(v) == w[::-1]:
            fired += 1
            distinct = len(set(w)) == n
            if distinct:
                fired_distinct += 1
                if n == 1:
                    fired_n1 += 1
                if PV.labels(v) == tuple(range(n - 1, -1, -1)):
                    fired_db += 1
                else:
                    bad += 1
                    print('   FAIL: rev-correct on distinct', w,
                          'but prov =', PV.labels(v))
            elif len(examples) < 3:
                examples.append((w, PV.labels(v)))
    print('PART 3 (forcing crux: chars outside Gamma(E) are never '
          'constants): %d output atoms checked, %d violations' %
          (checked, bad))
    print('  rev-correct outputs on the c/d domain: %d fired; %d with'
          ' pairwise-distinct w (%d of them single letters, n = 1),'
          ' and ALL %d had prov = DB -- the lemma\'s conclusion held'
          ' every time its hypothesis did' % (fired, fired_distinct,
          fired_n1, fired_db))
    print('  the non-distinct firings are palindromes (rev = a'
          ' rearrangement the identity already achieves), e.g.:')
    for (w, p) in examples:
        print('    w=%s prov=%s  (increasing, not DB -- distinctness'
              ' is exactly the hypothesis that fails)' % (w, p))
    print('  verdict:', 'VERIFIED' if bad == 0 else 'REFUTED')
    return bad == 0


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', '1'):
        ok &= part1()
    if which in ('all', '2'):
        ok &= part2()
    if which in ('all', '3'):
        ok &= part3()
    print('ROUND 12 spot-checks:', 'ALL VERIFIED' if ok else 'REFUTED')

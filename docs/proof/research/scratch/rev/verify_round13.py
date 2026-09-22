"""ROUND 13 spot-checks: the one-b run-vector calculus (REPORT sec 13).

Setting: Sigma = {a,b}, one-b texts a^x b a^y (run vector (x, y)), the
input family F = {a^i b a^j : i, j >= 1}, target: rev on F = the
exchange (i, j) -> (j, i) -- SETTLED this round by the CONSTRUCTION
(part C: E_swap = [b/w]bigsym computes rev on the FULL one-b
language {a^* b a^*}).

Part A -- LEMMA MATCH ANCHORING and the one-b pass calculus, checked at
    the string level on random one-b and multi-b texts and random
    pattern/replacement values:
    A1  a pattern value with >= 2 b's never matches in a one-b text;
    A2  a pattern value with exactly one b matches only at the text's
        unique b (its leading a's are the last p0 of the left run, its
        trailing a's the first p1 of the right run);
    A3  a b-free pattern with a b-free replacement maps a one-b text
        (x, y) to (psi(x), psi(y)) for ONE common eventually-affine
        psi (the same chunk map applied to each run independently,
        tiled from the run's left end, leftover at the right end);
    A4  a one-b pattern (p0, p1) with a one-b replacement (r0, r1),
        when it fires, maps (x, y) -> (x - p0 + r0, y - p1 + r1);
    A5  on multi-b texts, every match of an m-b pattern (m >= 2)
        spans m CONSECUTIVE text b's and consumes the interior runs
        EXACTLY.

Part B -- the construction catalogue of 13.3/13.4 (lcore/prov.py, the
    same expression checked at every (i, j) of a grid):
    merge a^{i+j}; doubling; halving (ceiling); constant shrinking of
    either run; merge minus one; the big symmetric value (i+j, i+j);
    the lock-deletion instance [e/(i, j-1)]X = a; the halved merge;
    the PIECEWISE DIFFERENCE [e/merge][aa/a]X = (i-j, 2j) / (2i, j-i)
    / b at i = j; the flank-swap mechanism (IF a (j, M, i) text with
    M > j is ever constructible, [e/(a^M b)] swaps in one pass) and the
    lock-deletion mechanism [e/(a^i b a^y)]X = a^{j-y}.

Part C -- THE CONSTRUCTION (13.4), in prov.py/lcore on the input:
    C1  E_swap = [b/w] bigsym with bigsym = C([e/b]w, b, [e/b]w)
        computes rev on the FULL one-b language {a^i b a^j : i,j >= 0}
        (grid + random (i,j) up to 250) -- the swap (i,j)->(j,i).
    C2  the discovery stepping stone [b/(ba)][ba/w]bigsym (replacement
        'ba' then shaving the +1) -- same domain.
    C3  prov structure: every a-atom survives, the original b-atom
        dies (the output's b is a constant); prov(E_swap,w) = the
        ascending labels 0..n-1 minus {i}.
    C4  the laundered variant L_a . L_b . E_swap (round-12 laundering
        composed with the construction): rev on the one-b language
        with prov = () everywhere over Sigma = {a,b}.
    C5  E_swap . E_swap = id (involution, as rev is).
    C6  the two-b lift fails concretely: [b/w2]big2 (the direct
        symmetrization lift, w2 = a^i b a^j b a^k, big2 =
        C([e/b]w2, b, [e/b]w2)) never fires (2-b pattern vs one-b
        text) and returns big2 unchanged; [e/w2](w2 . b) = b
        (collapse-back: deleting w from C(w, Z) returns Z).

The depth-<=2 falsification sweeps (the split search over the
    enriched one-b library, and the two-b frontier) live in
    round13_sweep.c / round13_sweep.log; this file reports A, B, C.

Each part runs in well under 60 s.
Usage: /usr/bin/python3 -W ignore verify_round13.py [A|B|C|all]
"""
import random
import sys

import prov as PV
from lcore import K, V, C, S


# ---------- string-level pass (same greedy semantics as prov.py) ----------
def spass(t, pat, repl):
    """repl: string (may be ''). Returns the output text."""
    i, out = 0, []
    while i < len(t):
        if t.startswith(pat, i):
            out.append(repl)
            i += len(pat)
        else:
            out.append(t[i])
            i += 1
    return ''.join(out)


def runs_of(t):
    """run vector of a text: (x_0, ..., x_k) with k = #b's."""
    v = t.split('b')
    return tuple(len(s) for s in v), t.count('b')


def partA():
    rng = random.Random(1313)
    # random pattern values: random run vectors over small lengths
    def rvec(nb, hi=4):
        return tuple(rng.randint(0, hi) for _ in range(nb + 1))
    def unvec(v):
        return 'b'.join('a' * x for x in v)
    f1 = f2 = f3 = f4 = f5 = 0
    bad = []
    for _ in range(40000):
        x, y = rng.randint(0, 9), rng.randint(0, 9)
        t = 'a' * x + 'b' + 'a' * y                      # one-b text
        pv = rvec(rng.randint(0, 2))
        rv = rvec(rng.randint(0, 2))
        pat, rep = unvec(pv), unvec(rv)
        if pat == '':            # the empty pattern is undefined in L
            continue
        out = spass(t, pat, rep)
        # A1: >=2 b's in the pattern -> no match (output unchanged)
        if pat.count('b') >= 2:
            f1 += 1
            if out != t:
                bad.append(('A1', t, pat, rep, out))
        # A2: exactly one b -> any match is at the text's b
        if pat.count('b') == 1:
            f2 += 1
            i = t.find(pat)
            while i != -1:
                if 'b' not in t[i:i + len(pat)] or t[i:i+len(pat)].count('b') != 1:
                    bad.append(('A2', t, pat, i))
                i = t.find(pat, i + 1)
        # A3: b-free pattern & b-free replacement: common run map
        if pat.count('b') == 0 and rep.count('b') == 0 and pat:
            f3 += 1
            (ox, oy) = runs_of(out)[0]
            # exact check: recompute per-run independently
            lx = len(spass('a' * x, pat, rep))
            ly = len(spass('a' * y, pat, rep))
            if (ox, oy) != (lx, ly) or runs_of(out)[1] != 1:
                bad.append(('A3', t, pat, rep, out))
        # A4: one-b pattern & one-b replacement: remnant algebra
        if pat.count('b') == 1 and rep.count('b') == 1 and pat:
            f4 += 1
            if x >= pv[0] and y >= pv[1]:
                exp = 'a' * (x - pv[0] + rv[0]) + 'b' + 'a' * (rv[1] + y - pv[1])
                if out != exp:
                    bad.append(('A4', t, pat, rep, out, exp))
        # A5: multi-b texts: exact interior, consecutive b's
        if pat.count('b') >= 2:
            nb = rng.randint(2, 4)
            tv = rvec(nb, 6)
            T = unvec(tv)
            i = T.find(pat)
            while i != -1:
                w = T[i:i + len(pat)]
                bs = [k for k in range(len(w)) if w[k] == 'b']
                # interior runs of the match equal the pattern's interior
                wp = w.split('b')
                pp = pat.split('b')
                if wp[1:-1] != pp[1:-1]:
                    bad.append(('A5', T, pat, i, w))
                # b's inside the match are consecutive in T
                tbs = [k for k in range(len(T)) if T[k] == 'b']
                idxs = {k for k in tbs if i <= k < i + len(w)}
                if len(idxs) != pat.count('b'):
                    bad.append(('A5b', T, pat, i))
                i = T.find(pat, i + 1)
            f5 += 1
    print('PART A (match anchoring + one-b calculus): '
          'A1 %d, A2 %d, A3 %d, A4 %d, A5 %d cases' % (f1, f2, f3, f4, f5))
    for b in bad[:8]:
        print('   ', b)
    print('  verdict:', 'VERIFIED' if not bad else 'REFUTED')
    return not bad


def partB():
    lab = PV.lab_input
    X = V(0)
    merge = S(K(''), K('b'), X)
    dbl = S(K('aa'), K('a'), X)
    half = S(K('a'), K('aa'), X)
    shrinkR = S(K('b'), C(K('b'), K('a')), X)
    shrinkL = S(K('b'), C(K('a'), K('b')), X)
    diff = S(K(''), merge, dbl)
    mergeM1 = S(K(''), C(K('b'), K('a')), X)
    bigsym = C(C(merge, K('b')), merge)
    lockdel = S(K(''), shrinkR, X)
    halfmrg = S(K('a'), K('aa'), merge)

    def val(e, w):
        return PV.content(PV.lden(e, (lab(w),)))

    ok = True

    def chk(name, cond):
        nonlocal ok
        ok &= bool(cond)
        if not cond:
            print('   FAIL', name)

    for i in range(1, 9):
        for j in range(1, 9):
            w = 'a' * i + 'b' + 'a' * j
            chk('merge', val(merge, w) == 'a' * (i + j))
            chk('dbl', val(dbl, w) == 'a' * (2 * i) + 'b' + 'a' * (2 * j))
            chk('half', val(half, w) ==
                'a' * ((i + 1) // 2) + 'b' + 'a' * ((j + 1) // 2))
            chk('shrinkR', val(shrinkR, w) == 'a' * i + 'b' + 'a' * (j - 1))
            chk('shrinkL', val(shrinkL, w) == 'a' * (i - 1) + 'b' + 'a' * j)
            chk('mergeM1', val(mergeM1, w) == 'a' * (i + j - 1))
            chk('bigsym', val(bigsym, w) ==
                'a' * (i + j) + 'b' + 'a' * (i + j))
            chk('lockdel', val(lockdel, w) == 'a')
            chk('halfmrg', val(halfmrg, w) == 'a' * ((i + j + 1) // 2))
            c = val(diff, w)
            if i > j:
                chk('diff>', c == 'a' * (i - j) + 'b' + 'a' * (2 * j))
            elif i == j:
                chk('diff=', c == 'b')
            else:
                chk('diff<', c == 'a' * (2 * i) + 'b' + 'a' * (j - i))
    print('B1 primitive catalogue on the 8x8 grid:',
          'VERIFIED' if ok else 'REFUTED')

    ok2 = True
    for i in range(1, 8):
        for j in range(1, 8):
            for M in (i + j, 2 * (i + j), i + 2 * j):
                if M <= j:
                    continue
                T = C(C(K('a' * j), K('b')),
                       C(C(K('a' * M), K('b')), K('a' * i)))
                E = S(K(''), C(K('a' * M), K('b')), T)
                ok2 &= val(E, 'a' * i + 'b' + 'a' * j) == \
                    'a' * j + 'b' + 'a' * i
    print('B2 flank-swap mechanism ([e/(a^M b)] on a (j, M, i) text,'
          ' M > j):', 'VERIFIED' if ok2 else 'REFUTED')

    ok3 = True
    for i in range(1, 8):
        for j in range(1, 8):
            for y in range(0, j):
                Vv = C(C(K('a' * i), K('b')), K('a' * y))
                E = S(K(''), Vv, X)
                ok3 &= val(E, 'a' * i + 'b' + 'a' * j) == 'a' * (j - y)
    print('B3 lock-deletion mechanism ([e/(a^i b a^y)]X = a^{j-y}):',
          'VERIFIED' if ok3 else 'REFUTED')
    return ok and ok2 and ok3


def partC():
    lab = PV.lab_input
    X = V(0)

    def L(expr, s):
        """L_s = [s/ss][ss/s], the round-12 laundering chain."""
        return S(K(s), K(s + s), S(K(s + s), K(s), expr))

    merge = S(K(''), K('b'), X)
    bigsym = C(C(merge, K('b')), merge)
    Eswap = S(K('b'), X, bigsym)                    # [b/w]bigsym
    Eshave = S(K('b'), K('ba'), S(K('ba'), X, bigsym))  # stepping stone
    Elaun = L(L(Eswap, 'a'), 'b')                    # L_a . L_b . Eswap
    # Eswap . Eswap: substitute Eswap for the input inside Eswap
    merge2 = S(K(''), K('b'), Eswap)
    bigsym2 = C(C(merge2, K('b')), merge2)
    Esq = S(K('b'), Eswap, bigsym2)
    # two-b lift
    mrg2 = S(K(''), K('b'), X)
    big2 = C(C(mrg2, K('b')), mrg2)
    lift = S(K('b'), X, big2)                        # [b/w2]big2
    collapse = S(K(''), X, C(X, K('b')))            # [e/w2](w2 . b)

    def val(e, w):
        return PV.content(PV.lden(e, (lab(w),)))

    def prv(e, w):
        return PV.labels(PV.lden(e, (lab(w),)))

    ok = True

    def chk(name, cond):
        nonlocal ok
        ok &= bool(cond)
        if not cond:
            print('   FAIL', name)

    # C1/C2: rev on the FULL one-b language (boundaries included)
    for i in range(0, 14):
        for j in range(0, 14):
            w = 'a' * i + 'b' + 'a' * j
            chk('C1', val(Eswap, w) == 'a' * j + 'b' + 'a' * i)
            chk('C2', val(Eshave, w) == 'a' * j + 'b' + 'a' * i)
    rng = random.Random(13)
    for _ in range(1000):
        i, j = rng.randint(0, 250), rng.randint(0, 250)
        w = 'a' * i + 'b' + 'a' * j
        chk('C1r', val(Eswap, w) == 'a' * j + 'b' + 'a' * i)
        chk('C2r', val(Eshave, w) == 'a' * j + 'b' + 'a' * i)
    print('C1/C2 E_swap computes rev on the full one-b language'
          ' {a^* b a^*}:', 'VERIFIED' if ok else 'REFUTED')

    # C3: prov structure (i,j >= 1 here; label i is the b)
    okp = True
    for i in range(1, 9):
        for j in range(1, 9):
            w = 'a' * i + 'b' + 'a' * j
            expect = tuple(t for t in range(i + j + 1) if t != i)
            if prv(Eswap, w) != expect:
                okp = False
                print('   FAIL C3', i, j, prv(Eswap, w), expect)
    print('C3 prov(E_swap,w) = ascending labels minus the b:',
          'VERIFIED' if okp else 'REFUTED')
    ok &= okp

    # C4: laundered variant -- rev with dead prov over Sigma={a,b}
    okl = True
    for i in range(0, 9):
        for j in range(0, 9):
            w = 'a' * i + 'b' + 'a' * j
            if val(Elaun, w) != 'a' * j + 'b' + 'a' * i or prv(Elaun, w) != ():
                okl = False
                print('   FAIL C4', i, j)
    for _ in range(300):
        i, j = rng.randint(0, 120), rng.randint(0, 120)
        w = 'a' * i + 'b' + 'a' * j
        if val(Elaun, w) != 'a' * j + 'b' + 'a' * i or prv(Elaun, w) != ():
            okl = False
            print('   FAIL C4r', i, j)
    print('C4 L_a.L_b.E_swap: rev with prov = ():',
          'VERIFIED' if okl else 'REFUTED')
    ok &= okl

    # C5: involution
    oki = True
    for i in range(0, 10):
        for j in range(0, 10):
            w = 'a' * i + 'b' + 'a' * j
            if val(Esq, w) != w:
                oki = False
                print('   FAIL C5', i, j, val(Esq, w))
    print('C5 E_swap . E_swap = id (involution):',
          'VERIFIED' if oki else 'REFUTED')
    ok &= oki

    # C6: the two-b lift fails concretely
    okf = True
    for i in range(1, 7):
        for j in range(1, 7):
            for k in range(1, 7):
                w2 = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
                big2v = 'a' * (i + j + k) + 'b' + 'a' * (i + j + k)
                if val(lift, w2) != big2v:       # 2-b pattern never fires
                    okf = False
                    print('   FAIL C6a', i, j, k, val(lift, w2))
                if val(lift, w2) == 'a' * k + 'b' + 'a' * j + 'b' + 'a' * i:
                    okf = False
                    print('   FAIL C6a-rev', i, j, k)
                if val(collapse, w2) != 'b':     # collapse-back
                    okf = False
                    print('   FAIL C6b', i, j, k, val(collapse, w2))
    print('C6 two-b lift dead ([b/w2]big2 never fires;'
          ' [e/w2](w2.b) = b):', 'VERIFIED' if okf else 'REFUTED')
    return ok & okp & okl & oki & okf


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', 'A'):
        ok &= partA()
    if which in ('all', 'B'):
        ok &= partB()
    if which in ('all', 'C'):
        ok &= partC()
    print('ROUND 13 spot-checks:', 'ALL VERIFIED' if ok else 'REFUTED')

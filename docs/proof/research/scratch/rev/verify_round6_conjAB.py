"""ROUND 6 (part 2) - the alternating-staircase family vs Conjectures A/B.

BACKGROUND.  The B2 triple hunt refuted the Left-Move Wall as stated (a
3-chain through pairwise-disjoint residuals exists at larger sizes).  The
mechanism behind it -- an ODD-length alternating needle B driven by the
greedy scan over an alternating text -- generalizes: with copies of w
inserted at sigma-sites and B = init^d(w), the emitted (surviving) atoms
sit at offsets  -(d-1)c mod (copy unit)  -- a MODULAR STAIRCASE.  Its
longest strictly decreasing run grows linearly in |w|:

  * sigma='b',  w = b(ab)^j      : mult = 2 (structural), LDS ~ n/2
        ==> LDS/mult -> infinity  ==> CONJECTURE A FALSE.
  * sigma='ba', w = b(ab)^j, d=4, n = 2j+1 == 1 mod 3 : mult = 1,
    LDS ~ n/6    ==> CONJECTURE B FALSE at mult 1.

Every number below is produced by the REAL provenance evaluator on the
REAL AST (init^d built by leaf-substitution composition of the verified
anchored init construction), and the CONTENT is cross-checked against
lcore's independent denotation.

Usage:  /usr/bin/python3 -W ignore verify_round6_conjAB.py
"""
import sys

import prov as PV
import lcore as L
from lcore import K, V
import r2lib as RL


# ----------------------------------------------------------- AST utilities

def sub_tree(e, repl):
    """Replace every ('V', 0) leaf of e by the AST `repl` (composition of
    single-variable expressions)."""
    if e == ('V', 0):
        return repl
    if isinstance(e, tuple):
        if e[0] == 'V':
            return e          # other variables (none used here)
        if e[0] == 'K':
            return e
        if e[0] == 'C':
            return ('C', sub_tree(e[1], repl), sub_tree(e[2], repl))
        if e[0] == 'S':
            return ('S', sub_tree(e[1], repl),
                    sub_tree(e[2], repl), sub_tree(e[3], repl))
        raise ValueError(e)
    return e


def initd(d):
    """AST for lambda x. init^d(x) via leaf composition."""
    e = V(0)
    for _ in range(d):
        e = sub_tree(RL.init_expr(), e)
    return e


# ----------------------------------------------------------- pipeline

def make_E(d, sigma):
    """E = [eps/init^d(X)] . [X/sigma]   (outer pass applied second)."""
    P = initd(d)
    inner = ('S', V(0), K(sigma), V(0))          # [X/sigma] X
    return ('S', K(''), P, inner)                # [eps/P] (inner)


def measure(E, w):
    lab = PV.lab_input(w)
    atoms = PV.lden(E, (lab,))
    prov = PV.labels(atoms)
    content = PV.content(atoms)
    # independent content check with the real denotation
    real = L.den(E, (w,))
    ok = (content == real)
    return dict(prov=prov, lds=PV.lds(prov), mult=PV.mult(prov),
                content=content, real_ok=ok)


# ----------------------------------------------------------- main

def main():
    print('SANITY: init^d correctness + full-pipeline content check')
    bad = 0
    for j in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12):
        w = 'b' + 'ab' * j
        for d in (1, 2, 3, 4, 5, 6):
            if len(w) <= d:
                continue
            lab = PV.lab_input(w)
            atoms = PV.lden(initd(d), (lab,))
            if PV.content(atoms) != w[:-d] or \
                    PV.labels(atoms) != list(range(len(w) - d)):
                print(f'  INIT BAD: w={w} d={d}')
                bad += 1
    print(f'  init^d: {"ALL OK" if bad == 0 else str(bad) + " FAILURES"}')

    print()
    print('FAMILY 1: E_d = [eps/init^d X].[X/b]X  on w = b(ab)^j')
    print('   j  n  d  mult  LDS   LDS/mult   content==den')
    for j in range(2, 13):
        w = 'b' + 'ab' * j
        n = len(w)
        for d in (2, 3, 4, 5, 6):
            if n <= d + 1:
                continue
            E = make_E(d, 'b')
            r = measure(E, w)
            if r['lds'] >= 3 or r['mult'] == 1:
                print(f'  {j:2d} {n:2d} {d:2d}  {r["mult"]:4d} '
                      f'{r["lds"]:4d}  {r["lds"]/max(1,r["mult"]):7.2f}   '
                      f'{r["real_ok"]}')

    print()
    print('FAMILY 2: E_d = [eps/init^d X].[X/ba]X  on w = b(ab)^j')
    print('   j  n  d  mult  LDS   LDS/mult   content==den')
    for j in range(2, 13):
        w = 'b' + 'ab' * j
        n = len(w)
        for d in (2, 3, 4, 5, 6):
            if n <= d + 1:
                continue
            E = make_E(d, 'ba')
            r = measure(E, w)
            if r['lds'] >= 3 or r['mult'] == 1:
                print(f'  {j:2d} {n:2d} {d:2d}  {r["mult"]:4d} '
                      f'{r["lds"]:4d}  {r["lds"]/max(1,r["mult"]):7.2f}   '
                      f'{r["real_ok"]}')

    print()
    print('WITNESS EXTENSION (mult-1 rows pushed to larger j, d=4, sigma=ba):')
    js = [3, 6, 9, 12, 15, 18, 21, 24, 27, 30]
    E = make_E(4, 'ba')
    for j in js:
        w = 'b' + 'ab' * j
        n = len(w)
        r = measure(E, w)
        print(f'  j={j:2d} n={n:2d} (n mod 3 = {n % 3}): mult={r["mult"]} '
              f'LDS={r["lds"]} ratio={r["lds"]/max(1,r["mult"]):.2f} '
              f'den_ok={r["real_ok"]}')

    print()
    print('WITNESS EXTENSION (family 1, d=4, sigma=b, mult-2 rows):')
    E = make_E(4, 'b')
    for j in (2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 24):
        w = 'b' + 'ab' * j
        n = len(w)
        r = measure(E, w)
        print(f'  j={j:2d} n={n:2d}: mult={r["mult"]} LDS={r["lds"]} '
              f'ratio={r["lds"]/max(1,r["mult"]):.2f} den_ok={r["real_ok"]}')


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    main()

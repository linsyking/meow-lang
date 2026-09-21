"""ROUND 6 (final witnesses) - machine-verifiable record.

PART 1: CONJECTURE A REFUTATION (extended domain).
  E2 = [eps/init^2 X].[X/b]X  and  E4 = [eps/init^4 X].[X/b]X
  on w_j = b(ab)^j, j = 2..40.  The output prov is a MODULAR STAIRCASE:
  labels  n-2, n-4, ..., 2, 0-ish  with a bounded number of boundary
  duplications, so  mult stays pinned (3 for d=2, 4 for d=4) while
  LDS grows linearly in j.  LDS/mult -> infinity refutes
  Conjecture A (LDS <= C(E) * mult).  Every row's content is
  cross-checked against lcore's independent denotation.

PART 2: the ROUND-5 LEFT-MOVE WALL refuted TWICE:
  (a) the B2 triple (found by the targeted B^inf-structured search in
      verify_round6_leftmove.py, re-verified here deterministically);
  (b) family 1's staircase: six+ pairwise-disjoint singleton residuals
      in strictly decreasing order (a chain of length j >> 2).

PART 3: family-1 prov structure printed for the record (the staircase).

Usage: /usr/bin/python3 -W ignore verify_round6_witness.py
"""
import sys

import prov as PV
import lcore as L
from lcore import K, V
import r2lib as RL
import verify_round5_phases as V5
from verify_round6_conjAB import initd
from verify_round6_leftmove import residuals_of, has_triple


def make_E(d, sigma):
    return ('S', K(''), initd(d), ('S', V(0), K(sigma), V(0)))


def row(d, j):
    w = 'b' + 'ab' * j
    E = make_E(d, 'b')
    lab = PV.lab_input(w)
    atoms = PV.lden(E, (lab,))
    prov = PV.labels(atoms)
    ok = PV.content(atoms) == L.den(E, (w,))
    return dict(j=j, n=len(w), prov=prov, lds=PV.lds(prov),
                mult=PV.mult(prov), ok=ok)


def main():
    print('PART 1a: E2 = [eps/init^2 X].[X/b]X on w = b(ab)^j')
    print('    j   n  mult  LDS   ratio   content==den')
    for j in list(range(2, 15)) + [20, 30, 40]:
        r = row(2, j)
        print(f'  {r["j"]:3d} {r["n"]:3d}  {r["mult"]:4d} {r["lds"]:4d} '
              f'{r["lds"]/max(1,r["mult"]):7.2f}   {r["ok"]}')
    print()
    print('PART 1b: E4 = [eps/init^4 X].[X/b]X on w = b(ab)^j')
    print('    j   n  mult  LDS   ratio   content==den')
    for j in list(range(4, 15)) + [16, 20, 24, 30, 40]:
        r = row(4, j)
        print(f'  {r["j"]:3d} {r["n"]:3d}  {r["mult"]:4d} {r["lds"]:4d} '
              f'{r["lds"]/max(1,r["mult"]):7.2f}   {r["ok"]}')

    print()
    print('PART 2a: the B2 triple, standalone deterministic check')
    B = 'ababa'
    A = 'bababab'
    gaps = ['aa', 'a', 'a', 'a']
    T = V5.make_text_tagged(gaps, A)
    res, oj, out = residuals_of(T, B)
    print(f'  text = {gaps[0]} A {gaps[1]} A {gaps[2]} A {gaps[3]} '
          f'(A={A}, B={B})')
    print(f'  residuals: { {k: sorted(v) for k, v in res.items()} }')
    t, e = has_triple(res)
    print(f'  has_triple = {t}, witness = {e}')

    print()
    print('PART 2b: family-1 staircase as a left-move chain (d=2, j=8)')
    r = row(2, 8)
    print(f'  w = b(ab)^8 (n={r["n"]}), prov = {r["prov"]}')
    print(f'  LDS = {r["lds"]}, mult = {r["mult"]}')

    print()
    print('PART 3: staircase structure (d=2): first/last few provs')
    for j in (4, 6, 8, 10, 12):
        r = row(2, j)
        print(f'  j={j:2d}: {r["prov"]}')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    main()

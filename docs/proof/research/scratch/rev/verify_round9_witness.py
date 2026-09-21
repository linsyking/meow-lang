"""ROUND 9 (final witnesses) - THEOREM B REFUTED, and the next invariant.

THE WITNESS FAMILY (all rows content-cross-checked against lcore's
independent denotation):

    E  =  [eps/tail^4 X] . [tail(X)/ab] X        (a FIXED 2-pass L expr)
    w_k = (bba)^k

    prov(w_k) = (0, 1, n-3, n-6, n-9, ..., 3, n-2, n-1)
    mult = 1 EXACTLY, LDS = k-1, for k = 5..12 (extended domain).

THE MECHANISM.  sigma = 'ab' sites at 3, 6, ..., 3k-3 (k-1 copies of
A = tail(w)); the text is period-3 with pre 'bb' and post 'ba'; B =
tail^4(w) has length 3k-4 = n-4; the greedy [eps/B] scan matches at
spacing |B|+3 and emits exactly one 'b' per copy at offsets
descending by 3 -- the modular staircase, CONFINED to the residue
class 0 mod 3 (the 'b' positions of w at 0, 3, 6, ...).  The
interior gap 'b's (also 0 mod 3) are all CONSUMED by the matches; the
pre (labels 0, 1) and post (labels n-2, n-1) survive with labels
outside the staircase's values.  Nothing wraps; the text ends on the
post gap; no offset is ever revisited.  Every previous family failed
one of these conditions (alternating: parity pigeonhole + tail dump;
the 48 text-level candidates: embedding infeasible); this one
satisfies all of them simultaneously.

CONSEQUENCES: Conjecture B (mult 1 => LDS <= C(E)) is FALSE; the
base-case conjecture (mult 1 => LDS <= 2 LDS(A)+1) is FALSE (here
LDS(A) = 1, LDS = k-1); Theorem A (Phase Bound) REMAINS TRUE (its
constant is value-dependent: |S| = k-1 <= (1+|O|)(1+|J|)+1 holds).

THE NEXT INVARIANT CANDIDATE (probe below): rev's prov is a
BIJECTION (every input position survives exactly once: mult 1,
|prov| = |w|, label set = all positions) AND fully descending
(LDS = |prov|).  The two-pass fragment provably cannot be a
descending bijection (a copy with >= 2 surviving atoms has ascending
labels; all-surviving means no deletion).  PROBE: over the round-7
exhaustive domain -- the TEXT level, a strict superset of realizable
pipelines since prov_A is an arbitrary injective labeling --
descending bijections exist ONLY for |w| <= 4 (110 essential
families, all prov_A a leading triple-reversal; e.g. w=abb needs
A=aaa with labels 2,1,0 -- a constant carrying input labels).  The
Theorem-B witness family is far from a bijection: |prov| = k+3 vs
|w| = 3k.

Usage: /usr/bin/python3 -W ignore verify_round9_witness.py
"""
import sys

import prov as PV
import lcore as L
from lcore import K, V
import toolkit as tk
import r2lib as RL
import itertools

sys.path.insert(0, L._LAZY_PASS)


def taild(d):
    e = V(0)
    for _ in range(d):
        e = tk.tail(RL.sg, e)
    return e


def witness_E():
    R = tk.tail(RL.sg, V(0))
    P = taild(4)
    return ('S', K(''), P, ('S', R, K('ab'), V(0)))


def part1():
    E = witness_E()
    print('WITNESS: E = [eps/tail^4 X].[tail(X)/ab]X on w = (bba)^k')
    print('   k  |w|  mult  LDS  len(prov)  prov                          den_ok')
    for k in (5, 6, 7, 8, 10, 12, 14, 16):
        w = 'bba' * k
        lab = PV.lab_input(w)
        atoms = PV.lden(E, (lab,))
        prov = PV.labels(atoms)
        print(f'  {k:3d} {len(w):4d}  {PV.mult(prov):3d}  '
              f'{PV.lds(prov):3d}  {len(prov):7d}   {prov if k <= 12 else "..."}'
              f'   {PV.content(atoms) == L.den(E, (w,))}')


def part2():
    print()
    print('PROBE: descending-bijection instances in the round-7 '
          'exhaustive domain?')
    print('  (mult 1 AND |prov| = |w| AND LDS = |prov| AND |w| >= 3)')
    from verify_round7_mult1 import frag_sim, stats_of, prov_variants
    sigs = ['a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'baa']
    As = [''.join(x) for n in range(1, 5)
          for x in itertools.product('ab', repeat=n)]
    Bs = [''.join(x) for n in range(1, 4)
          for x in itertools.product('ab', repeat=n)]
    Ws = [''.join(x) for n in range(1, 7)
          for x in itertools.product('ab', repeat=n)]
    n = hits = 0
    ex = []
    for A in As:
        for vA in prov_variants(A):
            A_lab = list(zip(A, vA))
            for B in Bs:
                for sig in sigs:
                    for w in Ws:
                        st = stats_of(frag_sim(w, A_lab, sig, B))
                        n += 1
                        if st['mult'] == 1 and len(st['prov']) == len(w) \
                                and len(w) >= 3 \
                                and st['lds'] == len(st['prov']):
                            hits += 1
                            ex.append((w, A, vA, B, sig))
    print(f'  {n} instances; descending bijections (|w|>=3): {hits}')
    fams = sorted({(w, A, tuple(vA)) for (w, A, vA, B, sig) in ex})
    print(f'  essential families (w, A, prov_A): {len(fams)}')
    print(f'  longest |w| with a descending bijection:',
          max((len(w) for (w, A, vA, B, sig) in ex), default=0))
    print('  NB: the text level is a strict SUPERSET of realizable')
    print('  pipelines (prov_A is an arbitrary injective labeling);')
    print('  even with that freedom, no |w| >= 5 admits one.')
    print('  Example family: w=abb, A=aaa, prov_A=(2,1,0) -- needs a')
    print('  constant A carrying input labels (constants carry none).')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    part1()
    part2()

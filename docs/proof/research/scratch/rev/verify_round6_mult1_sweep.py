"""ROUND 6 (part 3, v2) - the mult-1 hunt with CHEAP B constructions.

init^d via leaf-substitution blows up as 4^d (3.3M nodes at d=6), so this
sweep uses tail^d (tk.tail is linear in its argument) plus init^2 and
small cat-variants to sweep the needle's phase.  Question: does any
E = [eps/B(X)] . [X/sigma] X  achieve UNBOUNDED LDS at mult = 1?

Usage: /usr/bin/python3 -W ignore verify_round6_mult1_sweep.py
"""
import sys

import prov as PV
import lcore as L
from lcore import K, V
import r2lib as RL
import toolkit as tk
from verify_round6_conjAB import sub_tree

sys.path.insert(0, L._LAZY_PASS)


def taild(d):
    """AST for lambda x. tail^d(x)  (drops the FIRST d chars)."""
    e = V(0)
    for _ in range(d):
        e = tk.tail(RL.sg, e)
    return e


def init2():
    return sub_tree(RL.init_expr(),
                    sub_tree(RL.init_expr(), V(0)))


def cat(*es):
    acc = es[0]
    for e in es[1:]:
        acc = tk.cat(RL.sg, acc, e)
    return acc


def make_E(P, sigma):
    return ('S', K(''), P, ('S', V(0), K(sigma), V(0)))


def measure(E, w):
    lab = PV.lab_input(w)
    try:
        atoms = PV.lden(E, (lab,))
    except PV.Undefined:
        return None
    prov = PV.labels(atoms)
    return dict(prov=prov, lds=PV.lds(prov), mult=PV.mult(prov))


PATTERNS = [
    ('alt', lambda j: 'b' + 'ab' * j),
    ('baab', lambda j: 'baab' * j),
    ('baaab', lambda j: 'baaab' * j),
    ('aab', lambda j: 'aab' * j),
    ('ab_b', lambda j: 'ab' * j + 'b'),
    ('b_aab', lambda j: 'b' + 'aab' * j),
    ('ba_b', lambda j: 'ba' * j + 'b'),
]
SIGMAS = ['b', 'ba', 'ab', 'aab', 'baa', 'aa']


def bs():
    out = []
    for d in range(1, 9):
        out.append((f'tail^{d}', taild(d)))
    out.append(('init^2', init2()))
    for d in (2, 3, 4, 6):
        out.append((f'a.tail^{d}', cat(K('a'), taild(d))))
        out.append((f'tail^{d}.a', cat(taild(d), K('a'))))
        out.append((f'b.tail^{d}', cat(K('b'), taild(d))))
        out.append((f'tail^{d}.b', cat(taild(d), K('b'))))
    return out


def main():
    BS = bs()
    print(f'{len(BS)} B-constructions x {len(PATTERNS)} patterns x '
          f'{len(SIGMAS)} sigmas')
    print()
    print('MULT-1 rows with LDS >= 4:')
    hits = {}
    for pname, f in PATTERNS:
        for bname, P in BS:
            for sigma in SIGMAS:
                rows = []
                for j in range(2, 11):
                    w = f(j)
                    if len(w) <= 4:
                        continue
                    r = measure(make_E(P, sigma), w)
                    if r and r['mult'] == 1 and r['lds'] >= 4:
                        rows.append((j, r['lds']))
                if rows:
                    key = (pname, bname, sigma)
                    hits[key] = rows
                    print(f'  {pname:6s} B={bname:11s} sig={sigma:4s}: '
                          f'{rows}')
    if not hits:
        print('  (none)')
    print()
    print('TOP rows by LDS (any mult), best per (pattern, sigma):')
    best = {}
    for pname, f in PATTERNS:
        for bname, P in BS:
            for sigma in SIGMAS:
                for j in (6, 10):
                    w = f(j)
                    if len(w) <= 4:
                        continue
                    r = measure(make_E(P, sigma), w)
                    if not r:
                        continue
                    k = (pname, sigma)
                    if k not in best or (r['lds'], -r['mult']) > \
                            (best[k][2], -best[k][1]):
                        best[k] = (bname, r['mult'], r['lds'])
    for (pname, sigma), (bname, m, l) in sorted(best.items()):
        if l >= 5:
            print(f'  {pname:6s} sig={sigma:4s}: B={bname:11s} mult={m} '
                  f'LDS={l}')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    main()

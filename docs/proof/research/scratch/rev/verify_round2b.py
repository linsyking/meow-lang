"""Influence-flip experiment + deeper atom-prov corpus.

For E and w: D_E(w,p) = {i : out_i(w) != out_i(w^p)} where w^p flips w at p.
rev's influence: perfect anti-diagonal matching (p -> n-1-p).
Controls: rot1 (near-diagonal), rotr1 (one wrap), last (single cell),
[eps/b]X (monotone blob), [X/a]X (broadcast), enc/dec (local).

Quantities per (E, w):
  matching-ness: is every D(w,p) a singleton and every column hit once?
  disorder of the induced matching (where defined): the number of
    crossings  #{(p<p') : pi(p) > pi(p')}  and max displacement.
  broadcast: total influence mass sum_p |D(w,p)|.
"""
import random
import sys
from collections import defaultdict

import lcore as L
from lcore import K, V, C, S, comp, pipe, battery, rev
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN
rng = random.Random(31415)


def out_of(e, w):
    r = L.den_try(e, (w,))
    return None if r[0] != 'ok' else r[1]


def influence(e, w):
    """D(w,p) for all p (only p where the flipped char actually differs)."""
    base = out_of(e, w)
    if base is None:
        return None, None
    D = {}
    for p in range(len(w)):
        flip = 'a' if w[p] == 'b' else 'b'
        w2 = w[:p] + flip + w[p + 1:]
        o2 = out_of(e, w2)
        if o2 is None:
            D[p] = None
            continue
        if len(o2) == len(base):
            D[p] = [i for i in range(len(base)) if o2[i] != base[i]]
        else:
            D[p] = ('len', len(o2))
    return base, D


def describe(D, n):
    single = [p for p in D if isinstance(D[p], list) and len(D[p]) == 1]
    mass = sum(len(D[p]) for p in D if isinstance(D[p], list))
    # matching structure on singleton rows with singleton columns
    col = defaultdict(int)
    for p in single:
        col[D[p][0]] += 1
    perfect = [p for p in single if col[D[p][0]] == 1]
    pi = {p: D[p][0] for p in perfect}
    crossings = sum(1 for p in perfect for q in perfect
                     if p < q and pi[p] > pi[q])
    disp = max((abs(pi[p] - p) for p in perfect), default=0)
    return {'rows': len(D), 'singletons': len(single),
            'mass': mass, 'match_size': len(perfect),
            'crossings': crossings, 'maxdisp': disp}


W = [''.join(rng.choice('ab') for _ in range(12)) for _ in range(3)]
targets = {
    'rev': lambda w: rev(w),
    'id': lambda w: w,
    'rot1-content': lambda w: w[1:] + w[:1],
    'rotr1-content': lambda w: w[-1:] + w[:-1],
    'last-content': lambda w: w[-1:],
    'init-content': lambda w: w[:-1],
}
# expressions (evaluate via den; these compute the content functions)
exprs = {
    'X': V(0),
    '[eps/b]X': comp([('', 'b')], V(0)),
    '[X/a]X': comp([(V(0), 'a')], V(0)),
    '[ab/ba]X': comp([('ab', 'ba')], V(0)),
    'encX': tk.enc(sg, V(0)),
    'decX': tk.dec(sg, V(0)),
    'rot1': tk.cat(sg, tk.tail(sg, V(0)), tk.head(sg, V(0))),
    'lastX': RL.last_expr(),
    'initX': RL.init_expr(),
    'rotr1X': RL.rotr1_expr(),
    'nearmiss': pipe([('c', 'aa'), ('bc', 'cb'), ('c', 'aa')], V(0)),
}

print('=== content-function influence (the spec side) ===')
for name, f in targets.items():
    for w in W[:1]:
        n = len(w)
        D = {}
        base = f(w)
        for p in range(n):
            w2 = w[:p] + ('a' if w[p] == 'b' else 'b') + w[p + 1:]
            o2 = f(w2)
            D[p] = [i for i in range(len(base)) if o2[i] != base[i]]
        st = describe(D, n)
        print(f'  {name:14s} n={n}: {st}')

print('=== expression influence ===')
for name, e in exprs.items():
    for w in W[:1]:
        base, D = influence(e, w)
        if D is None:
            print(f'  {name:14s} UNDEFINED on {w}')
            continue
        st = describe(D, len(w))
        lenchanges = sum(1 for p in D if not isinstance(D[p], list))
        print(f'  {name:14s} n={len(w)}: {st} len-changing-rows={lenchanges}')

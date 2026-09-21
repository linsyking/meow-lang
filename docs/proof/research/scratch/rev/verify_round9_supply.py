"""ROUND 9 - the supply half of Theorem B, and the decisive question:
is a mult-1 STAIRCASE constructible at all?

The round-8 dissection of the max instance (E = [eps/tail^3 X].[X/ab]X,
w = baabaaba: chain 5 > 2, capped when the staircase fell into the gap
region) gives the cap mechanism: the emission offsets descend by
s = unit - spacing per copy; a WRAP revisits offsets (mult >= 2); the
text can absorb ONE descent into copies + gap.  The knife-edge count:
mult 1 needs  #copies c ~ (n+g)/gcd(s, n+g)  EXACTLY, a post-aligned
end (no tail dump of copy atoms), and gap labels disjoint from the
descent offsets.  With 2-char sigma the b-supply pigeonhole weakens
(w = sigma-sites + gaps has more b's), so the recipe might close.
THIS SCRIPT hunts for it directly:

PART 1: the extended direct hunt -- all period-2/3 input families
  (every phase), 8 sigmas including 3-char, R = the injective family,
  P = the 15 best needle constructions.  If mult 1 with LDS >= 3
  appears ANYWHERE, Theorem B is in danger (and we must know).

PART 2: death-reason breakdown of the chain-rich structures (round 8's
  48 + a fresh batch): WHY does each die -- sites not recovered /
  content mismatch / |A| > |w| (supply) / F-collision / DP infeasible.

PART 3: residue-class check: in every chain-rich structure, are the
  chain's offsets congruent mod (period of A's periodic end)?  The
  supply argument's key premise, verified.

Usage: /usr/bin/python3 -W ignore verify_round9_supply.py
"""
import itertools
import random
import sys
from collections import defaultdict

import prov as PV
import lcore as L
from lcore import K, V
import verify_round5_phases as V5
import verify_round6_leftmove as V6
from verify_round8_theoremB import (R_LIB, lden_cache, feas_and_embed,
                                    tagged_text, scan_cover,
                                    sites_recovered)

rng = random.Random(271828)

SIGMAS = ['b', 'a', 'ab', 'ba', 'aab', 'baa', 'abb', 'bba']


def w_families():
    fams = []
    for pat in ('ab', 'ba', 'aab', 'aba', 'abb', 'baa', 'bab', 'bba',
                'aa', 'bb'):
        for j in range(2, 9):
            fams.append(pat * j)
    for f in (lambda j: 'b' + 'ab' * j, lambda j: 'ab' * j + 'b',
              lambda j: 'ab' * j + 'a', lambda j: 'a' + 'ba' * j,
              lambda j: 'b' + 'aab' * j, lambda j: 'aab' * j + 'a'):
        for j in range(2, 9):
            fams.append(f(j))
    ws = list(dict.fromkeys(fams))
    ws += [''.join(x) for n in range(1, 8)
           for x in itertools.product('ab', repeat=n)]
    for t in range(120):
        ws.append(''.join(rng.choice('ab')
                          for _ in range(rng.randrange(6, 13))))
    return list(dict.fromkeys(ws))


def p_lib15():
    import verify_round6_mult1_sweep as S6
    keep = ('tail^1', 'tail^2', 'tail^3', 'tail^4', 'tail^6',
            'init^2', 'a.tail^2', 'a.tail^3', 'a.tail^4',
            'tail^2.a', 'tail^3.a', 'tail^4.a', 'b.tail^2',
            'tail^2.b', 'tail^3.b')
    BS = dict(S6.bs())
    return [(k, BS[k]) for k in keep if k in BS]


def part1():
    print('PART 1: extended direct hunt (period-2/3 families, 8 sigmas):')
    ws = w_families()
    PS = p_lib15()
    print(f'  inputs: {len(ws)}; R x P x sigma: {len(R_LIB)} x '
          f'{len(PS)} x {len(SIGMAS)}')
    best = (0, None)
    hist = defaultdict(int)
    n_tot = n_m1 = 0
    for rname, R in R_LIB:
        for w in ws:
            A_lab = lden_cache(R, w)
            if A_lab is None or not A_lab:
                continue
            if PV.lds([lb for (_, lb) in A_lab
                       if lb is not None]) != 1:
                continue
            for pname, P in PS:
                B_lab = lden_cache(P, w)
                if B_lab is None or not B_lab:
                    continue
                Bstr = ''.join(c for (c, _) in B_lab)
                for sig in SIGMAS:
                    surv = []
                    T = []
                    i = 0
                    # inline frag_sim (import would be circular-free but
                    # cheap enough to re-run; use verify_round7's)
                    from verify_round7_mult1 import frag_sim, stats_of
                    st = stats_of(frag_sim(w, A_lab, sig, Bstr))
                    n_tot += 1
                    if st['mult'] != 1:
                        continue
                    n_m1 += 1
                    hist[st['lds']] += 1
                    if st['lds'] > best[0]:
                        best = (st['lds'], (rname, pname, sig, w))
                        print(f'  *** new max at mult 1: LDS={best[0]} '
                              f'{best[1]}')
    print(f'  pipelines: {n_tot}; mult-1: {n_m1}; '
          f'LDS hist: {dict(sorted(hist.items()))}')
    print(f'  MAX LDS AT MULT 1: {best}')


def part2(trials=80000):
    print()
    print('PART 2: death-reason breakdown of chain-rich structures:')
    reasons = defaultdict(int)
    ex = {}
    for t in range(trials):
        lb = rng.randrange(2, 13)
        B = ''.join(rng.choice('ab') for _ in range(lb))
        m = lb
        n = rng.randrange(3, 15)

        def factor(lo, ln):
            return ''.join(B[(lo + s) % m] for s in range(ln))
        A = factor(rng.randrange(m), n)
        ncop = rng.randrange(3, 6)
        gaps = [factor(rng.randrange(m), rng.randrange(0, 5))
                for _ in range(ncop)]
        T = V5.make_text_tagged(gaps, A)
        res, oj, _ = V6.residuals_of(T, B)
        rs = [R for R in res.values() if R]
        if len(rs) < 3:
            continue
        if V6.max_dec_chain(res) < 3:
            continue
        if not all(not (x & y) for x, y in itertools.combinations(rs, 2)):
            reasons['residuals not disjoint'] += 1
            continue
        # candidate: try all sigmas
        died = True
        for sig in SIGMAS:
            w, Tt = tagged_text(gaps, A, sig)
            if not sites_recovered(w, sig, len(gaps)):
                r = 'sites not recovered'
            elif ''.join(x[0] for x in Tt) != T:
                r = 'content mismatch'
            else:
                alive = scan_cover(Tt, B)
                F = [Tt[j][1][1] for j in alive
                     if Tt[j][1][0] == 'gap']
                R_offsets = set().union(*rs)
                if len(A) > len(w):
                    r = '|A| > |w| (supply)'
                elif feas_and_embed(A, w, R_offsets, F) is None:
                    # which constraint?  retry without F:
                    if feas_and_embed(A, w, R_offsets, []) is None:
                        r = 'embedding infeasible (content/supply)'
                    else:
                        r = 'F-collision (gap labels)'
                else:
                    r = 'FEASIBLE'
                    died = False
                    ex.setdefault('FEASIBLE',
                                  (A, B, gaps, sig, w))
            reasons[r] += 1
            if r == 'FEASIBLE':
                break
        if died:
            ex.setdefault('all-sigma-death', (A, B, gaps))
    print(f'  structures: {trials}; death reasons '
          f'(per sigma attempt):')
    for k, v in sorted(reasons.items(), key=lambda kv: -kv[1]):
        print(f'    {k}: {v}')
    if 'FEASIBLE' in ex:
        print(f'  FEASIBLE example: {ex["FEASIBLE"]}')
        A, B, gaps, sig, w = ex['FEASIBLE']
        # full verification
        from verify_round7_mult1 import frag_sim, stats_of
        Tt = tagged_text(gaps, A, sig)[1]
        alive = scan_cover(Tt, B)
        F = [Tt[j][1][1] for j in alive if Tt[j][1][0] == 'gap']
        rs = None
        res, oj, _ = V6.residuals_of(V5.make_text_tagged(gaps, A), B)
        R_offsets = set().union(*[r for r in res.values() if r])
        emb = feas_and_embed(A, w, R_offsets, F)
        A_lab = [(A[i], emb[i]) for i in range(len(A))]
        st = stats_of(frag_sim(w, A_lab, sig, B))
        print(f'  verified pipeline: mult={st["mult"]} LDS={st["lds"]} '
              f'prov={st["prov"]}')


def part3():
    print()
    print('PART 3: residue-class check on chain offsets:')
    checked = same = 0
    for t in range(20000):
        lb = rng.randrange(2, 11)
        B = ''.join(rng.choice('ab') for _ in range(lb))
        m = lb
        n = rng.randrange(3, 13)

        def factor(lo, ln):
            return ''.join(B[(lo + s) % m] for s in range(ln))
        A = factor(rng.randrange(m), n)
        ncop = rng.randrange(3, 6)
        gaps = [factor(rng.randrange(m), rng.randrange(0, 4))
                for _ in range(ncop)]
        T = V5.make_text_tagged(gaps, A)
        res, oj, _ = V6.residuals_of(T, B)
        rs = [R for R in res.values() if R]
        if len(rs) < 2:
            continue
        # extract a decreasing chain greedily
        chain = []
        last = float('inf')
        for c in sorted(res):
            if not res[c]:
                continue
            pick = max((p for p in res[c] if p < last), default=None)
            if pick is not None:
                chain.append(pick)
                last = pick
        if len(chain) < 3:
            continue
        checked += 1
        d = {b - a for a, b in zip(chain, chain[1:])}
        if len(d) == 1:
            same += 1
    print(f'  chains >= 3 examined: {checked}; constant-descent '
          f'(uniform staircase): {same}')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    part1()
    part2()
    part3()

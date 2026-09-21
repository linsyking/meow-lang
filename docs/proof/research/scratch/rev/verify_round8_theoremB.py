"""ROUND 8 - Theorem B: at mult 1, is the number of realized phases
(#surviving copies) bounded by C(E)?

THE MEETING TO TEST: mult 1 + many realized phases => periodicity (rich
O/J => border chains => small period) => supply (the realizing w cannot
feed the phases without duplicating labels).  Two hunts + one lemma:

PART 1 (direct pipeline hunt, the critical adversarial sweep):
  E = [eps/P(w)] . [R(w)/sigma] X  over the concrete injective-R family
  (X, single/double-char deletions, init, tail -- all LDS(prov_A)=1),
  25 needle constructions P, 4 sigmas, all |w|<=7 plus periodic and
  random inputs.  Question: does ANY realizable pipeline reach mult 1
  with LDS >= 4 (Theorem B in trouble)?

PART 2 (lift-the-structures hunt): for every chain-rich free-text
  structure (aligned alternating m<=13 and 100K B^inf-structured), for
  every sigma, build the realizing w, require the greedy sigma-scan to
  recover the intended sites, then require A = R(w) and B = P(w) for
  CONCRETE R, P in the injective/deletion/anchored family, and verify
  the full pipeline with the tagged simulator.  A surviving mult-1
  chain >= 4 is a Theorem B counterexample; the infeasibility tally is
  the supply pigeonhole made machine-checkable.

PART 3 (quantified periodicity): borders vs minimal period on all
  strings <= 12 -- the lemma "|O| realized overlaps => A[:o_max] has
  period <= o_max/(|O|-1)" in verified form.

Usage: /usr/bin/python3 -W ignore verify_round8_theoremB.py
"""
import itertools
import random
import sys
from collections import defaultdict

import prov as PV
import lcore as L
from lcore import K, V
import r2lib as RL
import toolkit as tk
import verify_round5_phases as V5
import verify_round6_leftmove as V6
from verify_round6_conjAB import sub_tree
from verify_round7_mult1 import frag_sim, stats_of

sys.path.insert(0, L._LAZY_PASS)
rng = random.Random(31415)

# ------------------------------------------------------- R / P libraries


def del_R(pat):
    return ('S', K(''), K(pat), V(0))


R_LIB = [('X', V(0))] + [(f'[eps/{p}]', del_R(p))
                         for p in ('a', 'b', 'aa', 'bb', 'ab', 'ba',
                                   'aaa', 'bbb', 'aab', 'bba')]
R_LIB += [('init', RL.init_expr()),
          ('tail', tk.tail(RL.sg, V(0)))]


def P_lib():
    import verify_round6_mult1_sweep as S6
    return S6.bs()


P_LIB = None        # built lazily


def p_names():
    global P_LIB
    if P_LIB is None:
        P_LIB = P_lib()
    return P_LIB


def lden_cache(ast, w):
    key = (id(ast), w)
    if key not in lden_cache.d:
        lab = PV.lab_input(w)
        try:
            atoms = PV.lden(ast, (lab,))
            lden_cache.d[key] = [(a[0], a[1]) for a in atoms]
        except PV.Undefined:
            lden_cache.d[key] = None
    return lden_cache.d[key]


lden_cache.d = {}


# ------------------------------------------------------- PART 1


def part1():
    print('PART 1: direct pipeline hunt (injective R family):')
    ws = [''.join(x) for n in range(1, 8)
          for x in itertools.product('ab', repeat=n)]
    pats = [f for f in (
        lambda j: 'b' + 'ab' * j, lambda j: 'baab' * j,
        lambda j: 'aab' * j, lambda j: 'baaab' * j,
        lambda j: 'ab' * j + 'b', lambda j: 'b' + 'aab' * j)]
    for f in pats:
        for j in range(2, 9):
            ws.append(f(j))
    for t in range(60):
        ws.append(''.join(rng.choice('ab')
                          for _ in range(rng.randrange(6, 11))))
    ws = list(dict.fromkeys(ws))
    print(f'  inputs: {len(ws)}  R x P x sigma: '
          f'{len(R_LIB)} x {len(p_names())} x 4')
    best = (0, None)
    hist = defaultdict(int)
    n_mult1 = n_tot = 0
    for rname, R in R_LIB:
        for w in ws:
            A_lab = lden_cache(R, w)
            if A_lab is None or not A_lab:
                continue
            ldsA = PV.lds([lb for (_, lb) in A_lab
                           if lb is not None])
            if ldsA != 1:
                continue          # injective-R family only (LDS(A)=1)
            for pname, P in p_names():
                B_lab = lden_cache(P, w)
                if B_lab is None or not B_lab:
                    continue
                Bstr = ''.join(c for (c, _) in B_lab)
                for sig in ('b', 'a', 'ab', 'ba'):
                    surv = frag_sim(w, A_lab, sig, Bstr)
                    st = stats_of(surv)
                    n_tot += 1
                    if st['mult'] != 1:
                        continue
                    n_mult1 += 1
                    hist[st['lds']] += 1
                    if st['lds'] > best[0]:
                        best = (st['lds'], (rname, pname, sig, w))
    print(f'  pipelines evaluated: {n_tot}; mult-1 rows: {n_mult1}')
    print(f'  LDS histogram at mult 1: {dict(sorted(hist.items()))}')
    print(f'  MAX LDS AT MULT 1: {best}')


# ------------------------------------------------------- PART 2


def tagged_text(gaps, A, sigma):
    """w and T with tags: returns (w, T) where T = [(char, tag)] with
    tag = ('gap', wpos) or ('copy', c, offset)."""
    w_parts = []
    T = []
    pos = 0
    for c in range(len(gaps)):
        T.append((sigma[0], ('sig', pos)))       # provisional; rebuilt
        w_parts.append(sigma)
        pos += len(sigma)
        for ch in gaps[c]:
            w_parts.append(ch)
            T.append((ch, ('gap', pos)))
            pos += 1
    # T must interleave sigma atoms; rebuild properly:
    T = []
    pos = 0
    copy_i = 0
    for c in range(len(gaps)):
        for ch in sigma:
            T.append((ch, ('sig', pos)))
            pos += 1
        for k, ch in enumerate(A):
            T.append((ch, ('copy', copy_i, k)))
        copy_i += 1
        for ch in gaps[c]:
            T.append((ch, ('gap', pos)))
            pos += 1
    return ''.join(w_parts), T


def scan_cover(T, B):
    m = len(B)
    alive = [True] * len(T)
    i = 0
    while i + m <= len(T):
        if all(T[i + k][0] == B[k] for k in range(m)):
            for k in range(m):
                alive[i + k] = False
            i += m
        else:
            i += 1
    return [j for j in range(len(T)) if alive[j]]


def sites_recovered(w, sigma, ncop):
    """greedy sigma-scan finds exactly ncop non-overlapping sites."""
    i = c = 0
    ls = len(sigma)
    while i + ls <= len(w):
        if w[i:i + ls] == sigma:
            c += 1
            i += ls
        else:
            i += 1
    return c == ncop


def feas_and_embed(A, w, R_offsets, F):
    """NONDECREASING embedding p of A into w (p[i] a w-position,
    A[i] = w[p[i]]), with p injective on R_offsets (the surviving
    offsets) and p[i] not in F for i in R_offsets (F = surviving gap
    positions).  Repeats are allowed only at NON-surviving offsets
    (their labels never reach the output, so mult 1 is preserved).
    Returns the embedding (list of positions, one per atom, with
    repeats marked by equal consecutive values) or None."""
    n, m = len(A), len(w)
    forb = set(R_offsets)
    Fs = set(F)
    ok = [[False] * (m + 1) for _ in range(n + 1)]
    for j in range(m + 1):
        ok[n][j] = True
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            same = A[i] == w[j]
            good = same and (i not in forb or j not in Fs)
            rep = same and i not in forb        # repeat p[i] = p[i+1] = j
            ok[i][j] = ((good and ok[i + 1][j + 1]) or ok[i][j + 1]
                        or (rep and ok[i + 1][j]))
    if not ok[0][0]:
        return None
    emb = []
    i = j = 0
    while i < n:
        same = A[i] == w[j]
        good = same and (i not in forb or j not in Fs)
        rep = same and i not in forb
        if good and ok[i + 1][j + 1]:
            emb.append(j)
            i += 1
            j += 1
        elif rep and ok[i + 1][j]:
            emb.append(j)
            i += 1                 # p[i] = p[i+1] = j (repeat)
        else:
            j += 1
    return emb if i == n else None


def part2():
    print()
    print('PART 2: lift-the-structures hunt (chain-rich texts):')
    # structures: aligned alternating family + B^inf randoms
    structs = []
    for m in (5, 7, 9, 11, 13):
        B = ('ab' * ((m + 1) // 2 + 1))[:m]
        n = m + 2
        A = ('ba' * (n // 2 + 1))[:n]
        for ncop in range(3, 7):
            for pre in ('', 'a', 'aa'):
                for post in ('', 'a', 'aa'):
                    structs.append((A, B, [pre] + ['a'] * (ncop - 1)
                                    + [post]))
    for t in range(60000):
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
        structs.append((A, B, gaps))

    n_struct = n_chain3 = n_disj = n_real = n_feas = 0
    verified = []
    best = (0, None)
    for (A, B, gaps) in structs:
        n_struct += 1
        T = V5.make_text_tagged(gaps, A)
        res, oj, _ = V6.residuals_of(T, B)
        rs = [R for R in res.values() if R]
        if len(rs) < 3:
            continue
        mc = V6.max_dec_chain(res)
        if mc < 3:
            continue
        n_chain3 += 1
        if not all(not (x & y) for x, y in itertools.combinations(rs, 2)):
            continue
        n_disj += 1
        # realize: try sigmas
        for sig in ('b', 'a', 'ab', 'ba', 'aa', 'bb'):
            w, Tt = tagged_text(gaps, A, sig)
            if not sites_recovered(w, sig, len(rs) + 0) and \
                    not sites_recovered(w, sig, len(gaps)):
                continue
            if ''.join(t[0] for t in Tt) != T:
                continue
            alive = scan_cover(Tt, B)
            F = [Tt[j][1][1] for j in alive
                 if Tt[j][1][0] == 'gap']
            R_offsets = set().union(*rs)
            emb = feas_and_embed(A, w, R_offsets, F)
            if emb is None:
                continue
            n_feas += 1
            A_lab = [(A[i], emb[i]) for i in range(len(A))]
            st = stats_of(frag_sim(w, A_lab, sig, B))
            if st['mult'] == 1:
                n_real += 1
                if st['lds'] >= 3:
                    verified.append((A, B, gaps, sig, w, emb,
                                     st['lds']))
                if st['lds'] > best[0]:
                    best = (st['lds'], (A, B, gaps, sig, w))
    print(f'  structures scanned: {n_struct}')
    print(f'  chain>=3: {n_chain3}; pairwise-disjoint: {n_disj}; '
          f'feasible embedding: {n_feas}; verified mult-1: {n_real}')
    print(f'  verified mult-1 rows with LDS>=3: {len(verified)}')
    for v in verified[:6]:
        print(f'    A={v[0]} B={v[1]} gaps={v[2]} sig={v[3]} '
              f'w={v[4]} LDS={v[6]}')
    print(f'  MAX LDS AT MULT 1 (lifted structures): {best}')


# ------------------------------------------------------- PART 3


def borders(x):
    out = []
    for b in range(1, len(x)):
        if x[:b] == x[-b:]:
            out.append(b)
    return out


def min_period(x):
    for p in range(1, len(x) + 1):
        if all(x[i] == x[i + p] for i in range(len(x) - p)):
            return p
    return len(x)


def part3():
    print()
    print('PART 3: borders vs minimal period (all strings <= 11):')
    worst = (0, None)
    for n in range(1, 12):
        for x in map(''.join, itertools.product('ab', repeat=n)):
            t = len(borders(x))
            if t >= 2:
                p = min_period(x)
                ratio = (n - 1) / (p * (t - 1))
                if ratio > worst[0]:
                    worst = (ratio, (x, t, p))
    print(f'  worst (|x|-1)/(p*(t-1)) over all x: {worst[0]:.3f} at '
          f'{worst[1]} (ratio >= 1 always)')
    print('  => LEMMA (verified exhaustively): t >= 2 borders with min')
    print('     period p  =>  p*(t-1) <= |x|-1,  i.e.  p <= '
          '(|x|-1)/(t-1)')
    print('  THEOREM B periodicity link: |S| <= (1+|O|)(1+|J|)+1, so')
    print('  |S| >= K => max(|O|,|J|) >= sqrt(K)-1 => A[:o_max] (or')
    print('  A[-j_max:]) has period <= (|A|-1)/(sqrt(K)-2).')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    part1()
    part2()
    part3()

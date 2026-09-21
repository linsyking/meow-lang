"""ROUND 7 - the mult-1 theorem: prove what is provable, attack what is not.

THEOREM A (proved this round; verified in PART 1):
  In the two-pass fragment [A/sigma][eps/B] at output multiplicity 1:
   (i)   at most one surviving copy per realized (o,j) phase, so
         #surviving copies <= (1+|O|)(1+|J|)+1   [Lemma Phase];
   (ii)  the gap survivors' labels strictly increase in text order, so
         they contribute <= 1 to any decreasing chain;
   (iii) each surviving copy contributes <= LDS(prov_A);
  hence LDS(prov) <= [(1+|O|)(1+|J|)+1] * LDS(prov_A) + 1.
  Proof of (i): two surviving copies with equal phase keep identical
  offset sets (Lemma Phase); if nonempty they share an offset, hence a
  label prov_A[i], hence multiplicity >= 2.

THE BASE-CASE CONJECTURE (chain <= 2 LDS(A)+1 at mult 1) is REALIZA-
BILITY-DEPENDENT: PART 2a exhibits a free text (injective increasing
labels) with a mult-1 chain of length 4 (refuting the TEXT-level
statement), and the realizability analysis (parity pigeonhole: the
chain needs 5 b-atoms at descending positions, the realizable w offers
4 b-sites) blocks it at the pipeline level.  PART 2b hunts for a
realizable counterexample and finds none.

PART 3 (side probe): crossings chi for the staircase family E2 --
does the collapsing function with LDS ~ n/2 threaten rem:price
(chi <= c(E) |w|)?

Usage: /usr/bin/python3 -W ignore verify_round7_mult1.py
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
from verify_round6_conjAB import initd, make_E

rng = random.Random(7777)

# ------------------------------------------------------ tagged simulator


def frag_sim(w, A_lab, sigma, B_str):
    """[A/sigma] then [eps/B] with atom tags.

    A_lab: list of (char, label) -- the value A with its provenance.
    Returns survivors: list of (char, label, tag), tag =
    ('gap', wpos) or ('copy', c, offset).
    """
    T = []
    i, c = 0, 0
    ls = len(sigma)
    while i < len(w):
        if w[i:i + ls] == sigma:
            for k, (ch, lb) in enumerate(A_lab):
                T.append((ch, lb, ('copy', c, k)))
            c += 1
            i += ls
        else:
            T.append((w[i], i, ('gap', i)))
            i += 1
    m = len(B_str)
    i = 0
    alive = [True] * len(T)
    while i + m <= len(T):
        if all(T[i + k][0] == B_str[k] for k in range(m)):
            for k in range(m):
                alive[i + k] = False
            i += m
        else:
            i += 1
    return [t for j, t in enumerate(T) if alive[j]]


def prov_variants(A):
    """injective label sequences on |A| positions: LDS 1, 2, 3."""
    n = len(A)
    res = [list(range(n))]                       # LDS 1
    if n >= 2:
        v = list(range(n))
        for b in range(0, n - 1, 2):             # swap pairs: LDS 2
            v[b], v[b + 1] = v[b + 1], v[b]
        res.append(v)
    if n >= 3:
        v = list(range(n))
        for b in range(0, n - 2, 3):             # reverse triples: LDS 3
            v[b], v[b + 1], v[b + 2] = v[b + 2], v[b + 1], v[b]
        res.append(v)
    return res


def stats_of(surv):
    labels = [lb for (_, lb, _) in surv if lb is not None]
    copies = defaultdict(set)
    for (_, _, tg) in surv:
        if tg[0] == 'copy':
            copies[tg[1]].add(tg[2])
    return dict(prov=labels, lds=PV.lds(labels), mult=PV.mult(labels),
                ncop=len(copies), res=dict(copies))


# ------------------------------------------------------ PART 1


def part1():
    sigs = ['a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'baa']
    As = [''.join(x) for n in range(1, 5)
          for x in itertools.product('ab', repeat=n)]
    Bs = [''.join(x) for n in range(1, 4)
          for x in itertools.product('ab', repeat=n)]
    Ws = [''.join(x) for n in range(1, 7)
          for x in itertools.product('ab', repeat=n)]
    n_inst = n_ok = viol_a = viol_b = viol_c = 0
    max_lds_m1 = (0, None)
    max_cop_m1 = (0, None)
    # content cross-check sample
    bad_content = 0
    for A in As:
        for vA in prov_variants(A):
            A_lab = list(zip(A, vA))
            ldsA = PV.lds(vA)
            for B in Bs:
                O, J = V5.O_set(A, B), V5.J_set(A, B)
                ph = (1 + len(O)) * (1 + len(J)) + 1
                for sig in sigs:
                    for w in Ws:
                        surv = frag_sim(w, A_lab, sig, B)
                        n_inst += 1
                        st = stats_of(surv)
                        if n_inst % 4009 == 0:
                            # content check vs the real denotation
                            ast = ('S', K(''), K(B),
                                   ('S', K(A), K(sig), V(0)))
                            got = ''.join(c for (c, _, _) in surv)
                            if got != L.den(ast, (w,)):
                                bad_content += 1
                        if st['mult'] != 1:
                            continue
                        n_ok += 1
                        if st['ncop'] > ph:
                            viol_a += 1
                        if st['lds'] > st['ncop'] * ldsA + 1:
                            viol_b += 1
                        if st['lds'] > 2 * ldsA + 1:
                            viol_c += 1
                            if max_lds_m1[0] < st['lds']:
                                max_lds_m1 = (st['lds'],
                                              (w, A, vA, B, sig))
                        if st['lds'] > max_lds_m1[0]:
                            max_lds_m1 = (st['lds'], (w, A, vA, B, sig))
                        if st['ncop'] > max_cop_m1[0]:
                            max_cop_m1 = (st['ncop'], (w, A, vA, B, sig))
    print(f'PART 1: exhaustive realizable pipelines '
          f'(A<=4 x prov x B<=3 x 8 sigmas x |w|<=6): {n_inst} instances')
    print(f'  mult-1 instances: {n_ok}')
    print(f'  THEOREM A (i) #surviving copies <= phases: '
          f'{viol_a} violations')
    print(f'  THEOREM A (ii+iii) LDS <= #surv*LDS(A)+1: '
          f'{viol_b} violations')
    print(f'  BASE-CASE CONJECTURE LDS <= 2*LDS(A)+1: '
          f'{viol_c} violations')
    print(f'  max LDS at mult 1: {max_lds_m1}')
    print(f'  max #surviving copies at mult 1: {max_cop_m1}')
    print(f'  content cross-check (every 4009th vs L.den): '
          f'{bad_content} mismatches')

    # random larger batch
    n_inst = n_ok = viol_a = viol_b = viol_c = 0
    for t in range(20000):
        la = rng.randrange(1, 9)
        A = ''.join(rng.choice('ab') for _ in range(la))
        vA = rng.sample(range(la + 4), la)
        A_lab = list(zip(A, vA))
        ldsA = PV.lds(vA)
        B = ''.join(rng.choice('ab')
                    for _ in range(rng.randrange(1, 7)))
        sig = rng.choice(sigs)
        w = ''.join(rng.choice('ab')
                    for _ in range(rng.randrange(1, 11)))
        surv = frag_sim(w, A_lab, sig, B)
        st = stats_of(surv)
        n_inst += 1
        if st['mult'] != 1:
            continue
        n_ok += 1
        O, J = V5.O_set(A, B), V5.J_set(A, B)
        ph = (1 + len(O)) * (1 + len(J)) + 1
        if st['ncop'] > ph:
            viol_a += 1
        if st['lds'] > st['ncop'] * ldsA + 1:
            viol_b += 1
        if st['lds'] > 2 * ldsA + 1:
            viol_c += 1
    print(f'  random larger batch (A<=8, B<=6, |w|<=10, any prov): '
          f'{n_inst} instances, {n_ok} mult-1, '
          f'violations a/b/c: {viol_a}/{viol_b}/{viol_c}')


# ------------------------------------------------------ PART 2a


def part2a():
    print()
    print('PART 2a: TEXT-LEVEL mult-1 chains (free injective labels):')
    print('  the concrete instance (predicted chain 4):')
    A = 'babababab'
    B = 'abababa'
    gaps = ['a', 'a', 'a', 'a', 'a']     # V0..V4, 4 copies
    T = V5.make_text_tagged(gaps, A)
    res, oj, _ = V6.residuals_of(T, B)
    print(f'    A={A} B={B} gaps={gaps}')
    print(f'    residuals: { {k: sorted(v) for k, v in res.items()} }')
    print(f'    max disjoint decreasing chain: '
          f'{V6.max_dec_chain(res)}')

    print('  hunt: aligned alternating texts, m in 5..13, n = m+2,')
    print('        copies 3..6, pre/post in {"", a, aa}:')
    found = defaultdict(int)
    best = (0, None)
    for m in (5, 7, 9, 11, 13):
        B = ('ab' * ((m + 1) // 2 + 1))[:m]
        n = m + 2
        A = ('ba' * (n // 2 + 1))[:n]
        for ncop in range(3, 7):
            for pre in ('', 'a', 'aa'):
                for post in ('', 'a', 'aa'):
                    gaps = [pre] + ['a'] * (ncop - 1) + [post]
                    T = V5.make_text_tagged(gaps, A)
                    res, oj, _ = V6.residuals_of(T, B)
                    mc = V6.max_dec_chain(res)
                    found[mc] += 1
                    if mc > best[0]:
                        best = (mc, (m, n, ncop, pre, post,
                                     {k: sorted(v)
                                      for k, v in res.items()}))
    print(f'    chain histogram: {dict(sorted(found.items()))}')
    print(f'    best: {best}')
    print('  NOTE: chain 4 at the TEXT level refutes the text-level')
    print('  statement of the base-case conjecture; the pipeline')
    print('  statement survives because of the label-supply (parity')
    print('  pigeonhole) -- see REPORT 7.x.')


# ------------------------------------------------------ PART 2b


def part2b():
    print()
    print('PART 2b: realizable pipeline hunt (variable needles):')
    import verify_round6_mult1_sweep as S6
    BS = S6.bs()
    PAT = S6.PATTERNS
    SIG = S6.SIGMAS
    hits = []
    best = (0, None)
    for pname, f in PAT:
        for bname, P in BS:
            for sigma in SIG:
                for j in range(2, 17):
                    w = f(j)
                    if len(w) <= 4:
                        continue
                    lab = PV.lab_input(w)
                    E = ('S', K(''), P, ('S', V(0), K(sigma), V(0)))
                    try:
                        atoms = PV.lden(E, (lab,))
                    except PV.Undefined:
                        continue
                    prov = PV.labels(atoms)
                    m = PV.mult(prov)
                    d = PV.lds(prov)
                    if m == 1 and d >= 3:
                        hits.append((pname, bname, sigma, j, d))
                    if m == 1 and d > best[0]:
                        best = (d, (pname, bname, sigma, j))
    print(f'  mult-1 rows with LDS >= 3: {len(hits)}')
    for h in hits[:10]:
        print(f'    {h}')
    print(f'  max LDS at mult 1: {best}')


# ------------------------------------------------------ PART 3


def part3():
    print()
    print('PART 3: crossings side probe -- E2 = [eps/init^2 X].[X/b]X:')
    import verify_round4_hinges as H
    E2 = make_E(2, 'b')
    f = lambda w: L.den(E2, (w,))
    for j in (4, 6, 8, 10):
        w = 'b' + 'ab' * j
        D = H.influence_of(f, w)
        st = H.describe(D)
        print(f'  j={j:2d} |w|={len(w):2d}: rows={st["rows"]} '
              f'len-changing(discarded)={st["lenrows"]} '
              f'perfect={st["match"]} crossings={st["crossings"]} '
              f'maxdisp={st["maxdisp"]} '
              f'chi/|w|={st["crossings"]/len(w):.2f}')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    part1()
    part2a()
    part2b()
    part3()

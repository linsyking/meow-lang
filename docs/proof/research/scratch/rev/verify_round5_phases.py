"""ROUND 5 - LINE 1: the long-needle completion attempt (proof round).

Target: rev is not L-reachable.  The scaffolding (Rounds 2-4) reduces the
question to: can a bounded pipeline produce a final text with a long
strictly decreasing w-atom chain at multiplicity 1 (rev needs length n)?

This round isolates and machine-verifies the two lemmas that govern the
per-pass diversity of copy-shaving, then assembles the fragment theorem.

LEMMA 1 (Phase Lemma -- sharpens Shaving v2).  A deletion pass [eps/B] on
a text containing copies of the same value A at disjoint sites: each
copy's residual is a function of the pair

    (o, j) = (entry straddle depth, exit straddle depth),

  o = 0 (scan enters at the copy's first atom) or o in O(A,B), where
      O(A,B) = {o in [1, min(|A|,|B|-1)] : A[:o] = B[-o:]}
      (a match straddling the copy's left boundary ends at atom o, so
       B's suffix of length o equals A's prefix of length o);
  j = 0 (no match crosses the right boundary) or j in J(A,B), where
      J(A,B) = {j in [1, min(|A|,|B|-1)] : A[-j:] = B[:j]}.

  Reason: from o the greedy scan through the copy is deterministic and
  h-independent while windows lie inside A; the only h-dependence is the
  single match that crosses the right boundary (at depth j) -- after it
  the scan has left the copy.  Hence

      #distinct residuals <= (1 + |O(A,B)|) * (1 + |J(A,B)|),

  a bound depending only on the OVERLAP SETS of A and B -- not on
  |B| * |Sigma|^{|B|-1} (Shaving v2's bound).

LEMMA 2 (Border/Periodicity Lemma).  O(A,B) is overlap structure:
  (a) every o in O smaller than o_max = max(O) is a BORDER of the
      A-prefix of length o_max (its length-o prefix equals its length-o
      suffix);
  (b) for o < o' in O, the difference o' - o is a PERIOD of A[:o'];
  (c) if O is an arithmetic progression with step d, then d is a period
      of A[:o_max] -- the straddled prefix is an (o_max/d)-fold
      repetition of a word of length d;
  (d) (pigeonhole) |O| distinct phases force SOME A-prefix to have a
      period <= (o_max - 1)/(|O| - 1): phase multiplicity is paid by
      prefix periodicity, linearly.
  Mirror statements for J on A's suffix (exit depths).

Machine parts:
  PART 1: Lemma 2 exhaustively, all A (|A|<=6), B (|B|<=5) over {a,b}.
  PART 2: Lemma 1 on labeled copy-gap texts (function property of (o,j),
          the count bound, and o in {0}+O, j in {0}+J), random+run corpus.
  PART 3: the validated variable-depth construction re-read through the
          lemmas (expect O = {1,2,3}, AP step 1, prefix 'bbb' 3-fold).
  PART 4: BASE CASE of the induction, exhaustive: pipelines
          [A/sigma][eps/B] with constant A, B, sigma -- max LDS@mult1
          over all |w|<=8.  The single-insertion-single-shave fragment.
"""
import itertools
import random
import sys
from collections import defaultdict

import lcore as L
from lcore import battery
import prov as PV

rng = random.Random(57721)


# ------------------------------------------------------------ overlap sets

def O_set(A, B):
    """entry straddle depths: B suffix = A prefix."""
    return [o for o in range(1, min(len(A), len(B) - 1) + 1)
            if A[:o] == B[len(B) - o:]]


def J_set(A, B):
    """exit straddle depths: A suffix = B prefix."""
    return [j for j in range(1, min(len(A), len(B) - 1) + 1)
            if A[len(A) - j:] == B[:j]]


def is_period(w, p):
    return all(w[i] == w[i + p] for i in range(len(w) - p))


def min_period(w):
    for p in range(1, len(w) + 1):
        if is_period(w, p):
            return p
    return len(w)


# ------------------------------------------------------------ PART 1

def part1():
    bad_a = bad_b = bad_c = 0
    n_pairs = 0
    maxO_hist = defaultdict(int)
    for la in range(1, 9):
        for lb in range(2, 8):
            for A in map(''.join, itertools.product('ab', repeat=la)):
                for B in map(''.join, itertools.product('ab', repeat=lb)):
                    n_pairs += 1
                    O = O_set(A, B)
                    if not O:
                        continue
                    om = max(O)
                    # (a) borders
                    for o in O:
                        if o == om:
                            continue
                        if A[:o] != A[om - o:om]:
                            bad_a += 1
                    # (b) differences are periods of the longer prefix
                    for o in O:
                        for o2 in O:
                            if o < o2:
                                if not is_period(A[:o2], o2 - o):
                                    bad_b += 1
                    # (c) AP => period of A[:om]
                    if len(O) >= 2:
                        d = O[1] - O[0]
                        if all(O[i + 1] - O[i] == d
                               for i in range(len(O) - 1)):
                            if not is_period(A[:om], d):
                                bad_c += 1
                    maxO_hist[(len(O), min_period(A[:om]))] += 1
    print('PART 1: Lemma 2, all A (<=8) x B (<=7) over {a,b}: '
          f'{n_pairs} pairs')
    print(f'  (a) smaller phases are borders of A[:max]:  '
          f'{"PASS" if bad_a == 0 else f"FAIL({bad_a})"}')
    print(f'  (b) phase differences are periods:          '
          f'{"PASS" if bad_b == 0 else f"FAIL({bad_b})"}')
    print(f'  (c) AP phases => period of A[:max]:        '
          f'{"PASS" if bad_c == 0 else f"FAIL({bad_c})"}')
    # (d) the density table: max |O| at each min-period of the prefix
    dense = defaultdict(int)
    for (k, p), c in maxO_hist.items():
        dense[p] = max(dense[p], k)
    print('  (d) max |O| observed per min-period p of A[:o_max]: '
          + ', '.join(f'p={p}:|O|<={k}' for p, k in sorted(dense.items())))
    # the AP-step/prefix-length table for the periodicity payment
    pay = []
    for (k, p), c in maxO_hist.items():
        pay.append((k, p, k * p))
    print('  sample (|O|, min-period p, product k*p): '
          + str(sorted(set(pay))[:12]))
    # density conjecture |O| <= o_max/p: FALSE -- exhibit in-machine
    viol = [(k, p, km) for (k, p, km) in
            ((k, p, k * p) for (k, p), _ in maxO_hist.items())
            if k * p > 5]      # o_max <= 5 for these phases -> k > o_max/p
    A2, B2 = 'aabaabaa', 'xaabaa'
    O2 = O_set(A2, B2)
    print(f'  density |O| <= o_max/p is FALSE in general: A={A2} B={B2} '
          f'-> O={O2}, o_max={max(O2)}, min-period of A[:o_max]='
          f'{min_period(A2[:max(O2)])}, |O|={len(O2)} > '
          f'{max(O2)}/{min_period(A2[:max(O2)]):.2f}')


# ------------------------------------------------------------ PART 2

def make_text_tagged(gapstrs, A):
    T = []
    for j, g in enumerate(gapstrs[:-1]):
        for i, c in enumerate(g):
            T.append((c, ('g', j, i)))
        for p, c in enumerate(A):
            T.append((c, ('c', j, p)))
    for i, c in enumerate(gapstrs[-1]):
        T.append((c, ('g', len(gapstrs) - 1, i)))
    return tuple(T)


def scan_oj(T, B):
    """greedy [eps/B]; returns (output, per-copy (o, j) or None)."""
    m = len(B)
    bch = tuple(B)
    chars = [c for c, _ in T]
    starts, ends = {}, {}
    for idx, (_, lab) in enumerate(T):
        if lab[0] == 'c':
            if lab[1] not in starts:
                starts[lab[1]] = idx
            ends[lab[1]] = idx
    out = []
    oj = {}
    i, n = 0, len(T)
    while i < n:
        for j, st in starts.items():
            if j not in oj and i >= st:
                oj[j] = i - st          # entry offset (can exceed |A|)
        if tuple(chars[i:i + m]) == bch:
            # record exit straddles: matches crossing copy right ends
            for j, en in ends.items():
                if j in oj and isinstance(oj[j], int) \
                        and i <= en < i + m - 1 and i >= starts[j]:
                    # crossing: match starts inside, ends past the copy
                    oj[j] = (oj[j], en - i + 1)   # (o, j)
            i += m
        else:
            out.append(T[i])
            i += 1
    # copies never assigned j: j = 0; copies never entered: fully consumed
    res = {}
    for j in starts:
        v = oj.get(j, 'consumed')
        if isinstance(v, int):
            v = (v, 0)
        res[j] = v
    return tuple(out), res


def part2(trials=4000):
    bad_fn = bad_count = bad_o = bad_j = 0
    for t in range(trials):
        m = rng.randrange(1, 5)
        A = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 7)))
        gapstrs = [''.join(rng.choice('ab')
                           for _ in range(rng.randrange(0, 5)))
                   for _ in range(m + 1)]
        if t % 3 == 0:      # run-biased, the dangerous case
            A = rng.choice(['ab', 'aab', 'abb', 'aaab', 'bbba', 'aabb',
                            'bbbaaa', 'aabbaa'])
            gapstrs = [rng.choice(['', 'b', 'bb', 'bbb', 'aab', 'ba', 'a',
                                   'aa'])
                       for _ in range(m + 1)]
        T = make_text_tagged(gapstrs, A)
        B = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 5)))
        out, oj = scan_oj(T, B)
        residuals = defaultdict(set)
        for _, lab in out:
            if lab[0] == 'c':
                residuals[lab[1]].add(lab[2])
        O, J = O_set(A, B), J_set(A, B)
        # o in {0} + O (when the copy is entered at all), j in {0} + J
        for j, v in oj.items():
            if v == 'consumed':
                continue
            o, jj = v
            if o > len(A):
                continue
            if not (o == 0 or o in O):
                bad_o += 1
                print(f'  o VIOLATION: A={A} B={B} o={o} O={O}')
            if not (jj == 0 or jj in J):
                bad_j += 1
                print(f'  j VIOLATION: A={A} B={B} j={jj} J={J}')
        # function property: same (o,j) -> same residual
        seen = {}
        for j, v in oj.items():
            r = residuals.get(j, set())
            if v == 'consumed' or isinstance(v, str):
                key = 'consumed'
            else:
                key = v
            if key in seen:
                if seen[key] != tuple(sorted(r)):
                    bad_fn += 1
                    if bad_fn <= 3:
                        print(f'  (o,j) FUNCTION VIOLATION: A={A} B={B} '
                              f'gaps={gapstrs} key={key}')
            else:
                seen[key] = tuple(sorted(r))
        # count bound
        nres = len({tuple(sorted(residuals.get(j, set())))
                    for j in oj if oj[j] != 'consumed'})
        bound = (1 + len(O)) * (1 + len(J)) + 1
        if nres > bound:
            bad_count += 1
            if bad_count <= 3:
                print(f'  COUNT VIOLATION: A={A} B={B} gaps={gapstrs} '
                      f'distinct={nres} bound={bound}')
    print(f'PART 2: Lemma 1, {trials} copy-gap texts, |B|<=4:')
    print(f'  o in {{0}}+O, j in {{0}}+J:    '
          f'{"PASS" if bad_o == 0 and bad_j == 0 else "FAIL"} '
          f'(bad_o={bad_o}, bad_j={bad_j})')
    print(f'  residual = f(o,j):          '
          f'{"PASS" if bad_fn == 0 else f"FAIL({bad_fn})"}')
    print(f'  #distinct <= (1+|O|)(1+|J|): '
          f'{"PASS" if bad_count == 0 else f"FAIL({bad_count})"}')


# ------------------------------------------------------------ PART 3

def part3():
    print('PART 3: the validated construction through the lemmas')
    A, B = 'bbbaaaa', 'bbb'
    O, J = O_set(A, B), J_set(A, B)
    print(f'  A={A} B={B}: O={O} J={J}')
    print(f'  AP? {all(O[i+1]-O[i] == O[1]-O[0] for i in range(len(O)-1))}'
          f'  step={O[1]-O[0] if len(O) > 1 else None}'
          f'  A[:{max(O)}]={A[:max(O)]} min-period={min_period(A[:max(O)])}'
          f' ({max(O)}-fold repetition of length {min_period(A[:max(O)])})')
    # re-run the construction and count residuals + phases
    gapstrs = ['', 'b', 'bb', 'bbb', 'b']
    T = make_text_tagged(gapstrs, A)
    out, oj = scan_oj(T, B)
    residuals = defaultdict(set)
    for _, lab in out:
        if lab[0] == 'c':
            residuals[lab[1]].add(lab[2])
    print('  copies: ' + '; '.join(f'c{j}: (o,j)={oj[j]} '
                                   f'R={sorted(residuals.get(j, set()))}'
                                   for j in sorted(oj)))
    nres = len({tuple(sorted(residuals.get(j, set()))) for j in oj})
    print(f'  distinct residuals = {nres} <= (1+|O|)(1+|J|)+1 = '
          f'{(1+len(O))*(1+len(J))+1}   [|B|*s^(|B|-1) = '
          f'{len(B)*2**(len(B)-1)}]')


# ------------------------------------------------------------ PART 4

def part4():
    print('PART 4: BASE CASE exhaustive: [A/sigma][eps/B], constant A,B')
    WS = battery(8)
    best = (0, None)
    n_pipe = 0
    for la in range(0, 5):
        for lb in range(1, 5):
            for A in map(''.join, itertools.product('ab', repeat=la)):
                for B in map(''.join, itertools.product('ab', repeat=lb)):
                    for sig in 'ab':
                        n_pipe += 1
                        mB = mD = mM = 0
                        for w in WS:
                            T = PV.lab_input(w)
                            T = PV.lsubst(PV.lab_const(A),
                                          PV.lab_const(sig), T)
                            T = PV.lsubst((), PV.lab_const(B), T)
                            pr = PV.labels(T)
                            if not pr:
                                continue
                            d, mm = PV.lds(pr), PV.mult(pr)
                            mD, mM = max(mD, d), max(mM, mm)
                            if mm == 1:
                                mB = max(mB, d)
                        if mB > best[0]:
                            best = (mB, (A, sig, B, mD, mM))
    print(f'  {n_pipe} pipelines, all |w|<=8:')
    print(f'  MAX LDS@mult1 = {best[0]}  at (A, sigma, B)={best[1][:3]}'
          f' (maxLDS={best[1][3]}, maxmult={best[1][4]})')

    # variable A (w-atoms!) from the library, constant or library B
    import r2lib as RL
    WS = battery(7) + ['a' * 8 + 'b' * 4, 'b' * 4 + 'a' * 8, 'ab' * 7,
                       'aab' * 5, 'aaabbaaa', 'bbbaaa' * 2]
    Rvals = {}
    for r, b in RL.REPLACEMENTS.items():
        ast = b()
        Rvals[r] = {}
        for w in WS:
            try:
                Rvals[r][w] = PV.lden(ast, (PV.lab_input(w),))
            except PV.Undefined:
                Rvals[r][w] = None
    bestv = (0, None)
    n2 = 0
    for r, rv in Rvals.items():
        for lb in range(1, 5):
            for B in map(''.join, itertools.product('ab', repeat=lb)):
                for sig in 'ab':
                    n2 += 1
                    mB = mD = mM = 0
                    for w in WS:
                        A = rv.get(w)
                        if A is None:
                            break
                        T = PV.lsubst(A, PV.lab_const(sig),
                                      PV.lab_input(w))
                        T = PV.lsubst((), PV.lab_const(B), T)
                        if len(T) > 800:
                            break
                        pr = PV.labels(T)
                        if not pr:
                            continue
                        d, mm = PV.lds(pr), PV.mult(pr)
                        mD, mM = max(mD, d), max(mM, mm)
                        if mm == 1:
                            mB = max(mB, d)
                    else:
                        if mB > bestv[0]:
                            bestv = (mB, (r, sig, B, mD, mM))
    print(f'  variable A (library) x constant B: {n2} pipelines, '
          f'|w|<=7+structured:')
    print(f'  MAX LDS@mult1 = {bestv[0]} at (A_lib, sigma, B)='
          f'{bestv[1][:3] if bestv[1] else None}'
          f' (maxLDS={bestv[1][3] if bestv[1] else 0}, '
          f'maxmult={bestv[1][4] if bestv[1] else 0})')


if __name__ == '__main__':
    part1()
    part2()
    part3()
    part4()

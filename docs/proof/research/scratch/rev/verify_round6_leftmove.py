"""ROUND 6 - prove the Left-Move Wall (priority 1).

WALL (clean statement).  In a text V0 A V1 A ... Am Vm of copies of the
same value A at disjoint sites, under the greedy deletion pass [eps/B],
there do NOT exist three copies c1 < c2 < c3 and positions
p1 in R_c1, p2 in R_c2, p3 in R_c3 with p1 > p2 > p3 and the three
residuals pairwise disjoint.  (Weaker hypothesis than round 5's
"all residuals pairwise disjoint" -- no constraint on the other copies.)

PART A: persisted re-verification of the wall on round 5's exhaustive
  domain (1,152,480 texts) + the count reconciliation: under the
  convention "all nonempty residuals pairwise disjoint" the qualifying
  count is reported alongside "exists a disjoint pair".

PART B: THE TARGETED TRIPLE HUNT.  The phase algebra (round 5 sketch,
  this round's derivation) says a triple's stretches between picks are
  tiled by B-blocks: A[p+1:] gap1 A[:q] = B^k1, A[q+1:] gap2 A[:r] =
  B^k2 -- the whole habitat is B^INFINITY-STRUCTURED.  Two attacks:
   (B1) the ALL-STRADDLE SKELETON SOLVER: enumerate B, n, p > q > r,
        solve the six overlap equations
          A[:p] = B^inf-suffix(p),  A[p+1:] = B^inf-prefix,
          (same at q, r)
        fill the gaps with the forced B^inf factors, build the text,
        run the real greedy scan, and look for the triple.
   (B2) random B^inf-structured texts: A and all gaps drawn as factors
        of B^inf, sizes beyond round 5 (n <= 10, m <= 8, 4 copies).
  A found triple REFUTES the wall (the base-case proposition then needs
  size-dependent hypotheses); none found is the wall surviving its
  predicted habitat.

PART C: classification of realized left-move PAIRS (the proof's case
  analysis): (o, j) states, straddle vs internal consumption forms.
"""
import itertools
import random
from collections import defaultdict

import verify_round5_phases as V5

rng = random.Random(628318)


def residuals_of(T, B):
    out, oj = V5.scan_oj(T, B)
    res = {j: {l[2] for _, l in out if l[0] == 'c' and l[1] == j}
           for j in set(l[1] for _, l in T if l[0] == 'c')}
    return res, oj, out


def has_triple(res):
    """three copies in order with pairwise-disjoint residuals and
    strictly decreasing picks."""
    copies = sorted(j for j in res if res[j])
    for a, b, c in itertools.combinations(copies, 3):
        Ra, Rb, Rc = res[a], res[b], res[c]
        if Ra & Rb or Rb & Rc or Ra & Rc:
            continue
        for p in Ra:
            for q in Rb:
                if q >= p:
                    continue
                for r in Rc:
                    if r < q:
                        return True, (a, b, c, p, q, r)
    return False, None


def max_dec_chain(res):
    copies = sorted(j for j in res if res[j])
    # DP: state = set of (last_pos) per residual used?  need pairwise
    # disjointness among used copies -> small: brute force combos of 3
    # is enough for the wall; chain length via DP with subset check
    # (copied from round 5 but requiring disjointness of used copies)
    best = 0
    n = len(copies)
    # DP over copies with last position AND used-copy set (n small)
    memo = {}

    def rec(i, last, used_mask):
        nonlocal best
        if i == n:
            return 0
        key = (i, last, used_mask)
        if key in memo:
            return memo[key]
        out = rec(i + 1, last, used_mask)
        c = copies[i]
        ok = True
        for j2 in range(i):
            if used_mask >> j2 & 1 and res[copies[j2]] & res[c]:
                ok = False
                break
        if ok:
            for p in sorted(res[c], reverse=True):
                if p < last:
                    out = max(out, 1 + rec(i + 1, p,
                                           used_mask | (1 << i)))
        memo[key] = out
        return out

    return rec(0, float('inf'), 0)


# ------------------------------------------------------------ PART A

def part_a():
    n_texts = n_all = n_any = 0
    triples = 0
    ex = None
    for la in range(1, 5):
        As = [''.join(x) for x in itertools.product('ab', repeat=la)]
        for lb in range(1, 4):
            Bs = [''.join(x) for x in itertools.product('ab', repeat=lb)]
            for A in As:
                for B in Bs:
                    for m in (2, 3):
                        gs = [''.join(x) for x in itertools.product(
                            'ab', repeat=2)] + ['', 'a', 'b']
                        for gaps in itertools.product(gs, repeat=m + 1):
                            n_texts += 1
                            T = V5.make_text_tagged(list(gaps), A)
                            res, oj, _ = residuals_of(T, B)
                            rs = [R for R in res.values() if R]
                            if len(rs) >= 2:
                                if all(not (x & y) for x, y in
                                       itertools.combinations(rs, 2)):
                                    n_all += 1
                                if any(not (x & y) for x, y in
                                       itertools.combinations(rs, 2)):
                                    n_any += 1
                            t, e = has_triple(res)
                            if t:
                                triples += 1
                                ex = ex or (A, B, list(gaps), e)
    print(f'PART A (persisted wall re-verification):')
    print(f'  domain: |A|<=4, |B|<=3, gaps<=2, m in (2,3): {n_texts} texts')
    print(f'  qualifying (ALL nonempty residuals disjoint): {n_all}')
    print(f'  qualifying (EXISTS a disjoint pair): {n_any}')
    print(f'  TRIPLES (3 copies, disjoint, decreasing picks): {triples}')
    if ex:
        print(f'  EXAMPLE: {ex}')


# ------------------------------------------------------------ PART B1

def beta(B, i):
    m = len(B)
    return B[i % m]


def solve_all_straddle(B, n, p, q, r):
    """Solve the six equations for A; return A or None."""
    m = len(B)
    A = [None] * n
    for t in (p, q, r):
        for i in range(t):            # A[:t] = B^inf-suffix(t)
            v = beta(B, i - t)
            if A[i] not in (None, v):
                return None
            A[i] = v
        for i in range(t + 1, n):     # A[t+1:] = B^inf-prefix
            v = beta(B, i - t - 1)
            if A[i] not in (None, v):
                return None
            A[i] = v
    if None in A:
        return None
    # picks must be non-matching atoms: A[pick] != B[-1]
    for t in (p, q, r):
        if A[t] == B[-1]:
            return None
    return ''.join(A)


def part_b1():
    found = 0
    tried = 0
    best = ('', None)
    for lb in range(2, 7):
        for B in map(''.join, itertools.product('ab', repeat=lb)):
            m = lb
            for n in range(3, min(2 * m, 11)):
                lo, hi = max(0, n - m), min(m, n) - 1
                for p in range(lo, hi + 1):      # straddle ranges
                    for q in range(lo, p):
                        for r in range(lo, q):
                            A = solve_all_straddle(B, n, p, q, r)
                            if A is None:
                                continue
                            # gaps: forced factors of B^inf
                            need1 = (-(n - p - 1 - q)) % m
                            need2 = (-(n - q - 1 - r)) % m
                            for t1 in range(3):
                                g1 = need1 + t1 * m if need1 or t1 else 0
                                for t2 in range(3):
                                    g2 = need2 + t2 * m if need2 or t2 \
                                        else 0
                                    gap1 = ''.join(beta(B, n - p - 1 + s)
                                                   for s in range(g1))
                                    gap2 = ''.join(beta(B, n - q - 1 + s)
                                                   for s in range(g2))
                                    v0 = ''.join(beta(B, s)
                                                 for s in range(m - p))
                                    v4 = ''.join(beta(B, n - r - 1 + s)
                                                 for s in range(
                                                     m - (n - r - 1)))
                                    T = V5.make_text_tagged(
                                        [v0, gap1, gap2, v4], A)
                                    tried += 1
                                    res, oj, _ = residuals_of(T, B)
                                    t, e = has_triple(res)
                                    if t:
                                        found += 1
                                        if found <= 5:
                                            print(f'  TRIPLE FOUND: B={B} '
                                                  f'n={n} p,q,r={p,q,r} '
                                                  f'A={A} gaps='
                                                  f'{v0}|{gap1}|{gap2}|'
                                                  f'{v4} {e}')
                                    mc = max_dec_chain(res)
                                    if best[1] is None or \
                                            mc > best[1][-1]:
                                        best = (B, (n, p, q, r, A, mc))
    print(f'PART B1: all-straddle skeleton solver: {tried} constructed '
          f'texts')
    print(f'  TRIPLES: {found}')
    print(f'  (any chain>1 examples recorded: {best})')


# ------------------------------------------------------------ PART B2

def part_b2(trials=300000):
    found = 0
    tried = 0
    chains = defaultdict(int)
    for t in range(trials):
        lb = rng.randrange(2, 9)
        B = ''.join(rng.choice('ab') for _ in range(lb))
        m = lb
        n = rng.randrange(3, 11)

        def factor(lo, ln):
            return ''.join(beta(B, lo + s) for s in range(ln))
        A = factor(rng.randrange(m), n)
        if rng.random() < 0.3:    # inject non-matching breaks
            A = list(A)
            for _ in range(rng.randrange(1, 3)):
                i = rng.randrange(n)
                A[i] = 'a' if A[i] == 'b' else 'b'
            A = ''.join(A)
        mcop = rng.randrange(2, 5)
        gaps = [factor(rng.randrange(m), rng.randrange(0, 7))
                for _ in range(mcop + 1)]
        if rng.random() < 0.5:   # run-bias: make gaps B-suffix/prefix
            gaps = [''.join(rng.choice(B[-1] + 'ab') * 1
                            for _ in range(rng.randrange(0, 6)))
                    for _ in range(mcop + 1)]
        T = V5.make_text_tagged(gaps, A)
        tried += 1
        res, oj, _ = residuals_of(T, B)
        tr, e = has_triple(res)
        if tr:
            found += 1
            if found <= 5:
                print(f'  TRIPLE FOUND (B2): B={B} A={A} gaps={gaps} {e}')
        chains[max_dec_chain(res)] += 1
    print(f'PART B2: {tried} B^inf-structured random texts '
          f'(n<=10, m<=8, <=4 copies):')
    print(f'  TRIPLES: {found}')
    print(f'  max-decreasing-chain histogram: {dict(sorted(chains.items()))}')


# ------------------------------------------------------------ PART C

def part_c(trials=8000):
    forms = defaultdict(int)
    for t in range(trials):
        m = rng.randrange(2, 5)
        A = ''.join(rng.choice('ab') for _ in range(rng.randrange(2, 7)))
        gapstrs = [''.join(rng.choice('ab')
                           for _ in range(rng.randrange(0, 5)))
                   for _ in range(m + 1)]
        T = V5.make_text_tagged(gapstrs, A)
        B = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 5)))
        res, oj, _ = residuals_of(T, B)
        for c1 in range(m):
            for c2 in range(c1 + 1, m):
                if res.get(c1) and res.get(c2) and not (res[c1] & res[c2]):
                    if any(q < p for p in res[c1] for q in res[c2]):
                        v1, v2 = oj.get(c1), oj.get(c2)
                        forms[(v1, v2)] += 1
    print('PART C: left-move pairs (disjoint) by (o,j) state pairs:')
    for k, v in sorted(forms.items(), key=lambda kv: -kv[1])[:14]:
        print(f'  {k}: {v}')


if __name__ == '__main__':
    part_a()
    part_b1()
    part_b2()
    part_c()

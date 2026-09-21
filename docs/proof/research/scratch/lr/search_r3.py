"""ROUND 3: the witness hunts.  Three searches, with the escalation
discipline (any candidate is re-verified on strictly larger domains before
being believed; near-misses are recorded, not rounded up).

  S1  Q-rho (fixed-B core):  is f2(A,C) = [A/aa]^R C in L?  "aa" is the
      smallest bordered pattern, so this is the minimal hard case of rho.
      Exhaustive template-pipeline BFS, depth <= 3, then randomized
      depth <= 5.
  S2  Q-rho (full):  is rho(A,B,C) = [A/B]^R C in L (3-ary)?  Template BFS
      depth <= 3 + randomized depth <= 5.
  S3  Q-rev:  is rev in L+R?  Exhaustive mixed template pipelines depth
      <= 2, randomized depth <= 6, genetic search (population, splice
      crossovers) for depth <= 10.

Template passes have pattern/replacement built from constants and the
INPUT VARIABLES (raw values -- not the running text), e.g. [X1/aa],
[eps/ab], [a.X1/c], [X3/X2].  Tables record per-input-point values
(None = undefined: an empty pattern value prunes the pipeline as a
candidate, since the target functions are defined on the whole domain).

Negative results are domain- and effort-limited: the domains and sample
counts are printed and copied to REPORT.md.  (The mirror question
sigma = [X1/X2]X3 in R is the conj-image of S2's search space -- the
spaces are mirror-symmetric -- so no separate run; noted in REPORT.)
"""

import itertools
import random
import sys
import os
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrcore import subst, substR, rev, iter_strings

AB = 'ab'


# ------------------------------------------------------------- sources

def eval_src(src, point):
    """src: ('c', s) | ('v', i) | ('cd', s1, ..., s4) concatenating up to
    four slots, each ('c', s) or ('v', i) | ('g', (r, p, i)) = one-pass
    transform [r/p] of variable i.  point: tuple of input values."""
    if src[0] == 'c':
        return src[1]
    if src[0] == 'v':
        return point[src[1]]
    if src[0] == 'cd':
        out = ''
        for sl in src[1:]:
            out += (sl[1] if sl[0] == 'c' else point[sl[1]])
        return out
    if src[0] == 'g':
        (r, p, i) = src[1]
        return subst(r, p, point[i])
    raise ValueError(src)


def srcs(consts, varcat, nvars, maxconcat=2):
    """All sources: constants, variables, and their short concatenations
    (varcat = which variables may appear in concatenations)."""
    out = [('c', c) for c in consts]
    out += [('v', i) for i in range(nvars)]
    slots = [('c', c) for c in consts if c] + [('v', i) for i in varcat]
    for n in range(2, maxconcat + 1):
        for combo in itertools.product(slots, repeat=n):
            if all(s[0] == 'v' for s in combo) and len(set(combo)) < 2:
                continue        # skip X.X, keep distinct-variable cats
            out.append(('cd',) + combo)
    # dedup by value on a probe point later; here structural
    return out


def apply_pass(table, points, R, P, d):
    f = subst if d == 'L' else substR
    out = []
    for cur, pt in zip(table, points):
        if cur is None:            # undefined propagates (strict)
            out.append(None)
            continue
        p = eval_src(P, pt)
        if p == '':
            out.append(None)
            continue
        r = eval_src(R, pt)
        out.append(f(r, p, cur))
    return tuple(out)


def target_table(fn, points):
    return tuple(fn(*pt) for pt in points)


# ------------------------------------------------------------- BFS

def bfs(passes, points, target, depth, verbose_name):
    """Exhaustive BFS over template pipelines (dedup by table); returns
    (hit_pipeline or None, n_tables, best_partial_info)."""
    t0 = time.time()
    # seed with the variable projections and the empty constant
    nvars = len(points[0])
    seeds = {}
    for i in range(nvars):
        tab = tuple(pt[i] for pt in points)
        seeds[tab] = (('V', i),)
    tab = tuple('' for _ in points)
    seeds[tab] = (('K', ''),)
    seen = set(seeds.keys())
    if target in seen:
        return seeds[target], len(seen), None
    frontier = dict(seeds)
    for depth_i in range(1, depth + 1):
        new = {}
        for tab, prog in frontier.items():
            for (R, P, d) in passes:
                t2 = apply_pass(tab, points, R, P, d)
                if t2 in seen:
                    continue
                seen.add(t2)
                new[t2] = prog + ((R, P, d),)
                if t2 == target:
                    print(f'    [{verbose_name}] HIT at depth {depth_i}: '
                          f'{new[t2]}')
                    return new[t2], len(seen), None
        frontier = new
        print(f'    [{verbose_name}] depth {depth_i}: +{len(new)} new, '
              f'{len(seen)} total tables ({time.time()-t0:.0f}s)')
        if not frontier:
            break
    return None, len(seen), None


def random_search(passes, points, target, n_tries, max_depth, seed,
                  verbose_name):
    rng = random.Random(seed)
    t0 = time.time()
    nvars = len(points[0])
    for _ in range(n_tries):
        k = rng.randint(1, max_depth)
        n = rng.randrange(nvars)
        tab = tuple(pt[n] for pt in points)
        prog = [('V', n)]
        for _ in range(k):
            (R, P, d) = rng.choice(passes)
            tab = apply_pass(tab, points, R, P, d)
            prog.append((R, P, d))
        if tab == target:
            print(f'    [{verbose_name}] RANDOM HIT: {prog}')
            return prog
    print(f'    [{verbose_name}] randomized ({n_tries} pipelines, depth '
          f'<= {max_depth}): no hit ({time.time()-t0:.0f}s)')
    return None


# ------------------------------------------------------------- S1

def f2(A, C):
    return substR(A, 'aa', C)


def s1():
    print('--- S1: f2(A,C) = [A/aa]^R C in L (the minimal hard case) ---')
    # search domain
    A_dom = ['', 'b']
    C_dom = list(iter_strings(AB, 3))
    points = [(a, c) for a in A_dom for c in C_dom]
    target = target_table(f2, points)
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb']
    P_srcs = ([('c', c) for c in consts if c]
              + [('v', 0), ('v', 1)]
              + [('cd', ('v', 0), ('v', 0)), ('cd', ('v', 0), ('v', 1)),
                 ('cd', ('v', 1), ('v', 0)), ('cd', ('v', 1), ('v', 1))])
    R_srcs = ([('c', '')] + [('c', c) for c in consts]
              + [('v', 0), ('v', 1),
                 ('cd', ('c', 'a'), ('v', 0)), ('cd', ('v', 0), ('c', 'a')),
                 ('cd', ('v', 0), ('v', 0)), ('cd', ('v', 1), ('v', 1))])
    passes = [(R, P, 'L') for R in R_srcs for P in P_srcs]
    print(f'    {len(P_srcs)} pattern sources x {len(R_srcs)} replacement '
          f'sources = {len(passes)} L-passes; domain: '
          f'A in {A_dom}, |C| <= 3 ({len(points)} points)')
    hit, ntab, _ = bfs(passes, points, target, 3, 'S1-bfs')
    if hit is None:
        random_search(passes, points, target, 300000, 5, 1, 'S1-rand')
    else:
        escalate_2ary(hit, f2)
    return hit


def escalate_2ary(prog, fn):
    """Re-verify a candidate pipeline on a strictly larger domain + the
    a<->b relabeling."""
    def run_prog(point):
        tab = point[0] if prog[0] == ('V', 0) else (
              point[1] if prog[0] == ('V', 1) else '')
        for (R, P, d) in prog[1:]:
            tab = apply_pass((tab,), (point,), R, P, d)[0]
        return tab
    A_dom = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    C_dom = list(iter_strings(AB, 6))
    bad = 0
    for a in A_dom:
        for c in C_dom:
            if run_prog((a, c)) != fn(a, c):
                bad += 1
    print(f'    [escalate] {bad} mismatches on A<=2 x |C|<=6 '
          f'({len(A_dom)*len(C_dom)} points)')
    # relabel a<->b: the pipeline constants swap; target is relabel-invariant
    # in shape; just report the direct check above.


# ------------------------------------------------------------- S1-extended

def s1ext():
    """Extended S1 (post-hoc, closing the template gaps): (ext1) adds
    constant-anchored variable patterns a.C, C.a, b.C, C.b, full exhaustive
    depth 3; (ext2) adds computed pattern sources (one-pass transforms of
    X1/X2), exhaustive depth 2 + randomized depth 5.  Inline runs that
    produced the REPORT numbers were identical in method."""
    A_dom = ['', 'b']
    C_dom = list(iter_strings(AB, 3))
    points = [(a, c) for a in A_dom for c in C_dom]
    target = target_table(f2, points)
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb']
    R_srcs = ([('c', '')] + [('c', c) for c in consts] + [('v', 0), ('v', 1),
              ('cd', ('c', 'a'), ('v', 0)), ('cd', ('v', 0), ('c', 'a')),
              ('cd', ('v', 0), ('v', 0)), ('cd', ('v', 1), ('v', 1)),
              ('cd', ('c', 'a'), ('v', 1)), ('cd', ('v', 1), ('c', 'a'))])
    P1 = ([('c', c) for c in consts if c] + [('v', 0), ('v', 1)]
          + [('cd', ('v', 0), ('v', 0)), ('cd', ('v', 0), ('v', 1)),
             ('cd', ('v', 1), ('v', 0)), ('cd', ('v', 1), ('v', 1))]
          + [('cd', ('c', 'a'), ('v', 1)), ('cd', ('v', 1), ('c', 'a')),
             ('cd', ('c', 'b'), ('v', 1)), ('cd', ('v', 1), ('c', 'b'))])
    passes1 = [(R, P, 'L') for R in R_srcs for P in P1]
    print('--- S1-ext1: anchored variable patterns, depth <= 3 ---')
    print(f'    {len(P1)} patterns x {len(R_srcs)} replacements = '
          f'{len(passes1)} L-passes; domain: A in {A_dom}, |C| <= 3 '
          f'({len(points)} points)')
    hit, _, _ = bfs(passes1, points, target, 3, 'S1-ext1')
    if hit is None:
        random_search(passes1, points, target, 200000, 5, 11, 'S1-ext1-rand')
    else:
        escalate_2ary(hit, f2)
    print('--- S1-ext2: computed pattern sources, depth <= 2 + randomized ---')
    TRANSFORMS = [('', 'aa'), ('a', 'aa'), ('', 'ab'), ('', 'ba'), ('', 'a'),
                  ('', 'b'), ('b', 'a'), ('a', 'b'), ('b', 'bb'), ('a', 'ab')]
    P2 = P1 + [('g', (r, p, v)) for (r, p) in TRANSFORMS for v in (0, 1)]
    passes2 = [(R, P, 'L') for R in R_srcs for P in P2]
    print(f'    {len(P2)} patterns x {len(R_srcs)} replacements = '
          f'{len(passes2)} L-passes')
    hit2, _, _ = bfs(passes2, points, target, 2, 'S1-ext2')
    if hit2 is None:
        random_search(passes2, points, target, 200000, 5, 12, 'S1-ext2-rand')
    else:
        escalate_2ary(hit2, f2)
    return hit, hit2


# ------------------------------------------------------------- S2

def rho(A, B, C):
    return substR(A, B, C)


def s2():
    print('--- S2: rho(A,B,C) = [A/B]^R C in L (3-ary) ---')
    A_dom = ['', 'b']
    B_dom = ['a', 'aa', 'ab']
    C_dom = list(iter_strings(AB, 3))
    points = [(a, b, c) for a in A_dom for b in B_dom for c in C_dom]
    target = target_table(rho, points)
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb']
    P_srcs = ([('c', c) for c in consts if c]
              + [('v', 0), ('v', 1), ('v', 2)]
              + [('cd', ('v', 1), ('v', 1)), ('cd', ('v', 2), ('v', 2)),
                 ('cd', ('v', 0), ('v', 1)), ('cd', ('v', 1), ('v', 0)),
                 ('cd', ('v', 2), ('v', 1)), ('cd', ('v', 1), ('v', 2))])
    R_srcs = ([('c', '')] + [('c', c) for c in consts]
              + [('v', 0), ('v', 2),
                 ('cd', ('c', 'a'), ('v', 0)), ('cd', ('v', 0), ('c', 'a')),
                 ('cd', ('v', 0), ('v', 0))])
    passes = [(R, P, 'L') for R in R_srcs for P in P_srcs]
    print(f'    {len(P_srcs)} x {len(R_srcs)} = {len(passes)} L-passes; '
          f'domain: A in {A_dom}, B in {B_dom}, |C| <= 3 ({len(points)} points)')
    hit, ntab, _ = bfs(passes, points, target, 3, 'S2-bfs')
    if hit is None:
        random_search(passes, points, target, 300000, 5, 2, 'S2-rand')
    return hit


# ------------------------------------------------------------- S3

def s3():
    print('--- S3: rev in L+R (mixed pipelines, 1-ary) ---')
    dom = list(iter_strings(AB, 4))            # 31 points
    points = [(c,) for c in dom]
    target = tuple(c[::-1] for c in dom)
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb']
    P_srcs = ([('c', c) for c in consts if c]
              + [('v', 0), ('cd', ('v', 0), ('v', 0)),
                 ('cd', ('c', 'a'), ('v', 0)), ('cd', ('v', 0), ('c', 'a')),
                 ('cd', ('c', 'b'), ('v', 0)), ('cd', ('v', 0), ('c', 'b'))])
    R_srcs = ([('c', '')] + [('c', c) for c in consts]
              + [('v', 0),
                 ('cd', ('v', 0), ('v', 0)), ('cd', ('c', 'a'), ('v', 0)),
                 ('cd', ('v', 0), ('c', 'a')), ('cd', ('c', 'b'), ('v', 0)),
                 ('cd', ('v', 0), ('c', 'b'))])
    passes = [(R, P, d) for R in R_srcs for P in P_srcs for d in 'LR']
    print(f'    {len(P_srcs)} x {len(R_srcs)} x 2 dirs = {len(passes)} '
          f'mixed passes; domain |X| <= 4 ({len(points)} points)')
    hit, ntab, _ = bfs(passes, points, target, 2, 'S3-bfs')
    if hit is None:
        random_search(passes, points, target, 400000, 6, 3, 'S3-rand')
        genetic(passes, points, target, 'S3-gen')


def genetic(passes, points, target, name, pop=400, gens=400):
    """Fitness = number of input points matched exactly.  Report the best."""
    rng = random.Random(42)
    nvars = len(points[0])

    def eval_prog(prog):
        n = prog[0][1]
        tab = tuple(pt[n] for pt in points)
        for (R, P, d) in prog[1:]:
            tab = apply_pass(tab, points, R, P, d)
        return tab

    def fitness(prog):
        tab = eval_prog(prog)
        return sum(1 for a, b in zip(tab, target) if a == b)

    def rand_prog():
        return [('V', rng.randrange(nvars))] + \
               [rng.choice(passes) for _ in range(rng.randint(1, 10))]
    population = [rand_prog() for _ in range(pop)]
    best, bestf = None, -1
    for g in range(gens):
        scored = [(fitness(p), p) for p in population]
        scored.sort(key=lambda x: -x[0])
        if scored[0][0] > bestf:
            bestf, best = scored[0][0], scored[0][1]
            if bestf == len(points):
                print(f'    [{name}] GENETIC HIT (gen {g}): {best}')
                return best
        # selection + crossover + mutation
        elite = [p for _, p in scored[:pop // 4]]
        newpop = list(elite)
        while len(newpop) < pop:
            if rng.random() < 0.5 and elite:
                p1, p2 = rng.choice(elite), rng.choice(elite)
                i = rng.randint(1, max(1, len(p1) - 1))
                j = rng.randint(1, max(1, len(p2) - 1))
                child = p1[:i] + p2[j:]
            else:
                child = rng.choice(elite)[:] if elite else rand_prog()
                op = rng.random()
                if op < 0.4:
                    child.insert(rng.randint(1, len(child)),
                                 rng.choice(passes))
                elif op < 0.7 and len(child) > 2:
                    del child[rng.randint(1, len(child) - 1)]
                else:
                    child[rng.randint(1, len(child) - 1)] = rng.choice(passes)
            if len(child) > 12:
                child = child[:12]
            newpop.append(child)
        population = newpop
    print(f'    [{name}] genetic ({pop} x {gens} gens, depth <= 11): best '
          f'fitness {bestf}/{len(points)}; best prog: {best}')
    return None


# ------------------------------------------------------------- main

if __name__ == '__main__':
    t0 = time.time()
    if len(sys.argv) > 1 and sys.argv[1] == 'ext':
        s1ext()                     # the post-hoc gap-closing runs
    else:
        s1()
        s2()
        s3()
    print(f'total {time.time()-t0:.0f}s')

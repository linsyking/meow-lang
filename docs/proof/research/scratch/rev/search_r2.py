"""R2: synthesis escalation.  Is rev reachable by a pipeline of passes
whose patterns/replacements come from a library of L-expressible unary
functions (constants, markers, tail^k, last/init/rot [the ANCHOR family],
enc, halving, cat-with-constant, ...)?

Phases:
  0. subst(A,B,C) == C.replace(B,A) on a random corpus (justifies .replace)
  1. pattern library totality check (nonempty on ALL battery strings)
  2. exhaustive BFS depth 2 with behavior dedup -- coverage statement
  3. genetic / hill-climbing search to depth ~14, seeded with structured
     candidates; CEGIS re-verification of anything good on bigger batteries.

Pipeline semantics:  T_0 = w;  T_{i+1} = T_i.replace(P_i(w), R_i(w))
(right-to-left composition of the paper = left-to-right run order here;
patterns/replacements are functions of the ORIGINAL input w).
"""
import itertools
import random
import sys
import time

import lcore as L
from lcore import battery, rev, den_try
import r2lib as RL
from r2lib import PATTERNS, REPLACEMENTS

SG = RL.sg

# ------------------------------------------------------------------ phase 0
rng = random.Random(20260921)
CORP = []
for _ in range(20000):
    A = ''.join(rng.choice('abc') for _ in range(rng.randrange(0, 4)))
    B = ''.join(rng.choice('abc') for _ in range(rng.randrange(1, 4)))
    Cc = ''.join(rng.choice('abc') for _ in range(rng.randrange(0, 10)))
    CORP.append((A, B, Cc))
bad = [(A, B, Cc) for (A, B, Cc) in CORP
       if L.subst(A, B, Cc) != Cc.replace(B, A)]
print(f'phase 0: subst == str.replace on {len(CORP)} random triples: '
      f'{len(bad)} disagreements', flush=True)
assert not bad

# ------------------------------------------------------------------ phase 1
# pattern totality: value nonempty on every battery string (incl. eps)
BAT8 = battery(8)
pvals = {}     # name -> tuple of values on BAT8 (indexed later by battery)
for name, build in PATTERNS.items():
    e = build()
    vals = []
    for w in BAT8:
        r = den_try(e, (w,))
        if r[0] != 'ok':
            vals = None
            break
        vals.append(r[1])
    if vals is None or any(v == '' for v in vals):
        print(f'  pattern {name}: NOT total-nonempty -- dropped')
        PATTERNS = {k: v for k, v in PATTERNS.items() if k != name}
        continue
    pvals[name] = vals
rvals = {}
for name, build in REPLACEMENTS.items():
    e = build()
    vals = []
    for w in BAT8:
        r = den_try(e, (w,))
        if r[0] != 'ok':
            vals = None
            break
        vals.append(r[1])
    if vals is None:
        print(f'  replacement {name}: not total -- dropped')
        REPLACEMENTS = {k: v for k, v in REPLACEMENTS.items() if k != name}
        continue
    rvals[name] = vals
print(f'phase 1: {len(PATTERNS)} patterns, {len(REPLACEMENTS)} replacements '
      f'survive (total on |w|<=8)', flush=True)

PAT_NAMES = sorted(PATTERNS)
REP_NAMES = sorted(REPLACEMENTS)
PASSES = [(p, r) for p in PAT_NAMES for r in REP_NAMES
          if not (p == r and p in ('a', 'b', 'aa', 'ab', 'ba', 'bb'))]
print(f'  pass space: {len(PASSES)}')

# ------------------------------------------------------------------ batteries
# search battery: all strings <= 4 (31); verify battery: <= 6 then <= 8.
BS = battery(4)
BS_idx = {w: i for i, w in enumerate(BAT8)}      # map search battery into BAT8
S_IDX = [BAT8.index(w) for w in BS]
S_PAT = {p: [pvals[p][i] for i in S_IDX] for p in PAT_NAMES}
S_REP = {r: [rvals[r][i] for i in S_IDX] for r in REP_NAMES}
S_TGT = [rev(w) for w in BS]


def eval_pipeline(pass_list, texts=None, pat=None, rep=None):
    """pass_list = [(pname, rname), ...] run order; texts = initial tuple."""
    if texts is None:
        texts = list(BS)
    if pat is None:
        pat = S_PAT
        rep = S_REP
    T = texts
    for (p, r) in pass_list:
        pv, rv = pat[p], rep[r]
        T = [t.replace(pv[i], rv[i]) for i, t in enumerate(T)]
    return T


def score(out):
    exact = sum(1 for o, g in zip(out, S_TGT) if o == g)
    lcp = sum(next((j for j in range(min(len(o), len(g)) + 1)
                    if j == min(len(o), len(g)) or o[j] != g[j]), 0)
              for o, g in zip(out, S_TGT))
    mism = sum(sum(1 for a, b in zip(o, g) if a != b) + abs(len(o) - len(g))
               for o, g in zip(out, S_TGT))
    return (exact, lcp, -mism), exact, lcp, -mism


# ------------------------------------------------------------------ phase 2
# exhaustive BFS depth 2 with behavior dedup (coverage statement)
t0 = time.time()
ident = tuple(BS)
seen = {ident: None}
frontier = [ident]
best2 = None
for level in (1, 2):
    newf = []
    for sig in frontier:
        for (p, r) in PASSES:
            ns = tuple(t.replace(S_PAT[p][i], S_REP[r][i])
                       for i, t in enumerate(sig))
            if ns not in seen:
                seen[ns] = (sig, (p, r))
                newf.append(ns)
    frontier = newf
    print(f'  BFS level {level}: behaviors {len(seen)} ({time.time()-t0:.0f}s)',
          flush=True)
# is rev there?  and how close does anything get?
rev_sig = tuple(S_TGT)
print(f'phase 2: rev behavior reachable at depth<=2: {rev_sig in seen}')
rank = []
for sig in seen:
    (sc, ex, lcp, mm), *_ = (score(list(sig)),)
    rank.append((sc, sig))
rank.sort(reverse=True)
print(f'  best depth<=2 score: exact={rank[0][0][0]}, lcp={rank[0][0][1]}, '
      f'mism={-rank[0][0][2]}')
node, pl = rank[0][1], []
while seen[node] is not None:
    pre, last = seen[node]
    pl.append(last)
    node = pre
print(f'  best pipeline (run order): {list(reversed(pl))}')

# ------------------------------------------------------------------ phase 3
# genetic search
POP = 400
GEN = 400
rng = random.Random(97)


def rand_ind(k=None):
    k = k or rng.randrange(3, 13)
    return [rng.choice(PASSES) for _ in range(k)]


def fitness(ind):
    out = eval_pipeline(ind)
    sc, ex, lcp, mm = score(out)
    return sc


def mutate(ind):
    m = list(ind)
    op = rng.random()
    if op < 0.35 and m:
        m[rng.randrange(len(m))] = rng.choice(PASSES)
    elif op < 0.55 and m:
        m.insert(rng.randrange(len(m) + 1), rng.choice(PASSES))
    elif op < 0.7 and len(m) > 1:
        del m[rng.randrange(len(m))]
    elif op < 0.85 and len(m) > 1:
        i, j = rng.randrange(len(m)), rng.randrange(len(m))
        m[i], m[j] = m[j], m[i]
    else:
        m = rand_ind()
    return m[:16]


def crossover(a, b):
    if not a or not b:
        return list(a or b)
    i, j = rng.randrange(len(a)), rng.randrange(len(b))
    return (a[:i] + b[j:])[:16]


# seed: structured candidates (rotr1-unfoldings etc.)
SEEDS = []
for k in range(1, 4):
    # cat(last, cat(last.init, ... )) style: passes that prepend last chars
    SEEDS.append([('arotr', 'rotr1X')] * k)
    SEEDS.append([('aX', 'rotr1X')] * k)
pop = [rand_ind() for _ in range(POP - len(SEEDS))] + [list(s) for s in SEEDS]
fit = [fitness(p) for p in pop]
t0 = time.time()
GENS_DONE = 0
BEST_EVER = (None, (-1,))
stall = 0
for g in range(GEN):
    order = sorted(range(len(pop)), key=lambda i: fit[i], reverse=True)
    if fit[order[0]] > BEST_EVER[1]:
        BEST_EVER = (pop[order[0]], fit[order[0]])
        stall = 0
        print(f'  gen {g}: new best {fit[order[0]]} '
              f'pipeline={pop[order[0]]}', flush=True)
    else:
        stall += 1
    # next generation: elitism + mutation + crossover
    elite = [pop[i] for i in order[:20]]
    newpop = [list(e) for e in elite]
    while len(newpop) < POP:
        if rng.random() < 0.5:
            newpop.append(mutate(pop[rng.randrange(POP)]))
        else:
            newpop.append(crossover(pop[rng.randrange(POP)],
                                    pop[rng.randrange(POP)]))
    pop = newpop
    fit = [fitness(p) for p in pop]
    GENS_DONE = g + 1
    if BEST_EVER[1][0] == len(BS):      # exact on the whole search battery
        break
    if stall > 120:
        # reseed half
        for i in range(POP // 2):
            pop[i] = rand_ind()
            fit[i] = fitness(pop[i])
        stall = 0
print(f'phase 3: {GENS_DONE} generations, best fitness {BEST_EVER[1]} '
      f'({time.time()-t0:.0f}s)', flush=True)
print(f'  best pipeline: {BEST_EVER[0]}')

# ------------------------------------------------------------------ phase 4
# CEGIS: re-verify the best on ALL strings <= 8; report failure profile
bestp = BEST_EVER[0]
if bestp:
    B8 = BAT8
    P8 = {p: [pvals[p][BAT8.index(w)] for w in B8] for p in PAT_NAMES}
    R8 = {r: [rvals[r][BAT8.index(w)] for w in B8] for r in REP_NAMES}
    T = list(B8)
    for (p, r) in bestp:
        T = [t.replace(P8[p][i], R8[r][i]) for i, t in enumerate(T)]
    exact = sum(1 for o, w in zip(T, B8) if o == rev(w))
    print(f'phase 4: best pipeline exact on {exact}/{len(B8)} strings |w|<=8')
    for o, w in zip(T, B8):
        if len(w) <= 5 and o != rev(w):
            print(f'    w={w!r} got={o!r} want={rev(w)!r}')

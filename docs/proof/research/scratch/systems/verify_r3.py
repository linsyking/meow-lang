"""R3: the k-th-occurrence family L_k and rank-k Markov.  REPORT Sec. 8.

Parts:
  A. the CORRECTED two-sided measure lemma for the single-site family
     (anchored ^/$, once, repOcc(0/1/2)): hypotheses (i) subadditive+k,
     (ii)+(ii') two-sided split; machine-checked for 8 measures + the
     coordinator's counterexample measure (ends-with-a) as a NEGATIVE
     control (satisfies (i),(ii), violates (ii'), and violates the bound
     on [eps/b$](ab)); the four classical once-invariants with explicit
     recursions, verified on a mixed single-site corpus.
  B. the L_k ladder: BFS over constant-pattern pipelines for k=1,2,3;
     membership matrix of [a/b]_j across the spaces; other targets.
  C. k=2 vs ONCE: the disjoint-marker route re-verified over |Sigma|=3
     (thm:pos-hinge(ii)); over |Sigma|=2 (no fresh marker) searches for
     constant instances [a/b]_2-style functions in once spaces.
  D. rank-k Markov: rankm(0) == restart; the 930-rule census at ranks
     0,1,2 (paper: 170 divergent at rank 0); growth census at rank 1 vs
     the paper's 140/18/4 buckets; amplifier behavior at rank 1.
"""

import sys, os, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'rec', 'lazy_pass'))

from systems import anchored, once, subst, occ, repOcc, restart, rankm
import verify_r2 as r2                     # bfs, strings, Aev, K/V/C/AL/AR

from verify_r2 import (Aev, K, V, C, AL, AR, strings, bfs, target_fn)
SIGMA = ['a', 'b']
TOP, BOT = 'b', 'a'

# ===========================================================================
# A. two-sided measure lemma for the single-site family
# ===========================================================================
# Family node types: ('A', side) anchored, ('O',) once, ('K', k) repOcc(k).
# All are single splices: output = U R V with U, V prefix/suffix pieces of
# the scrutinee value (anchored: U=eps or V=eps).

def ev_node(ty, R, P, T):
    if ty[0] == 'A':
        return anchored(R, P, T, ty[1])
    if ty[0] == 'O':
        return once(R, P, T)
    return repOcc(ty[1], P, R, T)

NODE_TYPES = [('A', 'L'), ('A', 'R'), ('O',), ('K', 0), ('K', 1), ('K', 2)]

def mr(s):
    return max((len(list(g)) for _, g in itertools.groupby(s)), default=0)

def nocc(s, W):
    return sum(1 for i in range(len(s)) if s.startswith(W, i))

MEASURES = {   # name -> (fn, k)  [all satisfy (i),(ii),(ii')]
    '#a':          (lambda s: s.count('a'), 0),
    '#b':          (lambda s: s.count('b'), 0),
    'len':         (lambda s: len(s), 0),
    'maxrun':      (mr, 0),
    '|bal(a,b)|':  (lambda s: abs(s.count('a') - s.count('b')), 0),
    '#occ(ab)':    (lambda s: nocc(s, 'ab'), 1),
    '#occ(aab)':   (lambda s: nocc(s, 'aab'), 2),
    '#occ(ba)':    (lambda s: nocc(s, 'ba'), 1),
}
COUNTER = {'ends-a': (lambda s: 1 if s.endswith('a') else 0, 0)}

def check_hyp(mu, k, pairs, name):
    """check (i) mu(xy)<=mu(x)+mu(y)+k, (ii) mu(y)<=mu(xy)+mu(x),
       (ii') mu(x)<=mu(xy)+mu(y)"""
    for x, y in pairs:
        if mu(x + y) > mu(x) + mu(y) + k:      return 'i', (x, y)
        if mu(y) > mu(x + y) + mu(x):          return 'ii', (x, y)
        if mu(x) > mu(x + y) + mu(y):          return "ii'", (x, y)
    return None, None

def leaf_budget(e, mu, env):
    t = e[0]
    if t == 'K':   return mu(e[1])
    if t == 'V':   return mu(env[e[1]])
    if t == 'C':
        return leaf_budget(e[1], mu, env) + leaf_budget(e[2], mu, env)
    return (leaf_budget(e[1], mu, env) + leaf_budget(e[2], mu, env)
            + leaf_budget(e[3], mu, env))      # R, P, E (pattern included)

def nodes(e):
    t = e[0]
    if t in ('K', 'V'):  return 0
    if t == 'C':         return 1 + nodes(e[1]) + nodes(e[2])
    return 1 + nodes(e[1]) + nodes(e[2]) + nodes(e[3])

# --- classical invariants: explicit recursions for single-splice nodes
def inv_params(e):
    """returns dict: phi (fresh-char budgets, per char), alpha/beta (maxrun),
    K/v (balance), C/w (length) -- recursions:
      node (out = U R V, U,V pieces of scrutinee):  #c(out) <= #c(T)+#c(R)
      mr(out) <= 2 mr(T) + mr(R);  |Psi(out)| <= |Psi(T)|+|Psi(P)|+|Psi(R)|;
      |out| <= |T| + |R|."""
    t = e[0]
    if t == 'K':
        w = e[1]
        return {'phi': {c: w.count(c) for c in set(w)}, 'alpha': mr(w),
                'K': abs(w.count('a') - w.count('b')), 'C': len(w),
                'mult': {}}
    if t == 'V':
        return {'phi': {}, 'alpha': 0, 'K': 0, 'C': 0,
                'mult': {e[1]: 1}}
    if t == 'C':
        a, b = inv_params(e[1]), inv_params(e[2])
        phi = {}
        for d in (a['phi'], b['phi']):
            for c, v in d.items():  phi[c] = phi.get(c, 0) + v
        mult = dict(a['mult'])
        for i, v in b['mult'].items():
            mult[i] = mult.get(i, 0) + v
        return {'phi': phi, 'alpha': a['alpha'] + b['alpha'],
                'K': a['K'] + b['K'], 'C': a['C'] + b['C'], 'mult': mult}
    R, P, E = inv_params(e[1]), inv_params(e[2]), inv_params(e[3])
    phi = {}
    for d in (R['phi'], E['phi']):
        for c, v in d.items():  phi[c] = phi.get(c, 0) + v
    # maxrun needs MULTIPLICITIES: mr(URV) <= 2 mr(T) + mr(R) doubles the
    # scrutinee's variable contributions at every node (the paper's beta_i).
    mult = {i: 2 * v for i, v in E['mult'].items()}
    for i, v in R['mult'].items():
        mult[i] = mult.get(i, 0) + v
    return {'phi': phi, 'alpha': 2 * E['alpha'] + R['alpha'],
            'K': R['K'] + P['K'] + E['K'], 'C': R['C'] + E['C'],
            'mult': mult}

def ev_fam(e, env):
    t = e[0]
    if t == 'K':  return e[1]
    if t == 'V':  return env[e[1]]
    if t == 'C':  return ev_fam(e[1], env) + ev_fam(e[2], env)
    R = ev_fam(e[1], env); P = ev_fam(e[2], env); T = ev_fam(e[3], env)
    ty = e[4]
    return ev_node(ty, R, P, T)

def fam(depth, rng):
    if depth == 0 or rng.random() < 0.25:
        return V(rng.randrange(2)) if rng.random() < 0.5 else \
            K(''.join(rng.choice(SIGMA) for _ in range(rng.randrange(0, 4))))
    if rng.random() < 0.25:
        return ('C', fam(depth - 1, rng), fam(depth - 1, rng))
    ty = rng.choice(NODE_TYPES)
    return ('N', fam(depth - 1, rng), fam(depth - 1, rng),
            fam(depth - 1, rng), ty)

def part_A():
    pairs = [(x, y) for x in strings(SIGMA, 3) for y in strings(SIGMA, 3)]
    print("A1. hypothesis check (i),(ii),(ii') over 127x127 string pairs:")
    for name, (mu, k) in list(MEASURES.items()) + list(COUNTER.items()):
        bad, wit = check_hyp(mu, k, pairs, name)
        verdict = "satisfies (i),(ii),(ii')" if bad is None else \
                  f"VIOLATES {bad} at {wit}"
        print(f"   {name:12s}: {verdict}")
    # negative control: the counterexample measure breaks the bound
    mu = COUNTER['ends-a'][0]
    out = anchored('', 'b', 'ab', 'R')          # [eps/b$](ab) fires -> "a"
    bud = leaf_budget(AR(K(''), K('b'), K('ab')), mu, ('',))
    print(f"A2. negative control [eps/b$](ab): mu(out)={mu(out)} vs leaf "
          f"budget {bud} -> bound "
          f"{'REFUTED (one-sided)' if mu(out) > bud else 'holds'} "
          f"(coordinator's counterexample, machine-confirmed)")
    # family corpus: general lemma + classical invariants
    rng = random.Random(21)
    corpus = [fam(rng.randrange(1, 4), rng) for _ in range(2500)]
    D2 = strings(SIGMA, 4)
    bad = badc = checked = 0
    skipped = 0
    for e in corpus:
        for _ in range(8):
            env = (rng.choice(D2), rng.choice(D2))
            try:
                out = ev_fam(e, env)
            except ValueError:
                skipped += 1        # eps pattern in a once/repOcc node
                continue
            nd = nodes(e)
            for name, (mu, k) in MEASURES.items():
                checked += 1
                if mu(out) > leaf_budget(e, mu, env) + 2 * k * nd:
                    bad += 1
                    if bad < 4: print("VIOLATION", name, e, env)
            # classical: fresh char for a and b, maxrun, balance, length
            pr = inv_params(e)
            for c in 'ab':
                if out.count(c) > pr['phi'].get(c, 0) \
                   + sum(env[i].count(c) for i in varleaves(e)):
                    badc += 1
            if mr(out) > pr['alpha'] + \
               sum(m * mr(env[i]) for i, m in pr['mult'].items()):
                badc += 1
            if abs(out.count('a') - out.count('b')) > \
               pr['K'] + sum(abs(env[i].count('a') - env[i].count('b'))
                             for i in varleaves(e)):
                badc += 1
            if len(out) > pr['C'] + sum(len(env[i]) for i in varleaves(e)):
                badc += 1
    print(f"A3. family corpus (2500 random single-site expressions of depth "
          f"<=3, node types anchored ^/$, once, repOcc 0/1/2 mixed; 8 input "
          f"pairs |X_i|<=4; {skipped} undefined evaluations skipped -- eps "
          f"patterns are undefined for once/repOcc, defined for anchored): "
          f"general two-sided lemma {checked} checks, {bad} violations; "
          f"classical four invariants (explicit recursions), {badc} "
          f"violations")

def varleaves(e):
    t = e[0]
    if t == 'K':  return []
    if t == 'V':  return [e[1]]
    if t == 'C':  return varleaves(e[1]) + varleaves(e[2])
    return varleaves(e[1]) + varleaves(e[2]) + varleaves(e[3])

# ===========================================================================
# B. the L_k ladder
# ===========================================================================

def part_B():
    TS = strings(SIGMA, 5)
    CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    spaces = {}
    for k in (1, 2, 3):
        # NOTE: eps patterns are UNDEFINED for once/L_k (the greedy occurrence
        # list of eps is ill-posed), unlike the anchored calculus where the
        # anchored occurrence of eps is unique -- an asymmetry to record.
        passes = [(pat, rep) for pat in CONSTS if pat for rep in CONSTS]
        seen = bfs(passes, TS, 3,
                   lambda p, s: repOcc(k - 1, p[0], p[1], s))
        spaces[k] = seen
        print(f"B. L_{k} const-pattern space (repOcc({k-1},pat,rep)), "
              f"depth<=3: {len(seen)} distinct functions")
    print("   membership matrix (rows: target, cols: k=1,2,3):")
    rows = [('[a/b]_1 (once)', lambda s: repOcc(0, 'b', 'a', s)),
            ('[a/b]_2',        lambda s: repOcc(1, 'b', 'a', s)),
            ('[a/b]_3',        lambda s: repOcc(2, 'b', 'a', s)),
            ('[aa/b]_2',       lambda s: repOcc(1, 'b', 'aa', s)),
            ('rev',            lambda s: s[::-1]),
            ('sigma^|S|',      lambda s: 'a' * len(s)),
            ('isne',           lambda s: 'b' if s else '')]
    for name, fn in rows:
        memb = ['Y' if tuple(fn(s) for s in TS) in spaces[k] else '.'
                for k in (1, 2, 3)]
        print(f"     {name:16s}  {' '.join(memb)}")

# ===========================================================================
# C. k=2 vs ONCE
# ===========================================================================

def mark_chain(k, B, A, M, S):
    """thm:pos-hinge(ii): repOcc(k,B,A) = [M/B]_1^k [A/B]_1 [B/M]_1^k."""
    s = S
    for _ in range(k):
        s = once(M, B, s)
    s = once(A, B, s)
    for _ in range(k):
        s = once(B, M, s)
    return s

def part_C():
    # C1: disjoint-marker route over ternary (B over {a,b}, M = 'c')
    ok = 0
    for B in strings(['a', 'b'], 3):
        if not B: continue
        for A in strings(['a', 'b'], 2):
            for S in strings(['a', 'b'], 5):
                for k in (0, 1, 2):
                    assert mark_chain(k, B, A, 'c', S) == \
                        repOcc(k, B, A, S), (B, A, S, k)
                    ok += 1
    print(f"C1. thm:pos-hinge(ii) re-verified: {ok} exact (B over ab "
          f"|B|<=3, |A|<=2, |S|<=5, k<=2, marker c over ternary)")
    # C2: over binary (no fresh marker): search once spaces
    TS = strings(SIGMA, 4)
    CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    passes_o = [(pat, rep) for pat in [c for c in CONSTS if c]
                for rep in CONSTS]
    seen_o = bfs(passes_o, TS, 4, lambda p, s: once(p[1], p[0], s))
    print(f"C2. once const-pattern space, depth<=4 (test strings <=4): "
          f"{len(seen_o)} distinct functions")
    for name, fn in [('[a/b]_2',   lambda s: repOcc(1, 'b', 'a', s)),
                     ('[a/ab]_2',  lambda s: repOcc(1, 'ab', 'a', s)),
                     ('[aa/b]_2',  lambda s: repOcc(1, 'b', 'aa', s)),
                     ('[a/b]_1 (sanity)', lambda s: repOcc(0, 'b', 'a', s))]:
        target_fn(seen_o, TS, fn, name)
    # C3: variable-pattern once space, depth 2-3
    TS2 = [s for s in TS if s]      # eps excluded: variable patterns are
    VOC = [K('a'), K('b'), V(0), C(V(0), K('a')), C(V(0), K('b')),
           C(K('a'), V(0)), C(K('b'), V(0))]   # partial at eps
    passes_v = [(P, R) for P in VOC for R in VOC]
    seen_v = bfs(passes_v, TS2, 3,
                 lambda p, s: once(Aev(p[1], (s,)), Aev(p[0], (s,)), s))
    print(f"C3. once variable-pattern space (vocab X,Xa,Xb,aX,bX,a,b), "
          f"depth<=3: {len(seen_v)} distinct functions")
    for name, fn in [('[a/b]_2',  lambda s: repOcc(1, 'b', 'a', s)),
                     ('[a/ab]_2', lambda s: repOcc(1, 'ab', 'a', s))]:
        target_fn(seen_v, TS, fn, name)

# ===========================================================================
# D. rank-k Markov
# ===========================================================================

def run_rank(k, A, B, S, cap=5000, lencap=5000):
    """Corrected rank-k semantics: iterate while the pass FIRES (>= k+1
    greedy occurrences); inertness (not textual no-change) is the fixpoint;
    k=0 is then EXACTLY restart, A=B included."""
    if not B:
        raise ValueError
    s, steps = S, 0
    while True:
        O = occ(s, B)
        if len(O) <= k:
            return s
        i = O[k]
        t = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap or len(t) > lencap:
            return None
        s = t

def all_rules(maxlenA=4, maxlenB=4):
    As = strings(['a', 'b'], maxlenA)          # includes ''
    Bs = strings(['a', 'b'], maxlenB, minlen=1)
    return [(A, B) for A in As for B in Bs]

def part_D():
    # D1: rank 0 == restart
    ok = 0
    for (A, B) in all_rules(3, 3)[:200]:
        for S in strings(SIGMA, 5)[:40]:
            assert run_rank(0, A, B, S) == restart(A, B, S, cap=5000), (A, B, S)
            ok += 1
    print(f"D1. rank-0 == restart: {ok} exact agreements")
    # D2: census at ranks 0,1,2
    inputs = strings(SIGMA, 9)
    rules = all_rules(4, 4)
    print(f"D2. census: {len(rules)} binary rules |A|<=4 (eps allowed), "
          f"1<=|B|<=4, all inputs |S|<=9 ({len(inputs)} inputs)")
    results = {}
    for k in (0, 1, 2):
        div = set()
        for (A, B) in rules:
            for S in inputs:
                if run_rank(k, A, B, S) is None:
                    div.add((A, B))
                    break
        results[k] = div
        print(f"   rank {k}: {len(div)} divergent rules")
    d0, d1, d2 = results[0], results[1], results[2]
    print(f"   rank-0 vs paper: {len(d0)} (paper: 170)")
    bsubA = {(A, B) for (A, B) in rules if B in A}
    print(f"   rank-0 divergent with B subset A: "
          f"{len(d0 & bsubA)} (paper: 162); others: "
          f"{sorted(d0 - bsubA)}")
    cured = sorted(d0 - d1)
    created = sorted(d1 - d0)
    print(f"   rank-1 vs rank-0: cured (diverge@0, total@1): {cured}")
    print(f"                        created (total@0, diverge@1): {created}")
    print(f"   rank-2 vs rank-1: cured: {sorted(d1 - d2)}; "
          f"created: {sorted(d2 - d1)}")
    return rules, results, inputs

def part_D3(rules, results, inputs):
    # growth census at rank 0 (sanity vs paper 140/18/4) and rank 1
    sub = [(A, B) for (A, B) in rules if len(A) <= 3 and len(B) <= 3
           and (A, B) not in results[0]]
    print(f"D3. growth census among rank-0-total rules |A|,|B|<=3: "
          f"{len(sub)} rules (paper: 162)")
    for k in (0, 1):
        tot = [r for r in sub if r not in results.get(k, set())]
        expo, superl, linear = [], [], []
        for (A, B) in tot:
            f = []
            for n in range(1, 9):
                mx = 0
                for S in strings(SIGMA, n, n):
                    out = run_rank(k, A, B, S)
                    if out is None:
                        break
                    mx = max(mx, len(out))
                else:
                    f.append(mx)
                    continue
                f = None
                break
            if f is None:
                continue
            if any(v >= 2 ** (n / 2) for n, v in enumerate(f, 1)):
                expo.append((A, B))
            elif any(v > n + 4 for n, v in enumerate(f, 1)):
                superl.append((A, B))
            else:
                linear.append((A, B))
        print(f"   rank {k}: {len(tot)} total; {len(linear)} linear, "
              f"{len(superl)} superlinear (>n+4), {len(expo)} exponential "
              f"{expo if k else ''}")
    # amplifier at rank 1
    lens = []
    for n in range(1, 9):
        S = 'a' + 'b' * (n - 1)
        out = run_rank(1, 'baa', 'ab', S)
        lens.append(len(out) if out is not None else None)
    print(f"D4. amplifier [baa/ab] at rank 1 on ab^(n-1), n=1..8: "
          f"output lengths {lens}  (rank 0: 2^(n-1)+n-1)")

if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
    rules, results, inputs = part_D()
    part_D3(rules, results, inputs)
    print("verify_r3 done")

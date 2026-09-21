"""R2: the ANCHORED calculus deep dive.  REPORT.md Sec. 7 (round 2).

Parts:
  A. anchored expression evaluator (nodes K/V/C/S/AL/AR; AL = [R/^P]E,
     AR = [R/P$]E; anchored patterns may be EMPTY by design decision;
     'S' = the baseline pass, for evaluating toolkit sub-expressions).
  B. constructions: tail, init, cat, head, last, doubling, rest(X,Y),
     isne, prepend/append -- verified against reference on stated domains.
  C. L-SIMULATION: every anchored expression is an L-expression (comma code
     + guard m0*enc2(B) / enc2(B)*m1), hence ANCHORED <= L.  Guard lemma
     checked directly; node-level simulation on a grid; FULL translation of
     random anchored ASTs checked against the anchored evaluator.
  D. MEASURE LEMMA (corrected two-sided statement; the R2 draft's one-sided
     split was refuted by the coordinator -- see REPORT Sec. 7.4): for every
     nonnegative measure mu with (i) mu(xy) <= mu(x)+mu(y)+k_mu and the
     two-sided split (ii) mu(y) <= mu(xy)+mu(x) and (ii') mu(x) <=
     mu(xy)+mu(y), mu([E](S)) <= sum over R,P,E leaves.  All 8 measures
     below satisfy (ii'), so the checks stand.  Verified on a random
     expression corpus for 8 measures.
  E. searches: BFS over anchored pipelines (constant and variable-pattern
     vocabularies) with targets; BFS over ONCE pipelines for anchored
     conditionals.  All searches print counts and are re-runnable.
"""

import sys, os, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'rec', 'lazy_pass'))

from systems import anchored, once, subst, occ
import core                      # lazy_pass evaluator (independent cross-check)
import toolkit as tk             # lazy_pass toolkit builders (enc2, dec2, ...)

SIGMA = ['a', 'b']
TOP, BOT = 'b', 'a'              # paper's |Sigma|=2 choice (Prop. instances)

# ===========================================================================
# A. anchored expressions
# ===========================================================================
# AST: ('K', w) | ('V', i) | ('C', e1, e2) | ('S', R, P, E)  (baseline pass)
#      | ('AL', R, P, E) | ('AR', R, P, E)

class Undef(Exception):
    pass

def Aev(e, env):
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return env[e[1]]
    if t == 'C':
        return Aev(e[1], env) + Aev(e[2], env)
    if t == 'S':
        T = Aev(e[3], env); P = Aev(e[2], env); R = Aev(e[1], env)
        if P == '':
            raise Undef()
        return subst(R, P, T)
    R = Aev(e[1], env); P = Aev(e[2], env); T = Aev(e[3], env)
    if t == 'AL':
        return anchored(R, P, T, 'L')
    return anchored(R, P, T, 'R')

def K(w): return ('K', w)
def V(i): return ('V', i)
def C(a, b): return ('C', a, b)
def AL(R, P, E): return ('AL', R, P, E)      # [R/^P]E
def AR(R, P, E): return ('AR', R, P, E)      # [R/P$]E

def strings(sigma, maxlen, minlen=0):
    out = ['']
    for n in range(1, maxlen + 1):
        out += [''.join(p) for p in itertools.product(sigma, repeat=n)]
    return [s for s in out if len(s) >= minlen]

# ===========================================================================
# B. constructions
# ===========================================================================

# NOTE (bug caught by machine check): the naive products Pi_[eps/^sigma] and
# Pi_[eps/sigma$] are WRONG -- the factors interfere (after one fires, the
# next re-tests the moved boundary; [eps/^a][eps/^b] deletes TWO characters
# on "ba").  Correct: the once-toolkit's Doubled Marker lemma (paper
# lem:doubled) on the scaffold XXX: XX*sigma occurs as a PREFIX of XXX iff
# sigma = X[0], sigma*XX as a SUFFIX iff sigma = X[-1], and after a factor
# fires the remaining factors are inert BY LENGTH.
def T3(X=V(0)):       return C(C(X, X), X)                      # scaffold XXX
def tailX(X=V(0)):
    return AL(K(''), C(C(X, X), K('a')),
              AL(K(''), C(C(X, X), K('b')), T3(X)))
def initX(X=V(0)):
    return AR(K(''), C(K('a'), C(X, X)),
              AR(K(''), C(K('b'), C(X, X)), T3(X)))
def catE(X, Y):      return AL(X, K('a'), AR(Y, K('b'), K('ab')))
def headX(X=V(0)):   return AR(K(''), tailX(X), X)   # tail(X) is always a suffix
def lastX(X=V(0)):   return AL(K(''), initX(X), X)    # init(X) is always a prefix
def dblX(X=V(0)):    return AL(C(X, X), X, X)                 # [XX/^X]X
def restXY():        return AL(K(''), C(V(1), K('a')),        # rest(X,Y)
                              AL(C(V(1), K('a')), V(1), V(0)))
def isneX(X=V(0)):   # [eps/tail(X)$]([TOP/^a][TOP/^b]X)
    return AR(K(''), tailX(X), AL(K(TOP), K('a'), AL(K(TOP), K('b'), X)))

def part_B():
    ok = 0
    D1 = strings(SIGMA, 8)
    for s in D1:
        assert Aev(tailX(), (s,)) == (s[1:] if s else ''), s
        assert Aev(initX(), (s,)) == (s[:-1] if s else ''), s
        assert Aev(headX(), (s,)) == (s[:1] if s else ''), s
        assert Aev(lastX(), (s,)) == (s[-1:] if s else ''), s
        assert Aev(dblX(), (s,)) == s + s, s
        assert Aev(isneX(), (s,)) == (TOP if s != '' else ''), s
        ok += 6
    D2 = strings(SIGMA, 5)
    for x in D2:
        for y in D2:
            assert Aev(catE(V(0), V(1)), (x, y)) == x + y, (x, y)
            r = (x[len(y):] if x.startswith(y) else x) if y else x
            assert Aev(restXY(), (x, y)) == r, (x, y, Aev(restXY(), (x, y)))
            ok += 2
    print(f"B. constructions: {ok} checks, all exact "
          f"(|Sigma|=2, unary args <= 8 (511 strings), pairs <= 5 (63x63))")

# ===========================================================================
# C. L-simulation of anchored expressions  (ANCHORED <= L)
# ===========================================================================
# Translation (comma code over sg = BIN: b_='a', x='b'; markers m0=xb^2='baa',
# m1=xb^3='baaa'; codes have a-runs <= 1, markers contain 'aa'):
#   [A/^B] E  ->  strip dec2( [m0 enc2(A)/ m0 enc2(B)] (m0 enc2(E) m1) )
#   [A/B$] E  ->  strip dec2( [enc2(A) m1/ enc2(B) m1] (m0 enc2(E) m1) )
# strip = [eps/m0][eps/m1] (m1 first).  Guard lemma: m0 enc2(B) occurs in
# m0 enc2(S) m1 iff B is a prefix of S; enc2(B) m1 occurs iff B is a suffix.

sg = tk.BIN
M0 = sg.m(2)          # x b^2
M1 = sg.m(3)          # x b^3

def enc2str(s):
    return Aev(tk.enc2(sg, K(s)), (s,))

def sim_node(Ae, Be, Ee, side):
    """L-AST translating the anchored node with translated sub-expressions.
    ONE marker per side: text m0*enc2(E) for ^ (pattern m0*enc2(B) can only
    occur at the head, since codes are 'aa'-free and m0 contains 'aa');
    text enc2(E)*m1 for $ (pattern enc2(B)*m1 can only end at the tail)."""
    if side == 'L':
        T0 = C(K(M0), tk.enc2(sg, Ee))
        P = C(K(M0), tk.enc2(sg, Be))
        Q = C(K(M0), tk.enc2(sg, Ae))
        strip = (K(''), M0)
    else:
        T0 = C(tk.enc2(sg, Ee), K(M1))
        P = C(tk.enc2(sg, Be), K(M1))
        Q = C(tk.enc2(sg, Ae), K(M1))
        strip = (K(''), M1)
    body = tk.comp([strip, (Q, P)], T0)
    return tk.dec2(sg, body)

def translate(e):
    """Full anchored expression -> L expression (cat via toolkit builder)."""
    t = e[0]
    if t == 'K' or t == 'V':
        return e
    if t == 'C':
        return tk.cat(sg, translate(e[1]), translate(e[2]))
    if t in ('AL', 'AR'):
        return sim_node(translate(e[1]), translate(e[2]), translate(e[3]),
                        'L' if t == 'AL' else 'R')
    raise ValueError("mixed node in translate: use only anchored ASTs")

def part_C():
    # guard lemma, directly (one marker per side)
    ok = 0
    for S in strings(SIGMA, 6):
        for B in strings(SIGMA, 3):
            TL = M0 + enc2str(S)
            TR = enc2str(S) + M1
            assert ((M0 + enc2str(B)) in TL) == S.startswith(B), (S, B)
            assert ((enc2str(B) + M1) in TR) == S.endswith(B), (S, B)
            ok += 2
    # node-level simulation on a grid
    grid = [(A, B, S) for A in strings(SIGMA, 3) for B in strings(SIGMA, 3)
            for S in strings(SIGMA, 5)]
    cnt = 0
    for (A, B, S) in grid:
        for side in 'LR':
            ast = sim_node(K(A), K(B), K(S), side)
            got = core.run_eager({'main': (1, ast)}, 'main', (S,))
            assert got[0] == 'val', (A, B, S, side, got)
            got = got[1]
            want = anchored(A, B, S, side)
            assert got == want, (A, B, S, side, got, want)
            cnt += 1
    # full translation of random anchored ASTs (mixed AL/AR/C/K/V)
    rng = random.Random(11)

    def rand_a(depth):
        if depth == 0 or rng.random() < 0.3:
            return V(0) if rng.random() < 0.6 else \
                K(''.join(rng.choice(SIGMA) for _ in range(rng.randrange(0, 4))))
        if rng.random() < 0.3:
            return C(rand_a(depth - 1), rand_a(depth - 1))
        t = AL if rng.random() < 0.5 else AR
        return t(rand_a(depth - 1), rand_a(depth - 1), rand_a(depth - 1))

    fl = 0
    for _ in range(400):
        e = rand_a(3)
        ast = translate(e)
        core.check_program({'main': (1, ast)})  # raises on bad AST
        for _ in range(3):
            S = ''.join(rng.choice(SIGMA) for _ in range(rng.randrange(0, 7)))
            got = core.run_eager({'main': (1, ast)}, 'main', (S,))
            assert got[0] == 'val', (e, S, got)
            got = got[1]
            want = Aev(e, (S,))
            assert got == want, (e, S, got, want)
            fl += 1
    print(f"C. guard lemma: {ok} biconditional checks (|S|<=6, |B|<=3); "
          f"node-level L-simulation: {cnt}/{len(grid)*2} exact (|A|,|B|<=3, "
          f"|S|<=5, both sides); full translation: {fl}/{400*3} exact "
          f"(400 random anchored ASTs depth<=3, |S|<=6)")

# ===========================================================================
# D. measure lemma
# ===========================================================================
# mu must satisfy:  mu(xy) <= mu(x)+mu(y)+k        (subadditive up to k)
#                   mu(y)   <= mu(xy)+mu(x)        (split condition)
# Then mu(output of AL/AR node) <= mu(R)+mu(P)+mu(E)+k, and by induction
#   mu([E](S)) <= sum_{leaves in R,P,E subtrees} mu(leaf value) + k*#nodes.
# For suffix-monotone measures (mu(suffix) <= mu(whole): #c, len, maxrun,
# #occ) the pattern subtree can be dropped from the budget.

def mr(s):
    return max((len(list(g)) for _, g in itertools.groupby(s)), default=0)

def nocc(s, W):
    return sum(1 for i in range(len(s)) if s.startswith(W, i))

MEASURES = {   # name -> (fn, k)
    '#a':          (lambda s: s.count('a'), 0),
    '#b':          (lambda s: s.count('b'), 0),
    'len':         (lambda s: len(s), 0),
    'maxrun':      (mr, 0),
    '|bal(a,b)|':  (lambda s: abs(s.count('a') - s.count('b')), 0),
    '#occ(ab)':    (lambda s: nocc(s, 'ab'), 1),
    '#occ(aab)':   (lambda s: nocc(s, 'aab'), 2),
    '#occ(ba)':    (lambda s: nocc(s, 'ba'), 1),
}

def nodes(e):
    t = e[0]
    if t in ('K', 'V'):
        return 0
    if t == 'C':
        return 1 + nodes(e[1]) + nodes(e[2])
    return 1 + nodes(e[1]) + nodes(e[2]) + nodes(e[3])

def leaf_budget(e, mu, env, include_pattern):
    t = e[0]
    if t == 'K':
        return mu(e[1])
    if t == 'V':
        return mu(env[e[1]])
    if t == 'C':
        return leaf_budget(e[1], mu, env, include_pattern) + \
               leaf_budget(e[2], mu, env, include_pattern)
    bud = leaf_budget(e[1], mu, env, include_pattern) + \
          leaf_budget(e[3], mu, env, include_pattern)
    if include_pattern:
        bud += leaf_budget(e[2], mu, env, include_pattern)
    return bud

def part_D():
    rng = random.Random(7)

    def rand_expr(depth):
        if depth == 0 or rng.random() < 0.25:
            return V(rng.randrange(2)) if rng.random() < 0.5 else \
                K(''.join(rng.choice(SIGMA) for _ in range(rng.randrange(0, 4))))
        if rng.random() < 0.3:
            return C(rand_expr(depth - 1), rand_expr(depth - 1))
        t = AL if rng.random() < 0.5 else AR
        return t(rand_expr(depth - 1), rand_expr(depth - 1),
                 rand_expr(depth - 1))

    corpus = [rand_expr(rng.randrange(1, 4)) for _ in range(3000)]
    D2 = strings(SIGMA, 4)
    bad = badt = checked = checkedt = 0
    for e in corpus:
        for _ in range(8):
            env = (rng.choice(D2), rng.choice(D2))
            out = Aev(e, env)
            nd = nodes(e)
            for name, (mu, k) in MEASURES.items():
                bud = leaf_budget(e, mu, env, True)
                checked += 1
                if mu(out) > bud + k * nd:
                    bad += 1
                    if bad < 4:
                        print("VIOLATION(uniform)", name, e, env, mu(out),
                              bud + k * nd)
                if name != '|bal(a,b)|':
                    budt = leaf_budget(e, mu, env, False)
                    checkedt += 1
                    if mu(out) > budt + k * nd:
                        badt += 1
                        if badt < 4:
                            print("VIOLATION(tight)", name, e, env, mu(out),
                                  budt + k * nd)
    print(f"D. measure lemma: {checked} uniform-budget checks "
          f"(pattern included) and {checkedt} tight-budget checks "
          f"(pattern excluded, suffix-monotone measures) over {len(corpus)} "
          f"random anchored expressions (depth<=3) x 8 input pairs "
          f"(|X_i|<=4) x {len(MEASURES)} measures -- "
          f"{'ALL HOLD' if bad == 0 and badt == 0 else f'{bad}/{badt} VIOLATIONS'}")

# ===========================================================================
# E. searches
# ===========================================================================

def bfs(passes, testset, maxdepth, apply_pass):
    idf = tuple(testset)
    seen = {idf: 0}
    frontier = {idf}
    for d in range(1, maxdepth + 1):
        new = {}
        for f in frontier:
            cur = dict(zip(testset, f))
            for p in passes:
                g = tuple(apply_pass(p, cur[s]) for s in testset)
                if g not in seen and g not in new:
                    new[g] = d
        for g in new:
            seen[g] = d
        frontier = set(new)
        if not frontier:
            break
    return seen

def target_fn(seen, testset, fn, name):
    tgt = tuple(fn(s) for s in testset)
    hit = tgt in seen
    print(f"   target {name}: "
          f"{'FOUND at depth ' + str(seen[tgt]) if hit else 'ABSENT'} "
          f"(space size {len(seen)})")
    return hit

def part_E():
    TS = strings(SIGMA, 5)
    CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    # --- E1: anchored, constant patterns/replacements, both sides, depth 3
    passes = []
    for pat in CONSTS:
        for rep in CONSTS:
            passes.append(('AL', pat, rep))
            passes.append(('AR', pat, rep))
    seen = bfs(passes, TS, 3,
               lambda p, s: anchored(p[2], p[1], s, p[0][1]))
    print(f"E1. anchored const-pattern space (|pat|,|rep|<=2, both sides), "
          f"depth<=3: {len(seen)} distinct functions on 62 test strings")
    target_fn(seen, TS, lambda s: ('b' if s else ''), 'isne')
    target_fn(seen, TS, lambda s: s[::-1], 'rev')
    target_fn(seen, TS, lambda s: once('a', 'b', s), 'once [a/b]_1')
    target_fn(seen, TS, lambda s: 'a' * len(s), 'sigma^|S|')
    target_fn(seen, TS, lambda s: ('a' if s == '' else 'b'), 'is-eps')
    # --- E2: once, constant patterns (eps pattern undefined there), depth 3
    passes_o = [(pat, rep) for pat in [c for c in CONSTS if c]
                for rep in CONSTS]
    seen_o = bfs(passes_o, TS, 3, lambda p, s: once(p[1], p[0], s))
    print(f"E2. once const-pattern space (|pat|,|rep|<=2), depth<=3: "
          f"{len(seen_o)} distinct functions")
    target_fn(seen_o, TS, lambda s: anchored('a', 'ab', s, 'L'),
              'anchored [a/^ab]')
    target_fn(seen_o, TS, lambda s: once('a', 'b', s), 'once [a/b]_1 (sanity)')
    # --- E3: anchored, variable patterns/replacements, depth 2
    VOCAB = [K(''), K('a'), K('b'), V(0), C(V(0), K('a')), C(V(0), K('b')),
             C(K('a'), V(0)), C(K('b'), V(0))]
    passes_v = []
    for P in VOCAB:
        for R in VOCAB:
            passes_v.append(('AL', R, P))
            passes_v.append(('AR', R, P))

    def ap(p, s):
        return anchored(Aev(p[1], (s,)), Aev(p[2], (s,)), s, p[0][1])

    seen_v = bfs(passes_v, TS, 2, ap)
    print(f"E3. anchored variable-pattern space (vocab X, Xa, Xb, aX, bX, "
          f"a, b, eps), depth<=2: {len(seen_v)} distinct functions")
    target_fn(seen_v, TS, lambda s: ('b' if s else ''), 'isne')
    target_fn(seen_v, TS, lambda s: s[::-1], 'rev')
    target_fn(seen_v, TS, lambda s: once('a', 'b', s), 'once [a/b]_1')
    target_fn(seen_v, TS, lambda s: ('a' if s == '' else 'b'), 'is-eps')
    # --- E4: anchored const depth 4 (reduced pass set)
    RED = ['', 'a', 'b', 'ab', 'ba']
    passes_r = [(sd, pat, rep) for sd in 'LR' for pat in RED for rep in RED]
    seen_r = bfs(passes_r, TS, 4,
                 lambda p, s: anchored(p[2], p[1], s, p[0]))
    print(f"E4. anchored const-pattern space (pat,rep in eps,a,b,ab,ba), "
          f"depth<=4: {len(seen_r)} distinct functions")
    target_fn(seen_r, TS, lambda s: ('b' if s else ''), 'isne')
    target_fn(seen_r, TS, lambda s: once('a', 'b', s), 'once [a/b]_1')
    target_fn(seen_r, TS, lambda s: ('a' if s == '' else 'b'), 'is-eps')

if __name__ == '__main__':
    part_B()
    part_C()
    part_D()
    part_E()
    print("verify_r2 done")

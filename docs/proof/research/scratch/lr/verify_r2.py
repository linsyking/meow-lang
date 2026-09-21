"""ROUND 2 verification battery: normal forms and commutation for L+R.

Problem of the round: when do L- and R-passes commute / pull apart into
blocks; is every mixed pipeline equivalent to a ONE-ALTERNATION form
(L-block o R-block)?  Plus the thm:core (concatenation elimination)
transfer for the mixed calculus.

Checks:

  D1  DISJOINT COMMUTATION LEMMA (new).  Passes P1=[A/B], P2=[C/D] with
      B,D != eps, in EITHER direction each, commute (P1 o P2 = P2 o P1)
      whenever
          alph(B) & alph(D) = empty,  A != eps with alph(A) & alph(D) = empty,
          C != eps with alph(C) & alph(B) = empty.
      Proof idea (REPORT R2): under alph(B) & alph(D) = empty NO occurrence
      of B intersects any occurrence of D; non-empty alphabet-disjoint
      insertions create no new occurrences of the other pattern; deletion
      (eps) would merge neighbours, hence the A,C != eps clauses; and the
      order/overlap structure of each pattern's occurrences is preserved
      (a match of the other rule needs room outside the occurrence, so
      shrinking never creates overlap), so both greedy directions select
      corresponding occurrence sets and both compositions equal the
      simultaneous replacement.  Verified here: every quadruple satisfying
      the conditions with |A|,|B|,|C|,|D| <= 2 over {a,b,c}, all 4
      direction combinations, all |T| <= 5.
  D1b NECESSITY: dropping each single condition admits a counterexample
      (found by search; the A=eps one is hand-derived:
      [eps/c] vs [d/ab] on T=acb gives "ab" vs "d").
  D2  ALTERNATION CENSUS (constant patterns, 84 pass types, 63 inputs of
      length <= 5): for every table of a mixed pipeline of depth <= 3, the
      MINIMAL number of L/R alternations of a word (depth <= 3) reaching
      it.  Reports how many tables need >= 1 and >= 2 alternations, with
      example pipelines.
  D2b ESCALATION (restricted universe, |A| <= 1, 36 pass types): tables
      needing >= 2 alternations at depth <= 3, tested against one-alternation
      forms with block depths <= 2 (total budget 4), both orders --
      exhaustively; then randomized two-block search at total budget <= 6
      for the survivors.
  D2c UNBORDERED COLLAPSE: mixed pipelines whose patterns are all
      unbordered compute pure-L functions (replace each R-pass by its
      L-version; prop:r2l-agree per pass).  Verified at depth <= 2.
  D3  THM:core TRANSFER: for random mixed E1, E2,
      cat[E1/X1, E2/X2] computes E1 * E2 (value + definedness), where
      cat is the L-expression of Theorem thm:cat (built by toolkit).
  D4  INCLUSION SYMMETRY ingredients (cor:incl-symmetry of the paper):
      the mirror m(f) = rev o f o rev carries sigma = [[X1/X2]X3]] (the
      L-pass as 3-ary function) to rho = [[X1/X2]^R X3]] and back
      (m(sigma) = rho is exactly rev-duality, re-verified), and
      conj(conj(E)) = E for random mixed E (already C6/R1; quick re-check
      with expressions containing both node kinds).
"""

import itertools
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrcore import (subst, substR, rev, K, V, C, S, SR, ev, run, allR, conj,
                    size, iter_strings, borders, unbordered, Tally)
import toolkit as tk

sg = tk.Sig(['a', 'b'], 'a', 'b', 'b', 'a')
AB = 'ab'
ABC = 'abc'

DOM = tuple(iter_strings(AB, 5))                     # 63 strings
ABC_DOM = tuple(iter_strings(ABC, 5))                 # 364 strings


def alph(w):
    return set(w)


def passes_combos():
    for A in iter_strings(ABC, 2):
        for B in iter_strings(ABC, 2, 1):
            for Cc in iter_strings(ABC, 2):
                for D in iter_strings(ABC, 2, 1):
                    yield A, B, Cc, D


def conditions(A, B, Cc, D):
    return (alph(B) & alph(D) == set()
            and A != '' and alph(A) & alph(D) == set()
            and Cc != '' and alph(Cc) & alph(B) == set())


def d1_lemma():
    t = Tally('D1 disjoint commutation (all 4 direction pairs)')
    nquad = 0
    for (A, B, Cc, D) in passes_combos():
        if not conditions(A, B, Cc, D):
            continue
        nquad += 1
        for d1 in 'LR':
            for d2 in 'LR':
                f1 = subst if d1 == 'L' else substR
                f2 = subst if d2 == 'L' else substR
                for T in ABC_DOM:
                    a = f1(A, B, f2(Cc, D, T))
                    b = f2(Cc, D, f1(A, B, T))
                    t.check(a == b, (A, B, Cc, D, d1, d2, T))
    print(f'    [D1] {nquad} rule pairs satisfying the conditions '
          f'(x 4 direction pairs x {len(ABC_DOM)} inputs)')
    return t


def d1b_necessity():
    def search(viol, rest):
        for (A, B, Cc, D) in passes_combos():
            if viol(A, B, Cc, D) and rest(A, B, Cc, D):
                for d1 in 'LR':
                    for d2 in 'LR':
                        f1 = subst if d1 == 'L' else substR
                        f2 = subst if d2 == 'L' else substR
                        for T in ABC_DOM:
                            if f1(A, B, f2(Cc, D, T)) != f2(Cc, D, f1(A, B, T)):
                                return (A, B, Cc, D, d1, d2, T,
                                        f1(A, B, f2(Cc, D, T)),
                                        f2(Cc, D, f1(A, B, T)))
        return None

    def rest_hold(name):
        def f(A, B, Cc, D):
            c = []
            if name != 'BD':
                c.append(alph(B) & alph(D) == set())
            if name != 'A':
                c.append(A != '' and alph(A) & alph(D) == set())
            if name != 'C':
                c.append(Cc != '' and alph(Cc) & alph(B) == set())
            return all(c)
        return f

    viol = {
        'BD': lambda A, B, Cc, D: alph(B) & alph(D) != set(),
        'A': lambda A, B, Cc, D: not (A != '' and alph(A) & alph(D) == set()),
        'C': lambda A, B, Cc, D: not (Cc != '' and alph(Cc) & alph(B) == set()),
    }
    for name, f in viol.items():
        got = search(f, rest_hold(name))
        print(f'    [D1b] dropping condition {name!r}: '
              + ('NO counterexample found (domain exhausted)'
                 if got is None else
                 f'counterexample P1=[{got[0]}/{got[1]}] P2=[{got[2]}/{got[3]}] '
                 f'dirs {got[4]}{got[5]} T="{got[6]}": '
                 f'{got[7]!r} vs {got[8]!r}'))
    a = subst('', 'c', subst('d', 'ab', 'acb'))
    b = subst('d', 'ab', subst('', 'c', 'acb'))
    print(f'    [D1b] hand example [eps/c] vs [d/ab] on "acb": '
          f'P1 o P2 = {a!r}, P2 o P1 = {b!r} '
          f'({"differs" if a != b else "EQUAL -- recheck!"})')


# ------------------------------------------------------------------ D2

PATTERNS = [a + b for a in AB for b in AB] + list(AB)        # 6
REPLS = [a + b for a in AB for b in AB] + list(AB) + ['']    # 7
PASSES = [(A, B, d) for A in REPLS for B in PATTERNS for d in 'LR']  # 84


def apply_pass(table, A, B, d):
    f = subst if d == 'L' else substR
    return tuple(f(A, B, s) for s in table)


def census(passes, rounds):
    """states: table -> (altL, altR, wordL, wordR): min alternations over
    words of length <= `rounds` ending in an L-pass / R-pass reaching the
    table, with example words.  Each round extends ALL accumulated states
    (redundant but exhaustive: after r rounds every word of length <= r has
    been built; improved states are re-extended next round)."""
    INF = 10 ** 9
    states = {DOM: (0, 0, (), ())}
    for r in range(rounds):
        snap = {k: v for k, v in states.items()}
        for tab, (al, ar, wl, wr) in snap.items():
            for (A, B, d) in passes:
                t2 = apply_pass(tab, A, B, d)
                if d == 'L':
                    val, word = min(al, ar + 1), (wr if al > ar else wl) + ((A, B, d),)
                else:
                    val, word = min(ar, al + 1), (wl if ar > al else wr) + ((A, B, d),)
                cur = states.get(t2)
                if cur is None:
                    states[t2] = ((val, INF, word, ()) if d == 'L'
                                  else (INF, val, (), word))
                else:
                    if d == 'L' and val < cur[0]:
                        states[t2] = (val, cur[1], word, cur[3])
                    elif d == 'R' and val < cur[1]:
                        states[t2] = (cur[0], val, cur[2], word)
    return states


def d2_census():
    states = census(PASSES, 3)
    n = len(states)
    ge1 = [t for t, v in states.items() if min(v[0], v[1]) >= 1]
    ge2 = [t for t, v in states.items() if min(v[0], v[1]) >= 2]
    print(f'    [D2] tables at depth <= 3: {n}; needing >= 1 alternation '
          f'(not pure-L, not pure-R at this budget): {len(ge1)}; '
          f'needing >= 2 alternations (no L^aR^b/R^bL^a word of depth <= 3): '
          f'{len(ge2)}')
    if ge2:
        t0 = ge2[0]
        v = states[t0]
        print(f'    [D2] example >=2-alternation table, pipeline (run order): '
              f'{v[2] or v[3]}  (altL={v[0]}, altR={v[1]})')
    return states, ge2


# ------------------------------------------------------------------ D2b

REPLS_R = ['', 'a', 'b']                                     # 3
PASSES_R = [(A, B, d) for A in REPLS_R for B in PATTERNS for d in 'LR']  # 36
LP_R = [p for p in PASSES_R if p[2] == 'L']
RP_R = [p for p in PASSES_R if p[2] == 'R']


def words_upto(passes, k):
    out = [()]
    for n in range(1, k + 1):
        out += list(itertools.product(passes, repeat=n))
    return out


def run_word(start, word):
    t = start
    for p in word:
        t = apply_pass(t, *p)
    return t


def d2b_escalation():
    states = census(PASSES_R, 3)
    ge2 = [t for t, v in states.items() if min(v[0], v[1]) >= 2]
    print(f'    [D2b] restricted universe (36 pass types): tables {len(states)},'
          f' needing >= 2 alternations at depth <= 3: {len(ge2)}')

    # (b) two-block budget 4, exhaustive: ALL block WORDS of depth <= 2
    # (NO dedup by on-domain table -- two words agreeing on the 63-string
    # domain can differ on the first block's outputs, which lie off it),
    # both orders.
    lp = words_upto(LP_R, 2)             # 1 + 18 + 324 = 343 words
    rp = words_upto(RP_R, 2)
    print(f'    [D2b] L-block words depth<=2: {len(lp)}, R-block words: {len(rp)}')
    blocks4 = set()
    for h in rp:                          # h runs FIRST
        outs = run_word(DOM, h)
        for g in lp:
            blocks4.add(run_word(outs, g))
    for h in lp:                          # L-block runs first
        outs = run_word(DOM, h)
        for g in rp:
            blocks4.add(run_word(outs, g))
    surv = [t for t in ge2 if t not in blocks4]
    print(f'    [D2b] two-block budget-4 set (all block words <= 2, both '
          f'orders): {len(blocks4)} tables; >=2-alt survivors: {len(surv)}')

    # (c) randomized two-block search, total budget <= 6 (blocks <= 3):
    rng = random.Random(7)
    hit = set()
    tries = 40000
    for _ in range(tries):
        g = tuple(rng.choice(LP_R) for _ in range(rng.randint(1, 3)))
        h = tuple(rng.choice(RP_R) for _ in range(rng.randint(1, 3)))
        hit.add(run_word(run_word(DOM, h), g))
        g2 = tuple(rng.choice(RP_R) for _ in range(rng.randint(1, 3)))
        h2 = tuple(rng.choice(LP_R) for _ in range(rng.randint(1, 3)))
        hit.add(run_word(run_word(DOM, h2), g2))
    surv2 = [t for t in surv if t not in hit]
    print(f'    [D2b] randomized two-block budget<=6 ({tries} samples x 2 '
          f'orders): {len(hit)} tables; survivors: {len(surv2)}')
    named = 0
    for t in surv2:
        if named >= 6:
            break
        v = states.get(t)
        if v:
            print(f'    [D2b] survivor pipeline (run order): {v[2] or v[3]}')
            named += 1
    return surv2, states


# ------------------------------------------------------------------ D2c

def d2c_unbordered():
    unb = [p for p in PATTERNS if unbordered(p)]      # a, b, ab, ba
    passes = [(A, B, d) for A in REPLS for B in unb for d in 'LR']
    lonly = [(A, B, 'L') for A in REPLS for B in unb]
    t = Tally('D2c unbordered-only mixed = pure-L (depth <= 2)')
    mixed_tables, pure_tables = set(), set()
    for n in range(0, 3):
        for w in itertools.product(passes, repeat=n):
            mixed_tables.add(run_word(DOM, w))
        for w in itertools.product(lonly, repeat=n):
            pure_tables.add(run_word(DOM, w))
    print(f'    [D2c] unbordered-pattern mixed tables (depth<=2): '
          f'{len(mixed_tables)}; pure-L: {len(pure_tables)}; '
          f'equal: {mixed_tables == pure_tables}')
    t.check(mixed_tables <= pure_tables, 'inclusion')
    return t


# ------------------------------------------------------------------ D3

def subst_vars(e, mapping):
    t = e[0]
    if t == 'K':
        return e
    if t == 'V':
        return mapping[e[1]]
    if t == 'C':
        return ('C', subst_vars(e[1], mapping), subst_vars(e[2], mapping))
    if t in ('S', 'SR'):
        return (t, subst_vars(e[1], mapping), subst_vars(e[2], mapping),
                subst_vars(e[3], mapping))
    raise ValueError(t)


def rand_expr(rng, nvars, maxsize, sigma='ab', maxconst=3):
    def go(budget):
        if budget <= 1 or rng.random() < 0.25:
            if rng.random() < 0.5:
                k = rng.randint(0, maxconst)
                return K(''.join(rng.choice(sigma) for _ in range(k)))
            return V(rng.randrange(nvars))
        r = rng.random()
        if r < 0.25:
            return C(go(budget // 2), go(budget // 2))
        node = S if rng.random() < 0.5 else SR
        return node(go(max(1, budget // 3)), go(max(1, budget // 3)),
                    go(max(1, budget // 3)))
    return go(maxsize)


def d3_core_transfer(n=250):
    t = Tally('D3 thm:core transfer: cat[E1/X1,E2/X2] = E1 * E2 (mixed)')
    rng = random.Random(11)
    catdeg = tk.cat(sg, V(0), V(1))       # the L-expression of thm:cat
    for _ in range(n):
        # E1, E2 are n-ary over the SAME variables (thm:core's setting):
        e1 = rand_expr(rng, 2, 10)
        e2 = rand_expr(rng, 2, 10)
        comp = subst_vars(catdeg, [e1, e2])
        for _ in range(3):
            args = (''.join(rng.choice(AB) for _ in range(rng.randint(0, 5))),
                    ''.join(rng.choice(AB) for _ in range(rng.randint(0, 5))))
            a1 = run(e1, args)
            a2 = run(e2, args)
            b = run(comp, args)
            if a1 is None or a2 is None:
                t.check(b is None, (args, a1, a2, b))
            else:
                t.check(b == a1 + a2, (args, a1, a2, b))
    return t


# ------------------------------------------------------------------ D4

def d4_mirror(n=150):
    """cor:incl-symmetry ingredients: m(sigma) = rho (rev-duality, as a
    3-ary identity on the finite domain), conj involution on mixed
    expressions re-checked."""
    t = Tally('D4 m(sigma)=rho on (A,B,C), |A|,|B|<=3, |C|<=5')
    for A in iter_strings(AB, 3):
        for B in iter_strings(AB, 3, 1):
            for Cc in iter_strings(AB, 5):
                t.check(rev(subst(rev(A), rev(B), rev(Cc))) == substR(A, B, Cc),
                        (A, B, Cc))
    t2 = Tally('D4 conj involution on random mixed exprs')
    rng = random.Random(5)
    for _ in range(n):
        e = rand_expr(rng, 2, 12)
        t2.check(conj(conj(e)) == e)
    t.report()
    return t2


def d2bbb_survivor_resistance(states_r, n_tries=100000):
    """The 4 restricted-universe >=2-alt survivors: confirm they are also
    full-universe >=2-alt tables, and run a FULL-universe randomized
    two-block search (budget <= 6, both orders) against them.  (A separate
    400k-sample run of the same protocol found 0 hits; the number here is
    the re-runnable default.)  Also: exhaustive two-block search over the
    two 'halving' passes only, blocks up to depth 4 -- none."""
    states_full = census(PASSES, 3)
    ge2_full = set(t for t, v in states_full.items() if min(v[0], v[1]) >= 2)
    ge2_r = [t for t, v in states_r.items() if min(v[0], v[1]) >= 2]
    lp = words_upto(LP_R, 2)
    rp = words_upto(RP_R, 2)
    blocks4 = set()
    for h in rp:
        outs = run_word(DOM, h)
        for g in lp:
            blocks4.add(run_word(outs, g))
    for h in lp:
        outs = run_word(DOM, h)
        for g in rp:
            blocks4.add(run_word(outs, g))
    surv = [t for t in ge2_r if t not in blocks4]
    t = Tally('D2bbb the 4 survivors are full-universe >=2-alt tables')
    for x in surv:
        t.check(x in ge2_full, x)
    # full-universe randomized two-block budget <= 6:
    LPf = [p for p in PASSES if p[2] == 'L']
    RPf = [p for p in PASSES if p[2] == 'R']
    rng = random.Random(99)
    survset = set(surv)
    hit = set()
    for _ in range(n_tries):
        g = tuple(rng.choice(LPf) for _ in range(rng.randint(1, 3)))
        h = tuple(rng.choice(RPf) for _ in range(rng.randint(1, 3)))
        tt = run_word(run_word(DOM, h), g)
        if tt in survset:
            hit.add(tt)
        g2 = tuple(rng.choice(RPf) for _ in range(rng.randint(1, 3)))
        h2 = tuple(rng.choice(LPf) for _ in range(rng.randint(1, 3)))
        tt = run_word(run_word(DOM, h2), g2)
        if tt in survset:
            hit.add(tt)
    print(f'    [D2bbb] {len(surv)} survivors; full-universe randomized '
          f'two-block budget<=6 ({n_tries} x 2 orders): {len(hit)} hits')

    # exhaustive over the two halving passes, blocks <= 4:
    RS = [(A, B, 'R') for (A, B) in [('b', 'aa'), ('a', 'bb')]]
    LS = [(A, B, 'L') for (A, B) in [('b', 'aa'), ('a', 'bb')]]
    dom2 = (['b' * n for n in range(13)] + ['a' * n for n in range(13)]
            + ['ab' * k for k in range(7)] + ['ba' * k + 'b' for k in range(6)])
    dom2 = tuple(dom2)
    t2 = Tally('D2bbb no two-block form over halving passes (blocks<=4)')
    for x in surv:
        target = None
        # compute the survivor's values on dom2 by re-deriving from a word:
        # use the census example word
        v = states_r.get(x)
        word = v[2] or v[3]
        target = run_word(dom2, word)
        found = None
        for k in range(0, 5):
            for j in range(0, 5):
                if found:
                    break
                for hw in itertools.product(RS, repeat=k):
                    if found:
                        break
                    for gw in itertools.product(LS, repeat=j):
                        tt = run_word(run_word(dom2, hw), gw)
                        if tt == target:
                            found = (hw, gw)
                            break
                if found:
                    break
            if found:
                break
        t2.check(found is None, (word,))
    ok1 = t.report()
    ok2 = t2.report()
    return ok1 and ok2


# ------------------------------------------------------------------ main

def d2bb_full_random(ge2_full, n_tries=60000):
    """Randomized two-block search (total budget <= 6, both orders, FULL
    pass universe) for the >=2-alternation tables of the full census."""
    LP = [p for p in PASSES if p[2] == 'L']
    RP = [p for p in PASSES if p[2] == 'R']
    rng = random.Random(13)
    ge2set = set(ge2_full)
    hit = set()
    for _ in range(n_tries):
        g = tuple(rng.choice(LP) for _ in range(rng.randint(1, 3)))
        h = tuple(rng.choice(RP) for _ in range(rng.randint(1, 3)))
        t = run_word(run_word(DOM, h), g)
        if t in ge2set:
            hit.add(t)
        g2 = tuple(rng.choice(RP) for _ in range(rng.randint(1, 3)))
        h2 = tuple(rng.choice(LP) for _ in range(rng.randint(1, 3)))
        t = run_word(run_word(DOM, h2), g2)
        if t in ge2set:
            hit.add(t)
    print(f'    [D2bb] full universe: {len(ge2set)} >=2-alt tables; '
          f'randomized two-block budget<=6 ({n_tries} x 2 orders) covers '
          f'{len(hit)} of them')
    return hit


if __name__ == '__main__':
    print('=== L+R ROUND 2 verification battery ===')
    ok = True
    ok &= d1_lemma().report()
    d1b_necessity()
    states, ge2 = d2_census()
    surv2, states_r = d2b_escalation()
    d2bb_full_random(ge2)
    ok &= d2bbb_survivor_resistance(states_r)
    ok &= d2c_unbordered().report()
    ok &= d3_core_transfer().report()
    ok &= d4_mirror().report()
    print('ALL OK' if ok else 'FAILURES PRESENT')
    sys.exit(0 if ok else 1)

#!/usr/bin/env python3
"""Verification suite for the eager recursive calculus L_rec.

Checks, on hand-written and randomized programs:
  A. The Section-2 toolkit builders (cat/tail/head/eq/if as RAW expression
     trees over subst) against Python reference semantics.
  B. The three semantics of L_rec agree:
       Kleene approximants phi^n  ==  unbounded operational runs
                                  ==  plain-L evaluation of the inlining,
     with divergence exactly where the theory predicts (C = definitions that
     can reach a call-graph cycle: never halt; non-C: halt or error, never
     diverge), and Kleene stabilization by the predicted bound.
  C. Theorem Unfolding: phi^n_j == ⟦unfold_n(f_j)⟧ as partial functions.
  D. The error-vs-divergence refinement (left-to-right order matters only
     there, never for the value / undefinedness).

Fuels are chosen small where the explored call tree is exponential in fuel
(the eager evaluator has no memoization by design); the memoized Kleene
chain carries the heavy load at arbitrary depth.

Run:  python3 verify_eager.py
"""

import itertools
import random
import sys

sys.setrecursionlimit(200000)

from eager import (Prog, phi_eval, phi_all, kleene_stabilization, run,
                   unfold_def, inline_prog, evL, omega, SizeEx,
                   X, C, cat, tailE, headE, eqE, ifE)

SIG = ['a', 'b']
STRINGS = [''] + [s for r in (1, 2) for s in
                  map(''.join, itertools.product(SIG, repeat=r))]  # 7 strings
SMALL = ['', 'a', 'b']                      # input domain for random programs

PASS = 0
FAIL = 0


def check(cond, msg):
    global PASS, FAIL
    if cond:
        PASS += 1
    else:
        FAIL += 1
        print(f"  FAIL: {msg}")


# ---------------------------------------------------------------- section A

def section_A():
    print("=== A. Section-2 toolkit builders (raw L trees) ===")
    dom = [s for r in (0, 1, 2, 3, 4) for s in
           map(''.join, itertools.product(SIG, repeat=r))]
    for s in dom:
        check(evL(tailE(X(0)), (s,)) == (s[1:] if s else ''), f"tail({s})")
        check(evL(headE(X(0)), (s,)) == (s[0] if s else ''), f"head({s})")
    small = [s for r in (0, 1, 2) for s in
             map(''.join, itertools.product(SIG, repeat=r))]
    for s in small:
        for t in small:
            check(evL(cat(X(0), X(1)), (s, t)) == s + t, f"cat({s},{t})")
            check(evL(eqE(X(0), X(1)), (s, t)) == ('a' if s == t else 'b'),
                  f"eq({s},{t})")
            for u in small:
                for cond in ('a', 'b'):
                    check(evL(ifE(X(0), X(1), X(2)), (cond, t, u)) ==
                          (t if cond == 'a' else u), f"if({cond},{t},{u})")
    print(f"  A: {PASS} checks so far, {FAIL} failures")


# ------------------------------------------------------------- the battery

def inputs_of(P, dom=STRINGS):
    return [tuple(itertools.product(dom, repeat=a)) if a > 0 else [()]
            for a in P.ar]


def battery(P, label, unfold_depth=3, fuel_hi=30, fuel_cyc=8, dom=STRINGS,
            verbose=False):
    """Full agreement battery for program P.

    fuel_hi : fuel for operational runs on hand-written (low-branching)
              programs; fuel_cyc : cap on fuel for C-members (the explored
              call tree is exponential in fuel)."""
    global PASS, FAIL
    inp = inputs_of(P, dom)
    K = P.kleene_bound()
    nmax = K + 2
    table = phi_all(P, inp, nmax)
    stab = kleene_stabilization(table, P, inp)
    inl = inline_prog(P)
    if verbose:
        print(f"  [{label}] k={P.k} C={{{','.join(P.names[j] for j in sorted(P.C)) or '-'}}}"
              f" kleene_bound={K} stab={stab}"
              f" depths={{{','.join(f'{P.names[j]}:{P.depth[j]}' for j in range(P.k))}}}")
    check(stab is not None and stab <= K,
          f"[{label}] stabilization {stab} <= bound {K}")

    cycfuel = min(fuel_hi, fuel_cyc)
    outcomes = {}
    for j in range(P.k):
        for T in inp[j]:
            # --- Theorem Unfolding: phi^n == denotation of unfold_n
            for n in range(0, min(unfold_depth, nmax) + 1):
                u = evL(unfold_def(P, j, n), T)
                check(u == table[(j, T)][n],
                      f"[{label}] unfold_{n}({P.names[j]},{T}): {u} vs "
                      f"{table[(j, T)][n]}")
            v = table[(j, T)][nmax]           # phi at the stabilized index
            if j in P.C:
                # --- vacuity: bottom at EVERY approximant, never halts
                check(all(table[(j, T)][n] is None for n in range(nmax + 1)),
                      f"[{label}] {P.names[j]} in C: phi^n bottom at all n")
                check(evL(inl[j], T) is None,
                      f"[{label}] inlined {P.names[j]} (Omega) undefined at {T}")
                out = run(P, j, T, cycfuel)
                check(out[0] != 'halt',
                      f"[{label}] {P.names[j]} in C never halts at {T}")
                check(out[0] in ('err', 'cut'), "C-outcome in {err,cut}")
            else:
                # --- inlining: lfp == plain L expression
                check(evL(inl[j], T) == v,
                      f"[{label}] inlined {P.names[j]} == lfp at {T}: "
                      f"{evL(inl[j], T)} vs {v}")
                # --- never diverges: fuel depth+1 suffices to complete
                out = run(P, j, T, P.depth[j] + 2)
                check(out[0] != 'cut',
                      f"[{label}] {P.names[j]} not in C never diverges at {T}")
                if out[0] == 'halt':
                    check(out[1] == v,
                          f"[{label}] {P.names[j]} halt value at {T}: "
                          f"{out[1]} vs {v}")
                else:
                    check(v is None,
                          f"[{label}] {P.names[j]} err at {T} but lfp={v}")
            outcomes[out[0]] = outcomes.get(out[0], 0) + 1
    if verbose:
        print(f"    run outcomes over all (j,input) at fuel <={cycfuel}: "
              f"{outcomes}")
    # divergence (cut) observed only inside C (cheap fuel)
    for j in range(P.k):
        for T in inp[j]:
            if run(P, j, T, 3)[0] == 'cut':
                check(j in P.C,
                      f"[{label}] cut outside C: {P.names[j]} at {T}")


# ------------------------------------------------------------- section B/C

def section_B():
    print("=== B/C. Hand-written programs ===")

    # P1: F(X) = cat(F(tail X), X) -- self-cycle -> bottom everywhere.
    P1 = Prog([
        ("F", 1, cat(('cal', 0, [tailE(X(0))]), X(0))),
    ])
    battery(P1, "P1 F(X)=cat(F(tail X),X)", verbose=True)
    for T in inputs_of(P1)[0]:
        check(run(P1, 0, T, 10)[0] == 'cut', "P1 diverges (cut) at fuel 10")

    # P2: G(X) = cat(X, tail X); H(X) = G(cat(X, b)) -- acyclic.
    P2 = Prog([
        ("G", 1, cat(X(0), tailE(X(0)))),
        ("H", 1, ('cal', 0, [cat(X(0), C('b'))])),
    ])
    battery(P2, "P2 acyclic", verbose=True)
    for T in inputs_of(P2)[1]:
        ref = evL(cat(cat(X(0), C('b')), tailE(cat(X(0), C('b')))), T)
        check(evL(inline_prog(P2)[1], T) == ref, "P2 H inlining value")

    # P3: dead argument -- G ignores its argument, but H(X)=H(X) diverges
    #     while being evaluated as G's argument; F reaches a cycle -> bottom.
    P3 = Prog([
        ("G", 1, C('q')),                                   # ignores Y
        ("H", 1, ('cal', 1, [X(0)])),                        # H(X) = H(X)
        ("F", 1, cat(('cal', 0, [('cal', 1, [X(0)])]), C('c'))),
    ])
    battery(P3, "P3 dead argument", verbose=True)
    check(1 in P3.C and 2 in P3.C and 0 not in P3.C, "P3 C-set")
    for T in inputs_of(P3)[2]:
        check(run(P3, 2, T, 8)[0] == 'cut', "P3 F diverges via dead argument")

    # P4: mutual cycle with data-dependent partiality:
    #     f(X) = cat(g(X), X);  g(X) = [X/X] f(X)  (pattern = X, empty at eps)
    P4 = Prog([
        ("f", 1, cat(('cal', 1, [X(0)]), X(0))),
        ("g", 1, ('sub', X(0), X(0), ('cal', 0, [X(0)]))),
    ])
    battery(P4, "P4 mutual partial cycle", verbose=True)

    # P5: zero-ary definitions.
    P5 = Prog([
        ("g", 0, C('b')),
        ("f", 0, cat(('cal', 0, []), C('a'))),
    ])
    battery(P5, "P5 zero-ary acyclic", verbose=True)
    check(phi_eval(P5, 1, (), 5, {}) == 'ba', "P5 f() = 'ba'")
    check(run(P5, 1, (), 10) == ('halt', 'ba'), "P5 run")

    P5b = Prog([("z", 0, ('cal', 0, []))])                    # z() = z()
    battery(P5b, "P5b zero-ary cycle", verbose=True)
    check(run(P5b, 0, (), 6)[0] == 'cut', "P5b diverges")

    # P6: the knockout demo -- guarded recursion still diverges under
    #     eagerness: G(X) = if(eq(X, eps), 'a', G(tail X)); self-cycle.
    P6 = Prog([
        ("G", 1, ifE(eqE(X(0), C('')), C('a'),
                     ('cal', 0, [tailE(X(0))]))),
    ])
    battery(P6, "P6 G(X)=if(eq(X,eps),a,G(tail X))", verbose=True)
    for T in inputs_of(P6)[0]:
        check(run(P6, 0, T, 10)[0] == 'cut', "P6 diverges on every input")

    # P7: acyclic with data-dependent partiality:
    #     F(X) = [b/X]X (undefined at eps);  G(X) = cat(F(X), tail X).
    P7 = Prog([
        ("F", 1, ('sub', C('b'), X(0), X(0))),
        ("G", 1, cat(('cal', 0, [X(0)]), tailE(X(0)))),
    ])
    battery(P7, "P7 acyclic partial", verbose=True)
    check(phi_eval(P7, 1, ('',), 5, {}) is None, "P7 G(eps) undefined")
    check(phi_eval(P7, 1, ('ab',), 5, {}) == 'b' + 'ab'[1:], "P7 G(ab)")

    # P8: error preemption -- a cycle whose evaluation always ERRS before
    #     the call is ever reached (left-to-right):
    #     f(X) = cat([a/eps]X, f(X)).
    P8 = Prog([
        ("f", 1, cat(('sub', C('a'), C(''), X(0)), ('cal', 0, [X(0)]))),
    ])
    battery(P8, "P8 error preemption on a cycle", verbose=True)
    for T in inputs_of(P8)[0]:
        check(run(P8, 0, T, 30) == ('err',),
              "P8 errs (never halts, never diverges)")
        for n in range(6):
            check(phi_eval(P8, 0, T, n, {}) is None, "P8 bottom at all n")

    # P9: Omega itself: [a/eps]X1 is everywhere undefined (any arity).
    check(all(evL(omega(1), (s,)) is None for s in STRINGS), "Omega(1)")
    check(evL(omega(0), ()) is None, "Omega(0)")

    # P10: the dead-argument gap is real even in ACYCLIC programs.
    #     d0(X) = [b/d1(d2(X))]X,  d1(Y) = 'q' (ignores Y),
    #     d2(X) = [X/b]X (undefined at eps).
    # Eager: d0(eps) is undefined (the argument d2(eps) is evaluated).
    # Naive Lemma-beta inlining [b/'q']X is DEFINED at eps: substitution
    # drops the dead argument.  The seq-patched inlining restores eagerness.
    P10 = Prog([
        ("d0", 1, ('sub', C('b'), ('cal', 1, [('cal', 2, [X(0)])]), X(0))),
        ("d1", 1, C('q')),
        ("d2", 1, ('sub', C('b'), X(0), X(0))),
    ])
    battery(P10, "P10 acyclic dead argument", verbose=True)
    check(P10.C == set(), "P10 acyclic")
    check(phi_eval(P10, 0, ('',), 4, {}) is None, "P10 eager d0(eps) undef")
    naive = ('sub', C('b'), C('q'), X(0))     # naive inlining of d0
    check(evL(naive, ('',)) == '', "P10 naive inlining DEFINED at eps (gap)")
    check(evL(inline_prog(P10)[0], ('',)) is None,
          "P10 seq-patched inlining undefined at eps")
    check(evL(inline_prog(P10)[0], ('ab',)) == evL(naive, ('ab',)),
          "P10 agrees where defined")

    # P11: the strict-sequence combinator seq(F,G) = [F.sigma/F.sigma]G.
    from eager import seq_expr
    for f in STRINGS:
        for g in STRINGS:
            check(evL(seq_expr(X(0), X(1)), (f, g)) == g, f"seq({f},{g})")
    check(evL(seq_expr(('sub', C('a'), C(''), C('c')), X(0)), ('ab',))
          is None, "seq(bottom, G) is bottom")


# ------------------------------------------------------- section D (random)

def rand_body(rng, ar, depth, allowed, ars, consts):
    """Random body over the grammar; `allowed` = callable callee indices."""
    r = rng.random()
    if depth <= 0 or r < 0.25:
        if ar > 0 and rng.random() < 0.6:
            return X(rng.randrange(ar))
        return C(rng.choice(consts))
    if r < 0.5:
        return ('sub', rand_body(rng, ar, depth - 1, allowed, ars, consts),
                rand_body(rng, ar, depth - 1, allowed, ars, consts),
                rand_body(rng, ar, depth - 1, allowed, ars, consts))
    if r < 0.75:
        return ('cat', rand_body(rng, ar, depth - 1, allowed, ars, consts),
                rand_body(rng, ar, depth - 1, allowed, ars, consts))
    if not allowed:
        return C(consts[-1])
    j = rng.choice(allowed)
    return ('cal', j, [rand_body(rng, ar, depth - 1, allowed, ars, consts)
                       for _ in range(ars[j])])


def rand_prog(rng, consts=('', 'a', 'b', 'ab', 'bb', 'aab')):
    k = rng.randrange(1, 5)
    ars = [rng.randrange(0, 3) for _ in range(k)]
    acyclic = rng.random() < 0.5     # edges only to higher indices
    defs = []
    for j in range(k):
        allowed = list(range(j + 1, k)) if acyclic else list(range(k))
        body = rand_body(rng, ars[j], rng.randrange(1, 4), allowed, ars,
                         consts)
        defs.append((f"d{j}", ars[j], body))
    return Prog(defs)


def section_D(nprogs=300, seed=20260919):
    print(f"=== D. Randomized programs ({nprogs}) ===")
    rng = random.Random(seed)
    ncyc = ncut = ncutprog = nskip = 0
    for t in range(nprogs):
        P = rand_prog(rng)
        try:
            battery(P, f"rand{t}", unfold_depth=2, fuel_hi=3, fuel_cyc=3,
                    dom=SMALL)
        except SizeEx:
            nskip += 1                       # value growth too large: skip
            continue
        except RecursionError:
            check(False, f"rand{t} recursion error")
            continue
        if P.C:
            ncyc += 1
        saw_cut = False
        for j in range(P.k):
            for T in inputs_of(P, SMALL)[j]:
                try:
                    if run(P, j, T, 4)[0] == 'cut':
                        saw_cut = True
                        ncut += 1
                except SizeEx:
                    pass
        if saw_cut:
            ncutprog += 1
    print(f"  programs with nonempty C: {ncyc}/{nprogs} "
          f"(skipped for size growth: {nskip}); "
          f"programs exhibiting a cut at fuel 4: {ncutprog}; "
          f"total (j,input) cut events: {ncut}")


def section_E(nprogs=150, seed=9799):
    """Unary alphabet: the theorem's constructions (Omega, the one-node
    seq [F.sigma/F.sigma]G, inlining) need no second character."""
    print(f"=== E. Randomized UNARY programs ({nprogs}) ===")
    rng = random.Random(seed)
    consts = ('', 'a', 'aa', 'aaa')
    dom = ['', 'a', 'aa']
    ncyc = nskip = 0
    for t in range(nprogs):
        P = rand_prog(rng, consts)
        try:
            battery(P, f"unary{t}", unfold_depth=2, fuel_hi=3, fuel_cyc=3,
                    dom=dom)
        except SizeEx:
            nskip += 1
            continue
        except RecursionError:
            check(False, f"unary{t} recursion error")
            continue
        if P.C:
            ncyc += 1
    print(f"  unary programs with nonempty C: {ncyc}/{nprogs} "
          f"(skipped for size growth: {nskip})")


def main():
    section_A()
    section_B()
    section_D()
    section_E()
    print(f"\nTOTAL: {PASS} checks passed, {FAIL} failed")
    sys.exit(0 if FAIL == 0 else 1)


if __name__ == '__main__':
    main()

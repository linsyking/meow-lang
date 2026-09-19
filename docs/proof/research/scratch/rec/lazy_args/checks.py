# checks.py -- verification suite for the lazy-args (call-by-need) semantics of
# L_rec.  Sections:
#   (a) dead-argument separation examples: lazy halts and equals the plain-L
#       value of the pruned/unfolded expression E'; eager diverges (or errors).
#   (b) input-independence of termination: syntactic prediction (live
#       dependency graph) vs. actual machine behaviour on ALL short inputs.
#   (c) well-founded programs agree with the pruned plain-L expression
#       (the live unfolding), including epsilon-pattern undefinedness.
#   (d) liveness through chains: dead through two levels of calls, and the
#       fixpoint propagating deadness through two definitions; plus the
#       forcing instrumentation on every run: forced <= S*, and every live
#       parameter of every started call is forced on halting runs.
#   (f) eager/lazy agreement when both halt.

import itertools
import random
import sys
import traceback

sys.setrecursionlimit(200000)

import lrec as L

DIV = 'DIVERGE'
ERR = 'UNDEF(eps-pattern)'


def allstr(n, sigma='ab'):
    for k in range(n + 1):
        for t in itertools.product(sigma, repeat=k):
            yield ''.join(t)


def inputs_for(nin, maxlen):
    if nin == 0:
        return [()]
    if nin == 1:
        return [(s,) for s in allstr(maxlen)]
    dom = list(allstr(maxlen))
    return list(itertools.product(dom, repeat=nin))


def run(machine_method, prog, inp, budget=20000):
    """('val', s) | ERR | DIV  (Timeout/RecursionError ~ divergence)."""
    m = L.Machine(prog, budget=budget)
    try:
        r = getattr(m, machine_method)(inp)
        return r
    except (L.Timeout, RecursionError):
        return DIV


# ---------------------------------------------------------------- section (a)

def section_a():
    print("=" * 72)
    print("SECTION (a): dead-argument examples -- lazy halts, eager does not")
    print("=" * 72)

    examples = {}

    def add(name, funcs, main, nin, eager_kind):
        examples[name] = (L.Program(funcs, main, nin), eager_kind)

    # The task's flagship: F(X) = G(X, F(tail X)),  G(A,B) = A  (B dead in G).
    add('deadarg_tail (conjecture 4 example)',
        {'F': (1, L.Call('G', L.V(0), L.Call('F', L.TAIL(L.V(0))))),
         'G': (2, L.V(0))},
        L.Call('F', L.V(0)), 1, 'diverge')

    # Same without tail: F(X) = G(X, F(X)), G(A,B) = A  -- identity under lazy.
    add('deadarg_id',
        {'F': (1, L.Call('G', L.V(0), L.Call('F', L.V(0)))),
         'G': (2, L.V(0))},
        L.Call('F', L.V(0)), 1, 'diverge')

    # Smaller: constant function.  F(X) = G(F(X)), G(A) = c.
    add('deadarg_const',
        {'F': (1, L.Call('G', L.Call('F', L.V(0)))),
         'G': (1, L.K('a'))},
        L.Call('F', L.V(0)), 1, 'diverge')

    # Zero-ary variant, the smallest of all.
    add('deadarg_zero',
        {'F': (0, L.Call('G', L.Call('F'))),
         'G': (1, L.K('a'))},
        L.Call('F'), 0, 'diverge')

    # Mirror: dead slot first.  F(X) = G(F(X), X), G(A,B) = B.
    add('deadarg_mirror',
        {'F': (1, L.Call('G', L.Call('F', L.V(0)), L.V(0))),
         'G': (2, L.V(1))},
        L.Call('F', L.V(0)), 1, 'diverge')

    # Mutual recursion through the dead slot.
    add('deadarg_mutual',
        {'F': (1, L.Call('H', L.V(0))),
         'H': (1, L.Call('G', L.V(0), L.Call('F', L.V(0)))),
         'G': (2, L.V(0))},
        L.Call('F', L.V(0)), 1, 'diverge')

    # Eager ERRORS (not diverges) on the dead argument; lazy computes.
    add('deadarg_eagererr',
        {'F': (1, L.Call('G', L.V(0),
                         L.Pas(L.K('a'), L.K(''), L.V(0)))),
         'G': (2, L.V(0))},
        L.Call('F', L.V(0)), 1, 'err')

    for name, (prog, eager_kind) in examples.items():
        print("\n---", name, "( size", prog.size(), ")")
        print(prog.show())
        S = L.liveness(prog)
        print("  S* =", sorted(S))
        print("  terminates_lazy (graph):", L.terminates_lazy(prog),
              " terminates_eager (graph):", L.terminates_eager(prog))
        U, n = L.unfold(prog, S, cap=5000)
        print("  live unfolding E' =", L.show(U), "  (%d unfolding nodes)" % n)
        allok = True
        for inp in inputs_for(prog.ninputs, 4):
            env = {i: s for i, s in enumerate(inp)}
            lz = run('run_lazy', prog, inp)
            eg = run('run_eager', prog, inp)
            pl = L.eval_plain(U, env)
            eg_ok = (eg == DIV) if eager_kind == 'diverge' else (eg == ('err',))
            if not ((lz == pl) and eg_ok):
                allok = False
                print("   MISMATCH", inp, "lazy", lz, "plain", pl, "eager", eg)
        print("  lazy == plain-L(E') on all inputs of length<=4, eager %s "
              "everywhere:" % eager_kind, "OK" if allok else "FAIL")
        assert allok
    print("\nSECTION (a): OK")


# ---------------------------------------------------------------- section (d)

def section_d():
    print()
    print("=" * 72)
    print("SECTION (d): liveness through chains")
    print("=" * 72)

    # The recursive call is dead through TWO levels of calls: it sits in
    # argument 1 of a call to H, which itself sits in the (dead) argument 2 of
    # the call to G.  (H's parameters are live in H; the CALL to H is dead.)
    prog = L.Program(
        {'F': (1, L.Call('G', L.V(0),
                         L.Call('H', L.Call('F', L.TAIL(L.V(0))), L.V(0)))),
         'G': (2, L.V(0)),
         'H': (2, L.V(0))},
        L.Call('F', L.V(0)), 1)
    print("\n--- dead-through-two-call-levels")
    print(prog.show())
    S = L.liveness(prog)
    print("  S* =", sorted(S))
    print("  (note: (H,1) and (H,2) are live *in H*, but the only call to H")
    print("   sits in G's dead argument 2, so neither is ever forced)")
    U, n = L.unfold(prog, S, cap=5000)
    print("  live unfolding E' =", L.show(U))
    ok = True
    for inp in inputs_for(1, 4):
        lz = run('run_lazy', prog, inp)
        pl = L.eval_plain(U, {0: inp[0]})
        eg = run('run_eager', prog, inp)
        if lz != pl or eg != DIV:
            ok = False
            print("   MISMATCH", inp, lz, pl, eg)
    print("  lazy == E' on all inputs, eager diverges:", "OK" if ok else "FAIL")
    assert ok

    # The fixpoint itself propagating deadness through two definitions:
    # K(C) = c   (C unused),  M(B) = K(B),  P(A) = Q(M(A)),  Q(U) = U.
    # (K,1) dead -> B occurs only in a dead slot -> (M,1) dead -> A occurs only
    # in a dead slot -> (P,1) dead.  Two Kleene steps needed.
    prog2 = L.Program(
        {'P': (1, L.Call('Q', L.Call('M', L.V(0)))),
         'Q': (1, L.V(0)),
         'M': (1, L.Call('K', L.V(0))),
         'K': (1, L.K('a'))},
        L.Call('P', L.V(0)), 1)
    print("\n--- fixpoint deadness through two definitions")
    print(prog2.show())
    S2 = L.liveness(prog2)
    print("  S* =", sorted(S2), " (expect exactly {(Q,0)}; (P,0),(M,0),(K,0) dead)")
    assert S2 == {('Q', 0)}
    U2, _ = L.unfold(prog2, S2, cap=5000)
    print("  live unfolding E' =", L.show(U2))
    ok = True
    for inp in inputs_for(1, 4):
        lz = run('run_lazy', prog2, inp)
        pl = L.eval_plain(U2, {0: inp[0]})
        eg = run('run_eager', prog2, inp)
        if not (lz == pl == eg == ('val', 'a')):
            ok = False
            print("   MISMATCH", inp, lz, pl, eg)
    print("  lazy == E' == eager == 'a' on all inputs (P,Q,M,K all agree; only",
          "the deadness chain matters here):", "OK" if ok else "FAIL")
    assert ok

    print("\nSECTION (d): OK")


# ---------------------------------------------------------------- corpus

def corpus_curated():
    progs = []

    def add(name, funcs, main, nin):
        progs.append((name, L.Program(funcs, main, nin)))

    add('diverge_self_live_call',            # F(X)=cat(X,F(X)): live call chain
        {'F': (1, L.Cat(L.V(0), L.Call('F', L.V(0))))}, L.Call('F', L.V(0)), 1)
    add('diverge_deadarg_livecall',          # dead arg does NOT save: call live
        {'F': (1, L.Cat(L.K('c'.replace('c', 'a')), L.Call('F', L.V(0))))},
        L.Call('F', L.V(0)), 1)
    add('diverge_mutual_swap',
        {'F': (2, L.Cat(L.V(0), L.Call('F', L.V(1), L.V(0))))},
        L.Call('F', L.V(0), L.K('a')), 2)
    add('diverge_param_loop',                 # F(X)=F(X): dead arg, live chain
        {'F': (1, L.Call('F', L.V(0)))}, L.Call('F', L.V(0)), 1)
    add('halt_plain_pipeline',                # no recursion at all
        {'F': (1, L.Pas(L.V(0), L.K('b'), L.V(0)))}, L.Call('F', L.V(0)), 1)
    add('halt_nonrec_call',
        {'F': (1, L.Call('G', L.V(0))),
         'G': (1, L.Pas(L.K('ab'), L.K('a'), L.V(0)))}, L.Call('F', L.V(0)), 1)
    add('halt_diamond',                       # F calls G twice (duplication)
        {'F': (1, L.Cat(L.Call('G', L.V(0)), L.Call('G', L.Call('G', L.V(0))))),
         'G': (1, L.Pas(L.K('ba'), L.K('a'), L.V(0)))}, L.Call('F', L.V(0)), 1)
    add('halt_eps_pattern',                   # epsilon pattern: data-dependent
        {'F': (1, L.Call('G', L.V(0), L.Pas(L.K('a'), L.V(0), L.K('a')))),
         'G': (2, L.V(0))}, L.Call('F', L.V(0)), 1)
    add('halt_headtail',
        {'F': (1, L.Cat(L.HEAD(L.V(0)), L.Call('G', L.TAIL(L.V(0))))),
         'G': (1, L.Pas(L.K('a'), L.K('b'), L.V(0)))}, L.Call('F', L.V(0)), 1)
    add('halt_deadarg_in_deadarg',            # dead arg containing dead call
        {'F': (1, L.Call('G', L.V(0), L.Call('H', L.Call('F', L.V(0)), L.V(0)))),
         'G': (2, L.V(0)),
         'H': (2, L.V(1))}, L.Call('F', L.V(0)), 1)
    add('diverge_deadarg_err_never_reached',  # lazy diverges (live F chain)
        {'F': (1, L.Call('G', L.Call('F', L.V(0)), L.V(0))),
         'G': (2, L.V(1))}, L.Call('F', L.V(0)), 1)
    add('halt_deep_chain',
        {'A': (1, L.Call('B', L.V(0))),
         'B': (1, L.Call('C', L.V(0))),
         'C': (1, L.Call('D', L.V(0))),
         'D': (1, L.Pas(L.K('bb'), L.K('a'), L.V(0)))},
        L.Call('A', L.V(0)), 1)
    return progs


def corpus_random(n=250, seed=20260919):
    rng = random.Random(seed)
    progs = []
    seen = set()
    for _ in range(n):
        nf = rng.randint(1, 3)
        names = ['F', 'G', 'H'][:nf]
        ars = [rng.randint(0, 2) for _ in names]
        # main: call a random function with input vars
        fi = rng.randrange(nf)
        nin = ars[fi]
        main = L.Call(names[fi], *[L.V(i) for i in range(nin)])
        funcs = {}

        def rand_expr(depth, nvars):
            r = rng.random()
            if depth <= 0 or r < 0.25:
                if nvars and rng.random() < 0.6:
                    return L.V(rng.randrange(nvars))
                return L.K(rng.choice(['', 'a', 'b', 'ab', 'ba', 'aa']))
            if r < 0.55:
                return L.Pas(rand_expr(depth - 1, nvars),
                             rand_expr(depth - 1, nvars),
                             rand_expr(depth - 1, nvars))
            if r < 0.8:
                return L.Cat(rand_expr(depth - 1, nvars),
                             rand_expr(depth - 1, nvars))
            j = rng.randrange(nf)
            return L.Call(names[j],
                          *[rand_expr(depth - 1, nvars) for _ in range(ars[j])])

        for nm, ar in zip(names, ars):
            funcs[nm] = (ar, rand_expr(rng.randint(1, 3), ar))
        p = L.Program(funcs, main, nin)
        key = p.show()
        if key in seen:
            continue
        seen.add(key)
        progs.append(('rand%03d' % len(progs), p))
    return progs


# ------------------------------------------------------- sections (b), (c), (f)

def check_program(name, prog, maxlen, stats, budget=20000, cap=100000):
    """Run all four checks on one program.  Returns True iff all pass."""
    S = L.liveness(prog)
    pred_halt = L.dep_graph_acyclic_from_main(prog, S)
    pred_eager = L.terminates_eager(prog)
    U = None
    if pred_halt:
        try:
            U, n = L.unfold(prog, S, cap=cap)
        except L.CapExceeded:
            stats['unfold_cap'] += 1
            U = None
    all_ok = True
    inp_list = inputs_for(prog.ninputs, maxlen)
    for inp in inp_list:
        env = {i: s for i, s in enumerate(inp)}
        # ---- (b) input-independence of termination
        m = L.Machine(prog, budget=budget)
        try:
            lz = m.ev(prog.main, {i: ('inp', s) for i, s in enumerate(inp)})
            halted = True
        except (L.Timeout, RecursionError):
            lz = DIV
            halted = False
        if halted != pred_halt:
            all_ok = False
            print(f"  [{name}] TERMINATION MISMATCH on {inp}: machine halted="
                  f"{halted}, predicted={pred_halt}")
            break
        if not halted:
            # diverging run: check Confinement on the partial run
            if not m.forced <= S:
                all_ok = False
                print(f"  [{name}] CONFINEMENT VIOLATION: forced {m.forced - S}")
            continue
        stats['runs'] += 1
        # ---- forcing instrumentation on a halting run
        if not m.forced <= S:
            all_ok = False
            print(f"  [{name}] CONFINEMENT VIOLATION: forced {m.forced - S}")
        for g in m.started:
            for i in range(prog.funcs[g][0]):
                if (g, i) in S and (g, i) not in m.forced:
                    all_ok = False
                    print(f"  [{name}] FULL-VISITATION VIOLATION: live ({g},{i})"
                          f" of started call never forced")
        # ---- (c) agreement with the pruned plain-L expression
        if U is not None:
            pl = L.eval_plain(U, env)
            if lz != pl:
                all_ok = False
                print(f"  [{name}] DENOTATION MISMATCH on {inp}: lazy {lz} vs"
                      f" unfolding {pl}")
        # ---- (f) eager/lazy agreement when both halt:
        #      a value from eager forces the same value from lazy (Dead
        #      Irrelevance); eager may additionally err on a dead argument
        #      where lazy yields a value; lazy may never err where eager
        #      yields a value.
        if pred_eager:
            me = L.Machine(prog, budget=budget)
            try:
                eg = me.ee(prog.main, {i: ('inp', s) for i, s in enumerate(inp)})
            except (L.Timeout, RecursionError):
                eg = DIV
            if eg[0] == 'val' and lz != eg:
                all_ok = False
                print(f"  [{name}] EAGER/LAZY VALUE MISMATCH on {inp}: {eg} vs {lz}")
            if lz == ('err',) and eg[0] == 'val':
                all_ok = False
                print(f"  [{name}] LAZY ERR BUT EAGER VALUE on {inp}: {eg} vs {lz}")
            if eg == ('err',) and lz != ('err',):
                stats['eager_err_sep'] += 1
        # eager divergence must be total when predicted
        if not pred_eager and all_ok:
            me = L.Machine(prog, budget=budget)
            try:
                eg = me.ee(prog.main, {i: ('inp', s) for i, s in enumerate(inp)})
                halted_e = eg[0] in ('val', 'err')
            except (L.Timeout, RecursionError):
                halted_e = False
            if halted_e:
                all_ok = False
                print(f"  [{name}] EAGER TERMINATION MISMATCH on {inp}")
    if all_ok:
        stats['pass'] += 1
        if pred_halt:
            stats['lazy_halt'] += 1
            if pred_eager:
                stats['both_halt'] += 1
            else:
                stats['lazy_only'] += 1
        else:
            stats['lazy_div'] += 1
    else:
        stats['fail'] += 1
    return all_ok


def sections_bcf():
    print()
    print("=" * 72)
    print("SECTIONS (b),(c),(f): input-independence, plain-L agreement,")
    print("eager/lazy agreement -- curated + random corpus")
    print("=" * 72)
    stats = {'pass': 0, 'fail': 0, 'runs': 0, 'lazy_halt': 0, 'lazy_div': 0,
             'lazy_only': 0, 'both_halt': 0, 'unfold_cap': 0, 'eager_err_sep': 0}
    corpus = corpus_curated() + corpus_random(n=250, seed=20260919)
    for name, prog in corpus:
        maxlen = 4 if prog.ninputs <= 1 else 3
        if not check_program(name, prog, maxlen, stats):
            print("  FAILING PROGRAM:")
            print(prog.show())
            return stats, False
    print(f"\n  corpus: {len(corpus)} programs, {stats['runs']} halting runs")
    print(f"  lazy-halting programs: {stats['lazy_halt']}"
          f"  (of which eager-halting: {stats['both_halt']},"
          f" lazy-only (separations): {stats['lazy_only']})")
    print(f"  lazy-diverging programs: {stats['lazy_div']}"
          f"  unfolding cap hits: {stats['unfold_cap']}")
    print(f"  eager-err/lazy-value separations on inputs: {stats['eager_err_sep']}")
    print(f"  passed: {stats['pass']}   FAILED: {stats['fail']}")
    ok = stats['fail'] == 0
    print("SECTIONS (b),(c),(f):", "OK" if ok else "FAIL")
    return stats, ok


if __name__ == '__main__':
    section_a()
    section_d()
    stats, ok = sections_bcf()
    print()
    print("=" * 72)
    if ok:
        print("ALL CHECKS PASSED")
    else:
        print("SOME CHECKS FAILED")
    print("=" * 72)
    sys.exit(0 if ok else 1)

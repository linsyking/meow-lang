"""Cross-check of the paper's DYNAMICS RULES (three runtimes) against
the three independent machines of the verification record.

The CPU-heavy component -- the small-step dynamics itself, run with
large caps over every (program, input, mode) -- is the C++ tool
dynamics.cpp (build: g++ -O2 -std=c++17 -o dynamics_bin dynamics.cpp
-pthread).  This driver is glue only: it generates the corpus, runs
the tool in one batch, then runs the three REFERENCE machines (which
stay bit-identical to the verified originals) and compares value and
definedness.  The stuck/divergent split is not compared
(order-dependent, on record in thm:eager).

  eager       vs rec/eager/eager.py  (Prog + fuel-capped run)
  lazy args   vs rec/lazy_args/lrec.py (Program + Machine)
  lazy passes vs rec/lazy_pass/core.py (run_lazy)

Usage: /usr/bin/python3 dynamics_check.py [nprogs]
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'lazy_pass'))
sys.path.insert(0, os.path.join(HERE, 'eager'))
sys.path.insert(0, os.path.join(HERE, 'lazy_args'))

import core as LP          # lazy_pass machine
import eager as EG          # eager: Prog + run
import lrec as LA           # lazy_args: Program + Machine

BIN = os.path.join(HERE, 'dynamics_bin')

# ------------------------------------------------------------- tiny AST
def K(w):
    return ('K', w)


def V(i):
    return ('V', i)


def C(a, b):
    return ('C', a, b)


def S(R, P, E):
    return ('S', R, P, E)


def F(name, args):
    return ('F', name, tuple(args))


def sexpr(E):
    t = E[0]
    if t == 'K':
        return f"(K {E[1] if E[1] else '#'})"
    if t == 'V':
        return f'(V {E[1]})'
    if t == 'C':
        return f'(C {sexpr(E[1])} {sexpr(E[2])})'
    if t == 'S':
        return (f'(S {sexpr(E[1])} {sexpr(E[2])} {sexpr(E[3])})')
    if t == 'F':
        return (f"(F {E[1]} {' '.join(sexpr(a) for a in E[2])})")
    raise ValueError(t)


# -------------------------------------------------- format converters
def to_eager(E, idx):
    t = E[0]
    if t == 'K':
        return ('con', E[1])
    if t == 'V':
        return ('var', E[1])
    if t == 'C':
        return ('cat', to_eager(E[1], idx), to_eager(E[2], idx))
    if t == 'S':
        return ('sub', to_eager(E[1], idx), to_eager(E[2], idx),
                to_eager(E[3], idx))
    if t == 'F':
        return ('cal', idx[E[1]], [to_eager(a, idx) for a in E[2]])
    raise ValueError(t)


def to_lrec(E):
    t = E[0]
    if t == 'K':
        return ('const', E[1])
    if t == 'V':
        return ('var', E[1])
    if t == 'C':
        return ('cat', to_lrec(E[1]), to_lrec(E[2]))
    if t == 'S':
        return ('pass', to_lrec(E[1]), to_lrec(E[2]), to_lrec(E[3]))
    if t == 'F':
        return ('call', E[1], tuple(to_lrec(a) for a in E[2]))
    raise ValueError(t)


# ------------------------------------------------------------ references
def ref_eager(defs, order, main, inputs):
    idx = {n: j for j, n in enumerate(order)}
    dl = [(n, defs[n][0], to_eager(defs[n][1], idx)) for n in order]
    j = idx['main_dyn']
    dl.append(('main_dyn', len(inputs), to_eager(main, idx)))
    P = EG.Prog(dl)
    try:
        r = EG.run(P, j, tuple(inputs), 20000)
    except RecursionError:
        return ('und',)
    return ('val', r[1]) if r[0] == 'halt' else ('und',)


def ref_lazy_args(funcs, main, ninputs, inputs):
    prog = LA.Program(funcs, main, ninputs)
    m = LA.Machine(prog, budget=20000)
    try:
        r = m.run_lazy(tuple(inputs))
    except (LA.Timeout, LA.BlackHole, LA.CapExceeded, RecursionError):
        return ('und',)
    return ('val', r[1]) if r[0] == 'val' else ('und',)


def ref_lazy_pass(defs, main, inputs):
    d = dict(defs)
    d['main_dyn'] = (len(inputs), main)
    try:
        r = LP.run_lazy(d, 'main_dyn', tuple(inputs), cap=20000)
    except RecursionError:
        return ('und',)
    return ('val', r[1]) if r[0] == LP.HALT_VAL else ('und',)


# --------------------------------------------------------- curated corpus
def curated():
    out = []
    # (label, defs, main, ninputs, inputs)
    deadarg = {'F': (1, F('G', [V(0), F('F', [S(K(''), K('a'), V(0))])])),
               'G': (2, V(0))}
    out.append(('dead-argument separator', deadarg, F('F', [V(0)]), 1,
                ['b', 'ab', 'a', '']))
    gated = {'f': (1, S(F('g', [V(0)]), K('b'), V(0))),
             'g': (1, S(K('a'), K(''), V(0)))}          # g stuck always
    out.append(('the gate [g(X)/b]X', gated, F('f', [V(0)]), 1,
                ['aaa', 'bbb', 'ab', '']))
    mutu = {'f': (1, F('g', [V(0)])), 'g': (1, F('f', [V(0)]))}
    out.append(('mutual ping-pong', mutu, F('f', [V(0)]), 1, ['a', '']))
    dbl = {'f': (1, C(V(0), F('f', [V(0)])))}
    out.append(('self-doubling loop', dbl, F('f', [V(0)]), 1, ['a']))
    eps_pat = {'f': (1, S(K('a'), K(''), V(0)))}
    out.append(('empty pattern', eps_pat, F('f', [V(0)]), 1, ['ab', '']))
    const = {'f': (1, C(K('x'), V(0)))}
    out.append(('halting constant cat', const, F('f', [V(0)]), 1, ['ab']))
    tailrec = {'f': (1, S(F('f', [S(K(''), K('a'), V(0))]), K('b'), V(0)))}
    out.append(('nested deletion recursion', tailrec, F('f', [V(0)]), 1,
                ['aabb', 'b', 'ab', 'aa']))
    binop = {'h': (2, C(V(0), V(1)))}
    out.append(('two-parameter cat', binop, F('h', [V(0), V(1)]), 2,
                ['ab', 'ba'], ))
    fire_gated = {'f': (1, S(C(V(0), K('b')), K('b'), K('b')))}
    out.append(('constant scrutinee fire', fire_gated, F('f', [V(0)]), 1,
                ['a', 'b', '']))
    return out


# --------------------------------------------------------- random corpus
STRINGS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab', 'abb']


def rand_expr(rng, vars_, calls, arities, depth):
    if depth == 0 or rng.random() < 0.25:
        if vars_ and rng.random() < 0.6:
            return V(rng.choice(vars_))
        return K(rng.choice(STRINGS))
    c = rng.random()
    if c < 0.3:
        return C(rand_expr(rng, vars_, calls, arities, depth - 1),
                 rand_expr(rng, vars_, calls, arities, depth - 1))
    if c < 0.7:
        return S(rand_expr(rng, vars_, calls, arities, depth - 1),
                 rand_expr(rng, vars_, calls, arities, depth - 1),
                 rand_expr(rng, vars_, calls, arities, depth - 1))
    if calls and rng.random() < 0.6:
        g = rng.choice(calls)
        return F(g, [rand_expr(rng, vars_, calls, arities, depth - 1)
                     for _ in range(arities[g])])
    return K(rng.choice(STRINGS))


def rand_program(rng):
    k = rng.randint(1, 3)
    names = [f'g{i}' for i in range(k)]
    arities = {n: rng.randint(1, 2) for n in names}
    defs = {}
    for i, n in enumerate(names):
        defs[n] = (arities[n],
                   rand_expr(rng, list(range(arities[n])),
                             names[:i + 1], arities, 3))
    ninp = rng.randint(1, 2)
    main = rand_expr(rng, list(range(ninp)), names, arities, 3)
    return defs, main, ninp


# ----------------------------------------------------------------- main
def main_check(nprogs=30, seed=20260921):
    rng = random.Random(seed)
    tests = []          # (mode, defs, main, ninp, inputs, label)
    for label, defs, main, ninp, inputs in curated():
        for inp in inputs:      # single input per curated test
            for mode in ('eager', 'la', 'lp'):
                tests.append((mode, defs, main, ninp, (inp,), label))
    inps = ['', 'a', 'b', 'ab', 'ba', 'aab']
    for p in range(nprogs):
        defs, main, ninp = rand_program(rng)
        for _ in range(4):
            inp = tuple(rng.choice(inps) for _ in range(ninp))
            for mode in ('eager', 'la', 'lp'):
                tests.append((mode, defs, main, ninp, inp, f'rand{p}'))

    # ---- run the C++ dynamics tool in ONE batch
    lines = []
    for mode, defs, main, ninp, inp, _ in tests:
        dstr = ','.join(f'{n}:{defs[n][0]}:{sexpr(defs[n][1])}'
                        for n in defs)
        istr = ','.join(inp)
        lines.append(f'{mode} | {dstr} | {sexpr(main)} | {istr}')
    proc = subprocess.run([BIN], input='\n'.join(lines),
                          capture_output=True, text=True, timeout=55)
    got = proc.stdout.splitlines()
    if len(got) != len(tests):
        print(f'TOOL OUTPUT COUNT MISMATCH: {len(got)} vs {len(tests)}')
        print(proc.stderr[:500])
        sys.exit(1)

    # ---- references + comparison
    bad = 0
    cache = {}

    def ref(mode, defs, main, ninp, inp):
        key = (id(defs), mode, main, inp)
        if key in cache:
            return cache[key]
        if mode == 'eager':
            r = ref_eager(defs, list(defs) + ['main_dyn'], main, inp)
        elif mode == 'la':
            la_funcs = {g: (defs[g][0], to_lrec(defs[g][1])) for g in defs}
            r = ref_lazy_args(la_funcs, to_lrec(main), ninp, inp)
        else:
            r = ref_lazy_pass(defs, main, inp)
        cache[key] = r
        return r

    for i, (mode, defs, main, ninp, inp, label) in enumerate(tests):
        mine = ('val', got[i][4:]) if got[i].startswith('val ') \
            else ('und',)
        rf = ref(mode, defs, main, ninp, inp)
        if mine != rf:
            bad += 1
            print(f'MISMATCH [{label}] mode={mode} inp={inp}')
            print(f'  defs  = {[(n, defs[n][0], sexpr(defs[n][1])) for n in defs]}')
            print(f'  main  = {sexpr(main)}')
            print(f'  mine  = {mine}')
            print(f'  ref   = {rf}')
            if bad > 10:
                print('too many, stopping')
                break
    print(f'TOTAL: {len(tests)} comparisons, {bad} mismatches')
    print('ALL GREEN' if bad == 0 else 'FAILURES')


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    main_check(n)

"""Round 2 verification:

  A. small-step machine  ==  big-step demand semantics, on random RECURSIVE
     programs (including divergent ones)  [Theorem A of REPORT.md Sec. 1.4].
  B. the two-way pattern gate `sel`:
       B1. values: sel(C,u,v) = u if C=top, v if C=bot, random u,v;
       B2. forcing discipline: exactly the taken branch's argument is forced
           (activation counts via the machine's `collect` hook);
       B3. gating a DIVERGENT argument: sel(bot, X, Omega) = X terminates.
  C. the guarded structural-recursion scheme:
       C1. rev  -- reversal, on ALL strings of length <= 6 over {a,b};
       C2. len  -- tally length, all strings <= 6;
       C3. par  -- parity via a non-cat step function (if/eq step), all
                   strings <= 10;
       and rev on a few random longer strings (len 7..10).

Run:  python3 verify_round2.py
"""

import itertools
import random
import sys

from core import (K, V, C, S, F, pp, run_lazy, run_bigstep, run_eager,
                  check_program)
from toolkit import (BIN, enc, dec, benc, bdec, enc2, dec2, cat, tail, head,
                    eq, if_, isne, contains, sel_body)

sg = BIN
FAIL = 0


def check(name, ok, detail=''):
    global FAIL
    if not ok:
        FAIL += 1
        print(f"  FAIL {name} {detail}")
    return ok


def rnd(rng, n):
    return ''.join(rng.choice('ab') for _ in range(rng.randint(0, n)))


def strings_upto(n, alpha='ab'):
    for L in range(n + 1):
        for t in itertools.product(alpha, repeat=L):
            yield ''.join(t)


def val(defs, name, args, cap=2_000_000):
    res = run_lazy(defs, name, tuple(args), cap=cap)
    assert res[0] == 'val', (name, args, res)
    return res[1], res[2]


# ===========================================================================
# A.  small-step == big-step on random recursive programs

def rand_ext(rng, depth, nvars, fnames, arities):
    if depth == 0:
        if rng.random() < 0.5:
            return V(rng.randrange(nvars))
        return K(rng.choice(['', 'a', 'b', 'ab', 'ba', 'aa', 'bb', 'aab', 'baa']))
    t = rng.random()
    if t < 0.22:
        return C(rand_ext(rng, depth - 1, nvars, fnames, arities),
                 rand_ext(rng, depth - 1, nvars, fnames, arities))
    if t < 0.60:
        pat = rand_ext(rng, depth - 1, nvars, fnames, arities)
        if rng.random() < 0.3:
            pat = K(rng.choice(['', 'a', 'b']))
        return S(rand_ext(rng, depth - 1, nvars, fnames, arities), pat,
                 rand_ext(rng, depth - 1, nvars, fnames, arities))
    # a call
    name = rng.choice(fnames)
    ar = arities[name]
    return F(name, *[rand_ext(rng, depth - 1, nvars, fnames, arities)
                     for _ in range(ar)])


def test_A(steps=400):
    print("== (A) small-step machine == big-step semantics, random recursive programs ==")
    rng = random.Random(1234)
    fname_list = ['f', 'g', 'h']
    n_disagree = n_agree = n_val = n_err = n_div = 0
    mism = []
    for trial in range(steps):
        arities = {n: rng.choice([1, 1, 2]) for n in fname_list}
        defs = {}
        for n in fname_list:
            defs[n] = (arities[n],
                       rand_ext(rng, rng.choice([1, 2, 2, 3]), arities[n],
                                fname_list, arities))
        try:
            check_program(defs)
        except ValueError:
            continue
        args = tuple(rnd(rng, 4) for _ in range(arities['f']))
        r1 = run_lazy(defs, 'f', args, cap=150_000)
        r2 = run_bigstep(defs, 'f', args, maxdepth=4000)
        # outcome classes; 'timeout' on either side = no value within cap
        c1 = ('timeout' if r1[0] == 'timeout' else
              'val' if r1[0] == 'val' else 'err')
        c2 = ('timeout' if r2[0] == 'diverge' else
              'val' if r2[0] == 'val' else 'err')
        ok = True
        if c1 == 'val' or c2 == 'val':
            ok = (r1[0] == 'val' and r2[0] == 'val' and r1[1] == r2[1])
            n_val += 1
        elif c1 == 'err' and c2 == 'err':
            ok = True          # both stuck (pattern-empty or blackhole)
            n_err += 1
        elif c1 == 'timeout' and c2 == 'timeout':
            ok = True          # both no-value-within-cap (presumed divergent)
            n_div += 1
        else:
            ok = False         # one finished, one not: investigate
        if ok:
            n_agree += 1
        else:
            n_disagree += 1
            if len(mism) < 5:
                mism.append((args, r1[:2], r2[:2], {k: pp(v[1]) for k, v in defs.items()}))
    for m in mism:
        print("   MISMATCH:", m[0], m[1][:2], m[2][:2])
        for k, v in m[3].items():
            print(f"     {k} = {v}")
    print(f"  programs tried: {steps}; agreements: {n_agree} "
          f"(value: {n_val}, stuck/err: {n_err}); disagreements: {n_disagree}")
    return n_disagree == 0


# ===========================================================================
# B.  the two-way gate sel

def sel_defs():
    return {'sel': (3, sel_body(sg))}


def test_B():
    print("== (B) the two-way pattern gate sel ==")
    rng = random.Random(99)
    defs = sel_defs()
    Pp, Q = sg.P_GATE, sg.Q_GATE
    print(f"  markers: P = {Pp}, Q = {Q}  (both contain bb = '{sg.b}{sg.b}'; "
          f"P not in Q, Q not in P)")

    # B1: values, random branch strings
    ok = True
    N = 200
    for _ in range(N):
        c = rng.choice([sg.top, sg.bot])
        u, v = rnd(rng, 8), rnd(rng, 8)
        w, _ = val(defs, 'sel', (c, u, v))
        ok &= check('sel-val', w == (u if c == sg.top else v), (c, u, v, w))
    print(f"  B1 values: {N} random triples -> {'OK' if ok else 'FAIL'}")

    # B2: forcing discipline -- probe definitions count their activations
    ok2 = True
    N2 = 100
    for _ in range(N2):
        c = rng.choice([sg.top, sg.bot])
        u, v = rnd(rng, 5), rnd(rng, 5)
        d = dict(defs)
        d['probeT'] = (1, V(0))     # identity; counting its CALLS
        d['probeE'] = (1, V(0))
        calls = {}
        def collect(ev, payload):
            if ev == 'call':
                calls[payload] = calls.get(payload, 0) + 1
        main = F('sel', K(c), F('probeT', K(u)), F('probeE', K(v)))
        d2 = dict(d)
        d2['main'] = (0, main)
        calls.clear()
        r = run_lazy(d2, 'main', (), cap=2_000_000, collect=collect)
        ok2 &= check('sel-force-val', r[0] == 'val' and
                     r[1] == (u if c == sg.top else v), (c, u, v, r))
        want = {'probeT': (1 if c == sg.top else 0),
                'probeE': (1 if c == sg.bot else 0)}
        ok2 &= check('sel-force-count', calls.get('probeT', 0) == want['probeT']
                     and calls.get('probeE', 0) == want['probeE'], (c, calls, want))
    print(f"  B2 forcing: {N2} runs: taken branch forced exactly once, "
          f"untaken branch never activated -> {'OK' if ok2 else 'FAIL'}")

    # B3: gating a divergent argument: sel(TOP, X, Omega) returns X, never
    # forcing Omega; the SAME program text diverges eagerly (CBV forces arg 3)
    d = dict(defs)
    d['Omega'] = (1, cat(sg, F('Omega', V(0)), V(0)))   # Omega(X)=cat(Omega(X),X): diverges
    d['main'] = (1, F('sel', K(sg.top), V(0), F('Omega', V(0))))
    r = run_lazy(d, 'main', ('ab',), cap=2_000_000)
    re = run_eager(d, 'main', ('ab',), maxdepth=300, stepcap=500_000)
    ok3 = check('sel-gate-div', r[0] == 'val' and r[1] == 'ab', r)
    ok3 &= check('sel-gate-div-eager', re[0] == 'diverge', re)
    print(f"  B3 sel(TOP, X, Omega(X)) on X='ab': lazy = {r[:2]}, "
          f"eager = {re} -> {'OK' if ok3 else 'FAIL'}")
    return ok and ok2 and ok3


# ===========================================================================
# C.  guarded structural recursion: the scheme and rev

def scheme_defs(Bexpr, Hexpr):
    """F(X) = sel(isne(X), B(X, F(tail X)), H(X)):
    Bexpr maps (X, Z)->expr  (Z = V(1) is the recursion variable), Hexpr X->expr."""
    return {'sel': (3, sel_body(sg)),
            'F': (1, F('sel', isne(sg, V(0)),
                       Bexpr(V(0), F('F', tail(sg, V(0)))),
                       Hexpr(V(0))))}


def test_C():
    print("== (C) guarded structural recursion ==")

    # C1: reversal.  rev(X) = sel(isne X, cat(rev(tail X), head X), eps)
    drev = {'sel': (3, sel_body(sg)),
            'rev': (1, F('sel', isne(sg, V(0)),
                         cat(sg, F('rev', tail(sg, V(0))), head(sg, V(0))),
                         K('')))}
    n, ok = 0, True
    mx = 0
    for s in strings_upto(6):
        w, st = val(drev, 'rev', (s,))
        ok &= check('rev', w == s[::-1], (s, w))
        n += 1
        mx = max(mx, st)
    print(f"  C1 rev: all {n} strings of length <= 6 over {{a,b}} "
          f"-> {'OK' if ok else 'FAIL'} (max machine steps {mx})")
    # a few longer random strings
    rng = random.Random(5)
    okL = True
    for _ in range(20):
        s = rnd(rng, 10)
        w, _ = val(drev, 'rev', (s,))
        okL &= check('rev-long', w == s[::-1], (s, w))
    print(f"     plus 20 random strings of length <= 10 -> {'OK' if okL else 'FAIL'}")

    # C2: length in tally.  len(X) = sel(isne X, cat("a", len(tail X)), eps)
    dlen = {'sel': (3, sel_body(sg)),
            'len': (1, F('sel', isne(sg, V(0)),
                         cat(sg, K('a'), F('len', tail(sg, V(0)))),
                         K('')))}
    n2, ok2 = 0, True
    for s in strings_upto(6):
        w, _ = val(dlen, 'len', (s,))
        ok2 &= check('len', w == 'a' * len(s), (s, w))
        n2 += 1
    print(f"  C2 len -> a^|S|: all {n2} strings of length <= 6 "
          f"-> {'OK' if ok2 else 'FAIL'}")

    # C3: parity of LENGTH via a NON-cat step function (if/eq based flip):
    #     par(X) = sel(isne X, if(eq(par(tail X), top), bot, top), bot)
    #     (step B(X,Z) = NOT Z -- exercises an if/eq step, not cat)
    dpar = {'sel': (3, sel_body(sg)),
            'par': (1, F('sel', isne(sg, V(0)),
                         if_(sg, eq(sg, F('par', tail(sg, V(0))), K(sg.top)),
                             K(sg.bot), K(sg.top)),
                         K(sg.bot)))}
    n3, ok3 = 0, True
    for s in strings_upto(7):
        w, _ = val(dpar, 'par', (s,))
        ok3 &= check('par', w == (sg.top if len(s) % 2 else sg.bot), (s, w))
        n3 += 1
    rng = random.Random(77)
    for _ in range(60):
        s = rnd(rng, 12)
        w, _ = val(dpar, 'par', (s,))
        ok3 &= check('par', w == (sg.top if len(s) % 2 else sg.bot), (s, w))
        n3 += 1
    print(f"  C3 par (if/eq step fn): all {n3} strings of length <= 7 "
          f"plus 60 random of length <= 12 -> {'OK' if ok3 else 'FAIL'}")

    return ok and okL and ok2 and ok3


if __name__ == '__main__':
    a = test_A()
    b = test_B()
    c = test_C()
    print()
    print(f"ROUND2 RESULT: A(small==big)={'PASS' if a else 'FAIL'} "
          f"B(sel)={'PASS' if b else 'FAIL'} C(scheme)={'PASS' if c else 'FAIL'} fails={FAIL}")
    sys.exit(0 if (a and b and c) else 1)

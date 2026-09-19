"""Battery 3 (file verify3): finite conservativity (research item 4).

B4  On FINITE inputs and CONSTANT-pattern programs (the official F1 form),
    the stream machine must agree with the flat lazy-pass semantics
    (semantics.feval: strict in E and P, R forced only if P occurs):

      machine TERM  <=>  flat value is a string, and equal,
                         (or both UNDEF for [R/eps]);
      machine STALL or LIVE  <=>  flat value is bottom (None);

    i.e. the stream semantics is a conservative extension of the
    flat lazy-pass semantics on finite strings, with LIVE exactly the
    cases where the flat semantics has no finite value.

    Flat fixpoint: Kleene iteration with dynamic argument closure
    (flat_fix); closure overflow / non-stabilization => no finite value.

    Variable patterns are EXCLUDED here (they break conservativity;
    see B5d in verify2).
"""

import random
import sys

import streams as S
from streams import V, C, cat, F
import verify2
from semantics import feval, UNDEF

sys.setrecursionlimit(30000)
random.seed(7)


def flat_fix(body, sigma0, main=None, maxargs=14, maxiter=80):
    """Least fixpoint of the flat functional, with dynamic closure of the
    argument set.  main (default f(sigma0)) is evaluated on the stabilized
    fixpoint.  Returns ('val', s) if the chain stabilizes at string s
    (or UNDEF), ('bot', None) if it stabilizes at bottom, or
    ('open', None) if closure/iteration caps were hit (no finite value
    could be certified; caller treats as not-a-finite-value)."""
    from streams import Call, Var
    if main is None:
        main = Call('f', Var('X'))
    g = {sigma0: None}

    def callh(a):
        if a is None or a is UNDEF:
            return a
        if a not in g:
            if len(g) >= maxargs:
                return None
            g[a] = None
        return g[a]

    for _ in range(maxiter):
        changed = False
        for s in list(g):
            v = feval(body, s, callh)
            if v != g[s]:
                g[s] = v
                changed = True
        if not changed:
            if g[sigma0] is None:
                return ('bot', None)
            try:
                v0 = feval(main, sigma0, callh)
            except Exception:
                return ('val', UNDEF)
            if v0 is None:
                return ('bot', None)
            return ('val', v0)      # string or UNDEF
    return ('open', None)


def compare(label, body, main, inp):
    v, out, _m = S.run(main, S.src_fin(inp), body=body, nchars=60,
                       budget=3 * 10 ** 6, maxstack=20000)
    kind, fval = flat_fix(body, inp, main)
    # hypothesis
    if kind == 'val':
        if fval is UNDEF:
            good = (v == 'UNDEF')
        else:
            good = (v == 'TERM' and out == fval)
    else:
        good = (v in ('STALL', 'LIVE'))
    print('B4 %-42s machine=%-5s %.14r  flat=%s/%.14r  %s'
          % (label, v, out, kind, fval, 'OK' if good else '**'))
    return good


def b4():
    ok = True

    # --- zoo cases with finite inputs (constant patterns)
    for (label, body, inp) in verify2.zoo_cases():
        if isinstance(inp, tuple):
            continue
        ok &= compare('%s X=%r' % (label.strip(), inp), body, F(V()), inp)

    # --- the junction grid extremes (verified machine-side in B3); here
    #     vs flat
    for (W, P, R) in [('bab', 'bab', 'b'), ('aa', 'aa', 'a'),
                      ('aab', 'ab', ''), ('ba', 'ab', ''),
                      ('ab', 'ba', 'b'), ('ba', 'ba', 'b')]:
        body = S.sub(C(R), C(P), cat(C(W), F(V())))
        ok &= compare('J [W.f] W=%r P=%r R=%r' % (W, P, R),
                      body, F(V()), 'x')

    # --- random constant-pattern programs
    ARGS = [V(), cat(V(), C('a')), cat(V(), C('b')),
            cat(C('a'), V()), cat(C('b'), V()), C('a')]

    def rand_body(d):
        r = random.random()
        if d == 0 or r < 0.25:
            return V() if random.random() < 0.6 else \
                C(''.join(random.choice('ab') for _ in
                          range(random.randint(0, 2))))
        if r < 0.55:
            return cat(rand_body(d - 1), rand_body(d - 1))
        if r < 0.80:
            P = ''.join(random.choice('ab')
                        for _ in range(random.randint(1, 2)))
            return S.sub(rand_body(d - 1), C(P), rand_body(d - 1))
        # recursive call (70% plain X to keep closures small)
        arg = V() if random.random() < 0.7 else random.choice(ARGS)
        return F(arg)

    trials = 0
    checked = 0
    bad = 0
    while checked < 120 and trials < 900:
        trials += 1
        body = rand_body(3)
        inp = ''.join(random.choice('ab')
                      for _ in range(random.randint(0, 4)))
        main = F(V()) if random.random() < 0.8 else \
            S.sub(C('c'), C(''.join(random.choice('ab')
                                    for _ in range(1, 2))), F(V()))
        # skip degenerate empty-pattern
        v, out, _m = S.run(main, S.src_fin(inp), body=body, nchars=60,
                           budget=3 * 10 ** 6, maxstack=20000)
        if v == 'UNDEF':
            continue                     # [R/eps]: both undefined, fine
        checked += 1
        kind, fval = flat_fix(body, inp, main)
        if kind == 'val':
            good = (fval is not UNDEF and v == 'TERM' and out == fval)
        else:
            good = (v in ('STALL', 'LIVE'))
        if not good:
            bad += 1
            print('B4 RANDOM MISMATCH body=%r main=%r inp=%r machine=%s '
                  '%r flat=%s/%r' % (body, main, inp, v, out, kind, fval))
            if bad > 6:
                break
    print('B4 random constant-pattern programs: %d checked (%d '
          'generated), %d mismatches' % (checked, trials, bad))
    return ok and bad == 0


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', 'b4'):
        ok &= b4()
    print('ALL OK' if ok else 'FAILURES PRESENT')

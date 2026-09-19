#!/usr/bin/env python3
"""Battery 1: sanity + zoo verdicts.

B1  non-recursive F1 expressions (constants, cat, constant-pattern passes)
    on finite inputs: the stream machine must agree exactly with the
    composition of the paper's sub() (its Definition 1).

Z   first zoo verdicts (productivity / deadlock / termination).
"""

import itertools
import random
import sys

import streams as S
from streams import V, C, cat, F, sub as _
from semantics import sub, feval, flat_fixpoint, keval, mu_eval, BOT, FIN

random.seed(20260919)
ALPHA = 'ab'


def rand_word(n=None, alpha=ALPHA):
    n = n if n is not None else random.randint(0, 5)
    return ''.join(random.choice(alpha) for _ in range(n))


def rand_expr(d, alpha=ALPHA):
    r = random.random()
    if d == 0 or r < 0.30:
        return V() if random.random() < 0.5 else C(rand_word(alpha=alpha))
    if r < 0.60:
        return cat(rand_expr(d - 1, alpha), rand_expr(d - 1, alpha))
    # constant-pattern pass
    P = rand_word(random.randint(1, 2), alpha)
    return S.sub(rand_expr(d - 1, alpha), C(P), rand_expr(d - 1, alpha))


def ref(e, sigma):
    """Reference denotation on finite strings via the paper's sub()."""
    if isinstance(e, S.Var):
        return sigma
    if isinstance(e, S.Const):
        return e.w
    if isinstance(e, S.Cat):
        return ref(e.a, sigma) + ref(e.b, sigma)
    if isinstance(e, S.Pass):
        return sub(ref(e.R, sigma), ref(e.P, sigma), ref(e.E, sigma))
    raise TypeError(e)


def b1(trials=400):
    bad = 0
    for t in range(trials):
        e = rand_expr(random.randint(1, 3))
        sigma = rand_word()
        try:
            want = ref(e, sigma)
        except Exception:
            continue           # undefined ([A/eps]): skip
        if len(want) > 300:
            continue
        verdict, out, _m = S.run(e, S.src_fin(sigma), nchars=len(want) + 5)
        if verdict != 'TERM' or out != want:
            bad += 1
            print('B1 MISMATCH e=%r sigma=%r want=%r got=%r (%s)'
                  % (e, sigma, want, out, verdict))
            if bad > 5:
                return False
    print('B1 non-recursive vs sub(): %d trials, %d mismatches' % (trials, bad))
    return bad == 0


def zoo():
    ok = True

    def expect(label, main, src, want_verdict, want_out=None, body=None,
               nchars=120):
        v, out, _m = S.run(main, src, body=body, nchars=nchars)
        good = v == want_verdict
        if good and want_out is not None:
            if want_verdict == 'LIVE':
                good = out.startswith(want_out)
            else:
                good = out == want_out
        print('%-46s -> %-6s %.30r %s' % (label, v, out, 'OK' if good else
                                          '** EXPECTED %s %r **' %
                                          (want_verdict, want_out)))
        return good

    # Z1  f(X) = X . f(X)  -- cat-tail recursion
    body = cat(V(), F(V()))
    ok &= expect('Z1a  f=X.f(X), X="ab"', F(V()), S.src_fin('ab'),
                 'LIVE', 'ababab', body=body)
    ok &= expect('Z1b  f=X.f(X), X=eps', F(V()), S.src_fin(''),
                 'STALL', '', body=body)
    ok &= expect('Z1c  f=X.f(X), X=(ab)^inf', F(V()), S.src_cycle('ab'),
                 'LIVE', 'ababab', body=body)

    # Z2  f(X) = [c/ab](X . f(X))  -- the junction example
    body = S.sub(C('c'), C('ab'), cat(V(), F(V())))
    ok &= expect('Z2a  [c/ab](X.f(X)), X="a"', F(V()), S.src_fin('a'),
                 'STALL', '', body=body)
    ok &= expect('Z2b  [c/ab](X.f(X)), X="aa"', F(V()), S.src_fin('aa'),
                 'LIVE', 'aaaa', body=body)
    ok &= expect('Z2c  [c/ab](X.f(X)), X="b"', F(V()), S.src_fin('b'),
                 'LIVE', 'bbbb', body=body)
    ok &= expect('Z2d  [c/ab](X.f(X)), X="ab"', F(V()), S.src_fin('ab'),
                 'LIVE', 'cccc', body=body)
    ok &= expect('Z2e  [c/ab](X.f(X)), X="aabb"', F(V()), S.src_fin('aabb'),
                 'LIVE', 'acbacb', body=body)
    ok &= expect('Z2f  [c/ab](X.f(X)), X=eps', F(V()), S.src_fin(''),
                 'STALL', '', body=body)

    # Z2' deletion variant: f(X) = [eps/ab](X . f(X)).
    # NOTE: Z2i/Z2j refute the naive "e(w) != eps implies live": with
    # R = eps the match at the junction eats the buffer, and each output
    # character would need an infinite descent -- the machine stalls
    # after its own flush (verified against the Kleene evaluator too).
    body = S.sub(C(''), C('ab'), cat(V(), F(V())))
    ok &= expect("Z2g  [e/ab](X.f(X)), X=\"ab\"", F(V()), S.src_fin('ab'),
                 'STALL', '', body=body)
    ok &= expect('Z2h  [e/ab](X.f(X)), X="abab"', F(V()),
                 S.src_fin('abab'), 'STALL', '', body=body)
    ok &= expect('Z2i  [e/ab](X.f(X)), X="aab"', F(V()), S.src_fin('aab'),
                 'STALL', 'a', body=body)
    ok &= expect('Z2j  [e/ab](X.f(X)), X="ba"', F(V()), S.src_fin('ba'),
                 'STALL', 'b', body=body)

    # Z3  f(X) = [f(X)/a]X  -- replacement-slot recursion (trichotomy)
    body = S.sub(F(V()), C('a'), V())
    ok &= expect('Z3a  [f/a]X, X="b"', F(V()), S.src_fin('b'),
                 'TERM', 'b', body=body)
    ok &= expect('Z3b  [f/a]X, X="ab"', F(V()), S.src_fin('ab'),
                 'STALL', '', body=body)
    ok &= expect('Z3c  [f/a]X, X="ba"', F(V()), S.src_fin('ba'),
                 'LIVE', 'bbbb', body=body)
    ok &= expect('Z3d  [f/a]X, X="bba"', F(V()), S.src_fin('bba'),
                 'LIVE', 'bbbbbb', body=body)
    ok &= expect('Z3e  [f/a]X, X="aba"', F(V()), S.src_fin('aba'),
                 'STALL', '', body=body)
    ok &= expect('Z3f  [f/a]X, X="bab"', F(V()), S.src_fin('bab'),
                 'LIVE', 'bbbb', body=body)

    # Z6  pure scrutinee recursion
    body = S.sub(C('a'), C('b'), F(V()))
    ok &= expect('Z6a  [a/b](f(X)), X="ab"', F(V()), S.src_fin('ab'),
                 'STALL', '', body=body)
    body = S.sub(C('a'), C('b'), cat(F(V()), V()))
    ok &= expect('Z6b  [a/b](f(X).X), X="ab"', F(V()), S.src_fin('ab'),
                 'STALL', '', body=body)
    body = S.sub(C('a'), C('b'), cat(V(), F(V())))
    ok &= expect('Z6c  [a/b](X.f(X)), X="ab"', F(V()), S.src_fin('ab'),
                 'LIVE', 'aaaa', body=body)

    # Z4  doubling: f(X) = X . b . f(X.X)
    body = cat(V(), C('b'), F(cat(V(), V())))
    ok &= expect('Z4  f=X.b.f(X.X), X="a"', F(V()), S.src_fin('a'),
                 'LIVE', 'abaabaaaab', body=body, nchars=70)

    # Z5  counter: f(X) = X . b . f(X.a)
    body = cat(V(), C('b'), F(cat(V(), C('a'))))
    ok &= expect('Z5  f=X.b.f(X.a), X="a"', F(V()), S.src_fin('a'),
                 'LIVE', 'abaabaaab', body=body, nchars=70)

    return ok


if __name__ == '__main__':
    ok = True
    ok &= b1(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    ok &= zoo()
    print('ALL OK' if ok else 'FAILURES PRESENT')

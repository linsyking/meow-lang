#!/usr/bin/env python3
"""Battery 2: adequacy (machine vs Kleene denotation), guardedness grid,
variable patterns.

B2  For a zoo of recursive definitions and both finite and infinite inputs:
    the stream machine must agree with the least fixpoint computed
    independently by the Kleene evaluator (semantics.keval):
      machine LIVE   <=> Kleene chain unbounded,
      machine STALL  <=> chain stabilizes at (emitted, BOT),
      machine TERM   <=> chain stabilizes at (value, FIN),
    and the characters agree.

B3  Guardedness grid: f(X) = [R/P](W . f(X)) for all short W, P, R:
    verdict vs the pre-pull emission e(W), tabulated.  Tests the deadlock
    theorem (e(W)=eps => stall) and probes the R=eps boundary.

B5  Variable patterns: forcing-frontier bound, identity/absorption on
    infinite patterns.
"""

import itertools
import random
import sys

import streams as S
from streams import V, C, cat, F
from semantics import (sub, keval, mu_eval, feval, flat_fixpoint,
                       BOT, FIN, OMG, UndefinedPattern)

sys.setrecursionlimit(30000)
random.seed(42)

N = 40          # chars to compare
J = 100         # Kleene depth


# ------------------------------------------------------------- zoo (shared)

def zoo_cases():
    """(label, body, input-string-or-('cycle', p))"""
    Z = []
    Z.append(('Z1  f=X.f(X)            X=ab    ', cat(V(), F(V())), 'ab'))
    Z.append(('Z1  f=X.f(X)            X=eps   ', cat(V(), F(V())), ''))
    Z.append(('Z1  f=X.f(X)            X=a^w   ', cat(V(), F(V())), ('cycle', 'ab')))
    Z.append(('Z2a [c/ab](X.f(X))      X=a     ',
              S.sub(C('c'), C('ab'), cat(V(), F(V()))), 'a'))
    Z.append(('Z2b [c/ab](X.f(X))      X=aa    ',
              S.sub(C('c'), C('ab'), cat(V(), F(V()))), 'aa'))
    Z.append(('Z2c [c/ab](X.f(X))      X=b     ',
              S.sub(C('c'), C('ab'), cat(V(), F(V()))), 'b'))
    Z.append(('Z2d [c/ab](X.f(X))      X=ab    ',
              S.sub(C('c'), C('ab'), cat(V(), F(V()))), 'ab'))
    Z.append(('Z2e [c/ab](X.f(X))      X=aabb  ',
              S.sub(C('c'), C('ab'), cat(V(), F(V()))), 'aabb'))
    Z.append(('Z2g [e/ab](X.f(X))      X=ab    ',
              S.sub(C(''), C('ab'), cat(V(), F(V()))), 'ab'))
    Z.append(('Z2i [e/ab](X.f(X))      X=aab   ',
              S.sub(C(''), C('ab'), cat(V(), F(V()))), 'aab'))
    Z.append(('Z2j [e/ab](X.f(X))      X=ba    ',
              S.sub(C(''), C('ab'), cat(V(), F(V()))), 'ba'))
    Z.append(('Z3  [f/a]X              X=b     ',
              S.sub(F(V()), C('a'), V()), 'b'))
    Z.append(('Z3  [f/a]X              X=ab    ',
              S.sub(F(V()), C('a'), V()), 'ab'))
    Z.append(('Z3  [f/a]X              X=ba    ',
              S.sub(F(V()), C('a'), V()), 'ba'))
    Z.append(('Z3  [f/a]X              X=aba   ',
              S.sub(F(V()), C('a'), V()), 'aba'))
    Z.append(('Z6a [a/b](f(X))         X=ab    ',
              S.sub(C('a'), C('b'), F(V())), 'ab'))
    Z.append(('Z6c [a/b](X.f(X))       X=ab    ',
              S.sub(C('a'), C('b'), cat(V(), F(V()))), 'ab'))
    Z.append(('Z4  f=X.b.f(X.X)        X=a     ',
              cat(V(), C('b'), F(cat(V(), V()))), 'a'))
    Z.append(('Z5  f=X.b.f(X.a)        X=a     ',
              cat(V(), C('b'), F(cat(V(), C('a')))), 'a'))
    return Z


def b2():
    ok = True
    for (label, body, inp) in zoo_cases():
        if isinstance(inp, tuple):
            src = S.src_cycle(inp[1])
            # Kleene with a deep truncation of the infinite input
            xval = (inp[1] * (2 * N), OMG)
        else:
            src = S.src_fin(inp)
            xval = (inp, FIN)
        v, out, _m = S.run(F(V()), src, body=body, nchars=N,
                           budget=20 * 10 ** 6)
        kind, (chars, end) = mu_eval(body, xval, J=J, cap=4 * N + 16)
        # agreement
        if v == 'LIVE':
            good = (kind == 'growing' and len(chars) >= N
                    and chars[:N] == out[:N])
            exp = 'LIVE/unbounded'
        elif v == 'TERM':
            good = (kind == 'stab' and end == FIN and chars == out)
            exp = 'TERM/fin'
        else:  # STALL
            good = (kind == 'stab' and end == BOT and chars == out)
            exp = 'STALL/bot'
        if not good:
            ok = False
            print('B2 MISMATCH %-38s machine=%s/%.20r  kleene=%s/%r/%.20r'
                  % (label, v, out, kind, end, chars))
        print('B2 %-38s %-5s %-6s %.24r  %s' % (label, v, kind, out,
                                                'OK' if good else '**'))
    return ok


# ------------------------------------------------------ guardedness grid

def prepull_emission(W, P, R):
    """e(W): the pass-machine's emission after consuming the finite word W
    against pattern P (no end-of-input flush)."""
    pc = P
    buf = ''
    out = []
    for c in W:
        k = len(buf)
        pk = pc[k] if k < len(pc) else None
        if pk == c:
            buf += c
            # probe: pattern exhausted at len(buf) => match
            if len(buf) == len(pc):
                out.append(R)
                buf = ''
        else:
            b2 = buf + c
            keep = 0
            for L in range(len(b2) - 1, 0, -1):
                if b2[len(b2) - L:] == pc[:L]:
                    keep = L
                    break
            out.append(b2[:len(b2) - keep])
            buf = b2[len(b2) - keep:]
    return ''.join(out)


def b3(nc=25, ext=False):
    if ext:
        # three-letter word alphabet, two-letter pattern alphabet:
        # lets e(W) contain a character outside alphabet(P).
        words = [''.join(w) for n in (1, 2)
                 for w in itertools.product('abc', repeat=n)]
        maxw = 20000
    else:
        words = [''] + [''.join(w) for n in (1, 2, 3)
                        for w in itertools.product('ab', repeat=n)]
        maxw = 20000
    pats = [''.join(p) for n in (1, 2, 3)
            for p in itertools.product('ab', repeat=n)]
    reps = ['', 'a', 'b', 'c', 'ab']
    tally = {}
    bad = 0
    bnd = []
    fresh_ok = [0]
    for W in words:
        for P in pats:
            for R in reps:
                body = S.sub(C(R), C(P), cat(C(W), F(V())))
                v, out, _m = S.run(F(V()), S.src_fin('x'), body=body,
                                   nchars=nc, budget=2 * 10 ** 6,
                                   maxstack=maxw)
                e = prepull_emission(W, P, R)
                key = ('e=eps' if e == '' else 'e#eps',
                       'R=eps' if R == '' else 'R#eps', v)
                tally[key] = tally.get(key, 0) + 1
                # deadlock theorem: e(W)=eps -> stall, emitting nothing
                if e == '' and (v != 'STALL' or out != ''):
                    bad += 1
                    print('B3 VIOLATES deadlock theorem: W=%r P=%r R=%r '
                          'e=%r v=%s out=%r' % (W, P, R, e, v, out))
                # sufficient condition 1: |R| >= |P| and e#eps -> live
                if e != '' and len(R) >= len(P) and P and v != 'LIVE':
                    bad += 1
                    print('B3 VIOLATES |R|>=|P|: W=%r P=%r R=%r e=%r '
                          'v=%s out=%r' % (W, P, R, e, v, out))
                # sufficient condition 1b: single-char pattern and
                # e#eps -> live (pure relay argument)
                if e != '' and len(P) == 1 and v != 'LIVE':
                    bad += 1
                    print('B3 VIOLATES |P|=1 relay: W=%r P=%r R=%r e=%r '
                          'v=%s out=%r' % (W, P, R, e, v, out))
                # sufficient condition 2 (corrected): e(W) itself
                # contains a character outside alphabet(P) -> live
                if (e != '' and not (set(e) & set(P)) and v != 'LIVE'):
                    bad += 1
                    print('B3 VIOLATES fresh-emission: W=%r P=%r R=%r e=%r '
                          'v=%s out=%r' % (W, P, R, e, v, out))
                if (ext and e != '' and set(e) - set(P) and v == 'LIVE'):
                    fresh_ok[0] += 1
                # boundary bookkeeping: residual region
                if (e != '' and R != '' and len(R) < len(P)
                        and set(R) & set(P) and v != 'LIVE'):
                    bnd.append((W, P, R, e, out))
    print('B3 grid tally (e, R, verdict) -> count:')
    for k in sorted(tally):
        print('   %-28s %d' % (str(k), tally[k]))
    print('B3 residual region (e#eps, R#eps, |R|<|P|, R over alphabet(P))'
          ' stalls: %d examples:' % len(bnd))
    for (W, P, R, e, out) in bnd[:12]:
        print('   W=%-6r P=%-5r R=%-4r e=%r out=%r' % (W, P, R, e, out))
    print('B3 violations: %d   fresh-emission LIVE cases: %d'
          % (bad, fresh_ok[0]))
    return bad == 0


# --------------------------------------------------- variable patterns (B5)

def b5():
    ok = True

    def run_main(main, body, src, nchars=40):
        return S.run(main, src, body=body, nchars=nchars,
                     budget=3 * 10 ** 6, maxstack=20000)

    # f = X . f(X)  (the "square" stream); used as an infinite pattern
    sq = cat(V(), F(V()))

    # (a) frontier bound: [c/f(X)]X on finite inputs.  The machine must
    # force at most l+1 chars of the pattern, l = longest prefix of the
    # pattern's value that occurs as a factor of the scrutinee.
    for inp in ['b', 'a', 'ab', 'ba', 'aab', 'bab', 'abba', 'aabb', 'bba']:
        v, out, m = run_main(S.sub(C('c'), F(V()), V()), sq, S.src_fin(inp))
        pat_val = inp * 40           # f(inp) = inp^omega (enough for l)
        # longest prefix of the pattern's value occurring as a factor of
        # the (finite) scrutinee
        l = 0
        for i in range(len(pat_val) + 1):
            if inp and pat_val[:i] in inp:
                l = i
        forced = max(m.forced.values()) if m.forced else 0
        good = (v == 'TERM' and out == inp and forced <= l + 1)
        print('B5a frontier [c/f(X)]X X=%-5r -> %-5s %.10r forced=%d l=%d %s'
              % (inp, v, out, forced, l, 'OK' if good else '**'))
        ok &= good

    # (b) identity on infinite patterns: pattern a.X over scrutinee X with
    # X=(ab)^inf: no tail of the scrutinee equals the pattern, so the
    # pass is the identity (and live).
    main = S.sub(C('c'), cat(C('a'), V()), V())
    v, out, m = run_main(main, sq, S.src_cycle('ab'), nchars=30)
    good = v == 'LIVE' and out == 'ab' * 15
    print('B5b identity [c/aX]X, X=(ab)^inf          -> %-5s %.20r %s'
          % (v, out, 'OK' if good else '**'))
    ok &= good

    # (c) absorption: pattern X (the whole input stream) over scrutinee X:
    # [c/X]X on (ab)^inf absorbs forever, no output.
    main = S.sub(C('c'), V(), V())
    v, out, m = run_main(main, sq, S.src_cycle('ab'), nchars=30)
    good = v == 'STALL' and out == ''
    print('B5c absorption [c/X]X, X=(ab)^inf         -> %-5s %.10r %s'
          % (v, out, 'OK' if good else '**'))
    ok &= good

    # (d) conservativity break vs flat lazy-pass: [c/f(X)]X with the
    # infinite pattern f(X)=X.f(X): the machine forces only the frontier
    # and terminates; strict-in-P flat evaluation diverges.
    for inp in ['b', 'ab', 'aabb']:
        v, out, m = run_main(S.sub(C('c'), F(V()), V()), sq, S.src_fin(inp))
        g = {inp: None}
        for _ in range(60):
            g2 = {s: feval(sq, s, lambda a: g.get(a, None)) for s in g}
            if g2 == g:
                break
            g = g2
        flatpat = g[inp]            # flat value of f(inp): diverges
        good = (v == 'TERM' and out == inp and flatpat is None)
        print('B5d break [c/f(X)]X X=%-5r             -> %-5s %.10r '
              'flatpattern=%s %s' % (inp, v, out, flatpat,
                                     'OK' if good else '**'))
        ok &= good
    return ok


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', 'b2'):
        ok &= b2()
    if which in ('all', 'b3'):
        ok &= b3()
    if which in ('all', 'b5'):
        ok &= b5()
    print('ALL OK' if ok else 'FAILURES PRESENT')

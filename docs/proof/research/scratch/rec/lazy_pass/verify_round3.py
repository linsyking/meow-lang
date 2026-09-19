"""Round 3 verification: UNIVERSALITY pieces.

  A. shortlex successor  next = rev . incr . rev  (incr = little-endian
     increment by structural recursion); the orbit of next from eps must be
     the shortlex enumeration of ALL strings over {a,b}.
  B. pattern-gated minimization (the mu-scheme):
        W(X,Y) = sel( eq(cat(Y,Y), X), Y, W(X, next(Y)) )
        SQRT(X) = W(X, eps)     -- the string square root:
     on X = w.w returns w; on non-squares diverges (no value within cap).
  C. multi-argument structural recursion (primitive recursion with
     parameters): ADD and MULT on tallies.
  D. the Horner coding V : Sigma* -> a-tallies and its inverse DIGITS
     (built from the raw-L floor-halving pipeline), round trip.
  E. mutual recursion definable from SELF recursion via tagged pairing:
     even/odd on tallies as two mutually recursive definitions, and as ONE
     self-recursive definition F on tagged pairs  b.T / bb.T.
  F. a two-counter-machine COMPILER: from an instruction list to calculus
     definitions (parsers PCNT/TAKEA/DROPB/SKIPAB by structural recursion,
     step as a sel-tree over the program counter, RUN as the gated while
     loop); executed on a doubling machine on small inputs.

Run:  python3 verify_round3.py
"""

import itertools
import random
import sys

from core import K, V, C, S, F, pp, run_lazy, run_eager, check_program
from toolkit import (BIN, enc, dec, benc, bdec, enc2, dec2, cat, tail, head,
                    eq, if_, isne, contains, sel_body, comp)

sg = BIN
FAIL = 0
BASE = {'sel': (3, sel_body(sg))}


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


def val(defs, name, args, cap=3_000_000):
    res = run_lazy(defs, name, tuple(args), cap=cap)
    assert res[0] == 'val', (name, args, res)
    return res[1], res[2]


def succch(E):
    """succch(c) = the next character in the order a < b (c a single char)."""
    return if_(sg, eq(sg, E, K('a')), K('b'), K('a'))


# ===========================================================================
# A.  shortlex successor

def next_defs():
    d = dict(BASE)
    # incr(X): little-endian increment (X is the REVERSED string):
    #   incr(eps) = a;  if head X = b: a . incr(tail X);  else succch(head X) . tail X
    d['incr'] = (1, F('sel', isne(sg, V(0)),
                      F('sel', eq(sg, head(sg, V(0)), K('b')),
                         cat(sg, K('a'), F('incr', tail(sg, V(0)))),
                         cat(sg, succch(head(sg, V(0))), tail(sg, V(0)))),
                      K('a')))
    d['rev'] = (1, F('sel', isne(sg, V(0)),
                     cat(sg, F('rev', tail(sg, V(0))), head(sg, V(0))),
                     K('')))
    d['next'] = (1, F('rev', F('incr', F('rev', V(0)))))
    return d


def test_A():
    print("== (A) shortlex successor next = rev.incr.rev ==")
    d = next_defs()
    s, steps = val(d, 'next', ('',))
    check('next-eps', s == 'a', s)
    seq = ['']
    cur = ''
    for i in range(126):                      # orbit covers all strings <= 6
        cur, _ = val(d, 'next', (cur,))
        seq.append(cur)
    want = list(strings_upto(6))
    ok = check('next-orbit', seq == want,
               f"first divergence at index {next((i for i,(x,y) in enumerate(zip(seq,want)) if x!=y), None)}")
    print(f"  orbit of next from eps: 127 strings == shortlex enumeration of "
          f"all strings of length <= 6 -> {'OK' if ok else 'FAIL'}")
    return ok


# ===========================================================================
# B.  the mu-scheme: string square root

def sqrt_defs():
    d = next_defs()
    d['W'] = (2, F('sel', eq(sg, cat(sg, V(1), V(1)), V(0)),
                   V(1),
                   F('W', V(0), F('next', V(1)))))
    d['SQRT'] = (1, F('W', V(0), K('')))
    return d


def test_B():
    print("== (B) pattern-gated minimization: SQRT(X) = mu Y. YY = X ==")
    d = sqrt_defs()
    n, ok = 0, True
    for w in strings_upto(3):
        X = w + w
        r, _ = val(d, 'SQRT', (X,))
        ok &= check('sqrt', r == w, (X, r, w))
        n += 1
    print(f"  SQRT on all {n} squares X = w.w with |w| <= 3: exact -> "
          f"{'OK' if ok else 'FAIL'}")
    # non-squares diverge
    okd = True
    for X in ['a', 'ab', 'aba', 'aab', 'baa', 'abbb']:
        r = run_lazy(d, 'SQRT', (X,), cap=300_000)
        okd &= check('sqrt-div', r[0] in ('timeout', 'blackhole'), (X, r))
    print(f"  SQRT on 5 non-squares: no value within cap (divergent as "
          f"intended) -> {'OK' if okd else 'FAIL'}")
    return ok and okd


# ===========================================================================
# C.  multi-argument structural recursion: ADD, MULT on tallies

def addmult_defs():
    d = dict(BASE)
    # ADD(S,T) = if S = eps then T else ADD(tail S, a.T)
    d['ADD'] = (2, F('sel', isne(sg, V(0)),
                     F('ADD', tail(sg, V(0)), cat(sg, K('a'), V(1))),
                     V(1)))
    # MULT(S,T) = if S = eps then eps else ADD(T, MULT(tail S, T))
    d['MULT'] = (2, F('sel', isne(sg, V(0)),
                      F('ADD', V(1), F('MULT', tail(sg, V(0)), V(1))),
                      K('')))
    return d


def test_C():
    print("== (C) structural recursion with parameters: ADD, MULT on tallies ==")
    d = addmult_defs()
    n, ok = 0, True
    for i in range(6):
        for j in range(6):
            r, _ = val(d, 'ADD', ('a' * i, 'a' * j))
            ok &= check('add', r == 'a' * (i + j), (i, j, r))
            r, _ = val(d, 'MULT', ('a' * i, 'a' * j))
            ok &= check('mult', r == 'a' * (i * j), (i, j, r))
            n += 2
    print(f"  ADD and MULT on all 36 tally pairs (<= 5): {n} evaluations, "
          f"exact -> {'OK' if ok else 'FAIL'}")
    return ok


# ===========================================================================
# D.  the Horner coding V : Sigma* -> tallies and its inverse DIGITS

def coding_defs():
    d = dict(BASE)
    # V(X): INJECTIVE Horner coding into tallies (bijective numeration: a
    # sentinel high bit, i.e. base case 1):  V(eps) = a;  V(cT) = 2 V(T)+idx(c)
    d['V'] = (1, F('sel', isne(sg, V(0)),
                   cat(sg, cat(sg, F('V', tail(sg, V(0))), F('V', tail(sg, V(0)))),
                       if_(sg, eq(sg, head(sg, V(0)), K('a')), K(''), K('a'))),
                   K('a')))
    # raw-L floor-halving on a-tallies: HALF = [a/b][eps/a][b/aa] (run order
    # [b/aa], [eps/a], [a/b]) -- the mirror of the paper's Section 5.6 H.
    HALF = comp([(K('a'), K('b')), (K(''), K('a')), (K('b'), K('aa'))], V(0))
    d['HALF'] = (1, HALF)
    # ODD(n) = top iff n odd: structural flip
    d['ODD'] = (1, F('sel', isne(sg, V(0)),
                     if_(sg, F('ODD', tail(sg, V(0))), K(sg.bot), K(sg.top)),
                     K(sg.bot)))
    # DIGITS(n) = the inverse of V:  base n = a (value 1) -> eps;
    # else (n mod 2 ? b : a) . DIGITS(HALF n)   (little-endian)
    d['DIGITS'] = (1, F('sel', eq(sg, V(0), K('a')),
                        K(''),
                        cat(sg, if_(sg, F('ODD', V(0)), K('b'), K('a')),
                            F('DIGITS', F('HALF', V(0))))))
    return d


def test_D():
    print("== (D) Horner coding V and its inverse DIGITS ==")
    d = coding_defs()
    ok = True
    # HALF and ODD
    for n in range(0, 40):
        h, _ = val(d, 'HALF', ('a' * n,))
        o, _ = val(d, 'ODD', ('a' * n,))
        ok &= check('half', h == 'a' * (n // 2), (n, h))
        ok &= check('odd', o == (sg.top if n % 2 else sg.bot), (n, o))
    print("  HALF (raw-L pipeline) and ODD on tallies 0..39: exact")
    n, ok2 = 0, True
    for X in strings_upto(5):
        t, _ = val(d, 'V', (X,))
        nX = ((1 << len(X)) + int(X[::-1].replace('a', '0').replace('b', '1'), 2)
               if X else 1)
        ok2 &= check('V', t == 'a' * nX, (X, t, nX))
        back, _ = val(d, 'DIGITS', (t,))
        ok2 &= check('DIGITS.V', back == X, (X, t, back))
        n += 2
    print(f"  V and DIGITS(V(X)) == X on all 63 strings of length <= 5 "
          f"({n} evaluations) -> {'OK' if ok2 else 'FAIL'}")
    return ok and ok2


# ===========================================================================
# E.  mutual recursion from self recursion: even/odd on tallies

def evenodd_defs():
    d = dict(BASE)
    # direct mutual definitions
    d['even'] = (1, F('sel', isne(sg, V(0)), F('odd', tail(sg, V(0))), K(sg.top)))
    d['odd'] = (1, F('sel', isne(sg, V(0)), F('even', tail(sg, V(0))), K(sg.bot)))
    # single self-recursive F on tagged pairs:  tag in {b, bb}, tally = a*
    untag = comp([(K(''), K('b')), (K(''), K('bb'))], V(0))   # [eps/b][eps/bb]
    isodd_call = contains(sg, V(0), 'bb')
    d['F'] = (1, F('sel', isne(sg, untag),
                   F('F', cat(sg, F('sel', isodd_call, K('b'), K('bb')),
                              tail(sg, untag))),
                   F('sel', isodd_call, K(sg.bot), K(sg.top))))
    d['evenF'] = (1, F('F', cat(sg, K('b'), V(0))))
    d['oddF'] = (1, F('F', cat(sg, K('bb'), V(0))))
    return d


def test_E():
    print("== (E) mutual recursion definable from self: even/odd on tallies ==")
    d = evenodd_defs()
    n, ok = 0, True
    for k in range(0, 9):
        t = 'a' * k
        e1, _ = val(d, 'even', (t,))
        e2, _ = val(d, 'evenF', (t,))
        o1, _ = val(d, 'odd', (t,))
        o2, _ = val(d, 'oddF', (t,))
        we = sg.top if k % 2 == 0 else sg.bot
        wo = sg.bot if k % 2 == 0 else sg.top
        ok &= check('even', e1 == we and e2 == we, (k, e1, e2))
        ok &= check('oddm', o1 == wo and o2 == wo, (k, o1, o2))
        n += 2
    print(f"  direct mutual (even,odd) and single-F tagged version agree "
          f"with parity on tallies 0..8 ({n} pairs) -> {'OK' if ok else 'FAIL'}")
    return ok


# ===========================================================================
# F.  the 2-counter-machine compiler

# instruction format:
#   ('halt',)
#   ('inc', r, j)          counter r in {1,2}, goto j
#   ('decjz', r, jz, jnz)  if counter r = 0 goto jz else decrement, goto jnz
# configuration string:  b^i . a^{x+1} . b . a^{y+1} . b     (i = pc; x,y tallies)

def cm2_defs(instrs, out_counter=2):
    d = dict(BASE)
    # parsers (machine-independent), by structural recursion:
    # PCNT(C) = the leading b-run;  DROPB(C) = rest after leading b-run;
    # TAKEA(C) = leading a-run;     SKIPAB(C) = rest after first b (and it)
    d['PCNT'] = (1, F('sel', isne(sg, V(0)),
                      F('sel', eq(sg, head(sg, V(0)), K('b')),
                         cat(sg, K('b'), F('PCNT', tail(sg, V(0)))),
                         K('')),
                      K('')))
    d['DROPB'] = (1, F('sel', isne(sg, V(0)),
                       F('sel', eq(sg, head(sg, V(0)), K('b')),
                          F('DROPB', tail(sg, V(0))),
                          V(0)),
                       K('')))
    d['TAKEA'] = (1, F('sel', isne(sg, V(0)),
                       F('sel', eq(sg, head(sg, V(0)), K('a')),
                          cat(sg, K('a'), F('TAKEA', tail(sg, V(0)))),
                          K('')),
                       K('')))
    d['SKIPAB'] = (1, F('sel', isne(sg, V(0)),
                        F('sel', eq(sg, head(sg, V(0)), K('b')),
                           tail(sg, V(0)),
                           F('SKIPAB', tail(sg, V(0)))),
                        K('')))
    # projections of a configuration c:
    #   Xc = tail(TAKEA(DROPB c));  Yc = tail(TAKEA(SKIPAB(DROPB c)))
    Xc = tail(sg, F('TAKEA', F('DROPB', V(0))))
    Yc = tail(sg, F('TAKEA', F('SKIPAB', F('DROPB', V(0)))))

    def MK(iE, xE, yE):
        return cat(sg, iE, cat(sg, K('a'), cat(sg, xE,
                        cat(sg, K('b'), cat(sg, K('a'), cat(sg, yE, K('b')))))))

    # step(c): dispatch on PCNT(c) = b^i (i >= 1; i = 0 is halted)
    def case(i):
        ins = instrs[i - 1]
        if ins[0] == 'inc':
            _, r, j = ins
            xE, yE = (cat(sg, Xc, K('a')), Yc) if r == 1 else (Xc, cat(sg, Yc, K('a')))
            return MK(K('b' * j), xE, yE)
        else:
            _, r, jz, jnz = ins
            xe, ye = (Xc, eq(sg, Xc, K(''))) if r == 1 else (Yc, eq(sg, Yc, K('')))
            dec = tail(sg, xe)
            return F('sel', ye, MK(K('b' * jz), Xc, Yc), MK(K('b' * jnz), dec, Yc)) \
                if r == 1 else \
                F('sel', ye, MK(K('b' * jz), Xc, Yc), MK(K('b' * jnz), Xc, dec))

    body = K('')
    for i in reversed(range(1, len(instrs) + 1)):
        body = F('sel', eq(sg, F('PCNT', V(0)), K('b' * i)), case(i), body)
    d['step'] = (1, body)

    OUT = Yc if out_counter == 2 else Xc
    d['RUN'] = (1, F('sel', eq(sg, F('PCNT', V(0)), K('')),
                     OUT,
                     F('RUN', F('step', V(0)))))
    d['INIT'] = (1, MK(K('b'), V(0), K('')))     # pc = 1, c1 = input, c2 = 0
    d['MAIN'] = (1, F('RUN', F('INIT', V(0))))
    return d


def test_F():
    print("== (F) two-counter machines, compiled to definitions and RUN ==")
    # doubling machine: c2 := 2 * c1
    #   1: c1 = 0 ? goto 0 : (c1 -= 1; goto 2)
    #   2: c2 += 1; goto 3
    #   3: c2 += 1; goto 1
    instrs = [('decjz', 1, 0, 2), ('inc', 2, 3), ('inc', 2, 1)]
    d = cm2_defs(instrs, out_counter=2)
    ok = True
    for n in range(0, 6):
        r, st = val(d, 'MAIN', ('a' * n,))
        ok &= check('cm2-double', r == 'a' * (2 * n), (n, r, st))
    print(f"  doubling 2CM: MAIN(a^n) = a^2n for n = 0..5 -> {'OK' if ok else 'FAIL'}")

    # copy-and-add machine: c2 := c1 + c2 (c1 = n, c2 = m -> n + m)
    #   1: c1 = 0 ? goto 0 : (c1 -= 1; goto 2)
    #   2: c2 += 1; goto 1
    instrs2 = [('decjz', 1, 0, 2), ('inc', 2, 1)]
    d2 = cm2_defs(instrs2, out_counter=2)
    ok2 = True
    for n in range(0, 5):
        for m in range(0, 4):
            # start: pc=1, c1 = n, c2 = m -- need a custom INIT: rebuild below
            cfg = 'b' + 'a' * (n + 1) + 'b' + 'a' * (m + 1) + 'b'
            r, _ = val(d2, 'RUN', (cfg,))
            ok2 &= check('cm2-add', r == 'a' * (n + m), (n, m, r))
    print(f"  adder 2CM on RUN(config) for 20 (n,m) pairs: c2 = n+m -> "
          f"{'OK' if ok2 else 'FAIL'}")
    return ok and ok2


if __name__ == '__main__':
    a = test_A()
    b = test_B()
    c = test_C()
    d = test_D()
    e = test_E()
    f = test_F()
    print()
    print(f"ROUND3 RESULT: A(next)={'PASS' if a else 'FAIL'} B(mu)={'PASS' if b else 'FAIL'} "
          f"C(ADD/MULT)={'PASS' if c else 'FAIL'} D(coding)={'PASS' if d else 'FAIL'} "
          f"E(mutual)={'PASS' if e else 'FAIL'} F(2CM)={'PASS' if f else 'FAIL'} fails={FAIL}")
    sys.exit(0 if all([a, b, c, d, e, f]) else 1)

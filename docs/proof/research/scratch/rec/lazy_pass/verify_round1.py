"""Round 1 verification: (a) toolkit builders vs. Python truth, on random
strings; (b) CONSERVATIVITY: random CALL-FREE expressions, lazy-pass machine
vs. the eager denotation (Definition def:den) -- they must agree wherever the
eager denotation is defined, and every lazy Err must be eager-undefined;
(c) strict-extension example (lazy more defined than eager).

Run:  python3 verify_round1.py
"""

import itertools
import random
import sys

from core import K, V, C, S, F, pp, run_lazy, run_eager, ev_eager, Undefined, Diverge, subst, size
from toolkit import BIN, enc, dec, benc, bdec, enc2, dec2, cat, tail, head, eq, if_, isne, contains, sel_body, comp

sg = BIN
FAIL = 0


def check(name, ok, detail=''):
    global FAIL
    if not ok:
        FAIL += 1
        print(f"  FAIL {name} {detail}")
    return ok


def rnd(n):
    return ''.join(random.choice('ab') for _ in range(random.randint(0, n)))


def strings_upto(n, alpha='ab'):
    for L in range(n + 1):
        for t in itertools.product(alpha, repeat=L):
            yield ''.join(t)


# ---------------------------------------------------------------- (a) toolkit

def test_toolkit():
    print("== (a) raw-L toolkit builders vs Python truth ==")
    rng = random.Random(20260919)
    N = 400

    # evaluate a call-free expression with variables via a trivial
    # one-definition program whose body is the expression itself
    def val(e, *args):
        defs = {'main': (len(args), e)}
        res = run_lazy(defs, 'main', tuple(args), cap=500000)
        assert res[0] == 'val', (pp(e), args, res)
        return res[1]

    ok_enc = ok_cat = ok_ht = ok_eq = ok_if = ok_e2 = ok_benc = ok_cont = True
    for _ in range(N):
        w1, w2 = rnd(8), rnd(8)

        ok_enc &= check('enc', val(enc(sg, V(0)), w1) == w1.replace('a', 'ba'))
        ok_enc &= check('dec(enc)', val(dec(sg, enc(sg, V(0))), w1) == w1)
        ok_cat &= check('cat', val(cat(sg, V(0), V(1)), w1, w2) == w1 + w2)
        ok_ht &= check('tail', val(tail(sg, V(0)), w1) == (w1[1:] if w1 else ''))
        ok_ht &= check('head', val(head(sg, V(0)), w1) == (w1[:1] if w1 else ''))
        e = val(eq(sg, V(0), V(1)), w1, w2)
        ok_eq &= check('eq', e == (sg.top if w1 == w2 else sg.bot))
        w1c = rng.choice([sg.top, sg.bot])       # conditions must be top/bot
        w3 = rnd(4)
        e = val(if_(sg, V(0), V(1), V(2)), w1c, w2, w3)
        ok_if &= check('if', e == (w2 if w1c == sg.top else w3))
        ok_e2 &= check('enc2', val(enc2(sg, V(0)), w1) == ''.join(sg.x + c for c in w1))
        ok_e2 &= check('dec2', val(dec2(sg, enc2(sg, V(0))), w1) == w1)
        ok_e2 &= check('dec2.enc2', val(dec2(sg, V(0)), ''.join(sg.x + c for c in w1)) == w1)
        ok_benc &= check('bdec.benc', val(bdec(sg, benc(sg, V(0))), w1) == w1.replace('a', 'ba'))
        for B in ['a', 'b', 'ab', 'ba', 'aa', 'bb', 'aba']:
            c = val(contains(sg, V(0), B), w1)
            ok_cont &= check('contains', c == (sg.top if B in w1 else sg.bot), f'B={B} w={w1}')
    for nm, ok in [('enc/dec', ok_enc), ('cat', ok_cat), ('head/tail', ok_ht),
                   ('eq', ok_eq), ('if', ok_if), ('enc2/dec2', ok_e2),
                   ('benc', ok_benc), ('contains', ok_cont)]:
        print(f"  {nm:10s}: {'OK' if ok else 'FAIL'}  ({N} random pairs, len<=8)")
    return all([ok_enc, ok_cat, ok_ht, ok_eq, ok_if, ok_e2, ok_benc, ok_cont])


# ------------------------------------------------------- (b) conservativity

def rand_expr(rng, depth, nvars):
    if depth == 0:
        if rng.random() < 0.5:
            return V(rng.randrange(nvars))
        return K(rng.choice(['', 'a', 'b', 'ab', 'ba', 'aa', 'bb', 'aba', 'bab', 'aab', 'baa']))
    t = rng.random()
    if t < 0.30:
        return C(rand_expr(rng, depth - 1, nvars), rand_expr(rng, depth - 1, nvars))
    # substitution node: pattern biased towards sometimes-empty
    pat = rand_expr(rng, depth - 1, nvars)
    if rng.random() < 0.35:
        pat = K(rng.choice(['', 'a', 'b']))          # exercise [A/eps] paths
    return S(rand_expr(rng, depth - 1, nvars), pat, rand_expr(rng, depth - 1, nvars))


def test_conservativity():
    print("== (b) conservativity: call-free expressions, lazy machine vs eager denotation ==")
    rng = random.Random(42)
    NTRIAL, NSAMP = 30, 300
    agree_both = agree_lazy_more = err_cases = eager_unDef = timeouts = 0
    bad = []
    for trial in range(NTRIAL):
        for _ in range(NSAMP):
            nvars = rng.choice([1, 1, 2])
            e = rand_expr(rng, rng.choice([1, 2, 2, 3]), nvars)
            args = tuple(rnd(5) for _ in range(nvars))
            # eager denotation
            try:
                w = ev_eager({}, e, args)
                eager = ('val', w)
            except Undefined:
                eager = ('undef',)
            except Diverge:
                eager = ('div',)      # cannot happen call-free; guard anyway
            # lazy machine
            defs = {'main': (nvars, e)}
            res = run_lazy(defs, 'main', args, cap=2_000_000)
            if eager[0] == 'val':
                if res[0] == 'val' and res[1] == eager[1]:
                    agree_both += 1
                else:
                    bad.append((pp(e), args, eager, res))
            else:  # eager undefined (pattern-empty somewhere)
                eager_unDef += 1
                if res[0] == 'err':
                    err_cases += 1
                elif res[0] == 'val':
                    agree_lazy_more += 1
                elif res[0] == 'timeout':
                    timeouts += 1
                    bad.append((pp(e), args, eager, res))
                else:
                    bad.append((pp(e), args, eager, res))
    print(f"  trials={NTRIAL}x{NSAMP} random call-free expressions (vars<=2, depth<=3)")
    print(f"  eager defined        : {agree_both + len([b for b in bad])} cases, machine agreed on all: {agree_both} / {agree_both + sum(1 for b in bad if b[2][0]=='val')}")
    print(f"  eager undefined       : {eager_unDef} cases; machine Err: {err_cases}, machine Value (strict extension): {agree_lazy_more}")
    print(f"  machine timeouts     : {timeouts}")
    if bad:
        for b in bad[:5]:
            print("   MISMATCH:", b)
    return not bad and timeouts == 0


# --------------------------------------------------------- (c) strict example

def test_extension():
    print("== (c) strict extension: a call-free expression undefined eagerly, defined lazily ==")
    # E(X) = [ [X/eps-ish bad] / b ] X  -- replacement has an empty pattern
    # inside, so the eager denotation is undefined; over X = 'a' (no 'b') the
    # lazy pass is inert and the machine returns 'a'.
    E = S(S(V(0), K(''), K('')), K('b'), V(0))    # [ [X/eps] / b ] X
    defs = {'main': (1, E)}
    res = run_lazy(defs, 'main', ('a',))
    eag = run_eager(defs, 'main', ('a',))
    check('ext-lazy', res[0] == 'val' and res[1] == 'a', res)
    check('ext-eager', eag[0] == 'undef', eag)
    print(f"  E = {pp(E)}")
    print(f"  on X='a':  eager = {eag},  lazy = {res}")
    return res[0] == 'val' and res[1] == 'a' and eag[0] == 'undef'


if __name__ == '__main__':
    random.seed(7)
    a = test_toolkit()
    b = test_conservativity()
    c = test_extension()
    print()
    print(f"ROUND1 RESULT: toolkit={'PASS' if a else 'FAIL'} conservativity={'PASS' if b else 'FAIL'} extension={'PASS' if c else 'FAIL'} fails={FAIL}")
    sys.exit(0 if (a and b and c) else 1)

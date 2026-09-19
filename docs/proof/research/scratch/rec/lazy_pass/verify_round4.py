"""Round 4 verification: CONSEQUENCES.

  D.  design-lesson demos:
       D1: FINDING -- under lazy-pass the paper's `if` IS a two-way gate:
           only the taken branch is forced (probes); it gates divergent
           branches; and a whole scheme (rev) runs through it;
       D2: the naive one-way gate [B(X, F(tail X))/P]if(isne X, P, H) is
           UNSOUND: witness F(X) = [Omega(X)/a]if(isne X, a, a) diverges on
           X = eps though the intended base case is the constant a;
       D3: ungated structural recursion F(X) = cat(F(tail X), head X)
           diverges (lazy and eager); the gated version is rev (round 2).
  E.  eager-vs-lazy on the SAME program text:
       E1: [Omega(X)/b]X on X = a: lazy returns a (replacement discarded),
           eager diverges;
       E2: sel(TOP, X, Omega(X)): lazy returns X, eager diverges (round 2 B3).
  T5. X |-> X^{2^{|X|}}  (the Section-4-unreachable function):
       A(S,W) = sel(isne S, A(tail S, cat(W,W)), W);  EXP(X) = A(X,X);
       verified on ALL strings of length <= 4.
  T9. tower growth, TOTAL definition:
       REPL (single-leftmost replacement by structural recursion), the two
       restarts AMP1 = [baa/ab]^m and AMP2 = [ab/aa]^m as gated while
       loops, BLOCK = AMP2 . AMP1, and
           TWR(S) = sel(isne S, BLOCK(TWR(tail S)), "aaaa").
       Cross-checks: AMP1/AMP2 against the paper's restart() (imported from
       paper_variants/verify_variants.py); BLOCK against the Corollary
       cor:towers formula; TWR(S) = a^{K_|S|} on all strings of length <= 3
       with K = 4, 6, 14, 254.

Run:  python3 verify_round4.py
"""

import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'paper_variants'))
from verify_variants import restart          # noqa: E402  (paper primitive)

from core import K, V, C, S, F, pp, run_lazy, run_eager, subst
from toolkit import (BIN, enc, dec, benc, bdec, enc2, dec2, cat, tail, head,
                     eq, if_, isne, contains, sel_body, comp)

sg = BIN
FAIL = 0
BASE = {'sel': (3, sel_body(sg))}


def check(name, ok, detail=''):
    global FAIL
    if not ok:
        FAIL += 1
        print(f"  FAIL {name} {detail}", flush=True)
    return ok


def strings_upto(n, alpha='ab'):
    for L in range(n + 1):
        for t in itertools.product(alpha, repeat=L):
            yield ''.join(t)


def val(defs, name, args, cap=20_000_000):
    res = run_lazy(defs, name, tuple(args), cap=cap)
    assert res[0] == 'val', (name, args, res)
    return res[1], res[2]


# ===========================================================================
# D. design-lesson demos

def omega_defs():
    d = dict(BASE)
    d['Omega'] = (1, cat(sg, F('Omega', V(0)), V(0)))
    return d


def test_D():
    print("== (D) design-lesson demos ==", flush=True)
    # D1: under LAZY-PASS the paper's `if` guards: only the taken branch is
    # forced (the untaken branch's enc() sits in a replacement slot whose
    # pattern bb never occurs in the taken branch's enc-image).
    d = dict(BASE)
    d['probeT'] = (1, V(0))
    d['probeE'] = (1, V(0))
    d['main'] = (3, if_(sg, V(0), F('probeT', V(1)), F('probeE', V(2))))
    ok1 = True
    for c in [sg.top, sg.bot]:
        calls = {}
        r = run_lazy(d, 'main', (c, 'u', 'v'), cap=2_000_000,
                     collect=lambda ev, p: calls.update({p: calls.get(p, 0) + 1})
                     if ev == 'call' else None)
        wantT = 1 if c == sg.top else 0
        wantE = 1 if c == sg.bot else 0
        ok1 &= check('if-probes', r[0] == 'val' and r[1] == ('u' if c == sg.top else 'v')
                     and calls.get('probeT', 0) == wantT and calls.get('probeE', 0) == wantE,
                     (c, r, calls))
    print(f"  D1 if(C, probeT(u), probeE(v)): ONLY the taken branch's probe "
          f"activates (C=TOP and C=BOT) -> {'OK' if ok1 else 'FAIL'}: under "
          f"lazy-pass, if IS a two-way gate (it fails to guard only under the "
          f"eager denotation, cf. the paper's Remark rem:total-rep)", flush=True)

    # D1b: if gates DIVERGENT branches
    d = dict(BASE)
    d['Omega'] = (1, cat(sg, F('Omega', V(0)), V(0)))
    d['m1'] = (1, if_(sg, K(sg.top), V(0), F('Omega', V(0))))
    d['m2'] = (1, if_(sg, K(sg.bot), F('Omega', V(0)), V(0)))
    r1 = run_lazy(d, 'm1', ('ab',), cap=2_000_000)
    r2 = run_lazy(d, 'm2', ('ab',), cap=2_000_000)
    e1 = run_eager(d, 'm1', ('ab',), maxdepth=200, stepcap=300_000)
    ok1b = check('if-gate-div1', r1[0] == 'val' and r1[1] == 'ab', r1)
    ok1b &= check('if-gate-div2', r2[0] == 'val' and r2[1] == 'ab', r2)
    ok1b &= check('if-gate-eager', e1[0] == 'diverge', e1)
    print(f"  D1b if(TOP, X, Omega) = if(BOT, Omega, X) = X (lazy), while the "
          f"eager semantics diverges -> {'OK' if ok1b else 'FAIL'}", flush=True)

    # D1c: a whole scheme through if instead of sel: rev_if on all strings <= 6
    d = dict(BASE)
    d['revif'] = (1, if_(sg, isne(sg, V(0)),
                         cat(sg, F('revif', tail(sg, V(0))), head(sg, V(0))),
                         K('')))
    n1, ok1c = 0, True
    for s in strings_upto(6):
        r, _ = val(d, 'revif', (s,))
        ok1c &= check('revif', r == s[::-1], (s, r))
        n1 += 1
    print(f"  D1c rev through the paper's if (no sel): all {n1} strings of "
          f"length <= 6 reversed exactly -> {'OK' if ok1c else 'FAIL'}", flush=True)

    # D2: the naive one-way gate is unsound
    d = dict(BASE)
    d['Omega'] = (1, cat(sg, F('Omega', V(0)), V(0)))
    d['F'] = (1, S(F('Omega', V(0)), K('a'),
                   if_(sg, isne(sg, V(0)), K('a'), K('a'))))
    r = run_lazy(d, 'F', ('',), cap=300_000)
    ok2 = check('naive-gate-div', r[0] in ('timeout', 'blackhole'), r)
    print(f"  D2 naive gate F(X) = [Omega(X)/a]if(isne X, a, a): F(eps) = {r[0]} "
          f"(diverges; intended base was the constant a) -> "
          f"{'OK (witness shown)' if ok2 else 'FAIL'}", flush=True)

    # D3: ungated structural recursion diverges under BOTH semantics
    d = dict(BASE)
    d['BAD'] = (1, cat(sg, F('BAD', tail(sg, V(0))), head(sg, V(0))))
    rl = run_lazy(d, 'BAD', ('abc',), cap=300_000)
    re = run_eager(d, 'BAD', ('abc',), maxdepth=300, stepcap=300_000)
    ok3 = check('ungated-lazy', rl[0] in ('timeout', 'blackhole'), rl)
    ok3 &= check('ungated-eager', re[0] == 'diverge', re)
    print(f"  D3 ungated F(X) = cat(F(tail X), head X): lazy = {rl[0]}, eager = "
          f"{re[0]} (both diverge); the gated version is rev (round 2) -> "
          f"{'OK' if ok3 else 'FAIL'}", flush=True)
    return ok1 and ok1b and ok1c and ok2 and ok3


# ===========================================================================
# E.  eager vs lazy on the same text

def test_E():
    print("== (E) eager-divergent programs, lazy-terminating ==", flush=True)
    d = omega_defs()
    # E1: the replacement is discarded (pattern absent)
    d['main'] = (1, S(F('Omega', V(0)), K('b'), V(0)))
    r = run_lazy(d, 'main', ('a',), cap=2_000_000)
    re = run_eager(d, 'main', ('a',), maxdepth=300, stepcap=500_000)
    ok1 = check('E1-lazy', r[0] == 'val' and r[1] == 'a', r)
    ok1 &= check('E1-eager', re[0] == 'diverge', re)
    print(f"  E1 [Omega(X)/b]X on X='a': lazy = {r[:2]}, eager = {re} -> "
          f"{'OK' if ok1 else 'FAIL'}", flush=True)
    # E2: gated divergent argument (round 2 B3, repeated for the record)
    d['main'] = (1, F('sel', K(sg.top), V(0), F('Omega', V(0))))
    r = run_lazy(d, 'main', ('ab',), cap=2_000_000)
    re = run_eager(d, 'main', ('ab',), maxdepth=300, stepcap=500_000)
    ok2 = check('E2-lazy', r[0] == 'val' and r[1] == 'ab', r)
    ok2 &= check('E2-eager', re[0] == 'diverge', re)
    print(f"  E2 sel(TOP, X, Omega(X)) on X='ab': lazy = {r[:2]}, eager = {re} -> "
          f"{'OK' if ok2 else 'FAIL'}", flush=True)
    return ok1 and ok2


# ===========================================================================
# T5.  X |-> X^{2^{|X|}}

def test_T5():
    print("== (T5) EXP(X) = X^{2^{|X|}}  (unreachable in L, Section 4) ==", flush=True)
    d = dict(BASE)
    # A(S,W) = if S = eps then W else A(tail S, cat(W,W))
    d['A'] = (2, F('sel', isne(sg, V(0)),
                   F('A', tail(sg, V(0)), cat(sg, V(1), V(1))),
                   V(1)))
    d['EXP'] = (1, F('A', V(0), V(0)))
    n, ok = 0, True
    for X in strings_upto(4):
        r, st = val(d, 'EXP', (X,))
        ok &= check('exp', r == X * (2 ** len(X)), (X, len(r), st))
        n += 1
    print(f"  EXP on all {n} strings of length <= 4 (|X|=4 gives |output| = 64): "
          f"exact -> {'OK' if ok else 'FAIL'}", flush=True)
    return ok


# ===========================================================================
# T9.  tower growth

def tower_defs():
    d = dict(BASE)
    # PRE(B,S): does S start with B?  (recursion on B; S is a parameter
    # that is itself consumed along the way: the scheme allows arbitrary
    # parameter transformations, only the first argument must descend)
    d['PRE'] = (2, F('sel', isne(sg, V(0)),
                     F('sel', isne(sg, V(1)),
                        F('sel', eq(sg, head(sg, V(1)), head(sg, V(0))),
                           F('PRE', tail(sg, V(0)), tail(sg, V(1))),
                           K(sg.bot)),
                        K(sg.bot)),
                     K(sg.top)))
    # LEN(S) = a^{|S|}
    d['LEN'] = (1, F('sel', isne(sg, V(0)),
                     cat(sg, K('a'), F('LEN', tail(sg, V(0)))), K('')))
    # DROP(S,k): drop |k| characters
    d['DROP'] = (2, F('sel', isne(sg, V(1)),
                      F('DROP', tail(sg, V(0)), tail(sg, V(1))),
                      V(0)))
    # REPL(A,B,S): replace the LEFTMOST occurrence of B by A (recursive
    # scan; S = eps is the base, then PRE decides match-vs-skip)
    d['REPL'] = (3, F('sel', isne(sg, V(2)),
                      F('sel', F('PRE', V(1), V(2)),
                         cat(sg, V(0), F('DROP', V(2), F('LEN', V(1)))),
                         cat(sg, head(sg, V(2)),
                             F('REPL', V(0), V(1), tail(sg, V(2))))),
                      K('')))
    # AMP1 = the restart of [baa/ab];  AMP2 = the restart of [ab/aa]
    d['AMP1'] = (1, F('sel', contains(sg, V(0), 'ab'),
                      F('AMP1', F('REPL', K('baa'), K('ab'), V(0))),
                      V(0)))
    d['AMP2'] = (1, F('sel', contains(sg, V(0), 'aa'),
                      F('AMP2', F('REPL', K('ab'), K('aa'), V(0))),
                      V(0)))
    d['BLOCK'] = (1, F('AMP1', F('AMP2', V(0))))   # [ab/aa]-restart first, amplifier second
    # TWR: strip the amplifier's b-prefix with [eps/b] so the output is a
    # pure a-run:  TWR(S) = a^{K_|S|}, K_0 = 4, K_{n+1} = 2^{K_n/2+1} - 2
    d['TWR'] = (1, F('sel', isne(sg, V(0)),
                      S(K(''), K('b'), F('BLOCK', F('TWR', tail(sg, V(0))))),
                      K('aaaa')))
    return d


def test_T9():
    print("== (T9) tower growth: a TOTAL definition with tower output ==", flush=True)
    d = tower_defs()
    rng = random.Random(2026)

    # (i) REPL vs Python single-leftmost replacement
    ok0 = True
    for _ in range(60):
        S = ''.join(rng.choice('ab') for _ in range(rng.randint(0, 8)))
        for A, B in [('baa', 'ab'), ('ab', 'aa'), ('a', 'b'), ('ba', 'ab')]:
            i = S.find(B)
            want = (S[:i] + A + S[i + len(B):]) if i >= 0 else S
            r, _ = val(d, 'REPL', (A, B, S))
            ok0 &= check('repl', r == want, (A, B, S, r, want))
    print(f"  REPL (single-leftmost replacement) vs Python on 240 cases: "
          f"{'OK' if ok0 else 'FAIL'}", flush=True)

    # (ii) AMP1/AMP2 vs the paper's restart() primitive
    okA = True
    for _ in range(40):
        S = ''.join(rng.choice('ab') for _ in range(rng.randint(0, 7)))
        r1, _ = val(d, 'AMP1', (S,))
        r2, _ = val(d, 'AMP2', (S,))
        okA &= check('amp1', r1 == restart('baa', 'ab', S), (S, r1))
        okA &= check('amp2', r2 == restart('ab', 'aa', S), (S, r2))
    print(f"  AMP1, AMP2 (gated while loops) vs the paper's restart() on 80 "
          f"random strings (len <= 7): {'OK' if okA else 'FAIL'}", flush=True)

    # (iii) BLOCK vs the Corollary cor:towers formula
    okB = True
    for m in range(0, 3):
        for K in range(1, 9):
            S = 'b' * m + 'a' * K
            r, _ = val(d, 'BLOCK', (S,))
            j = K // 2
            want = 'b' * (m + j) + 'a' * (2 ** (j + 1) - 2 + (K % 2))
            okB &= check('block', r == want, (m, K, r, want))
    print(f"  BLOCK vs the amplifier formula b^m a^K -> b^(m+j) a^(2^(j+1)-2+K%2) "
          f"on 24 inputs (m<=2, K<=8): {'OK' if okB else 'FAIL'}", flush=True)

    # (iv) TWR(S) = a^{K_|S|} on all strings of length <= 3
    K = [4, 6, 14, 254]
    n, okT = 0, True
    for S in strings_upto(3):
        r, st = val(d, 'TWR', (S,))
        okT &= check('twr', r == 'a' * K[len(S)], (S, len(r), st))
        n += 1
    print(f"  TWR on all {n} strings of length <= 3: TWR(S) = a^K with "
          f"K = 4, 6, 14, 254 by |S| -> {'OK' if okT else 'FAIL'}", flush=True)
    print(f"  (K_{{n+1}} = 2^(K_n/2 + 1) - 2; K_4 = 2^128 - 2, beyond any "
          f"feasible run but forced by the verified formula)", flush=True)
    return ok0 and okA and okB and okT


if __name__ == '__main__':
    dres = test_D()
    eres = test_E()
    t5 = test_T5()
    t9 = test_T9()
    print()
    print(f"ROUND4 RESULT: D(demos)={'PASS' if dres else 'FAIL'} E(eager-vs-lazy)={'PASS' if eres else 'FAIL'} "
          f"T5(EXP)={'PASS' if t5 else 'FAIL'} T9(tower)={'PASS' if t9 else 'FAIL'} fails={FAIL}")
    sys.exit(0 if all([dres, eres, t5, t9]) else 1)

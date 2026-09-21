"""rev-reachability research -- core module.

QUESTION (paper docs/proof/main.tex, open problem 2 of Sec. 4 / hinge 2 of
Sec. 5.6):  is string reversal  rev(w) = w[::-1]  reachable in the FLAT
calculus L (Def. def:exp / def:den: no recursion, eager/strict in ALL
sub-expressions) over some/any finite alphabet with |Sigma| >= 2?

This module:
  * reuses the paper's primitive `subst` (Def. def:subst) VERBATIM from the
    cross-verified rec/lazy_pass/core.py (do not duplicate -- one source);
  * provides `den` -- an INDEPENDENT implementation of Def. def:den for
    call-free expressions (ASTs of the paper's grammar), written from the
    paper and cross-checked against rec/lazy_pass/core.ev_eager (which on
    call-free expressions is exactly def:den);
  * the rev oracle and small test-battery helpers.

Expression AST (identical node shape to rec/lazy_pass/core.py so that the
toolkit builders can be imported directly):
    ('K', w)        constant
    ('V', i)        i-th variable (0-based)
    ('C', e1, e2)   concatenation
    ('S', R, P, E)  [R/P]E   (P pattern, R replacement, E scrutinee)

Composition convention (paper):  [A1/B1][A2/B2]E applies [A2/B2] first.
`comp(passes, E)` takes passes in PAPER order, `pipe(passes, E)` in run
order.
"""

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_LAZY_PASS = os.path.join(_HERE, '..', 'rec', 'lazy_pass')
if _LAZY_PASS not in sys.path:
    sys.path.insert(0, _LAZY_PASS)

from core import subst as _subst          # noqa: E402  (cross-verified)
from core import K, V, C, S                # noqa: E402  (AST builders)
import core as _coremod                    # noqa: E402

subst = _subst


class Undefined(Exception):
    """[A/eps]: the pattern value of a pass is the empty string."""


def den(e, args):
    """The paper's Definition def:den for CALL-FREE expressions.

    den(('S', R, P, E))(args) = [den(R)/den(P)] den(E), undefined when
    den(P) = epsilon.  Strict in every sub-expression.  Independent of
    core.ev_eager (which is used only for cross-checking)."""
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return args[e[1]]
    if t == 'C':
        return den(e[1], args) + den(e[2], args)
    if t == 'S':
        R, P, E = e[1], e[2], e[3]
        T = den(E, args)
        B = den(P, args)
        if B == '':
            raise Undefined()
        A = den(R, args)
        return subst(A, B, T)
    raise ValueError(f'bad node {t}')


def den_try(e, args):
    """('ok', w) or ('undef', None)."""
    try:
        return ('ok', den(e, args))
    except Undefined:
        return ('undef', None)


def rev(w):
    return w[::-1]


# --------------------------------------------------------------------------
# pass-composition helpers (paper order vs run order)

def comp(passes, E):
    """passes = [(A1,B1),...,(Ak,Bk)] in PAPER order: builds
    [A1/B1][A2/B2]...[Ak/Bk]E.  The RIGHTMOST runs FIRST."""
    acc = E
    for (A, B) in reversed(passes):
        acc = S(A if isinstance(A, tuple) else K(A),
                B if isinstance(B, tuple) else K(B), acc)
    return acc


def pipe(passes, E):
    """passes in RUN order: passes[0] runs first."""
    return comp(list(reversed(passes)), E)


def pp(e, prec=0):
    """paper-notation pretty printer."""
    t = e[0]
    if t == 'K':
        return f'"{e[1]}"' if e[1] != '' else 'eps'
    if t == 'V':
        return f'X{e[1]+1}'
    if t == 'C':
        s = f'{pp(e[1],1)}·{pp(e[2],1)}'
        return f'({s})' if prec > 1 else s
    if t == 'S':
        return f'[{pp(e[1],0)}/{pp(e[2],0)}]{pp(e[3],2)}'
    raise ValueError(t)


def size(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + size(e[1]) + size(e[2])
    if t == 'S':
        return 1 + size(e[1]) + size(e[2]) + size(e[3])
    raise ValueError(t)


def variables(e):
    t = e[0]
    if t == 'V':
        return {e[1]}
    if t == 'K':
        return set()
    if t == 'C':
        return variables(e[1]) | variables(e[2])
    if t == 'S':
        return variables(e[1]) | variables(e[2]) | variables(e[3])
    raise ValueError(t)


# --------------------------------------------------------------------------
# test batteries

import itertools


def all_strings(n, sigma='ab'):
    return [''.join(t) for m in range(n + 1)
            for t in itertools.product(sigma, repeat=m)]


def battery(n, sigma='ab'):
    """all strings of length <= n; returns list."""
    return all_strings(n, sigma)


def eval_on(e, tests, arity=1):
    """evaluate unary e on the battery; returns list of ('ok',w)/('undef',)."""
    return [den_try(e, (s,)) for s in tests]

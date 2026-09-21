"""L+R core: eager evaluator for the MIXED calculus (L-passes and R-passes).

System under study (this directory): the paper's expression calculus of
Def. def:exp with TWO node kinds, no recursion, strict eager denotation as in
Def. def:den:

    ('K', w)        constant string w
    ('V', i)        i-th parameter (0-based)
    ('C', e1, e2)   concatenation e1 e2
    ('S', R, P, E)  L-pass  [R/P]E   (Def. def:subst: left-to-right sweep,
                    leftmost match first, all occurrences, never rescans
                    inserted text)
    ('SR', R, P, E) R-pass  [R/P]^R E (Def. def:r2l: right-to-left sweep,
                    rightmost match first, all occurrences, never rescans
                    inserted text)

[A/eps] is undefined in both directions; undefinedness propagates strictly
(exception PatternEmpty).

The two primitives are implemented INDEPENDENTLY here:

  * subst  -- the greedy leftmost loop (same as core.py of
              rec/lazy_pass and verify_variants.py);
  * substR -- an ITERATIVE right-to-left collector (rightmost match, then
              continue strictly left of the insertion), written fresh for
              this directory.  It is cross-checked against rev-duality
              (thm:rev-duality:  substR(A,B,C) == rev(subst(revA,revB,revC)))
              in verify_r1.py -- two independent derivations of the R-pass.

`toolkit` (rec/lazy_pass/toolkit.py, the cross-verified Section-2 builder
library) is importable for reuse: its ASTs use only 'S' nodes, which this
evaluator understands unchanged; `allR` converts them to all-R expressions
(for re-verifying thm:r2l-toolkit with an independent evaluator).
"""

import sys
sys.setrecursionlimit(200000)
sys.path.insert(0,
    '/home/cc/projects/meow-lang/docs/proof/research/scratch/rec/lazy_pass')


# --------------------------------------------------------------- primitives

def subst(A, B, C):
    """[A/B]C -- paper Definition def:subst. [A/eps] undefined -> raises."""
    if not B:
        raise ValueError("[A/eps] undefined")
    out, i, n, m = [], 0, len(C), len(B)
    while i < n:
        if C[i:i + m] == B:
            out.append(A)
            i += m
        else:
            out.append(C[i])
            i += 1
    return ''.join(out)


def substR(A, B, C):
    """[A/B]^R C -- paper Definition def:r2l.

    C = XBY with |Y| minimal  =>  [A/B]^R C = ([A/B]^R X) . A . Y.
    Iterative: repeatedly take the RIGHTMOST occurrence of B in the still
    unscanned prefix C[:end], emit (A, gap) pairs right-to-left, continue
    with end = match start.  Inserted text (A) is never part of the search
    space again -- matches of later (more-left) rounds live in C[:s].
    """
    if not B:
        raise ValueError("[A/eps]^R undefined")
    parts = []
    end = len(C)
    while end >= len(B):
        s = C.rfind(B, 0, end)
        if s < 0:
            break
        parts.append(C[s + len(B):end])   # gap to the right of this match
        parts.append(A)                   # the insertion
        end = s
    parts.append(C[:end])                 # unscanned left part
    return ''.join(reversed(parts))


def rev(s):
    return s[::-1]


# --------------------------------------------------------------- AST

def K(w):  return ('K', w)
def V(i):  return ('V', i)
def C(e1, e2): return ('C', e1, e2)
def S(R, P, E):  return ('S', R, P, E)     # L-node  [R/P]E
def SR(R, P, E): return ('SR', R, P, E)    # R-node  [R/P]^R E


class PatternEmpty(Exception):
    """[A/eps]: the pattern value is the empty string."""


def ev(e, env):
    """Strict eager denotation (Def. def:den, extended with the R-node).
    env: tuple of strings.  Raises PatternEmpty on an empty pattern value."""
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return env[e[1]]
    if t == 'C':
        return ev(e[1], env) + ev(e[2], env)
    if t == 'S' or t == 'SR':
        T = ev(e[3], env)
        B = ev(e[2], env)
        A = ev(e[1], env)
        if B == '':
            raise PatternEmpty
        return subst(A, B, T) if t == 'S' else substR(A, B, T)
    raise ValueError(f'bad node {t}')


def run(e, args, default=None):
    """Evaluate; on PatternEmpty return `default`."""
    try:
        return ev(e, tuple(args))
    except PatternEmpty:
        return default


# --------------------------------------------------------------- structure

def size(e):
    t = e[0]
    if t in ('K', 'V'):
        return 1
    if t == 'C':
        return 1 + size(e[1]) + size(e[2])
    if t in ('S', 'SR'):
        return 1 + size(e[1]) + size(e[2]) + size(e[3])
    raise ValueError(t)


def allR(e):
    """Convert every L-node to an R-node (constants and structure kept)."""
    t = e[0]
    if t in ('K', 'V'):
        return e
    if t == 'C':
        return ('C', allR(e[1]), allR(e[2]))
    if t == 'S':
        return ('SR', allR(e[1]), allR(e[2]), allR(e[3]))
    if t == 'SR':
        return ('SR', allR(e[1]), allR(e[2]), allR(e[3]))
    raise ValueError(t)


def conj(e):
    """The rev-conjugate of thm:conjugation: constant W -> rev W, every node
    [R/P] -> [R~/P~]^R (and [R/P]^R -> [R~/P~]), concatenation children
    swapped.  An involution: conj(conj(e)) == e."""
    t = e[0]
    if t == 'K':
        return ('K', e[1][::-1])
    if t == 'V':
        return e
    if t == 'C':
        return ('C', conj(e[2]), conj(e[1]))
    if t == 'S':
        return ('SR', conj(e[1]), conj(e[2]), conj(e[3]))
    if t == 'SR':
        return ('S', conj(e[1]), conj(e[2]), conj(e[3]))
    raise ValueError(t)


def pp(e, prec=0):
    t = e[0]
    if t == 'K':
        return f'"{e[1]}"' if e[1] != '' else '"eps"'
    if t == 'V':
        return f'X{e[1]+1}'
    if t == 'C':
        s = f'{pp(e[1], 1)}·{pp(e[2], 1)}'
        return f'({s})' if prec > 1 else s
    if t == 'S':
        return f'[{pp(e[1], 0)}/{pp(e[2], 0)}]{pp(e[3], 2)}'
    if t == 'SR':
        return f'[{pp(e[1], 0)}/{pp(e[2], 0)}]^R {pp(e[3], 2)}'
    raise ValueError(t)


# --------------------------------------------------------------- word utils

def iter_strings(sigma, maxlen, minlen=0):
    """All strings over sigma with minlen <= |s| <= maxlen, in length-lex order."""
    import itertools
    for L in range(minlen, maxlen + 1):
        for tup in itertools.product(sigma, repeat=L):
            yield ''.join(tup)


def borders(w):
    """All proper borders of w (nonempty, != w): u proper prefix AND suffix."""
    return [w[:i] for i in range(1, len(w))
            if w[:i] == w[len(w) - i:]]


def unbordered(w):
    return not borders(w)


# --------------------------------------------------------------- testing kit

def fun_table(e, arity, domain):
    """The finite function table of e over domain^arity (values may be None
    for PatternEmpty).  For equivalence checks on finite domains."""
    import itertools
    out = []
    for args in itertools.product(domain, repeat=arity):
        out.append(run(e, args))
    return tuple(out)


class Tally:
    def __init__(self, name):
        self.name, self.n, self.bad = name, 0, []
    def check(self, cond, note=''):
        self.n += 1
        if not cond:
            self.bad.append(note)
    def report(self):
        if self.bad:
            print(f'[{self.name}] FAIL: {self.n} checks, '
                  f'{len(self.bad)} bad; first: {self.bad[:3]}')
        else:
            print(f'[{self.name}] ok: {self.n} checks, 0 failures')
        return not self.bad

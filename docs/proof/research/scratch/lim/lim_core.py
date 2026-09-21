"""lim_core.py -- the L + lim calculus: the paper's grammar plus ONE node.

Target paper: docs/proof/main.tex ("A Theory of String Substitution over
Finite Alphabets").  Notation: def:subst = the primitive (one left-to-right
sweep, leftmost-first, never rescanning inserted text); def:exp/def:den =
the expression grammar and its eager denotation; def:markov = the restart
variant; thm:amplifier / cor:towers = the amplifier family.

Grammar implemented here (NO recursion, NO call nodes -- flat expressions
of the paper's Section 3 plus the new node):

    ('K', w)          constant string w
    ('V', i)          the i-th variable (0-based)
    ('C', e1, e2)     concatenation e1 e2
    ('S', R, P, E)    the paper's pass node  [R/P]E   (eager, strict)
    ('L', E, E0)      lim(E) started at E0     -- THE NEW NODE

The user's operator.  "lim(E) for a unary expression E in Exp_1; the orbit
s_0 = X, s_{k+1} = E(s_k); the value of lim(E)(X) is the first s_K with
s_{K+1} = s_K; if no such K exists, undefined."

Hygienic formalization (needed because the paper's Exp has "no binders --
capture-free" and we must not break Lemma lem:beta): the node carries an
explicit START expression, exactly the way the pass node carries its
scrutinee:

  * E  in Exp_1 is the ITERAND.  Its variable X1 is BOUND by the node and
    denotes the CURRENT ORBIT POINT.  (Validator: only V(0) may occur.)
  * E0 in Exp_n is the START: s_0 = [[E0]](S_1..S_n).
  * ('L', E, E0) is in Exp_n; its free variables are those of E0.

In unary contexts the paper notation lim(E)(X) is ('L', E, V(0)).
Substitution [F/X_i] acts on E0 and not on E (E is closed under outer
variables), so Lemma lem:beta (composition) survives verbatim; nested
lim nodes are allowed (E0 may itself contain lim, and E's sub-expressions
may contain lim nodes whose own Exp_1 parts are evaluated in the orbit
environment).

Denotation of ('L', E, E0) at S = (S_1..S_n):

    s_0     = [[E0]](S)                     (undefined -> lim undefined)
    s_{k+1} = [[E]](s_k)                    (undefined -> lim undefined)
    value   = the first s_K with s_{K+1} = s_K
    undefined if no such K exists.

Operational caps (the paper's census convention: cap exceeded = presumed
divergence): a shared budget counts every substitution AND every orbit
iteration; a produced string longer than maxlen aborts.  Both raise
Diverge, reported as verdict 'div'.

`subst` is the paper's Definition def:subst, character-for-character the
same function as research/scratch/rec/lazy_pass/core.py and
research/scratch/paper_variants/verify_variants.py.  `subst_fast` is
CPython str.replace (leftmost-first, non-overlapping, never rescanning
inserted text -- the same contract; cross-verified in verify_r1 part 0).

`restart` is the paper's Definition def:markov (single-rule Markov), copied
from verify_variants.py, with an added length cap.
"""

import sys
sys.setrecursionlimit(100000)


# ---------------------------------------------------------------------------
# the primitive

def subst(A, B, C):
    """[A/B]C -- paper Definition def:subst (greedy leftmost, non-overlapping,
    never restarting inside inserted text).  [A/eps] undefined -> raises."""
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


def subst_fast(A, B, C):
    """Same contract as subst, via CPython str.replace (C speed).
    str.replace scans left to right, takes the leftmost non-overlapping
    matches, and never rescans the replacement: exactly def:subst."""
    if not B:
        raise ValueError("[A/eps] undefined")
    return C.replace(B, A)


def restart(A, B, C, cap=5000, caplen=1 << 22):
    """[A/B]^m C -- paper Definition def:markov: replace the leftmost B,
    rescan from 0, until B-free.  None = diverged (step or length cap)."""
    if not B:
        raise ValueError
    s, steps = C, 0
    while B in s:
        steps += 1
        if steps > cap or len(s) > caplen:
            return None
        i = s.find(B)
        s = s[:i] + A + s[i + len(B):]
    return s


# ---------------------------------------------------------------------------
# AST

def K(w):  return ('K', w)
def V(i):  return ('V', i)
def C(e1, e2): return ('C', e1, e2)
def S(R, P, E): return ('S', R, P, E)          # [R/P]E
def L(E, E0):   return ('L', E, E0)            # lim(E) started at E0


def check(e, n=None, bound_ok=True, _ctx='root'):
    """Structural check; also enforces the lim arity discipline: the iterand
    of an ('L',E,E0) node may contain ONLY the variable V(0)."""
    t = e[0]
    if t == 'K':
        return
    if t == 'V':
        if n is not None and e[1] >= n:
            raise ValueError(f"variable X{e[1]+1} out of arity in {_ctx}")
        return
    if t == 'C':
        check(e[1], n, bound_ok, _ctx); check(e[2], n, bound_ok, _ctx); return
    if t == 'S':
        check(e[1], n, bound_ok, _ctx)
        check(e[2], n, bound_ok, _ctx)
        check(e[3], n, bound_ok, _ctx); return
    if t == 'L':
        check(e[1], 1, bound_ok, _ctx + '.iterand')   # iterand: Exp_1 only
        check(e[2], n, bound_ok, _ctx + '.start'); return
    raise ValueError(f"bad node {t}")


def vars_of(e):
    out = set()
    def go(e):
        t = e[0]
        if t == 'K': return
        if t == 'V': out.add(e[1]); return
        if t == 'C': go(e[1]); go(e[2]); return
        if t == 'S': go(e[1]); go(e[2]); go(e[3]); return
        if t == 'L': go(e[2]); return            # E is closed (bound var 0)
        raise ValueError(t)
    go(e)
    return out


def size(e):
    t = e[0]
    if t in ('K', 'V'): return 1
    if t == 'C': return 1 + size(e[1]) + size(e[2])
    if t == 'S': return 1 + size(e[1]) + size(e[2]) + size(e[3])
    if t == 'L': return 1 + size(e[1]) + size(e[2])
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
    if t == 'L':
        return f'lim({pp(e[1], 0)})[{pp(e[2], 1)}]'
    raise ValueError(t)


# ---------------------------------------------------------------------------
# the eager evaluator with the lim node

class Undefined(Exception):
    """[A/eps] under eager semantics (paper def:den)."""

class Diverge(Exception):
    """budget exhausted: presumed divergence (cap convention)."""


class Budget:
    def __init__(self, maxsteps=1_000_000, maxlen=1 << 20):
        self.maxsteps, self.maxlen = maxsteps, maxlen
        self.steps = 0
        self.subst = 0
        self.orbit = 0
    def tick(self):
        self.steps += 1
        if self.steps > self.maxsteps:
            raise Diverge()
    def guard(self, w):
        if len(w) > self.maxlen:
            raise Diverge()


def ev(e, env, bud):
    """Eager denotation of the extended grammar.  env = tuple of strings.
    Raises Undefined (empty pattern) / Diverge (budget)."""
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return env[e[1]]
    if t == 'C':
        return ev(e[1], env, bud) + ev(e[2], env, bud)
    if t == 'S':
        T = ev(e[3], env, bud)
        B = ev(e[2], env, bud)
        A = ev(e[1], env, bud)
        if B == '':
            raise Undefined()
        bud.tick(); bud.subst += 1
        w = subst_fast(A, B, T)
        bud.guard(w)
        return w
    if t == 'L':
        s = ev(e[2], env, bud)          # the start
        return orbit(e[1], s, bud)
    raise ValueError(t)


def orbit(E, s, bud):
    """The orbit of the iterand E (an Exp_1, evaluated at V(0) = current
    point) from s: returns the first fixed point, raises Diverge if the
    budget runs out first."""
    bud.guard(s)
    while True:
        bud.tick(); bud.orbit += 1
        t = ev(E, (s,), bud)
        if t == s:
            return t
        bud.guard(t)
        s = t


def run(e, args, maxsteps=1_000_000, maxlen=1 << 20):
    """Evaluate the unary/whatever expression e on the tuple args.
    Returns ('val', w, budget) | ('undef',) | ('div',)."""
    bud = Budget(maxsteps, maxlen)
    try:
        w = ev(e, tuple(args), bud)
        return ('val', w, bud)
    except Undefined:
        return ('undef',)
    except Diverge:
        return ('div',)


# ---------------------------------------------------------------------------
# direct (expression-free) orbit of a single pass -- used by the census,
# which does not need the AST machinery.  Cross-checked against the
# evaluator in verify_r1.

def orbit_pass(A, B, C, capsteps=4000, caplen=1 << 20):
    """lim([A/B])(C) computed directly: iterate the sweep s -> [A/B]s until
    s_{k+1} = s_k.  Returns ('val', w, sweeps) | ('div',)."""
    if not B:
        raise ValueError
    s, k = C, 0
    while True:
        t = subst_fast(A, B, s)
        k += 1
        if t == s:
            return ('val', t, k)
        if k > capsteps or len(t) > caplen:
            return ('div',)
        s = t

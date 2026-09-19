#!/usr/bin/env python3
"""Stream semantics for recursive definitions over the substitution calculus.

The primitive [R/P]S is one greedy left-to-right pass, leftmost-first,
non-overlapping, never rescanning inserted text (paper Def 1); a single
constant-pattern pass is an online causal process whose state is the
longest suffix of the text read so far that is a proper prefix of P
(the classical pattern-matching automaton; paper Thm "subsequential").
Here the scrutinee is a STREAM (finite or infinite string) and the pass
is run as that causal process:

  * the greedy scan consumes the scrutinee character by character;
  * state = longest suffix of consumed text that is a proper prefix of
    the pattern; a mismatch is detected with only as much of the pattern
    as has been compared, and flushes every character that can no longer
    belong to a match;
  * on completing a match the process emits the replacement's characters
    (the replacement is itself a stream, forced exactly then), and the
    scan resumes after the match with a fresh state, never rescanning
    the inserted text.

Fragment F1: one variable X, one recursive definition f(X) = body,
constants, cat, pass nodes.  Patterns may be arbitrary expressions (a
pattern is then itself a stream, pulled lazily along the comparison
frontier -- research item 3); in F1 they are constants.

The interpreter is an EXPLICIT process machine: a demand-driven tree of
processes (one node per expression evaluation), stepped by a flat loop
with a work stack -- no Python recursion, so arbitrarily deep unfolding
is fine and deadlock is detected by budget/depth caps only.

A run answers a demand with a character, with end-of-stream (EOS), or
stalls (no answer ever): the last is the operational face of the
least-fixpoint bottom.
"""

import itertools
import sys

EOS = None


class UndefinedPattern(Exception):
    """[A/eps] is undefined (paper Def 1)."""


class BudgetExceeded(Exception):
    """Step budget exhausted (absorbing / non-emitting loop)."""


class DeepStall(Exception):
    """Process-stack cap exceeded (deadlock by infinite regress)."""


# --------------------------------------------------------------------- AST

class Exp(object):
    __slots__ = ()


class Var(Exp):
    __slots__ = ('name',)

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name


class Const(Exp):
    __slots__ = ('w',)

    def __init__(self, w):
        self.w = w

    def __repr__(self):
        return repr(self.w)


class Cat(Exp):
    __slots__ = ('a', 'b')

    def __init__(self, a, b):
        self.a, self.b = a, b

    def __repr__(self):
        return '(%r . %r)' % (self.a, self.b)


class Pass(Exp):
    __slots__ = ('R', 'P', 'E', 'nid')

    _count = [0]

    def __init__(self, R, P, E):
        self.R, self.P, self.E = R, P, E
        Pass._count[0] += 1
        self.nid = Pass._count[0]

    def __repr__(self):
        return '[%r/%r]%r' % (self.R, self.P, self.E)


class Call(Exp):
    __slots__ = ('name', 'arg')

    def __init__(self, name, arg):
        self.name, self.arg = name, arg

    def __repr__(self):
        return '%s(%r)' % (self.name, self.arg)


# convenience constructors
def V(name='X'):
    return Var(name)


def C(w):
    return Const(w)


def cat(*es):
    assert es
    e = es[0]
    for x in es[1:]:
        e = Cat(e, x)
    return e


def sub(R, P, E):
    """[R/P]E"""
    return Pass(R, P, E)


def F(arg, name='f'):
    return Call(name, arg)


# ------------------------------------------------------------- the machine

class Machine(object):
    def __init__(self, body, name='f'):
        self.defs = {name: body}
        self.steps = 0
        self.budget = 50 * 10 ** 6
        self.maxstack = 300000
        self.forced = {}       # pass node id -> max pattern prefix pulled

    def tick(self):
        self.steps += 1
        if self.steps > self.budget:
            raise BudgetExceeded()

    def xsrc(self, env, name):
        """Resolve the source bound to `name` in `env`, with path
        compression: chains of variable-to-variable argument bindings
        collapse to the underlying source.  Returns a zero-arg factory
        producing a fresh process per call (call-by-name re-evaluation)."""
        seen = []
        v = env.get(name)
        while isinstance(v, Arg):
            if isinstance(v.e, Var):
                seen.append((env, name))
                env, name = v.env, v.e.name
                v = env.get(name)
            else:
                f = (lambda vv: (lambda: self.mkproc(vv.e, vv.env)))(v)
                for (e2, n2) in seen:
                    e2[n2] = f
                return f
        for (e2, n2) in seen:
            e2[n2] = v
        return v

    def mkproc(self, e, env):
        """A fresh process computing the value of e under env."""
        if isinstance(e, Var):
            return self.xsrc(env, e.name)()
        if isinstance(e, Const):
            return ConstProc(e.w)
        if isinstance(e, Cat):
            return CatProc(e, env)
        if isinstance(e, Pass):
            return PassProc(e, env)
        if isinstance(e, Call):
            return CallProc(e, env, self.defs[e.name])
        raise TypeError('bad expression %r' % (e,))

    def pull(self, root):
        """Demand one character from the process `root`.

        Returns a character, or EOS (None) when the process is exhausted.
        """
        stack = [root]
        while True:
            self.tick()
            if len(stack) > self.maxstack:
                raise DeepStall()
            r = stack[-1].step(self)
            # r is ('out', c) | ('eos',) | ('need', child)
            while r[0] in ('out', 'eos'):
                if len(stack) == 1:
                    return r[1] if r[0] == 'out' else None
                stack.pop()
                c = r[1] if r[0] == 'out' else None
                r = stack[-1].got(c, self)
            if r[0] == 'need':
                stack.append(r[1])


class ConstProc(object):
    __slots__ = ('w', 'i')

    def __init__(self, w):
        self.w, self.i = w, 0

    def step(self, m):
        if self.i < len(self.w):
            self.i += 1
            return ('out', self.w[self.i - 1])
        return ('eos',)

    def got(self, c, m):
        raise AssertionError('ConstProc.got')


class Arg(object):
    """A deferred argument binding: X is bound to the expression `e`
    evaluated in `env` (call-by-name)."""
    __slots__ = ('e', 'env')

    def __init__(self, e, env):
        self.e, self.env = e, env


class RelayProc(object):
    """Relays a child process created lazily by `factory` (Var, Call)."""
    __slots__ = ('factory', 'child')

    def __init__(self, factory):
        self.factory = factory
        self.child = None

    def step(self, m):
        if self.child is None:
            self.child = self.factory()
        return ('need', self.child)

    def got(self, c, m):
        if c is None:
            return ('eos',)
        return ('out', c)


class CatProc(object):
    __slots__ = ('e', 'env', 'phase', 'child')

    def __init__(self, e, env):
        self.e, self.env = e, env
        self.phase = 0          # 0 = left, 1 = right
        self.child = None

    def step(self, m):
        if self.child is None:
            self.child = m.mkproc(self.e.a if self.phase == 0 else self.e.b,
                                  self.env)
        return ('need', self.child)

    def got(self, c, m):
        if c is not None:
            return ('out', c)
        # left exhausted: move to the right part
        if self.phase == 0:
            self.phase = 1
            self.child = m.mkproc(self.e.b, self.env)
            return ('need', self.child)
        self.child = None
        return ('eos',)


class CallProc(object):
    """f(G): evaluate the body with X bound to a fresh-source factory for G."""
    __slots__ = ('child', 'arg', 'env', 'body')

    def __init__(self, e, env, body):
        self.arg, self.env, self.body = e.arg, env, body
        self.child = None

    def step(self, m):
        if self.child is None:
            env2 = dict(self.env)
            env2['X'] = Arg(self.arg, self.env)
            self.child = m.mkproc(self.body, env2)
        return ('need', self.child)

    def got(self, c, m):
        if c is None:
            return ('eos',)
        return ('out', c)


class PassProc(object):
    """[R/P]E as a causal process (the heart of the interpreter).

    State: buffer (longest suffix of consumed scrutinee that is a proper
    prefix of the pattern), the pattern cache `pc` (chars forced so far),
    `pat_done` (pattern source exhausted), an output queue, a pending
    input character, the current sub-state, and the per-match replacement
    process (fresh on each match; its value is re-derived, never reread).
    """
    __slots__ = ('e', 'env', 'pc', 'pat_done', 'buf', 'outq', 'pend',
                 'state', 'scr', 'pat', 'rproc', 'pending_need')

    def __init__(self, e, env):
        self.e, self.env = e, env
        self.pc = ''
        self.pat_done = False
        self.buf = ''
        self.outq = []
        self.pend = None
        self.state = 'init'
        self.scr = None
        self.pat = None
        self.rproc = None
        self.pending_need = None   # 'cmp' | 'probe' | 'probe0'

    # -- helpers
    def _mkR(self, m):
        if self.rproc is None:
            self.rproc = m.mkproc(self.e.R, self.env)
        return self.rproc

    def _resume(self, m):
        """Produce the next event after any internal state change."""
        if self.state == 'drain':
            return ('need', self._mkR(m))
        if self.outq:
            return ('out', self.outq.pop(0))
        return ('need', self.scr)

    def _match(self):
        # replacement: fresh process; scan resumes after it, fresh state
        self.state = 'drain'
        self.rproc = None
        self.buf = ''

    def _compare(self, c, m):
        """Resolve the comparison of the input char c.  Returns
        ('need', pattern) if a pattern char must be forced first
        (pending_need is set accordingly), or None if the comparison is
        complete (the caller continues with _resume)."""
        k = len(self.buf)
        if k < len(self.pc):
            pk = self.pc[k]
        elif self.pat_done:
            pk = None
        else:
            self.pending_need = 'cmp'
            self.pend = c
            return ('need', self.pat)
        if pk == c:
            self.buf += c
            # post-extension probe: is the pattern exhausted at len(buf)?
            if len(self.buf) < len(self.pc):
                return None
            if self.pat_done:            # len(buf) == len(pc): full match
                self._match()
                return None
            self.pending_need = 'probe'
            return ('need', self.pat)
        # mismatch: fall back to the longest suffix of buf+c that is a
        # proper prefix of the pattern.  Candidates have length
        # <= |buf| <= |pc|-1 (invariant), so only cached chars are used.
        b2 = self.buf + c
        keep = 0
        for L in range(len(b2) - 1, 0, -1):
            if b2[len(b2) - L:] == self.pc[:L]:
                keep = L
                break
        self.outq.extend(b2[:len(b2) - keep])
        self.buf = b2[len(b2) - keep:]
        return None

    def step(self, m):
        st = self.state
        if st == 'init':
            self.scr = m.mkproc(self.e.E, self.env)
            self.pat = m.mkproc(self.e.P, self.env)
            self.pending_need = 'probe0'
            self.state = 'scan'
            return ('need', self.pat)
        if st == 'drain':
            return ('need', self._mkR(m))
        if st == 'flush':
            if self.outq:
                return ('out', self.outq.pop(0))
            return ('eos',)
        # 'scan'
        if self.outq:
            return ('out', self.outq.pop(0))
        return ('need', self.scr)

    def got(self, c, m):
        # deliver events from scr / pat / rproc, according to pending_need
        # and state.
        if self.state == 'drain':
            if c is None:
                self.rproc = None
                self.state = 'scan'
                return ('need', self.scr)
            return ('out', c)
        # pattern deliveries
        if self.pending_need is not None:
            mode = self.pending_need
            self.pending_need = None
            if c is None:
                self.pat_done = True
                if mode == 'probe0':
                    raise UndefinedPattern('[R/eps] undefined')
                if mode == 'probe':
                    # pattern exhausted exactly at len(buf): full match
                    self._match()
                    return self._resume(m)
                # mode == 'cmp': pattern ended at index len(buf); the
                # stashed char cannot extend -> mismatch with pk = None
                self._compare(self.pend, m)
                return self._resume(m)
            self.pc += c
            m.forced[self.e.nid] = max(m.forced.get(self.e.nid, 0),
                                       len(self.pc))
            if mode == 'probe0':
                return self._resume(m)
            if mode == 'probe':
                # pattern continues: no match yet
                return self._resume(m)
            # mode == 'cmp'
            r = self._compare(self.pend, m)
            if r is not None:
                return r
            return self._resume(m)
        # scrutinee delivery
        if self.state == 'flush':
            raise AssertionError('late delivery')
        if c is None:
            # scrutinee exhausted: flush the buffer, then EOS
            self.outq.extend(self.buf)
            self.buf = ''
            self.state = 'flush'
            if self.outq:
                return ('out', self.outq.pop(0))
            return ('eos',)
        r = self._compare(c, m)
        if r is not None:
            return r
        return self._resume(m)


# ------------------------------------------------------------------ sources
# A source factory is a zero-arg callable returning a fresh PROCESS.

class SrcProc(object):
    __slots__ = ('it',)

    def __init__(self, it):
        self.it = it

    def step(self, m):
        m.tick()
        try:
            return ('out', next(self.it))
        except StopIteration:
            return ('eos',)

    def got(self, c, m):
        raise AssertionError('SrcProc.got')


def src_fin(w):
    return lambda: SrcProc(iter(w))


def src_cycle(p):
    """The infinite periodic stream p^omega (p nonempty)."""
    return lambda: SrcProc(itertools.cycle(p))


def src_gen(gen):
    """Arbitrary deterministic generator of characters (must be
    re-instantiable per call: gen is a zero-arg function)."""
    return lambda: SrcProc(gen())


# ------------------------------------------------------------------- driver

LIVE, TERM, STALL, UNDEF = 'LIVE', 'TERM', 'STALL', 'UNDEF'


def run(main, src, body=None, nchars=200, budget=50 * 10 ** 6,
        name='f', maxstack=None):
    """Run `main` on the source `src` (a factory).

    Returns (verdict, output, machine): verdict is
      LIVE  -- at least nchars characters were emitted,
      TERM  -- the process ended (EOS) with a finite output,
      STALL -- no further answer (deadlock or absorbing loop),
      UNDEF -- undefined ([R/eps]).
    """
    mach = Machine(body if body is not None else main, name)
    mach.budget = budget
    if maxstack is not None:
        mach.maxstack = maxstack
    root = mach.mkproc(main, {'X': src})
    out = []
    verdict = TERM
    try:
        while len(out) < nchars:
            c = mach.pull(root)
            if c is None:
                break
            out.append(c)
        else:
            verdict = LIVE
    except UndefinedPattern:
        verdict = UNDEF
    except (BudgetExceeded, DeepStall):
        verdict = STALL
    return verdict, ''.join(out), mach

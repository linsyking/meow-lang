#!/usr/bin/env python3
"""Machinery for the EAGER recursive calculus L_rec over the paper's primitive.

Paper: "A Theory of String Substitution over Finite Alphabets"
  - Definition def:subst: [A/B]C = one greedy left-to-right pass, leftmost
    match first, non-overlapping, never rescanning inserted text; [A/eps]
    undefined.
  - Definition def:den: expressions Exp_n with strict denotation.
New stage: a finite set of first-order definitions f_1..f_k, bodies in the
extended grammar whose only new node is the CALL f_j(E_1..E_m) (arity-checked).
EAGER semantics: call-by-value, every constructor strict in every
sub-expression, the whole system read as the LEAST fixed point.

Three mutually independent computations, which the theory says coincide:
  1. phi : Kleene approximants phi^n of the denotational fixpoint
     (phi^0 = bottom; phi^{n+1}_j(S) = ⟦B_j⟧_{phi^n}(S)).
  2. run : unbounded eager operational evaluation (left-to-right), outcomes
     Halt(v) / Err (empty pattern) / Cut (fuel exhausted -- presumed Div).
  3. unfold / inline : syntactic call elimination producing plain L
     expressions (Theorem Unfolding / Theorem Inlining of the report),
     evaluated with a call-free evaluator.

The pass [A/B] is subst(A, B, C) from
research/scratch/paper_variants/verify_variants.py (there called subst; the
task brief calls it sub). No other built-ins: cat / tail / head / eq / if are
inlined as raw expression trees exactly per the paper's Section 2 formulas.

Expressions (tuples):
  ('var', i)        the variable X_{i+1}
  ('con', w)        constant string w
  ('sub', R, P, E)  [R/P]E   (P evaluated; if eps -> undefined)
  ('cat', A, B)     AB
  ('cal', j, es)    call f_j(es...) -- j indexes the program's definition list
A program is a list of (name, arity, body).
"""

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(_HERE, '..', '..', 'paper_variants'))
from verify_variants import subst as _raw_subst  # noqa: E402  ([A/B]C)

# Guard against value-length explosion in randomized programs (a body like
# cat(cat(X,X),cat(X,X)) squares its string each Kleene level).  Purely a
# testing device: raises so the caller can skip that program.
MAXLEN = 4000


class SizeEx(Exception):
    pass


def subst(A, B, C):
    """[A/B]C, paper Definition def:subst, with a testing length guard."""
    if len(A) > MAXLEN or len(B) > MAXLEN or len(C) > MAXLEN:
        raise SizeEx()
    return _raw_subst(A, B, C)


def _catguard(a, b):
    if len(a) + len(b) > MAXLEN:
        raise SizeEx()
    return a + b


# --------------------------------------------------------------- expressions

def vars_of(E):
    """Set of variable indices occurring in E."""
    t = E[0]
    if t == 'var':
        return {E[1]}
    if t == 'con':
        return set()
    if t == 'cat':
        return vars_of(E[1]) | vars_of(E[2])
    if t == 'sub':
        return vars_of(E[1]) | vars_of(E[2]) | vars_of(E[3])
    if t == 'cal':
        s = set()
        for e in E[2]:
            s |= vars_of(e)
        return s
    raise ValueError(t)


def subst_expr(E, Fs):
    """E[F_1/X_1, ..., F_m/X_m]: replace ('var', i-1) by Fs[i-1]."""
    t = E[0]
    if t == 'var':
        return Fs[E[1]]
    if t == 'con':
        return E
    if t == 'cat':
        return ('cat', subst_expr(E[1], Fs), subst_expr(E[2], Fs))
    if t == 'sub':
        return ('sub', subst_expr(E[1], Fs), subst_expr(E[2], Fs),
                subst_expr(E[3], Fs))
    if t == 'cal':
        return ('cal', E[1], [subst_expr(e, Fs) for e in E[2]])
    raise ValueError(t)


def calls_in(E):
    """List of callee indices of call nodes in E (syntactic)."""
    t = E[0]
    if t in ('var', 'con'):
        return []
    if t == 'cat':
        return calls_in(E[1]) + calls_in(E[2])
    if t == 'sub':
        return calls_in(E[1]) + calls_in(E[2]) + calls_in(E[3])
    if t == 'cal':
        return [E[1]] + sum((calls_in(e) for e in E[2]), [])
    raise ValueError(t)


# ------------------------------------------------------------------ programs

class Prog:
    """A program: list of definitions (name, arity, body)."""

    def __init__(self, defs):
        self.defs = list(defs)          # [(name, arity, body)]
        self.names = [d[0] for d in defs]
        self.ar = [d[1] for d in defs]
        self.body = [d[2] for d in defs]
        self.k = len(defs)
        # --- call graph: edge j -> l iff body_j contains a call node f_l
        self.edges = [sorted(set(calls_in(b))) for b in self.body]
        # --- nodes on a cycle, and C = nodes that can REACH a cycle
        self.on_cycle = set()
        for j in range(self.k):
            seen, stack = {j}, [j]
            while stack:                       # can j reach j (nonempty path)?
                u = stack.pop()
                for v in self.edges[u]:
                    if v == j:
                        self.on_cycle.add(j)
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
        self.C = set()
        for j in range(self.k):
            if j in self.on_cycle:
                self.C.add(j)
                continue
            seen, stack = {j}, [j]             # can j reach an on-cycle node?
            hit = False
            while stack and not hit:
                u = stack.pop()
                for v in self.edges[u]:
                    if v in self.on_cycle:
                        hit = True
                        break
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
            if hit:
                self.C.add(j)
        # --- DAG depth below non-C nodes (longest call-edge path from j)
        self.depth = {}
        for j in range(self.k):
            if j in self.C:
                self.depth[j] = None            # infinity
        def dep(j):
            """depth(j) = number of edges on the longest call path from j."""
            if j in self.depth:
                return self.depth[j]
            self.depth[j] = 0                   # guard (graph is a DAG here)
            d = max([dep(l) + 1 for l in self.edges[j]], default=0)
            self.depth[j] = d
            return d
        for j in range(self.k):
            if j not in self.C:
                dep(j)
        # topological order of the non-C region
        self.topo = sorted((j for j in range(self.k) if j not in self.C),
                           key=lambda j: self.depth[j])

    def kleene_bound(self):
        """Theorem (Quantitative stabilization): phi^n = lfp for
        n >= max(1, max_{j not in C} depth(j)+1); on C, phi^n = bottom for
        all n. So the chain stabilizes by this index (global bound <= k+1)."""
        m = max([self.depth[j] + 1 for j in range(self.k)
                 if j not in self.C], default=0)
        return max(1, m)


# --------------------------------------------- 1. Kleene approximants (phi)

def phi_eval(P, j, inp, n, memo):
    """phi^n_j(inp): the n-th Kleene approximant, = ⟦B_j⟧_{phi^{n-1}}(inp).

    Evaluates the body with every call node interpreted by phi^{n-1} (the
    callee's body), the call's ARGUMENTS still being evaluated at level n.
    Returns a string or None (undefined)."""
    if n == 0:
        return None
    key = (j, inp, n)
    if key in memo:
        return memo[key]
    memo[key] = None                            # (recursion descends in n)
    v = phi_ev(P, P.body[j], inp, n - 1, memo)  # phi^n = ⟦B_j⟧_{phi^{n-1}}
    memo[key] = v
    return v


def phi_ev(P, E, T, n, memo):
    """⟦E⟧_{phi^n}(T) -- strict, all constructors, calls at phi^n."""
    t = E[0]
    if t == 'var':
        return T[E[1]]
    if t == 'con':
        return E[1]
    if t == 'cat':
        a = phi_ev(P, E[1], T, n, memo)
        b = phi_ev(P, E[2], T, n, memo)
        return None if (a is None or b is None) else _catguard(a, b)
    if t == 'sub':
        r = phi_ev(P, E[1], T, n, memo)
        p = phi_ev(P, E[2], T, n, memo)
        e = phi_ev(P, E[3], T, n, memo)
        if r is None or p is None or e is None or p == '':
            return None
        return subst(r, p, e)
    if t == 'cal':
        j, es = E[1], E[2]
        vs = tuple(phi_ev(P, e, T, n, memo) for e in es)
        if any(v is None for v in vs):
            return None
        return phi_eval(P, j, vs, n, memo)
    raise ValueError(t)


def phi_all(P, inputs, nmax):
    """phi^n_j on all (j, input) for n=0..nmax; returns dict (j,inp)->[vals]."""
    memo = {}
    table = {(j, inp): [None] * (nmax + 1)
             for j in range(P.k) for inp in inputs[j]}
    for n in range(nmax + 1):
        for j in range(P.k):
            for inp in inputs[j]:
                table[(j, inp)][n] = phi_eval(P, j, inp, n, memo)
    return table


def kleene_stabilization(table, P, inputs):
    """Least n such that phi^n = phi^{n+1} pointwise on the test domain."""
    nmax = max(len(v) - 1 for v in table.values())
    for n in range(nmax):
        if all(table[(j, inp)][n] == table[(j, inp)][n + 1]
               for j in range(P.k) for inp in inputs[j]):
            return n
    return None


# ------------------------------------- 2. unbounded operational evaluation

class ErrEx(Exception):
    """Empty-pattern abort: [A/eps]."""


class FuelEx(Exception):
    """Fuel exhausted before completion (presumed divergence)."""


def run(P, j, inp, fuel, count=None):
    """Eager left-to-right evaluation with depth-fuel `fuel`.

    Returns ('halt', v) | ('err',) | ('cut',).  Entering a callee body costs
    one fuel unit; arguments of a call are evaluated at the current fuel.
    Evaluation order inside ('sub',R,P,E) is R, then P, then E, then the
    empty-pattern check."""
    try:
        v = op_ev(P, P.body[j], inp, fuel, count)
        return ('halt', v)
    except ErrEx:
        return ('err',)
    except FuelEx:
        return ('cut',)


def op_ev(P, E, T, fuel, count=None):
    t = E[0]
    if t == 'var':
        return T[E[1]]
    if t == 'con':
        return E[1]
    if t == 'cat':
        a = op_ev(P, E[1], T, fuel, count)
        b = op_ev(P, E[2], T, fuel, count)
        return _catguard(a, b)
    if t == 'sub':
        r = op_ev(P, E[1], T, fuel, count)
        p = op_ev(P, E[2], T, fuel, count)
        e = op_ev(P, E[3], T, fuel, count)
        if p == '':
            raise ErrEx()
        return subst(r, p, e)
    if t == 'cal':
        j, es = E[1], E[2]
        vs = tuple(op_ev(P, e, T, fuel, count) for e in es)
        if fuel == 0:
            raise FuelEx()
        if count is not None:
            count[0] += 1
        return op_ev(P, P.body[j], vs, fuel - 1, count)
    raise ValueError(t)


# ------------------------------- 3. syntactic unfolding / inlining (to L)

def omega(arity):
    """The everywhere-undefined L expression [a/eps]<anything>, any arity."""
    return ('sub', ('con', 'a'), ('con', ''), ('con', 'c'))


def _uses_var(E, i):
    return i in vars_of(E)


SIGMA = 'a'          # any character of Sigma


def seq_expr(F, G):
    """seq(F, G) = [F.sigma / F.sigma] G  (one sub node, any alphabet).

    Forces F (twice: as R and as P, both strict positions), then returns G:
    by the paper's Identity Substitution theorem, [A/A]S = S whenever
    A <> eps, and A = F.sigma is never empty (it ends in the character
    sigma).  If F is undefined, the R position is undefined and so is the
    whole node.  This is the strict-sequence combinator of L."""
    R = ('cat', F, C(SIGMA))
    P = ('cat', F, C(SIGMA))
    return ('sub', R, P, G)


def force_unused(U, Fs):
    """Eager (call-by-value) call elimination for one call node.

    Plain substitution U[F_1/X_1, ..., F_q/X_q] (Lemma beta) evaluates F_i
    only when X_i OCCURS in U -- a call-by-name behavior.  The eager call
    node is strict in ALL its arguments, so every F_i whose variable is
    unused by U must still be forced: wrap with seq(F_i, .).  U is assumed
    call-free; when U is Omega the call is bottom regardless of the
    arguments and Omega is returned unchanged."""
    t = U[0]
    if t == 'sub' and U[2] == ('con', ''):      # U is Omega
        return U
    E = subst_expr(U, Fs)
    for i, F in enumerate(Fs):
        if not _uses_var(U, i):
            E = seq_expr(F, E)
    return E


def unfold_def(P, j, n):
    """unfold_n(f_j) in Exp_{m_j} (call-free), with unfold_0(f_j) = Omega:
       unfold_{n+1}(f_j) = Unfold_{n+1}(B_j), where a call node
       f_l(E_1..E_q) is replaced by force_unused(unfold_n(f_l),
       [Unfold_{n+1}(E_1), ..., Unfold_{n+1}(E_q)]) -- the plain
       substitution unfolded one level, with the dead arguments forced."""
    if n == 0:
        return omega(P.ar[j])
    return unfold_ev(P, P.body[j], n)


def unfold_ev(P, E, n):
    t = E[0]
    if t in ('var', 'con'):
        return E
    if t == 'cat':
        return ('cat', unfold_ev(P, E[1], n), unfold_ev(P, E[2], n))
    if t == 'sub':
        return ('sub', unfold_ev(P, E[1], n), unfold_ev(P, E[2], n),
                unfold_ev(P, E[3], n))
    if t == 'cal':
        j, es = E[1], E[2]
        return force_unused(unfold_def(P, j, n - 1),
                             [unfold_ev(P, e, n) for e in es])
    raise ValueError(t)


def inline_prog(P):
    """The complete inlining E^infty_j for every j:
       j in C      -> Omega (the everywhere-undefined L expression);
       j not in C  -> the topological inlining of the DAG below j."""
    done = {}
    for j in range(P.k):
        done[j] = omega(P.ar[j]) if j in P.C else None
    for j in P.topo:                       # increasing depth order
        done[j] = inline_ev(P, P.body[j], done)
    return [done[j] for j in range(P.k)]


def inline_ev(P, E, done):
    t = E[0]
    if t in ('var', 'con'):
        return E
    if t == 'cat':
        return ('cat', inline_ev(P, E[1], done), inline_ev(P, E[2], done))
    if t == 'sub':
        return ('sub', inline_ev(P, E[1], done), inline_ev(P, E[2], done),
                inline_ev(P, E[3], done))
    if t == 'cal':
        j, es = E[1], E[2]
        return force_unused(done[j], [inline_ev(P, e, done) for e in es])
    raise ValueError(t)


def evL(E, T):
    """Call-free L evaluator (Definition def:den)."""
    t = E[0]
    if t == 'var':
        return T[E[1]]
    if t == 'con':
        return E[1]
    if t == 'cat':
        a = evL(E[1], T)
        b = evL(E[2], T)
        return None if (a is None or b is None) else _catguard(a, b)
    if t == 'sub':
        assert not calls_in(E), "evL on call-free expression"
        r = evL(E[1], T)
        p = evL(E[2], T)
        e = evL(E[3], T)
        if r is None or p is None or e is None or p == '':
            return None
        return subst(r, p, e)
    raise ValueError(t)


# ------------------------------------------------ Section 2 toolkit (raw L)
# Sigma = {a, b}, b = 'b' (sigma_1), x = 'a' (sigma_2), top = 'a', bot = 'b'.

X = lambda i: ('var', i)                    # noqa: E731
C = lambda w: ('con', w)                    # noqa: E731


def enc(E):
    """enc_{b,x}(S) = [xb/b]S  (Theorem thm:enc)."""
    return ('sub', C('ab'), C('b'), E)


def dec(E):
    """dec_{b,x}(T) = [b/xb]T."""
    return ('sub', C('b'), C('ab'), E)


def cat(A, B):
    """cat(X,Y) = dec([enc(X)/xb^2][enc(Y)/xb^3](xb^2 xb^3))  (thm:cat)."""
    t = ('sub', enc(B), C('abbb'), C('abbabbb'))   # [enc(Y)/xb^3] first
    t = ('sub', enc(A), C('abb'), t)               # then [enc(X)/xb^2]
    return dec(t)                                  # then dec


def tailE(E):
    """tail(X) = dec([eps/bb][eps/bba][eps/bbab](bb enc(X)))  (thm:headtail,
    N = 2 so the product over i = 3..N is empty; rightmost pass first)."""
    t = ('cat', C('bb'), enc(E))
    t = ('sub', C(''), C('bbab'), t)
    t = ('sub', C(''), C('bba'), t)
    t = ('sub', C(''), C('bb'), t)
    return dec(t)


def headE(E):
    """head(X) = dec([eps/enc(tail(X)) bb](enc(X) bb))  (thm:headtail)."""
    pat = ('cat', enc(tailE(E)), C('bb'))
    scr = ('cat', enc(E), C('bb'))
    return dec(('sub', C(''), pat, scr))


def benc(E):
    """benc(X) = xb^2 enc(X) xb^2."""
    return ('cat', ('cat', C('abb'), enc(E)), C('abb'))


def eqE(A, B):
    """eq(X,Y) = [bot/benc(X)][top/benc(Y)](benc(X)), top='a', bot='b'."""
    t = ('sub', C('a'), benc(B), benc(A))    # [top/benc(Y)] first
    return ('sub', C('b'), benc(A), t)       # then [bot/benc(X)]


def ifE(Cond, A, B):
    """if(C,X,Y) = dec([enc(Y)/bb]([enc(X)/top][bb/bot]C))  (Selection)."""
    t = ('sub', C('bb'), C('b'), Cond)       # [bb/bot]C first
    t = ('sub', enc(A), C('a'), t)            # then [enc(X)/top]
    t = ('sub', enc(B), C('bb'), t)           # then [enc(Y)/bb]
    return dec(t)

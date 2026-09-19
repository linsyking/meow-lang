# lrec.py -- L_rec: finite sets of named first-order recursive definitions over
# raw L (the substitution calculus of the paper, Definitions def:exp / def:den),
# with three evaluators and the analysis machinery for the LAZY-ARGUMENTS
# (call-by-need) semantics:
#
#   * liveness fixpoint  S* = mu F   (which (function, parameter) pairs are live)
#   * live dependency graph          (decides termination: acyclic <=> halts)
#   * live unfolding  U(M)            (the plain-L expression denotationally equal
#                                     to a well-founded program)
#   * lazy machine  (explicit thunks + memoization, completely strict constructors)
#   * eager machine (call-by-value: all arguments evaluated before the call)
#   * plain-L evaluator for unfolded expressions (uses the paper's primitive)
#
# Alphabet Sigma = {a, b} throughout (b = sigma_1, x = sigma_2 for the toolkit).
#
# The substitution primitive is the one of
# research/scratch/paper_variants/verify_variants.py (subst), i.e. paper
# Definition def:subst: greedy leftmost-first, non-overlapping, never
# restarting inside inserted text; [A/eps] undefined.

import sys

# ---------------------------------------------------------------- primitive


class PatEps(Exception):
    """[A/epsilon] is undefined (paper: def:subst)."""


def sub(A, B, C):
    """[A/B]C -- paper Definition def:subst."""
    if not B:
        raise PatEps("[A/eps] undefined")
    out, i, n, m = [], 0, len(C), len(B)
    while i < n:
        if C[i:i + m] == B:
            out.append(A)
            i += m
        else:
            out.append(C[i])
            i += 1
    return ''.join(out)


# ---------------------------------------------------------------- AST (tuples)
#
# ('var', i)            parameter / input variable
# ('const', s)          string constant
# ('pass', R, P, E)     [R/P]E      (R = replacement, P = pattern, E = scrutinee)
# ('cat', E1, E2)       E1 E2
# ('call', g, args)     g(E1,...,Em), args a tuple of expressions


def V(i):
    return ('var', i)


def K(s):
    return ('const', s)


def Pas(R, P, E):
    return ('pass', R, P, E)


def Cat(a, b):
    return ('cat', a, b)


def Call(g, *args):
    return ('call', g, tuple(args))


def size(E):
    t = E[0]
    if t in ('var', 'const'):
        return 1
    if t == 'cat':
        return 1 + size(E[1]) + size(E[2])
    if t == 'pass':
        return 1 + size(E[1]) + size(E[2]) + size(E[3])
    if t == 'call':
        return 1 + sum(size(a) for a in E[2])
    raise ValueError(E)


def show(E, names=None):
    """Human-readable one-line rendering (X,Y,Z for vars)."""
    names = names or {}
    t = E[0]
    if t == 'var':
        return names.get(E[1], "XYZ"[E[1]] if E[1] < 3 else f"X{E[1]}")
    if t == 'const':
        return repr(E[1]) if E[1] != '' else "''"
    if t == 'cat':
        return f"({show(E[1], names)} {show(E[2], names)})"
    if t == 'pass':
        return f"[{show(E[1], names)}/{show(E[2], names)}]{show(E[3], names)}"
    if t == 'call':
        return f"{E[1]}({', '.join(show(a, names) for a in E[2])})"
    raise ValueError(E)


class Program:
    """funcs: name -> (arity, body).  main: expression over input vars
    0..ninputs-1.  '@main' is used as owner name for main in the analyses."""

    def __init__(self, funcs, main, ninputs):
        self.funcs = dict(funcs)
        self.main = main
        self.ninputs = ninputs

    def size(self):
        return sum(size(b) for (_, b) in self.funcs.values()) + size(self.main)

    def show(self):
        lines = []
        for g, (ar, b) in self.funcs.items():
            names = {i: "ABCDU"[i] if i < 5 else f"A{i}" for i in range(ar)}
            lines.append(f"  {g}({', '.join(names[i] for i in range(ar))}) = {show(b, names)}")
        mn = {i: "XYZ"[i] if i < 3 else f"X{i}" for i in range(self.ninputs)}
        lines.append(f"  main = {show(self.main, mn)}")
        return "\n".join(lines)


# ---------------------------------------------------------------- liveness
#
# Given S (a set of (function, index) pairs), a position inside the body of
# some function is S-EVALUATED if it is reachable from the root by:
#   - descending into any child of a pass node or cat node at an evaluated
#     position (constructors are strict in *all* children, exactly as in
#     def:den), or
#   - descending into argument i of a call g(...) at an evaluated position,
#     but only when (g, i) in S.
#
# F(S) = { (g,i) : parameter i occurs at an S-evaluated position of g's body }.
# Liveness S* = mu F (least fixpoint; Kleene iteration from the empty set).


def live_param_occurrences(body, S, fname):
    """Indices of fname's parameters occurring at S-evaluated positions."""
    out = set()

    def walk(E, ev):
        t = E[0]
        if t == 'var':
            if ev:
                out.add(E[1])
        elif t == 'cat':
            walk(E[1], ev)
            walk(E[2], ev)
        elif t == 'pass':
            walk(E[1], ev)
            walk(E[2], ev)
            walk(E[3], ev)
        elif t == 'call':
            g, args = E[1], E[2]
            for i, a in enumerate(args):
                walk(a, ev and ((g, i) in S))

    walk(body, True)
    return out


def liveness(prog):
    """S* = least fixpoint of F."""
    S = set()
    while True:
        S2 = set()
        for g, (ar, body) in prog.funcs.items():
            for i in live_param_occurrences(body, S, g):
                S2.add((g, i))
        if S2 == S:
            return S
        S = S2


def all_pairs(prog):
    return {(g, i) for g, (ar, b) in prog.funcs.items() for i in range(ar)}


# ------------------------------------------------------- live dependency graph
#
# Nodes: call sites (owner, path) with owner a function name or '@main' and
# path the tree address of the call node inside owner's body, restricted to
# S-evaluated call nodes (only those ever run).
# Edges from a call node c calling g:
#   (a) to every S-evaluated call node in the body of g;
#   (b) to every S-evaluated call node inside a *live* argument of c
#       (nodes of c's owner whose path extends c's path by the argument index).
# Roots: the S-evaluated call nodes of main.
# The live unfolding is finite  <=>  no cycle is reachable from the roots.


def live_calls(E, S):
    """[(path, callexpr)] for every S-evaluated call node in E (root evaluated)."""
    res = []

    def walk(E, ev, path):
        t = E[0]
        if t == 'cat':
            walk(E[1], ev, path + (0,))
            walk(E[2], ev, path + (1,))
        elif t == 'pass':
            walk(E[1], ev, path + (0,))
            walk(E[2], ev, path + (1,))
            walk(E[3], ev, path + (2,))
        elif t == 'call':
            if ev:
                res.append((path, E))
            g, args = E[1], E[2]
            for i, a in enumerate(args):
                walk(a, ev and ((g, i) in S), path + (i,))

    walk(E, True, ())
    return res


def _owner_live_calls(prog, S):
    d = {}
    for g, (ar, body) in prog.funcs.items():
        d[g] = live_calls(body, S)
    d['@main'] = live_calls(prog.main, S)
    return d


def successors(prog, olc, S, node):
    """Edges from call node `node` = (owner, path) with expr `ce`."""
    owner, path = node
    ce = _expr_at(prog, owner, path)
    g = ce[1]
    succ = set()
    # (a) evaluated calls in the callee's body
    for p2, _ in olc[g]:
        succ.add((g, p2))
    # (b) evaluated calls inside the live arguments of c
    for i in range(len(ce[2])):
        if (g, i) in S:
            prefix = path + (i,)
            for p2, _ in olc[owner]:
                if p2[:len(prefix)] == prefix:
                    succ.add((owner, p2))
    return succ


def _expr_at(prog, owner, path):
    body = prog.main if owner == '@main' else prog.funcs[owner][1]
    E = body
    for i in path:
        t = E[0]
        if t == 'cat':
            E = E[1 + i]
        elif t == 'pass':
            E = E[1 + i]
        elif t == 'call':
            E = E[2][i]
        else:
            raise ValueError("bad path")
    return E


def dep_graph_acyclic_from_main(prog, S):
    """True iff no cycle is reachable from main's S-evaluated call nodes."""
    olc = _owner_live_calls(prog, S)
    color = {}  # 0 = in progress, 1 = done

    def dfs(u):
        color[u] = 0
        for v in successors(prog, olc, S, u):
            c = color.get(v)
            if c == 0:
                return False
            if c is None and not dfs(v):
                return False
        color[u] = 1
        return True

    for p, _ in olc['@main']:
        u = ('@main', p)
        if color.get(u) is None:
            if not dfs(u):
                return False
    return True


def terminates_lazy(prog):
    """Lazy-args machine halts (on every input) iff this is True."""
    S = liveness(prog)
    return dep_graph_acyclic_from_main(prog, S)


def terminates_eager(prog):
    """Eager machine halts iff the FULL dependency graph (S = all pairs) is
    acyclic from main."""
    return dep_graph_acyclic_from_main(prog, all_pairs(prog))


# ---------------------------------------------------------------- unfolding


class CapExceeded(Exception):
    pass


def unfold(prog, S, cap=100000):
    """The live unfolding U(main): expand every call at an evaluated position,
    substituting live arguments, skipping dead ones entirely.  Dead parameters
    are never looked up (asserted -- this is the 'dead parameters occur only
    at dead positions' lemma checked at runtime).  Returns (tree, node_count).
    Raises CapExceeded if the materialized unfolding passes `cap` nodes."""
    counter = [0]

    def go(E, env, owner):
        counter[0] += 1
        if counter[0] > cap:
            raise CapExceeded()
        t = E[0]
        if t == 'var':
            i = E[1]
            if owner != '@main':
                assert (owner, i) in S, \
                    f"dead parameter {i} of {owner} looked up in unfolding"
            return env[i]
        if t == 'const':
            return E
        if t == 'cat':
            return ('cat', go(E[1], env, owner), go(E[2], env, owner))
        if t == 'pass':
            return ('pass', go(E[1], env, owner), go(E[2], env, owner),
                    go(E[3], env, owner))
        if t == 'call':
            g, args = E[1], E[2]
            newenv = {}
            for i, a in enumerate(args):
                if (g, i) in S:
                    newenv[i] = go(a, env, owner)  # live arg: unfold in caller ctx
                # dead arg: skipped entirely
            return go(prog.funcs[g][1], newenv, g)

    tree = go(prog.main, {i: ('var', i) for i in range(prog.ninputs)}, '@main')
    return tree, counter[0]


# ---------------------------------------------------------------- machines


class Timeout(Exception):
    pass


class BlackHole(Exception):
    pass


class Thunk:
    __slots__ = ('expr', 'env', 'g', 'i', 'state', 'val')

    def __init__(self, expr, env, g, i):
        self.expr, self.env, self.g, self.i = expr, env, g, i
        self.state = 'susp'  # susp | busy | val | err
        self.val = None


class Machine:
    """Big-step call-by-need (lazy-args) and call-by-value (eager) machines.

    Constructors are COMPLETELY STRICT exactly as def:den: a pass node
    evaluates all three of R, P, E (errors do not cut siblings off; only
    divergence dominates), a cat node evaluates both concatenands.  Only CALL
    ARGUMENTS are thunked in the lazy machine.  Outcomes: ('val', s) or
    ('err',) (an epsilon pattern somewhere below); Timeout ~ divergence."""

    def __init__(self, prog, budget=500000):
        self.prog = prog
        self.budget = budget
        self.steps = 0
        self.forced = set()        # (g, i) actually forced
        self.started = set()       # g whose body evaluation started

    def tick(self):
        self.steps += 1
        if self.steps > self.budget:
            raise Timeout()

    # ---- lazy ----

    def run_lazy(self, inputs):
        env = {i: ('inp', s) for i, s in enumerate(inputs)}
        return self.ev(self.prog.main, env)

    def ev(self, E, env):
        self.tick()
        t = E[0]
        if t == 'const':
            return ('val', E[1])
        if t == 'var':
            b = env[E[1]]
            if isinstance(b, tuple):  # ('inp', s)
                return ('val', b[1])
            return self.force(b)
        if t == 'cat':
            r1 = self.ev(E[1], env)
            r2 = self.ev(E[2], env)
            if r1[0] == 'err' or r2[0] == 'err':
                return ('err',)
            return ('val', r1[1] + r2[1])
        if t == 'pass':
            rR = self.ev(E[1], env)   # all three evaluated, always
            rP = self.ev(E[2], env)
            rE = self.ev(E[3], env)
            if rR[0] == 'err' or rP[0] == 'err' or rE[0] == 'err':
                return ('err',)
            if rP[1] == '':
                return ('err',)
            return ('val', sub(rR[1], rP[1], rE[1]))
        if t == 'call':
            g, args = E[1], E[2]
            thunks = [Thunk(a, env, g, i) for i, a in enumerate(args)]
            self.started.add(g)
            nenv = {i: th for i, th in enumerate(thunks)}
            return self.ev(self.prog.funcs[g][1], nenv)
        raise ValueError(E)

    def force(self, th):
        if th.state == 'val':
            return ('val', th.val)
        if th.state == 'err':
            return ('err',)
        if th.state == 'busy':
            raise BlackHole()
        th.state = 'busy'
        self.forced.add((th.g, th.i))
        r = self.ev(th.expr, th.env)
        th.state = r[0]
        th.val = r[1] if r[0] == 'val' else None
        return r

    # ---- eager ----

    def run_eager(self, inputs):
        env = {i: ('inp', s) for i, s in enumerate(inputs)}
        return self.ee(self.prog.main, env)

    def ee(self, E, env):
        self.tick()
        t = E[0]
        if t == 'const':
            return ('val', E[1])
        if t == 'var':
            b = env[E[1]]
            if isinstance(b, tuple):  # ('inp', s)
                return ('val', b[1])
            raise ValueError("thunk in eager environment")
        if t == 'cat':
            r1 = self.ee(E[1], env)
            r2 = self.ee(E[2], env)
            if r1[0] == 'err' or r2[0] == 'err':
                return ('err',)
            return ('val', r1[1] + r2[1])
        if t == 'pass':
            rR = self.ee(E[1], env)
            rP = self.ee(E[2], env)
            rE = self.ee(E[3], env)
            if rR[0] == 'err' or rP[0] == 'err' or rE[0] == 'err':
                return ('err',)
            if rP[1] == '':
                return ('err',)
            return ('val', sub(rR[1], rP[1], rE[1]))
        if t == 'call':
            g, args = E[1], E[2]
            rs = [self.ee(a, env) for a in args]  # all arguments, always
            if any(r[0] == 'err' for r in rs):
                return ('err',)
            self.started.add(g)
            for i, r in enumerate(rs):
                self.forced.add((g, i))
            nenv = {i: ('inp', r[1]) for i, r in enumerate(rs)}
            return self.ee(self.prog.funcs[g][1], nenv)
        raise ValueError(E)


# ---------------------------------------------------------------- plain L


def eval_plain(E, env, _memo=None):
    """Strict plain-L evaluation (def:den) of a call-free expression.
    env: var index -> string.  Returns ('val', s) or ('err',).
    Memoized by node identity: sound because evaluation is pure."""
    if _memo is None:
        _memo = {}
    key = id(E)
    if key in _memo:
        return _memo[key]
    t = E[0]
    if t == 'const':
        r = ('val', E[1])
    elif t == 'var':
        r = ('val', env[E[1]])
    elif t == 'cat':
        r1 = eval_plain(E[1], env, _memo)
        r2 = eval_plain(E[2], env, _memo)
        r = ('err',) if (r1[0] == 'err' or r2[0] == 'err') else ('val', r1[1] + r2[1])
    elif t == 'pass':
        rR = eval_plain(E[1], env, _memo)
        rP = eval_plain(E[2], env, _memo)
        rE = eval_plain(E[3], env, _memo)
        if rR[0] == 'err' or rP[0] == 'err' or rE[0] == 'err' or rP[1] == '':
            r = ('err',)
        else:
            r = ('val', sub(rR[1], rP[1], rE[1]))
    else:
        raise ValueError("call node in plain expression: %r" % (E,))
    _memo[key] = r
    return r


def denotation_of_program(prog, inputs, cap=100000):
    """The unfolding denotation: U finite -> eval_plain(U, inputs);
    U infinite -> None (diverges).  Also returns the unfolding."""
    S = liveness(prog)
    if not dep_graph_acyclic_from_main(prog, S):
        return None, None
    U, n = unfold(prog, S, cap)
    return eval_plain(U, {i: s for i, s in enumerate(inputs)}), U


# ---------------------------------------------------------------- toolkit
#
# Section 2 constructions over Sigma = {a, b} with b = sigma_1 = 'a' (the
# escaped character) and x = sigma_2 = 'b' (the escape character), as in the
# paper's Theorems thm:enc, thm:cat, thm:headtail, eq, if.

TOP, BOT = 'b', 'a'   # sigma_2, sigma_1:  TOP != b is required and holds


def ENC(E):
    return Pas(K('ba'), K('a'), E)


def DEC(E):
    return Pas(K('a'), K('ba'), E)


def TAIL(E):
    inner = Cat(K('aa'), ENC(E))
    p = Pas(K(''), K('aaba'), inner)   # [eps/s1 s1 s2 s1] runs first
    p = Pas(K(''), K('aab'), p)
    p = Pas(K(''), K('aa'), p)
    return DEC(p)


def HEAD(E):
    t = TAIL(E)
    pat = Cat(ENC(t), K('aa'))
    return DEC(Pas(K(''), pat, Cat(ENC(E), K('aa'))))


def BENC(E):
    return Cat(K('baa'), Cat(ENC(E), K('baa')))


def EQE(X, Y):
    return Pas(K(BOT), BENC(X), Pas(K(TOP), BENC(Y), BENC(X)))


def IFE(C, X, Y):
    return DEC(Pas(ENC(Y), K('aa'),
                   Pas(ENC(X), K(TOP),
                       Pas(K('aa'), K(BOT), C))))

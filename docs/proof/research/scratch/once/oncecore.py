"""Hinge 1 workspace: is ONCE (the once-calculus) L-reachable?

Sharpest probe (paper main.tex:983): is "delete the leftmost b" -- the
single once-node [eps/b]_1 -- expressible in the plain calculus L?

This module: primitives, evaluator, target functions, and search machinery.

  * subst(A,B,C)   the paper's Def. def:subst, OWN loop implementation
                   (independent of rec/lazy_pass/core.py and systems.py;
                   cross-checked in verify_r1.py against both and against
                   Python str.replace, which implements exactly the greedy
                   leftmost / non-overlapping / no-rescan semantics for
                   constant patterns).
  * once(A,B,C)    [A/B]_1 C -- Def. def:once (leftmost occurrence only).
  * evalL(e, X)    eager evaluator for unary call-free L-expressions
                   (AST: ('K',w) ('V',i) ('C',e1,e2) ('S',R,P,E)); raises
                   PatternEmpty on an empty pattern value.  Cross-checked
                   against rec/lazy_pass/core.ev_eager (defs={}).
  * targets        del1b (THE probe), rep1b, delallb (control).
  * BFS machinery  behavior signatures = tuple of images of a fixed test
                   set; dedup BFS over constant-pattern passes; distance
                   statistics vs. a target; pipeline reconstruction.

Composition convention: a PIPELINE [passes in run order] applies
passes[0] first.  Paper order is right-to-left.
"""
import itertools

# --------------------------------------------------------------- primitives


def subst(A, B, C):
    """[A/B]C -- paper Definition def:subst (own independent implementation).
    [A/eps] undefined -> raises ValueError."""
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


def once(A, B, C):
    """[A/B]_1 C -- paper Definition def:once: replace the LEFTMOST
    occurrence of B by A; identity if B does not occur."""
    if not B:
        raise ValueError("[A/eps]_1 undefined")
    i = C.find(B)
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]


# ------------------------------------------------------- target functions


def del1b(C):
    """delete the leftmost b (identity if none) -- THE probe."""
    i = C.find('b')
    return C if i < 0 else C[:i] + C[i + 1:]


def rep1b(C):
    """replace the leftmost b by a (identity if none)."""
    i = C.find('b')
    return C if i < 0 else C[:i] + 'a' + C[i + 1:]


def delallb(C):
    return C.replace('b', '')


TARGETS = {'del1b': del1b, 'rep1b': rep1b, 'delallb': delallb}


# ----------------------------------------------------- L-expression evaluator


class PatternEmpty(Exception):
    pass


def evalL(e, X):
    """Eager denotation (paper Def. def:den) of a UNARY call-free
    expression.  e is ('K',w) | ('V',0) | ('C',e1,e2) | ('S',R,P,E)."""
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return X
    if t == 'C':
        return evalL(e[1], X) + evalL(e[2], X)
    if t == 'S':
        T = evalL(e[3], X)
        B = evalL(e[2], X)
        if B == '':
            raise PatternEmpty()
        A = evalL(e[1], X)
        return subst(A, B, T)
    raise ValueError(t)


# ------------------------------------------------------------- test domains


def binstrings(maxlen):
    """all strings over {a,b} of length <= maxlen, in a canonical order."""
    out = []
    for n in range(maxlen + 1):
        out.extend(''.join(t) for t in itertools.product('ab', repeat=n))
    return out


def ternstrings(maxlen):
    out = []
    for n in range(maxlen + 1):
        out.extend(''.join(t) for t in itertools.product('abc', repeat=n))
    return out


# ------------------------------------------------------------- pass spaces


def const_passes(alpha, pat_len, rep_len):
    """All constant passes (P,R) with 1 <= |P| <= pat_len,
    0 <= |R| <= rep_len over alphabet alpha (paper's search space)."""
    pats = [''.join(t) for k in range(1, pat_len + 1)
            for t in itertools.product(alpha, repeat=k)]
    repls = [''] + [''.join(t) for k in range(1, rep_len + 1)
                    for t in itertools.product(alpha, repeat=k)]
    return [(P, R) for P in pats for R in repls]


def apply_const(passes, C):
    """Apply a constant-pattern pipeline (run order) to C."""
    for (P, R) in passes:
        C = C.replace(P, R)
    return C


def apply_var(passes, C):
    """Apply a VARIABLE-pattern pipeline (run order) to C.
    Each pass is (Rname, Pname) resolved by VOCAB: pattern/replacement are
    functions of the ORIGINAL input C (calculus semantics: patterns see
    only the input variables)."""
    for (rn, pn) in passes:
        P = VOCAB[pn](C)
        R = VOCAB[rn](C)
        if P == '':
            raise PatternEmpty()
        C = subst(R, P, C)
    return C


# ------------------------------------------- vocabulary for variable searches
# Each entry: name -> fn(C) = value of that sub-expression on input C.
# Every fn here is L-COMPUTABLE; most are cross-checked against real
# L-ASTs in verify_r1.py (the toolkit builders of rec/lazy_pass/toolkit.py).

def _halve(C):
    """H = [b/a][eps/b][a/bb] on run order [a/bb] then [eps/b] then [b/a]
    (paper prop:unary-once): halves b-runs, deletes odd residues."""
    return C.replace('bb', 'a').replace('b', '').replace('a', 'b')


def _unary_len_b(C):
    """b^|C| = [b/Sigma]C  (single-character substitution lemma)."""
    return 'b' * len(C)


def _enc(C):
    """enc_{b,x} with b='a', x='b': [xb/b] = escape every a by ba."""
    return C.replace('a', 'ba')


def _dec(C):
    return C.replace('ba', 'a')


VOCAB = {
    'eps':   (lambda C: ''),
    'a':     (lambda C: 'a'),
    'b':     (lambda C: 'b'),
    'X':     (lambda C: C),
    'Xa':    (lambda C: C + 'a'),
    'Xb':    (lambda C: C + 'b'),
    'aX':    (lambda C: 'a' + C),
    'bX':    (lambda C: 'b' + C),
    'XX':    (lambda C: C + C),
    'H':     _halve,
    'Hb':    (lambda C: _halve(C) + 'b'),
    'aH':    (lambda C: 'a' + _halve(C)),
    'len':   _unary_len_b,
    'lenb':  (lambda C: 'b' * len(C) + 'b'),
    'enc':   _enc,
    'dec':   _dec,
    'tail':  (lambda C: C[1:]),
    'init':  (lambda C: C[:-1]),
    'head':  (lambda C: C[:1]),
    'last':  (lambda C: C[-1:]),
    'aXa':   (lambda C: 'a' + C + 'a'),
    'bXb':   (lambda C: 'b' + C + 'b'),
    'XaX':   (lambda C: C + 'a' + C),
    'XbX':   (lambda C: C + 'b' + C),
    'aXb':   (lambda C: 'a' + C + 'b'),
    'bXa':   (lambda C: 'b' + C + 'a'),
}

# the run-order pass space for variable searches: all (rname, pname)
VAR_PASSES = [(r, p) for r in VOCAB for p in VOCAB]


# --------------------------------------------------------------- BFS search


class BehaviorBFS:
    """Dedup BFS over behaviors on a fixed test set.

    passes: list of pass descriptors (opaque; applied by `apply_passes`).
    apply(signature, pass) -> new signature.
    """

    def __init__(self, testset, passes, apply_fn, targets=None):
        self.test = list(testset)
        self.sig0 = tuple(self.test)
        self.passes = passes
        self.apply_fn = apply_fn
        self.targets = dict(targets or {})
        self.seen = {self.sig0: None}     # sig -> (prev sig, pass)
        self.level = [self.sig0]
        self.found = {}
        self.dists = {}                   # level -> sorted dist list

    def _check_targets(self, depth):
        for name, tsig in self.targets.items():
            if tsig in self.seen and name not in self.found:
                node, pl = tsig, []
                while self.seen[node] is not None:
                    prev, last = self.seen[node]
                    pl.append(last)
                    node = prev
                self.found[name] = (depth, list(reversed(pl)))

    def run_level(self):
        """One more pass of depth.  Returns (n_new, n_frontier)."""
        newf = []
        for sig in self.level:
            for p in self.passes:
                ns = self.apply_fn(sig, p)
                if ns not in self.seen:
                    self.seen[ns] = (sig, p)
                    newf.append(ns)
        self.level = newf
        return len(newf)

    def target_sigs(self):
        return {name: tuple(f(s) for s in self.test)
                for name, f in self.targets.items()}

    def pipeline_of(self, sig):
        node, pl = sig, []
        while self.seen[node] is not None:
            prev, last = self.seen[node]
            pl.append(last)
            node = prev
        return list(reversed(pl))

    def dist_stats(self, tsig, k=10):
        """distance distribution of ALL seen behaviors to tsig; the k
        closest with their pipelines."""
        best = []
        import heapq
        h = []                            # max-heap of (-dist, sig)
        for sig in self.seen:
            d = sum(1 for a, b in zip(sig, tsig) if a != b)
            if len(h) < k:
                heapq.heappush(h, (-d, sig))
            elif -h[0][0] > d:
                heapq.heapreplace(h, (-d, sig))
        best = sorted((-nd, sig) for (nd, sig) in h)
        return best


def apply_const_sig(sig, p):
    P, R = p
    return tuple(s.replace(P, R) for s in sig)


def apply_var_sig(sig, p):
    """sig = tuple of ORIGINAL test strings paired positionally with the
    ORIGINAL inputs -- variable passes need the original input to compute
    patterns.  We carry (orig, cur) tuples instead."""
    raise NotImplementedError("use VarBFS")


class VarBFS:
    """BFS over variable-pattern pipelines.  A state is the tuple of current
    texts, one per test input; applying a pass recomputes pattern/replacement
    from the ORIGINAL input (index-aligned)."""

    def __init__(self, testset, passes):
        self.test = list(testset)
        self.sig0 = tuple(self.test)
        self.passes = passes
        self.seen = {self.sig0: None}
        self.level = [self.sig0]
        self.found = {}

    def apply(self, sig, p):
        rn, pn = p
        out = []
        for orig, cur in zip(self.test, sig):
            P = VOCAB[pn](orig)
            R = VOCAB[rn](orig)
            if P == '':
                return None               # undefined on this input
            out.append(subst(R, P, cur))
        return tuple(out)

    def run_level(self):
        newf = []
        for sig in self.level:
            for p in self.passes:
                ns = self.apply(sig, p)
                if ns is not None and ns not in self.seen:
                    self.seen[ns] = (sig, p)
                    newf.append(ns)
        self.level = newf
        return len(newf)

    def pipeline_of(self, sig):
        node, pl = sig, []
        while self.seen[node] is not None:
            prev, last = self.seen[node]
            pl.append(last)
            node = prev
        return list(reversed(pl))

"""Core: the LAZY-PASS abstract machine for recursive definitions over raw L.

Semantics implemented here (REPORT.md, Section 1-2):

  * expressions (extends the paper's Def. def:exp with one node):
        ('K', w)            constant string w
        ('V', i)            i-th parameter (0-based)
        ('C', e1, e2)       concatenation  e1 e2
        ('S', R, P, E)      the paper's node [R/P]E  (P pattern, R replacement,
                            E scrutinee), now with LAZY REPLACEMENT:
                            E and P are forced strictly; R is forced only if
                            the value of P occurs in the value of E.
        ('F', name, args)    call to a named definition, CALL-BY-NEED:
                            arguments become shared, memoized thunks.

  * a program is a dict  name -> (arity, body); a call node must name a
    definition of matching arity (checked by `check_program`).

  * the machine is the deterministic small-step machine of REPORT.md Sec. 1.2:
    explicit stack of frames + heap of thunk cells.  Halting states:
    Value(w) / Err('pattern-empty') ([A/eps]) / Div-by-blackhole /
    timeout (step cap: presumed divergence).

The eager reference semantics (for the conservative-extension theorem and the
eager-vs-lazy comparisons) is `ev_eager`: same grammar, strict in R, and
call-by-value in arguments.  On call-free expressions it is exactly the
paper's Definition def:den.

`subst` is the paper's Definition def:subst (greedy leftmost, non-overlapping,
never rescanning inserted text), copied from verify_variants.py.
"""

# --------------------------------------------------------------------------
# the primitive

def subst(A, B, C):
    """[A/B]C -- paper Definition 1 (greedy leftmost, non-overlapping, never
    restarting inside inserted text). [A/eps] undefined -> raises."""
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


# --------------------------------------------------------------------------
# AST

def K(w):  return ('K', w)
def V(i):  return ('V', i)
def C(e1, e2): return ('C', e1, e2)
def S(R, P, E): return ('S', R, P, E)          # [R/P]E
def F(name, *args): return ('F', name, tuple(args))


def subst_expr(R, P, E):
    """[R/P]E as an AST (alias of S, kept for readability)."""
    return ('S', R, P, E)


def check_program(defs):
    for name, (ar, body) in defs.items():
        _check(body, defs, name, set())


def _check(e, defs, ctx, bound):
    t = e[0]
    if t == 'K' or t == 'V':
        return
    if t == 'C':
        _check(e[1], defs, ctx, bound); _check(e[2], defs, ctx, bound); return
    if t == 'S':
        for x in (e[1], e[2], e[3]):
            _check(x, defs, ctx, bound)
        return
    if t == 'F':
        name = e[1]
        if name not in defs:
            raise ValueError(f"call to undefined {name} in {ctx}")
        ar = defs[name][0]
        if len(e[2]) != ar:
            raise ValueError(f"arity mismatch calling {name} in {ctx}")
        for x in e[2]:
            _check(x, defs, ctx, bound)
        return
    raise ValueError(f"bad node {e}")


def size(e):
    t = e[0]
    if t in ('K', 'V'): return 1
    if t == 'C': return 1 + size(e[1]) + size(e[2])
    if t == 'S': return 1 + size(e[1]) + size(e[2]) + size(e[3])
    if t == 'F': return 1 + sum(size(x) for x in e[2])
    raise ValueError(t)


# --------------------------------------------------------------------------
# pretty printer (paper notation)

def pp(e, prec=0):
    t = e[0]
    if t == 'K':
        w = e[1]
        return f'"{w}"' if w != '' else '"eps"'
    if t == 'V':
        return f'X{e[1]+1}'
    if t == 'C':
        s = f'{pp(e[1], 1)}·{pp(e[2], 1)}'
        return f'({s})' if prec > 1 else s
    if t == 'S':
        s = f'[{pp(e[1], 0)}/{pp(e[2], 0)}]{pp(e[3], 2)}'
        return s
    if t == 'F':
        return f'{e[1]}({", ".join(pp(x, 0) for x in e[2])})'
    raise ValueError(t)


# --------------------------------------------------------------------------
# THE LAZY-PASS MACHINE  (small-step, explicit stack + heap)

# frames:
#   ('catL', e2, env)      waiting for left operand of a concatenation
#   ('catR', w)            waiting for right operand (left value w)
#   ('subE', R, P, env)    waiting for scrutinee of [R/P]_
#   ('subP', T, R, env)    waiting for pattern (scrutinee value T)
#   ('subR', T, B)         waiting for replacement (T scrutinee, B pattern,
#                          B != eps and B in T -- replacement WILL be forced)
#   ('upd', loc)           thunk update
#
# control: ('eval', expr, env)  |  ('val', w)
# heap cells: ('val', w) | ('thunk', expr, env) | ('blackhole',)

HALT_VAL, HALT_ERR, HALT_BLACK, HALT_TIMEOUT = 'val', 'err', 'blackhole', 'timeout'


def run_lazy(defs, fname, args, cap=2_000_000, collect=None):
    """Run definition `fname` on the tuple of strings `args`.

    Returns (HALT_VAL, w, steps) | (HALT_ERR, 'pattern-empty', steps)
           | (HALT_BLACK, None, steps) | (HALT_TIMEOUT, steps_run, steps).

    `collect`, if given, is called with (event, payload) at every activation
    and thunk force -- used by the verification scripts to count demands.
    """
    heap = {}
    def newcell(v):
        loc = len(heap)
        heap[loc] = v
        return loc

    env = tuple(newcell(('val', a)) for a in args)
    try:
        body = defs[fname][1]
    except KeyError:
        raise ValueError(f"unknown definition {fname}")

    control = ('eval', body, env)
    stack = []
    steps = 0

    while True:
        steps += 1
        if steps > cap:
            return (HALT_TIMEOUT, steps, steps)
        tag = control[0]
        if tag == 'eval':
            expr, cenv = control[1], control[2]
            t = expr[0]
            if t == 'K':
                control = ('val', expr[1])
            elif t == 'V':
                loc = cenv[expr[1]]
                cell = heap[loc]
                ct = cell[0]
                if ct == 'val':
                    control = ('val', cell[1])
                elif ct == 'thunk':
                    if collect is not None:
                        collect('force', loc)
                    stack.append(('upd', loc))
                    heap[loc] = ('blackhole',)
                    control = ('eval', cell[1], cell[2])
                else:                       # blackhole: genuine cycle
                    return (HALT_BLACK, None, steps)
            elif t == 'C':
                stack.append(('catL', expr[2], cenv))
                control = ('eval', expr[1], cenv)
            elif t == 'S':
                # [R/P]E : scrutinee first, then pattern, then (only if the
                # pattern occurs) the replacement.
                stack.append(('subE', expr[1], expr[2], cenv))
                control = ('eval', expr[3], cenv)
            elif t == 'F':
                name = expr[1]
                ar, bodyj = defs[name]
                if len(expr[2]) != ar:
                    raise ValueError(f"arity mismatch calling {name}")
                env2 = tuple(newcell(('thunk', a, cenv)) for a in expr[2])
                if collect is not None:
                    collect('call', name)
                control = ('eval', bodyj, env2)
            else:
                raise ValueError(f"bad node {t}")
        else:
            # ('val', w)
            w = control[1]
            if not stack:
                return (HALT_VAL, w, steps)
            fr = stack.pop()
            ft = fr[0]
            if ft == 'catL':
                stack.append(('catR', w))
                control = ('eval', fr[1], fr[2])
            elif ft == 'catR':
                control = ('val', fr[1] + w)
            elif ft == 'subE':
                # scrutinee value w arrived; evaluate the pattern next
                stack.append(('subP', w, fr[1], fr[3]))
                control = ('eval', fr[2], fr[3])
            elif ft == 'subP':
                T, R, renv = fr[1], fr[2], fr[3]
                B = w
                if B == '':
                    return (HALT_ERR, 'pattern-empty', steps)
                if B not in T:
                    control = ('val', T)         # PASS IS INERT: R never forced
                else:
                    stack.append(('subR', T, B))
                    control = ('eval', R, renv)
            elif ft == 'subR':
                control = ('val', subst(w, fr[2], fr[1]))
            elif ft == 'upd':
                heap[fr[1]] = ('val', w)
                # control stays ('val', w)
            else:
                raise ValueError(f"bad frame {ft}")


# --------------------------------------------------------------------------
# EAGER reference semantics (strict replacement, call-by-value arguments).
# On call-free expressions this is exactly Definition def:den of the paper.

class Undefined(Exception):
    """[A/eps] under eager semantics."""

class Diverge(Exception):
    """depth/step cap exceeded -- presumed divergence."""

def ev_eager(defs, e, env, depth=0, maxdepth=4000, maxsteps=[0], stepcap=10**7):
    if depth > maxdepth:
        raise Diverge()
    maxsteps[0] += 1
    if maxsteps[0] > stepcap:
        raise Diverge()
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return env[e[1]]
    if t == 'C':
        return (ev_eager(defs, e[1], env, depth, maxdepth, maxsteps, stepcap)
                + ev_eager(defs, e[2], env, depth, maxdepth, maxsteps, stepcap))
    if t == 'S':
        T = ev_eager(defs, e[3], env, depth, maxdepth, maxsteps, stepcap)
        B = ev_eager(defs, e[2], env, depth, maxdepth, maxsteps, stepcap)
        A = ev_eager(defs, e[1], env, depth, maxdepth, maxsteps, stepcap)
        if B == '':
            raise Undefined()
        return subst(A, B, T)
    if t == 'F':
        name = e[1]
        ar, body = defs[name]
        if len(e[2]) != ar:
            raise ValueError(f"arity mismatch calling {name}")
        vals = tuple(ev_eager(defs, x, env, depth, maxdepth, maxsteps, stepcap)
                     for x in e[2])
        return ev_eager(defs, body, vals, depth + 1, maxdepth, maxsteps, stepcap)
    raise ValueError(t)


def run_eager(defs, fname, args, maxdepth=4000, stepcap=10**7):
    """Returns ('val', w) | ('undef',) | ('diverge',)."""
    try:
        w = ev_eager(defs, defs[fname][1], tuple(args), 0, maxdepth, [0], stepcap)
        return ('val', w)
    except Undefined:
        return ('undef',)
    except Diverge:
        return ('diverge',)


# --------------------------------------------------------------------------
# BIG-STEP demand semantics (the proof-friendly equivalent of the machine;
# REPORT.md Sec. 1.4).  Mirrors rules (K)(V)(C)(S-inert)(S-fire)(F) with an
# explicit heap; reading a blackhole or an empty pattern is stuck.

class PatternEmpty(Exception):
    """stuck: [A/eps] in big-step semantics."""

class Blackhole(Exception):
    """stuck: a thunk was demanded whose evaluation is in progress."""

def ev_bigstep(defs, e, env, heap, depth=0, maxdepth=100000):
    """env: tuple of heap locations; heap: dict.  Returns (w, heap).
    Raises PatternEmpty / Blackhole / Diverge (depth cap)."""
    if depth > maxdepth:
        raise Diverge()
    t = e[0]
    if t == 'K':
        return e[1], heap
    if t == 'V':
        loc = env[e[1]]
        cell = heap[loc]
        if cell[0] == 'val':
            return cell[1], heap
        if cell[0] == 'blackhole':
            raise Blackhole()
        # thunk: mark, evaluate, memoize
        heap[loc] = ('blackhole',)
        w, heap = ev_bigstep(defs, cell[1], cell[2], heap, depth + 1, maxdepth)
        heap[loc] = ('val', w)
        return w, heap
    if t == 'C':
        w1, heap = ev_bigstep(defs, e[1], env, heap, depth + 1, maxdepth)
        w2, heap = ev_bigstep(defs, e[2], env, heap, depth + 1, maxdepth)
        return w1 + w2, heap
    if t == 'S':
        T, heap = ev_bigstep(defs, e[3], env, heap, depth + 1, maxdepth)
        B, heap = ev_bigstep(defs, e[2], env, heap, depth + 1, maxdepth)
        if B == '':
            raise PatternEmpty()
        if B not in T:
            return T, heap                       # R untouched
        A, heap = ev_bigstep(defs, e[1], env, heap, depth + 1, maxdepth)
        return subst(A, B, T), heap
    if t == 'F':
        name = e[1]
        ar, body = defs[name]
        if len(e[2]) != ar:
            raise ValueError(f"arity mismatch calling {name}")
        env2 = tuple(len(heap) + i for i in range(ar))
        for i, a in enumerate(e[2]):
            heap[env2[i]] = ('thunk', a, env)
        w, heap = ev_bigstep(defs, body, env2, heap, depth + 1, maxdepth)
        return w, heap
    raise ValueError(t)


def run_bigstep(defs, fname, args, maxdepth=100000):
    """Returns ('val', w) | ('err','pattern-empty') | ('err','blackhole')
    | ('diverge',).  Should agree with run_lazy on every program."""
    heap = {}
    env = tuple(len(heap) + i for i in range(len(args)))
    for i, a in enumerate(args):
        heap[env[i]] = ('val', a)
    try:
        w, _ = ev_bigstep(defs, defs[fname][1], env, heap, 0, maxdepth)
        return ('val', w)
    except PatternEmpty:
        return ('err', 'pattern-empty')
    except Blackhole:
        return ('err', 'blackhole')
    except Diverge:
        return ('diverge',)

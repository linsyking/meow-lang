#!/usr/bin/env python3
"""Three reference evaluators for comparison against the stream machine.

1. sub(A,B,C): the paper's Definition 1 primitive (greedy leftmost,
   non-overlapping, never rescanning inserted text) -- copied from the
   paper's research/scratch/paper_variants/verify_variants.py.

2. feval: a finite-string "lazy-pass" evaluator following the sibling
   design principle: strict in the scrutinee E and in the pattern P, but
   the replacement R is forced only if P occurs in the value of E.
   Recursion: Kleene iteration of the induced functional on the flat
   domain, over a finite input set (exact least fixpoint there), plus a
   depth-bounded variant.

3. keval: the denotational evaluator over the lazy-list domain
   D = {w:bot} + {w:!} + Sigma^omega  (partial / finite-total / infinite),
   ordered by prefix on partials, totals maximal.  keval(body, xval, j)
   computes the j-th Kleene iterate D_j of the functional
   Phi(g)(s) = [[body]][g/f, s/X];  the least fixpoint is the sup over j.
   Values: (chars, end) with end in {'bot','!'}; 'omega' never needs
   materializing (infinite inputs are fed as deep-enough truncations,
   which only lowers information).
"""

import streams
from streams import (Var, Const, Cat, Pass, Call, V, C, cat, F,
                     UndefinedPattern)

# ------------------------------------------------------- the paper's sub()


def sub(A, B, S):
    """[A/B]S -- paper Definition 1. [A/eps] raises (undefined)."""
    if not B:
        raise UndefinedPattern('[A/eps] undefined')
    out, i, n, m = [], 0, len(S), len(B)
    while i < n:
        if S[i:i + m] == B:
            out.append(A)
            i += m
        else:
            out.append(S[i])
            i += 1
    return ''.join(out)


# ------------------------------------------------- flat lazy-pass evaluator

UNDEF = 'UNDEF'


def feval(e, sigma, callh, depth=10 ** 6):
    """Finite-string lazy-pass evaluation.  callh(argstr) resolves f(arg).

    Returns a string, UNDEF, or None (divergence).  Strict in E and P;
    R is forced only if P occurs in the value of E."""
    if isinstance(e, Var):
        return sigma
    if isinstance(e, Const):
        return e.w
    if isinstance(e, Cat):
        a = feval(e.a, sigma, callh, depth)
        if a is None or a is UNDEF:
            return a
        b = feval(e.b, sigma, callh, depth)
        if b is None or b is UNDEF:
            return b
        return a + b
    if isinstance(e, Pass):
        p = feval(e.P, sigma, callh, depth)
        if p is None or p is UNDEF:
            return p
        if p == '':
            return UNDEF
        s = feval(e.E, sigma, callh, depth)
        if s is None or s is UNDEF:
            return s
        if p not in s:
            return s                        # gate never opens: R unforced
        r = feval(e.R, sigma, callh, depth)  # gate opens: force R
        if r is None or r is UNDEF:
            return r
        return sub(r, p, s)
    if isinstance(e, Call):
        a = feval(e.arg, sigma, callh, depth)
        if a is None or a is UNDEF:
            return a
        return callh(a)
    raise TypeError('bad expression %r' % (e,))


def flat_fixpoint(body, inputs, maxiter=200):
    """Kleene iteration of the flat functional over a finite input set.

    Returns g: sigma -> value (string / UNDEF / None)."""
    g = {s: None for s in inputs}
    for _ in range(maxiter):
        g2 = {}
        for s in inputs:
            g2[s] = feval(body, s, lambda a, g=g: g.get(a, None))
        if g2 == g:
            return g
        g = g2
    return g     # did not stabilize within maxiter (values are then an
                 # under-approximation; caller should be wary)


# ------------------------------------------- Kleene evaluator on lazy lists
# Value: (chars, end), end in {'bot','!'}.

BOT = 'bot'
FIN = '!'
OMG = 'omg'   # truncation of an infinite stream (open beyond the cut)


TRUNC = [False]      # set when a value was truncated at the cap
CAP = [10 ** 9]


def _capv(v):
    chars, end = v
    if len(chars) > CAP[0]:
        TRUNC[0] = True
        return (chars[:CAP[0]], BOT)
    return v


def keval(e, xval, prog_body, j):
    """D_j(body-ish): evaluate e with X := xval ((chars,end)) and f resolved
    with j unfoldings (Call at ambient index j unfolds the body at j-1,
    its argument evaluated at j).  Values longer than CAP[0] are truncated
    (a lower bound with end BOT, TRUNC flagged)."""
    if isinstance(e, Var):
        return xval
    if isinstance(e, Const):
        return (e.w, FIN)
    if isinstance(e, Cat):
        a, aend = keval(e.a, xval, prog_body, j)
        if len(a) > CAP[0]:
            return _capv((a, BOT))
        if aend == FIN:
            b, bend = keval(e.b, xval, prog_body, j)
            return _capv((a + b, bend))
        return (a, aend)      # partial or omega-truncated left blocks right
    if isinstance(e, Pass):
        p = keval(e.P, xval, prog_body, j)
        if p[1] == FIN and len(p[0]) > CAP[0]:
            return _capv(('', BOT))
        s = keval(e.E, xval, prog_body, j)
        if len(s[0]) > CAP[0]:
            s = _capv((s[0], BOT))

        def rval():
            return keval(e.R, xval, prog_body, j)
        return _capv(kpass(p, s, rval))
    if isinstance(e, Call):
        if j == 0:
            return ('', BOT)
        arg = keval(e.arg, xval, prog_body, j)
        return keval(prog_body, arg, prog_body, j - 1)
    raise TypeError('bad expression %r' % (e,))


def kpass(pval, sval, rthunk):
    """The pass on lazy-list values (denotationally: the causal process).

    pval: (p, pend) -- pattern value; sval: (s, send) -- scrutinee value.
    rthunk(): replacement value (forced per completed match)."""
    p, pend = pval
    s, send = sval
    if pend == FIN and p == '':
        raise UndefinedPattern('[R/eps] undefined')
    out = []
    buf = ''
    si = 0
    while True:
        if len(buf) + sum(len(x) for x in out) > CAP[0] + 8:
            TRUNC[0] = True
            return (''.join(out)[:CAP[0]], BOT)
        if si < len(s):
            c = s[si]
            si += 1
        elif send == FIN:
            return (''.join(out) + buf, FIN)
        else:
            return (''.join(out), send)
        b2 = buf + c
        # pattern char at index len(buf)
        k = len(buf)
        if k < len(p):
            pk = p[k]
        elif pend == FIN:
            pk = None            # pattern exhausted exactly at k
        else:
            return (''.join(out), BOT)      # pattern stuck: stall
        if pk == c:
            buf = b2
            # probe: pattern exhausted at len(buf) means a full match
            if pend == FIN and len(buf) == len(p):
                r, rend = rthunk()
                out.append(r)
                if rend == BOT:
                    return (''.join(out), BOT)
                buf = ''
        else:
            # longest suffix of b2 that is a proper prefix of the pattern;
            # candidates have length <= |buf| <= |pattern|-1, so only the
            # already-known pattern prefix is ever consulted.
            keep = 0
            for L in range(len(b2) - 1, 0, -1):
                if b2[len(b2) - L:] == p[:L]:
                    keep = L
                    break
            out.append(b2[:len(b2) - keep])
            buf = b2[len(b2) - keep:]


def mu_eval(body, xval, J=200, cap=None, window=3):
    """Sup of the Kleene chain D_j(body, xval), j = 0..J.

    Returns ('stab', (chars, end)) if the chain stabilizes (the least
    fixpoint is the finite value chars with end BOT or FIN), else
    ('growing', (chars, end)) with the last iterate (the fixpoint has at
    least len(chars) characters; compare only that many).  With `cap`,
    iterates are truncated at that length (a lower bound), and a
    stabilization under truncation is reported as growing.

    CAVEAT: the chain is evaluated at ONE input, so it can plateau
    (D_j = D_{j+1}) while deeper arguments still grow and a later
    iterate increases again.  Stabilization is therefore only reported
    after `window` consecutive equal iterates; a genuine stabilization
    of the whole functional shows up as one eventually (all zoo cases
    stabilize with window <= 3, and 'growing' is always sound)."""
    if cap is not None:
        CAP[0] = cap
    prev = ('', BOT)
    trunc_any = False
    same = 0
    for j in range(J + 1):
        TRUNC[0] = False
        v = keval(body, xval, body, j)
        trunc_any = trunc_any or TRUNC[0]
        a, _ = prev
        b, _ = v
        if not a == b[:len(a)]:
            raise AssertionError('Kleene chain not increasing at j=%d: %r %r'
                                 % (j, prev, v))
        if j > 0 and v == prev:
            same += 1
            if same >= window:
                if v[1] == OMG:
                    # stabilized at an omega-truncation: open beyond cut
                    return ('growing', v)
                if not TRUNC[0] and not trunc_any:
                    return ('stab', v)
                # stabilized only because of truncation: long fixpoint
                return ('growing', v)
        else:
            same = 0
        prev = v
    return ('growing', prev)

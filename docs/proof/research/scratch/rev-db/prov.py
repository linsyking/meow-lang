"""Provenance-tracking evaluator for L (def:den).

A value is a tuple of ATOMS (char, label) with label in N (an input position)
or None (a constant character).  The semantics is EXACTLY def:den — labels
ride along and never affect matching — so the label sequence of the final
value records WHICH INPUT POSITION (or constant) each output character came
from: the PROVENANCE.

Definitions on a value's label sequence prov (w-labels only, in order):
  mult(prov) = max multiplicity of a label (>=1; 1 iff the value is a
               subsequence-without-repetition of w + constants),
  LDS(prov)  = longest strictly decreasing subsequence,
  LIS(prov)  = longest strictly increasing subsequence.

CONJECTURES UNDER TEST (see REPORT.md):
  A: LDS <= C(E) * mult              for all w,
  B: LDS <= C(E)                     on all w with mult = 1
                                                (rev: LDS = n, mult = 1).
"""
from lcore import K, V, C, S


class Undefined(Exception):
    pass


def lab_input(w):
    """the input string as a labeled value: position labels"""
    return tuple((c, i) for i, c in enumerate(w))


def lab_const(W):
    return tuple((c, None) for c in W)


def lsubst(A, B, T):
    """[A/B]T on labeled values; A, B labeled, B nonempty."""
    m = len(B)
    bchars = tuple(c for c, _ in B)
    out = []
    i, n = 0, len(T)
    while i < n:
        if tuple(c for c, _ in T[i:i + m]) == bchars:
            out.extend(A)
            i += m
        else:
            out.append(T[i])
            i += 1
    return tuple(out)


def lden(e, args):
    """def:den with provenance.  args = tuple of labeled values."""
    t = e[0]
    if t == 'K':
        return lab_const(e[1])
    if t == 'V':
        return args[e[1]]
    if t == 'C':
        return lden(e[1], args) + lden(e[2], args)
    if t == 'S':
        R, P, E = e[1], e[2], e[3]
        T = lden(E, args)
        B = lden(P, args)
        if not B:
            raise Undefined()
        A = lden(R, args)
        return lsubst(A, B, T)
    raise ValueError(t)


def labels(val):
    """the label sequence (w-labels only)"""
    return tuple(l for _, l in val if l is not None)


def mult(prov):
    if not prov:
        return 1
    from collections import Counter
    return max(Counter(prov).values())


def _lis_strict(seq):
    """longest strictly increasing subsequence, O(n log n) patience."""
    import bisect
    tails = []
    for x in seq:
        i = bisect.bisect_left(tails, x)
        if i == len(tails):
            tails.append(x)
        else:
            tails[i] = x
    return len(tails)


def lds(seq):
    """longest strictly decreasing subsequence = LIS on negated seq."""
    return _lis_strict([-x for x in seq])


def lis(seq):
    return lds([-x for x in seq])


def content(val):
    return ''.join(c for c, _ in val)


def stats(e, w):
    """evaluate with provenance; returns dict or None if undefined."""
    try:
        val = lden(e, (lab_input(w),))
    except Undefined:
        return None
    prov = labels(val)
    return {'out': content(val), 'prov': prov, 'mult': mult(prov),
            'lds': lds(prov), 'lis': lis(prov)}

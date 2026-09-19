"""Core library for the RESTART variant study.

Semantics implemented:
  subst(A,B,C)   -- the paper's Definition 1 (baseline L): left-to-right,
                    leftmost-first, non-overlapping, never rescans inserted text.
  restart(A,B,C)  -- the restart variant [A/B]^m C: repeat { find the leftmost
                    occurrence of B in the CURRENT string; replace it by A;
                    restart the scan from position 0 } until B no longer occurs.

Both raise Undefined when B == epsilon (the paper's convention).
restart raises Diverge when the step cap is exceeded (divergence suspicion).
"""
import itertools


class Undefined(Exception):
    pass


class Diverge(Exception):
    pass


def subst(A, B, C):
    """Paper Definition 1 (baseline)."""
    if B == "":
        raise Undefined("[A/eps] is undefined")
    out = []
    i = 0
    n = len(C)
    lb = len(B)
    while i < n:
        if C.startswith(B, i):
            out.append(A)
            i += lb
        else:
            out.append(C[i])
            i += 1
    return "".join(out)


def restart(A, B, C, cap=200000):
    """Restart semantics. Returns (result, steps). Raises Diverge on cap."""
    if B == "":
        raise Undefined("[A/eps]^m is undefined")
    s = C
    steps = 0
    while True:
        i = s.find(B)
        if i < 0:
            return s, steps
        s = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap:
            raise Diverge("cap exceeded, len=%d" % len(s))


def restart_steps(A, B, C, cap=200000):
    return restart(A, B, C, cap)


def chars(s):
    return set(s)


def disjoint(A, B):
    """A and B share no character."""
    return len(chars(A) & chars(B)) == 0


def all_strings(sigma, maxlen):
    """All strings over sigma, by increasing length."""
    for L in range(maxlen + 1):
        for t in itertools.product(sigma, repeat=L):
            yield "".join(t)


def all_patterns(sigma, minlen, maxlen):
    for L in range(minlen, maxlen + 1):
        for t in itertools.product(sigma, repeat=L):
            yield "".join(t)


def fmt_pair(A, B):
    return "[%s/%s]" % (A if A else "e", B)

"""Core library: baseline (safe) replace and unsafe rescan replace.

Baseline [A/B]C   : left-to-right, leftmost-first, non-overlapping,
                     scan resumes AFTER the inserted text (paper Def 1).
Rescan  [A/B]^u C  : same, but on a match the scan CONTINUES AT THE FIRST
                     CHARACTER OF THE INSERTED TEXT (re-enters inserted text).
                     Partial function - may diverge; we use a step cap.
"""

import sys
from functools import lru_cache

sys.setrecursionlimit(100000)


def subst_safe(A, B, C):
    """Paper Definition 1: [A/B]C, C.replace(B, A) with leftmost-first scan.

    B == epsilon is undefined behavior; we return None to signal it.
    """
    if B == "":
        return None
    return C.replace(B, A)


class Diverge(Exception):
    pass


def subst_unsafe(A, B, C, cap=10**6):
    """[A/B]^u C: unsafe rescan replace.

    Single left-to-right scan with a moving output position `out` (prefix
    already emitted, frozen). At scan position `i` in the *current* string
    s: if B matches at i, replace it by A in s and CONTINUE THE SCAN AT THE
    FIRST CHARACTER OF THE INSERTED A, i.e. at position i (the new text at
    position i is exactly A). Otherwise advance i by one.

    Implemented iteratively: s is a list; on match we splice A in place of
    B and keep i unchanged (i is now the first char of the inserted A).
    Matches may overlap the frozen prefix? No: positions < i are frozen
    (already scanned/replaced), so matches must start at >= i.

    cap: max number of match-steps; raises Diverge if exceeded.
    """
    if B == "":
        return None
    s = list(C)
    i = 0
    nB = len(B)
    steps = 0
    while True:
        n = len(s)
        # try to find a match of B starting at some position >= i
        j = _find_from(s, B, i, n)
        if j is None:
            return "".join(s)
        steps += 1
        if steps > cap:
            raise Diverge((A, B, C, "".join(s), i))
        # freeze everything before j (already final)
        s[j:j + nB] = list(A)
        i = j  # rescan from first char of inserted text
        if i > len(s):
            i = len(s)


def _find_from(s, B, i, n):
    """Leftmost occurrence of B in s starting at position >= i, or None."""
    nB = len(B)
    if nB == 0:
        return None
    b0 = B[0]
    p = i
    while p + nB <= n:
        if s[p] == b0 and "".join(s[p:p + nB]) == B:
            return p
        p += 1
    return None


def eq_unsafe(A, B, C, cap=10**6):
    """True/False/Diverge marker for [A/B]^u C (None for B=epsilon)."""
    try:
        return subst_unsafe(A, B, C, cap)
    except Diverge:
        return "DIVERGE"


def all_strings(sigma, maxlen):
    out = [""]
    cur = [""]
    for _ in range(maxlen):
        nxt = [c + s for c in sigma for s in cur]
        out.extend(nxt)
        cur = nxt
    return out


def compare(A, B, C, cap=10**5):
    """Return (safe, unsafe_or_diverge)."""
    return subst_safe(A, B, C), eq_unsafe(A, B, C, cap)

"""Primitives for the design-space study (research/scratch/systems/).

Each primitive is the paper's Definition def:subst with one design choice
changed (or one combination changed).  All are total on nonempty patterns
unless noted; all raise ValueError on an empty pattern where the paper's
calculus is undefined.

  subst(A,B,C)      baseline L: leftmost-first, all occurrences, never rescan
  once(A,B,C)       [A/B]_1 : leftmost occurrence only            (paper 5.1)
  onceR(A,B,C)      rightmost occurrence only                     (paper 5.1 rem)
  substR(A,B,C)     rightmost-first, all occurrences              (paper 5.3, R)
  rescan(A,B,C)     re-enters inserted text                       (paper 5.4, u)
  restart(A,B,C)    single-rule Markov to fixpoint                (paper 5.5, m)
  repOcc(k,B,A,C)   replace the k-th greedy occurrence (0-based)  (paper 5.2)
  anchored(A,B,C,side)  ANCHORED pass (NEW, this study):
       side='L'  [A/^B]:  if B is a PREFIX  of C, replace it by A; else C
       side='R'  [A/B$]:  if B is a SUFFIX  of C, replace it by A; else C
       the empty pattern is DEFINED here (the anchored occurrence of eps is
       unique): [A/^eps]C = A C, [A/eps$]C = C A.  Rationale in REPORT Sec. 2.
  rankm(k,A,B,C)    RANK-k MARKOV (NEW, this study = 5.2 x 5.5):
       iterate repOcc(k,B,A,.) until B-free (leftmost-greedy ranks).
  multi_native(pairs,S)  NATIVE one-sweep multi-pattern (NEW, this study):
       one left-to-right sweep; at each position try pairs in priority
       order; on the first match emit its replacement and skip the match;
       inserted text is never rescanned (single sweep, like one pass).
  rep_ref(pairs,S)  the paper's freezing semantics (Def. def:rep), for
       contrast with multi_native.
"""

import sys
sys.setrecursionlimit(100000)


# ----------------------------------------------------------------- baseline


def subst(A, B, C):
    """[A/B]C -- greedy leftmost, non-overlapping, never restarting inside
    inserted text (paper Definition def:subst)."""
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


# ----------------------------------------------------------------- once family


def occ(C, B):
    """Greedy leftmost-first, non-overlapping occurrence start positions of B
    in C (exactly the scan of subst stopped at each hit) -- paper 5.2 occ."""
    if not B:
        raise ValueError("occ(.,eps) undefined")
    O, i, n, m = [], 0, len(C), len(B)
    while i <= n - m:
        if C[i:i + m] == B:
            O.append(i)
            i += m
        else:
            i += 1
    return O


def once(A, B, C):
    """[A/B]_1 C -- replace the leftmost occurrence of B by A (paper 5.1)."""
    if not B:
        raise ValueError("[A/eps]_1 undefined")
    i = C.find(B)
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]


def onceR(A, B, C):
    """[A/B]_1^R C -- replace the rightmost occurrence of B by A."""
    if not B:
        raise ValueError
    i = C.rfind(B)
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]


def repOcc(k, B, A, C):
    """repOcc(k,B,A,S) (paper 5.2, 0-based rank over greedy occ list):
    replace the k-th occurrence by A if it exists, else S."""
    if not B:
        raise ValueError("repOcc(.,eps,.,.) undefined")
    O = occ(C, B)
    if k >= len(O):
        return C
    i = O[k]
    return C[:i] + A + C[i + len(B):]


# ----------------------------------------------------------------- direction


def rfind(B, C):
    for s in range(len(C) - len(B), -1, -1):
        if C.startswith(B, s):
            return s
    return None


def substR(A, B, C):
    """[A/B]^R C -- rightmost-first, all occurrences, resume left of inserted
    text (paper 5.3)."""
    if not B:
        raise ValueError
    s = rfind(B, C)
    if s is None:
        return C
    return substR(A, B, C[:s]) + A + C[s + len(B):]


# ----------------------------------------------------------------- re-entry


def rescan(A, B, C, cap=100000):
    """[A/B]^u C (paper 5.4): freeze prefix, resume AT the first character of
    the inserted text.  None = diverged (cap exceeded)."""
    if not B:
        raise ValueError
    O, T, steps = [], C, 0
    while B in T:
        steps += 1
        if steps > cap:
            return None
        q = T.find(B)
        O.append(T[:q])
        T = A + T[q + len(B):]
    return ''.join(O) + T


def restart(A, B, C, cap=100000):
    """[A/B]^m C (paper 5.5): single-rule Markov, leftmost, rescan from 0,
    until B-free.  None = diverged."""
    if not B:
        raise ValueError
    s, steps = C, 0
    while B in s:
        steps += 1
        if steps > cap:
            return None
        i = s.find(B)
        s = s[:i] + A + s[i + len(B):]
    return s


def rankm(k, A, B, C, cap=100000):
    """RANK-k MARKOV (NEW): iterate "replace the (k+1)-th greedy occurrence
    of B by A" while the pass FIRES, i.e. while >= k+1 greedy occurrences
    exist; the value is the first INERT state; None = never inert (diverged).
    Corrected in R3: the R1 reading "iterate until the string stops changing"
    was WRONG for A = B (a firing that changes nothing loops forever -- it
    never becomes inert; the paper's Markov agrees: A = B diverges).  For
    k=0 the inertness criterion is exactly B-freeness, so rankm(0) == restart
    (paper 5.5) VERBATIM, including the A = B divergence."""
    if not B:
        raise ValueError
    s, steps = C, 0
    while True:
        O = occ(s, B)
        if len(O) <= k:
            return s                    # inert: no (k+1)-th occurrence
        i = O[k]
        t = s[:i] + A + s[i + len(B):]
        steps += 1
        if steps > cap:
            return None
        s = t


# ----------------------------------------------------------------- anchored (NEW)


def anchored(A, B, C, side):
    """[A/^B]C (side='L'): if B is a prefix of C, replace it by A; else C.
    [A/B$]C (side='R'): same at the end.  B=eps is DEFINED (unique anchored
    occurrence): [A/^eps]C = A C, [A/eps$]C = C A."""
    if side == 'L':
        if C.startswith(B):
            return A + C[len(B):]
        return C
    if side == 'R':
        if C.endswith(B):
            return C[:len(C) - len(B)] + A
        return C
    raise ValueError("side must be 'L' or 'R'")


# ----------------------------------------------------------------- multi-pattern


def multi_native(pairs, S, require_nonempty=True):
    """NATIVE one-sweep multi-pattern (NEW): single left-to-right sweep; at
    each position try pairs [(P1,R1),...,(Pn,Rn)] in priority order; first
    match wins, emit its replacement, skip the whole match; inserted text is
    never rescanned.  Contrast with rep_ref (freezing rounds)."""
    out, i, n = [], 0, len(S)
    while i < n:
        hit = False
        for (P, R) in pairs:
            if require_nonempty and not P:
                raise ValueError("empty pattern in multi_native")
            if S[i:i + len(P)] == P:
                out.append(R)
                i += len(P)
                hit = True
                break
        if not hit:
            out.append(S[i])
            i += 1
    return ''.join(out)


def rep_ref(pairs, S):
    """The paper's freezing semantics (Definition def:rep), reference."""
    frozen = [0] * len(S)
    for i, (Xi, _) in enumerate(pairs, 1):
        if not Xi:
            continue
        m, j = len(Xi), 0
        while j + m <= len(S):
            if all(frozen[j + k] == 0 for k in range(m)) and S[j:j + m] == Xi:
                for k in range(m):
                    frozen[j + k] = i
                j += m
            else:
                j += 1
    out, j = [], 0
    while j < len(S):
        if frozen[j] == 0:
            out.append(S[j])
            j += 1
        else:
            i = frozen[j]
            out += pairs[i - 1][1]
            j += len(pairs[i - 1][0])
    return ''.join(out)


# ----------------------------------------------------------------- self-test


if __name__ == '__main__':
    # smoke tests, quick sanity only
    assert subst('ab', 'b', 'b') == 'ab'
    assert once('a', 'b', 'bbb') == 'abb'
    assert onceR('a', 'b', 'bbb') == 'bba'
    assert repOcc(1, 'b', 'a', 'bbb') == 'bab'
    assert repOcc(2, 'b', 'a', 'bbb') == 'bba'
    assert substR('ab', 'b', 'b') == 'ab'
    # paper thm:rescan-agree's separating instance: A='ba', B='ab', C='abb'
    assert rescan('ba', 'ab', 'abb') == 'bba'     # re-enters inserted text
    assert subst('ba', 'ab', 'abb') == 'bab'      # (baseline differs)
    assert restart('ba', 'ab', 'aabb') == 'bbaa'   # the sorter: b*a* normal form
    assert rankm(0, 'ba', 'ab', 'aabb') == 'bbaa'  # k=0 == restart
    assert anchored('X', 'ab', 'abc', 'L') == 'Xc'
    assert anchored('X', 'bc', 'abc', 'R') == 'aX'
    assert anchored('X', 'abc', 'ab', 'R') == 'ab'  # not a suffix
    # rank-2 markov smoke: on 'abab', occurrences of 'ab' at 0,2; replace 2nd
    assert rankm(1, 'X', 'ab', 'abab') == 'abX'
    # native multi-pattern vs freezing: the separating example from REPORT 3.4
    assert multi_native([('b', 'X'), ('ab', 'Y')], 'aab') == 'aY'
    assert rep_ref([('b', 'X'), ('ab', 'Y')], 'aab') == 'aaX'
    print("systems.py: all smoke tests pass")

"""Semantics for l2r (paper Definition 1) and r2l (its mirror), plus rev duality tests.

l2r (paper Def 1): scan C left-to-right, replace leftmost-first, non-overlapping,
resume after inserted text (never rescanned).
r2l (mirror): scan C from the RIGHT, replace rightmost-first, non-overlapping,
resume LEFT of inserted text (never rescanned).
Both undefined when B == ''.

Mirror of the paper's recursive Def 1:
  l2r : [A/B]C  = X  A [A/B]Y   where C = XBY, |X| minimal  (leftmost occurrence)
  r2l: [A/B]R C = ([A/B]R X) A Y  where C = XBY, |Y| minimal  (rightmost occurrence)
"""


def subst_l2r(A, B, C):
    """Paper Definition 1, iterative greedy scan."""
    if B == "":
        raise ValueError("[A/eps] undefined")
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


def _rightmost_occ(B, C):
    """Largest s with C[s:s+|B|] == B, or None."""
    lb = len(B)
    for s in range(len(C) - lb, -1, -1):
        if C.startswith(B, s):
            return s
    return None


def subst_r2l(A, B, C):
    """Mirror of Definition 1 (recursive, rightmost occurrence)."""
    if B == "":
        raise ValueError("[A/eps] undefined")
    s = _rightmost_occ(B, C)
    if s is None:
        return C
    return subst_r2l(A, B, C[:s]) + A + C[s + len(B):]


def rev(S):
    return S[::-1]


def subst_r2l_iter(A, B, C):
    """Linear greedy r2l scan: pointer sweeps right-to-left; a match is taken
    when B ends exactly at the pointer; after a replacement the pointer jumps
    to the start of the inserted text (never rescanned)."""
    if B == "":
        raise ValueError("[A/eps] undefined")
    out = []
    j = len(C)
    lb = len(B)
    while j > 0:
        if j - lb >= 0 and C[j - lb:j] == B:
            out.append(A)
            j -= lb
        else:
            out.append(C[j - 1])
            j -= 1
    return "".join(reversed(out))


def subst_r2l_via_rev(A, B, C):
    """Candidate duality: r2l = rev . l2r . rev with rev'd operands."""
    return rev(subst_l2r(rev(A), rev(B), rev(C)))


def occurs(B, C):
    """All start positions of B in C."""
    return [i for i in range(len(C) - len(B) + 1) if C.startswith(B, i)]


def is_unbordered(B):
    """B has no proper nonempty prefix that is also a suffix."""
    for k in range(1, len(B)):
        if B[:k] == B[len(B) - k:]:
            return False
    return True

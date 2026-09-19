"""Core semantics for once-r research.

Semantics implemented:
  L      : baseline replace-all, left-to-right, leftmost-first, non-overlapping,
           never rescanning inserted text (paper Definition 1).
  R2L    : replace-all scanning right-to-left (rightmost-first, non-overlapping,
           never rescanning inserted text).
  once-l : replace the single LEFTMOST occurrence.
  once-r : replace the single RIGHTMOST occurrence.

All are partial: pattern must be nonempty.
"""

def find_all(s, pat):
    """All start positions of (possibly overlapping) occurrences of pat in s."""
    if not pat:
        raise ValueError("empty pattern")
    out = []
    start = 0
    while True:
        i = s.find(pat, start)
        if i < 0:
            return out
        out.append(i)
        start = i + 1

def subst_L(A, B, C):
    """Baseline Definition 1."""
    assert B
    if B not in C:
        return C
    # leftmost-first, non-overlapping, never rescan inserted text
    out = []
    i = 0
    n = len(C)
    while i < n:
        if C.startswith(B, i):
            out.append(A)
            i += len(B)
        else:
            out.append(C[i])
            i += 1
    return "".join(out)

def subst_R2L(A, B, C):
    """Right-to-left mirror of Definition 1."""
    assert B
    if B not in C:
        return C
    out = []
    i = len(C)
    while i > 0:
        if i - len(B) >= 0 and C.startswith(B, i - len(B)):
            out.append(A)
            i -= len(B)
        else:
            i -= 1
            out.append(C[i])
    return "".join(reversed(out))

def subst_once_l(A, B, C):
    assert B
    if B not in C:
        return C
    i = C.find(B)  # leftmost
    return C[:i] + A + C[i + len(B):]

def subst_once_r(A, B, C):
    assert B
    i = C.rfind(B)  # rightmost
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]

SEM = {
    "L": subst_L,
    "R2L": subst_R2L,
    "once-l": subst_once_l,
    "once-r": subst_once_r,
}

# ---------------------------------------------------------------------------
# Expression calculus (paper Definition of Exp / Denotation, instantiated to a
# chosen primitive).  Grammar:
#   Var(i)                 variable X_i
#   Const(w)               constant string w (may be empty as replacement)
#   Subst(R, P, E)         [R/P] E   applied to value of E
#   Cat(E1, E2)            concatenation node (excluded in 'core' mode)
# Denotation: patterns must be nonempty-valued, else UNDEFINED (None).

class Var:
    __slots__ = ("i",)
    def __init__(self, i): self.i = i
    def __repr__(self): return f"X{self.i}"
    def __eq__(self, o): return isinstance(o, Var) and o.i == self.i
    def __hash__(self): return hash(("v", self.i))

class Const:
    __slots__ = ("w",)
    def __init__(self, w): self.w = w
    def __repr__(self): return repr(self.w) if self.w else "''"
    def __eq__(self, o): return isinstance(o, Const) and o.w == self.w
    def __hash__(self): return hash(("c", self.w))

class Subst:
    __slots__ = ("R", "P", "E")
    def __init__(self, R, P, E): self.R, self.P, self.E = R, P, E
    def __repr__(self): return f"[{self.R!r}/{self.P!r}]{self.E!r}"
    def __eq__(self, o): return isinstance(o, Subst) and o.R == self.R and o.P == self.P and o.E == self.E
    def __hash__(self): return hash(("s", self.R, self.P, self.E))

class Cat:
    __slots__ = ("a", "b")
    def __init__(self, a, b): self.a, self.b = a, b
    def __repr__(self): return f"({self.a!r} {self.b!r})"
    def __eq__(self, o): return isinstance(o, Cat) and o.a == self.a and o.b == self.b
    def __hash__(self): return hash(("k", self.a, self.b))

def evalE(E, sem, inputs):
    """Returns string or None (undefined: some pattern evaluated to epsilon)."""
    if isinstance(E, Var):
        return inputs[E.i]
    if isinstance(E, Const):
        return E.w
    if isinstance(E, Cat):
        a = evalE(E.a, sem, inputs)
        b = evalE(E.b, sem, inputs)
        if a is None or b is None:
            return None
        return a + b
    if isinstance(E, Subst):
        v = evalE(E.E, sem, inputs)
        p = evalE(E.P, sem, inputs)
        r = evalE(E.R, sem, inputs)
        if v is None or p is None or r is None:
            return None
        if p == "":
            return None
        return sem(r, p, v)
    raise TypeError(E)

def is_core(E):
    if isinstance(E, (Var, Const)):
        return True
    if isinstance(E, Subst):
        return is_core(E.R) and is_core(E.P) and is_core(E.E)
    return False

# ---------------------------------------------------------------------------
# Counting / structural measures used in the theorems.

def var_leaves(E):
    if isinstance(E, Var):
        return 1
    if isinstance(E, Const):
        return 0
    if isinstance(E, Cat):
        return var_leaves(E.a) + var_leaves(E.b)
    return var_leaves(E.R) + var_leaves(E.P) + var_leaves(E.E)

def nodes(E):
    if isinstance(E, (Var, Const)):
        return 0
    if isinstance(E, Cat):
        return 1 + nodes(E.a) + nodes(E.b)
    return 1 + nodes(E.R) + nodes(E.P) + nodes(E.E)

def leaves(E):
    if isinstance(E, (Var, Const)):
        return 1
    if isinstance(E, Cat):
        return leaves(E.a) + leaves(E.b)
    return leaves(E.R) + leaves(E.P) + leaves(E.E)

def size(E):
    if isinstance(E, (Var, Const)):
        return 1
    if isinstance(E, Cat):
        return 1 + size(E.a) + size(E.b)
    return 1 + size(E.R) + size(E.P) + size(E.E)

def show(E):
    if isinstance(E, Var): return f"X{E.i}"
    if isinstance(E, Const): return f"'{E.w}'"
    if isinstance(E, Cat): return f"({show(E.a)} {show(E.b)})"
    return f"[{show(E.R)}/{show(E.P)}]{show(E.E)}"

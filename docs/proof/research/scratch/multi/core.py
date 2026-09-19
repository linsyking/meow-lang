"""Core semantics for the `multi` variant (unrestricted simultaneous multi-pattern replace).

Everything mirrors the paper (docs/proof/main.tex) and its Lean reference
(docs/proof/lean/Subst.lean):

  * subst(A, B, C)        -- paper Definition 1 ([A/B]C), leftmost-first,
                             non-overlapping, never rescans inserted text.
  * rep_ref(pairs, S)     -- the paper's Definition (Multiple Substitution,
                             Semantics), a.k.a. freezing; matches Lean's repRef.
  * repC_paper            -- the paper's Theorem (Multiple Substitution)
                             construction (enc = [xb/b]).
  * enc2/dec2, repC_comma -- the *comma code* construction studied here
                             (w_c = x*c for every character c).

Composition convention: functions compose right-to-left as in the paper;
in code we simply write pipelines left-to-right in application order,
i.e. `pipeline(reps, S)` applies reps[0] first.
"""


def subst(A: str, B: str, C: str) -> str:
    """[A/B]C per Definition 1. B must be nonempty."""
    assert B != "", "pattern must be nonempty"
    out = []
    i = 0
    n = len(C)
    m = len(B)
    while i < n:
        if C.startswith(B, i):
            out.append(A)
            i += m  # scan resumes after the INSERTED text
        else:
            out.append(C[i])
            i += 1
    return "".join(out)


# ---------------------------------------------------------------------------
# The multi primitive: freezing semantics (paper Definition "Multiple
# Substitution, Semantics").  No hypothesis on the patterns beyond != "".
# ---------------------------------------------------------------------------

def rep_ref(pairs, S: str) -> str:
    """rep_n(S; X1->Y1; ...; Xn->Yn) by freezing.

    pairs = [(X1, Y1), ..., (Xn, Yn)], all Xi != "".
    Round i scans S left-to-right; a match of Xi is admissible only if it lies
    entirely in unfrozen positions; greedy leftmost-first, non-overlapping;
    after a match the scan resumes at the end of the matched block.
    Finally every frozen block is replaced simultaneously by its Yi.
    """
    n = len(pairs)
    if n == 0:
        return S
    assert all(X != "" for X, _ in pairs), "patterns must be nonempty"
    L = len(S)
    frozen = [0] * L  # 0 = unfrozen, else round number i
    for i, (X, _) in enumerate(pairs, start=1):
        m = len(X)
        p = 0
        while p < L:
            if frozen[p] != 0:
                p += 1
                continue
            if p + m <= L and S.startswith(X, p) and all(
                frozen[q] == 0 for q in range(p, p + m)
            ):
                for q in range(p, p + m):
                    frozen[q] = i
                p += m
            else:
                p += 1
    out = []
    p = 0
    while p < L:
        if frozen[p] == 0:
            out.append(S[p])
            p += 1
        else:
            i = frozen[p]
            X, Y = pairs[i - 1]
            out.append(Y)
            p += len(X)
    return "".join(out)


# ---------------------------------------------------------------------------
# One-pass multi-pattern variants (secondary question).
# ---------------------------------------------------------------------------

def rep_onepass(pairs, S: str, rule="longest") -> str:
    """One left-to-right pass. At each position p, among the patterns matching
    at p (all positions of S are 'fresh'), pick per `rule`:
      'longest' : the longest matching pattern (leftmost-longest);
      'first'   : the smallest-index matching pattern (first-rule-wins).
    Replace and resume scanning after the *replacement text* (never rescan).
    """
    assert all(X != "" for X, _ in pairs)
    out = []
    p = 0
    L = len(S)
    while p < L:
        cands = [(j, X) for j, (X, _) in enumerate(pairs) if S.startswith(X, p)]
        if not cands:
            out.append(S[p])
            p += 1
            continue
        if rule == "longest":
            j, X = max(cands, key=lambda t: len(t[1]))
        elif rule == "first":
            j, X = min(cands, key=lambda t: t[0])
        else:
            raise ValueError(rule)
        out.append(pairs[j][1])
        p += len(X)  # resume after the original match (replacement not rescanned)
    return "".join(out)


# ---------------------------------------------------------------------------
# The paper's enc/dec and rep_n construction (Theorem "Multiple Substitution").
# ---------------------------------------------------------------------------

def enc(b: str, x: str, S: str) -> str:
    return subst(x + b, b, S)


def dec(b: str, x: str, S: str) -> str:
    return subst(b, x + b, S)


def repC_paper(b: str, x: str, pairs, S: str) -> str:
    """The paper's construction.  m_i = x b^{i+1}.

    rename+repair passes i = 1..n:
        [m_i / enc(X_i)]  then  [enc(X_i) b / m_{i+1}]
    instantiation passes i = n..1:
        [enc(Y_i) / m_i]
    finally dec.
    """
    n = len(pairs)
    T = enc(b, x, S)
    for i, (X, _) in enumerate(pairs, start=1):
        m_i = x + b * (i + 1)
        m_next = x + b * (i + 2)
        T = subst(m_i, enc(b, x, X), T)          # rename
        T = subst(enc(b, x, X) + b, m_next, T)    # repair
    for i in range(n, 0, -1):
        Y = pairs[i - 1][1]
        m_i = x + b * (i + 1)
        T = subst(enc(b, x, Y), m_i, T)           # instantiate
    return dec(b, x, T)


# ---------------------------------------------------------------------------
# Comma-code construction (the new one studied in this report).
# ---------------------------------------------------------------------------

_enc2_cache = {}

def enc2(b: str, x: str, S: str, alphabet) -> str:
    """Comma code: every character c is encoded as the block  x*c.

    Realized as passes: first [xx/x] (double the x's), then [x*c/c] for each
    c != x (prefix every other character by x).  Order matters: the x-doubling
    must run first so that the x's inserted by later passes are not doubled.
    """
    key = (b, x, S, alphabet)
    if key in _enc2_cache:
        return _enc2_cache[key]
    T = subst(x + x, x, S)
    for c in alphabet:
        if c != x:
            T = subst(x + c, c, T)
    _enc2_cache[key] = T
    return T


def dec2(b: str, x: str, S: str, alphabet) -> str:
    """Inverse of enc2: collapse every non-x block x*c to c, then halve the
    x-runs with [x/xx].  (Runs of x's are exactly concatenations of the block
    'xx', hence even, and the greedy scan of [x/xx] takes whole blocks.)"""
    T = S
    for c in alphabet:
        if c != x:
            T = subst(c, x + c, T)
    return subst(x, x + x, T)


def repC_comma(b: str, x: str, pairs, S: str, alphabet) -> str:
    """Comma-code version of repC: same architecture (rename, repair,
    instantiate, decode) but with the equal-length comma code enc2.

    Structural facts used (all verified computationally in verify.py):
      (F1) enc2-images contain no "bb": every 'b' of an image is a data
           character and is followed by the comma 'x'.
      (F2) markers m_i = x b^{i+1} contain "bb", begin with 'x'; so they never
           occur inside images and never straddle image/marker junctions.
      (F3) all codewords have length 2, so any occurrence of an image enc2(X)
           that starts at a unit boundary is genuine, and any occurrence that
           starts at a data position (only possible when X = x^k) is preceded
           one position earlier by an overlapping genuine occurrence --
           shadowing is impossible.
      (F4) every spurious match (one that reaches into a marker) is followed
           by 'b', and the repair pass [enc2(X_i) b / m_{i+1}] restores the
           text exactly.
    """
    n = len(pairs)
    T = enc2(b, x, S, alphabet)
    for i, (X, _) in enumerate(pairs, start=1):
        m_i = x + b * (i + 1)
        m_next = x + b * (i + 2)
        T = subst(m_i, enc2(b, x, X, alphabet), T)          # rename
        T = subst(enc2(b, x, X, alphabet) + b, m_next, T)   # repair
    for i in range(n, 0, -1):
        Y = pairs[i - 1][1]
        m_i = x + b * (i + 1)
        T = subst(enc2(b, x, Y, alphabet), m_i, T)          # instantiate
    return dec2(b, x, T, alphabet)


# ---------------------------------------------------------------------------
# Small helpers.
# ---------------------------------------------------------------------------

def all_strings(alphabet, maxlen):
    """All strings over alphabet, by increasing length, up to maxlen."""
    res = [""]
    frontier = [""]
    for _ in range(maxlen):
        nxt = []
        for s in frontier:
            for c in alphabet:
                t = s + c
                nxt.append(t)
        res.extend(nxt)
        frontier = nxt
    return res

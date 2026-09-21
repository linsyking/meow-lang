"""Shared library for the alphabet-invariance research round.

Implements the paper's primitives and calculus exactly as defined:
  - def:subst  (main.tex ~line 112): left-to-right, leftmost-first,
    all occurrences, never rescanning inserted text; [A/eps] undefined.
  - def:once (~line 888), def:r2l (~line 1114), k-th occurrence (prop:kth).
  - def:exp / def:den (~lines 671-695): expression AST + denotation.
  - def:deg (~line 811), def:safe/Anch (~line 733).
  - def:rep (~line 512): multiple substitution by freezing, and the
    expression of thm:multiple substitution (~line 547).
Comma-free (Golomb) dictionaries and the transfer construction.
"""
from itertools import product

UNDEF = None  # undefinedness sentinel


# ---------- primitives ----------

def subst(A, B, C):
    """[A/B]C per def:subst. B must be nonempty."""
    assert B != '', 'pattern must be nonempty'
    res = []
    i = 0
    while True:
        j = C.find(B, i)
        if j < 0:
            res.append(C[i:])
            return ''.join(res)
        res.append(C[i:j])
        res.append(A)
        i = j + len(B)


def once_subst(A, B, C):
    """[A/B]_1 C per def:once: replace the leftmost occurrence only."""
    assert B != ''
    j = C.find(B)
    if j < 0:
        return C
    return C[:j] + A + C[j + len(B):]


def rsubst(A, B, C):
    """[A/B]^R C per def:r2l: rightmost occurrence, resume to its left."""
    assert B != ''
    pieces = []
    i = len(C)
    while True:
        j = C.rfind(B, 0, i)
        if j < 0:
            pieces.append(C[:i])
            break
        pieces.append(C[j + len(B):i])
        pieces.append(A)
        i = j
    return ''.join(reversed(pieces))


def kth_subst(A, B, C, k):
    """[A/B]_k C: replace the k-th occurrence in the greedy scan order (1-based)."""
    assert B != ''
    pos = []
    i = 0
    while True:
        j = C.find(B, i)
        if j < 0:
            break
        pos.append(j)
        i = j + len(B)
    if len(pos) < k:
        return C
    j = pos[k - 1]
    return C[:j] + A + C[j + len(B):]


def apply_pass(mode, A, B, C):
    if B == '':
        return UNDEF
    if mode == 'L':
        return subst(A, B, C)
    if mode == 'once':
        return once_subst(A, B, C)
    if mode == 'R':
        return rsubst(A, B, C)
    if isinstance(mode, tuple) and mode[0] == 'kth':
        return kth_subst(A, B, C, mode[1])
    raise ValueError(mode)


def occ_positions(C, B):
    """All (not just greedy) start positions of B in C."""
    if B == '':
        return list(range(len(C) + 1))
    res = []
    i = 0
    while True:
        j = C.find(B, i)
        if j < 0:
            return res
        res.append(j)
        i = j + 1


# ---------- expression calculus (def:exp / def:den) ----------
# AST: ('var', i) | ('const', w) | ('pass', R, P, E) | ('cat', E1, E2)
# NB: in [R/P] the SECOND sub-expression P is the pattern (paper's notation).

def ev(E, args, mode='L'):
    t = E[0]
    if t == 'var':
        return args[E[1]]
    if t == 'const':
        return E[1]
    if t == 'cat':
        v1 = ev(E[1], args, mode)
        v2 = ev(E[2], args, mode)
        if v1 is UNDEF or v2 is UNDEF:
            return UNDEF
        return v1 + v2
    if t == 'pass':
        vR = ev(E[1], args, mode)
        vP = ev(E[2], args, mode)
        vE = ev(E[3], args, mode)
        if vR is UNDEF or vP is UNDEF or vE is UNDEF:
            return UNDEF
        return apply_pass(mode, vR, vP, vE)
    raise ValueError(E)


def size(E):
    t = E[0]
    if t in ('var', 'const'):
        return 1
    if t == 'cat':
        return 1 + size(E[1]) + size(E[2])
    return 1 + size(E[1]) + size(E[2]) + size(E[3])


def depth(E):
    t = E[0]
    if t in ('var', 'const'):
        return 0
    if t == 'cat':
        return 1 + max(depth(E[1]), depth(E[2]))
    return 1 + max(depth(E[1]), depth(E[2]), depth(E[3]))


def deg(E):
    """def:deg."""
    t = E[0]
    if t == 'var':
        return 1
    if t == 'const':
        return 0
    if t == 'cat':
        return max(deg(E[1]), deg(E[2]))
    return deg(E[3]) + deg(E[1])


def anchored(E):
    t = E[0]
    if t == 'var':
        return False
    if t == 'const':
        return E[1] != ''
    if t == 'cat':
        return anchored(E[1]) or anchored(E[2])
    return False  # pass node


def safe(E):
    t = E[0]
    if t in ('var', 'const'):
        return True
    if t == 'cat':
        return safe(E[1]) and safe(E[2])
    return anchored(E[2]) and safe(E[1]) and safe(E[2]) and safe(E[3])


def subst_ast(E, mapping):
    """E[F...] : capture-free replacement of variables by expressions."""
    t = E[0]
    if t == 'var':
        return mapping.get(E[1], E)
    if t == 'const':
        return E
    if t == 'cat':
        return ('cat', subst_ast(E[1], mapping), subst_ast(E[2], mapping))
    return ('pass', subst_ast(E[1], mapping), subst_ast(E[2], mapping),
            subst_ast(E[3], mapping))


def all_strings(alphabet, maxlen):
    """All strings over the alphabet of length 0..maxlen."""
    res = ['']
    cur = ['']
    for _ in range(maxlen):
        cur = [s + c for s in cur for c in alphabet]
        res.extend(cur)
    return sorted(res)


# ---------- comma-free dictionaries ----------

def comma_free(D):
    """Uniform-length dictionary D is comma-free (Golomb):
    no codeword occurs in u*v at a junction-straddling position."""
    Dset = set(D)
    assert Dset and len(next(iter(Dset))) == len(next(iter(Dset)))
    ell = len(next(iter(Dset)))
    for u in D:
        for v in D:
            uv = u + v
            for p in range(1, ell):
                if uv[p:p + ell] in Dset:
                    return False
    return True


def dict_family(alphabet, a, b, ell):
    """Explicit comma-free family (our Lemma 'existence'):
    { a a m b : m in alphabet^{ell-3}, 'aa' not a factor of m, m[0] != a }.
    Every codeword contains 'aa' only at position 0 and ends with b, so in
    u*v the factor 'aa' occurs only at 0 and ell; codewords start with
    'aa', hence occur only aligned. Requires ell >= 3, a != b in alphabet."""
    assert ell >= 3 and a != b and a in alphabet and b in alphabet
    words = set()
    for m in product(alphabet, repeat=ell - 3):
        ms = ''.join(m)
        if a + a in ms:
            continue
        if ell > 3 and ms[0] == a:
            continue
        words.add(a + a + ms + b)
    return sorted(words)


def make_coding(src_alphabet, tgt_alphabet, ell=None, a=None, b=None):
    """Injective character-wise coding src -> tgt via a comma-free dict."""
    tgt = sorted(tgt_alphabet)
    if a is None:
        a = tgt[0]
    if b is None:
        b = tgt[1]
    if ell is None:
        # smallest ell with enough codewords
        ell = 3
        while len(dict_family(tgt, a, b, ell)) < len(src_alphabet):
            ell += 1
            assert ell <= 40, 'dictionary growth failure'
    D = dict_family(tgt, a, b, ell)
    assert len(D) >= len(src_alphabet), (len(D), len(src_alphabet))
    assert comma_free(D)
    cmap = {s: w for s, w in zip(sorted(src_alphabet), D)}
    return cmap, D, ell


def enc(cmap, S):
    return ''.join(cmap[ch] for ch in S)


# ---------- transfer construction (Theorem: Transfer, direction 1) ----------

def transfer(E, cmap):
    t = E[0]
    if t == 'var':
        return E
    if t == 'const':
        return ('const', enc(cmap, E[1]))
    if t == 'cat':
        return ('cat', transfer(E[1], cmap), transfer(E[2], cmap))
    return ('pass', transfer(E[1], cmap), transfer(E[2], cmap),
            transfer(E[3], cmap))


# ---------- multiple substitution: semantics (def:rep) and expression ----------

def rep_sem(S, pairs):
    """rep_n(S; X_1,Y_1; ...; X_n,Y_n) by freezing (def:rep).
    Undefined (UNDEF) if some X_i is empty."""
    n = len(S)
    label = [-1] * n  # round that froze each position
    for i, (X, Y) in enumerate(pairs):
        if X == '':
            return UNDEF
        p = 0
        while p + len(X) <= n:
            if any(label[q] >= 0 for q in range(p, p + len(X))):
                p += 1
                continue
            if S[p:p + len(X)] == X:
                for q in range(p, p + len(X)):
                    label[q] = i
                p += len(X)
            else:
                p += 1
    out = []
    q = 0
    while q < n:
        if label[q] >= 0:
            i = label[q]
            out.append(pairs[i][1])
            q += len(pairs[i][0])
        else:
            out.append(S[q])
            q += 1
    return ''.join(out)


def enc2_expr(var_index, b, x, others):
    """enc^2_x(Z) as an expression: [x c_1/c_1]...[x c_M/c_M][xx/x] Z
    (right-to-left: doubling pass first). others = Gamma \\ {x} (any order)."""
    E = ('var', var_index)
    E = ('pass', ('const', x + x), ('const', x), E)          # [xx/x] runs first
    for c in reversed(others):                                # then [x c_M/c_M] ... [x c_1/c_1]
        E = ('pass', ('const', x + c), ('const', c), E)
    return E


def dec2_expr(inner, b, x, others):
    """dec^2_x applied to `inner`: [x/xx][c_M/x c_M]...[c_1/x c_1]
    (right-to-left: [c_1/x c_1] first, halving last)."""
    E = inner
    for c in others:                                           # [c_1/xc_1], then [c_2/xc_2], ...
        E = ('pass', ('const', c), ('const', x + c), E)
    E = ('pass', ('const', x), ('const', x + x), E)           # [x/xx] last
    return E


def rep_expr(vS, vX, vY, n, b, x, others):
    """The expression of thm:multiple substitution:
       dec^2( (prod_{i=1..n} [E_{Y_i}/m_i]) (prod_{i=1..n} [E_{X_i} b/m_{i+1}][m_i/E_{X_i}]) E_S )
    with variable indices vS (scrutinee), vX[i], vY[i] (0-based slots).
    Right-to-left: renaming rounds run i = 1..n; instantiations i = n..1."""
    def m(i):
        return ('const', x + b * (i + 1))
    E = enc2_expr(vS, b, x, others)
    for i in range(1, n + 1):
        E = ('pass', m(i), enc2_expr(vX[i - 1], b, x, others), E)          # [m_i/E_{X_i}]
        E = ('pass', ('cat', enc2_expr(vX[i - 1], b, x, others), ('const', b)),
             m(i + 1), E)                                                  # [E_{X_i} b/m_{i+1}]
    for i in range(n, 0, -1):
        E = ('pass', enc2_expr(vY[i - 1], b, x, others), m(i), E)          # [E_{Y_i}/m_i]
    return dec2_expr(E, b, x, others)


def rep_apply_expr(n, b, x, others, S_expr, X_exprs, Y_exprs):
    """rep_expr with the 2n+1 argument slots filled by given expressions."""
    E = rep_expr(0, {i: i + 1 for i in range(n)}, {i: n + 1 + i for i in range(n)},
                 n, b, x, others)
    mapping = {0: S_expr}
    for i in range(n):
        mapping[i + 1] = X_exprs[i]
        mapping[n + 1 + i] = Y_exprs[i]
    return subst_ast(E, mapping)

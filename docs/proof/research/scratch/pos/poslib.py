# poslib.py -- core library for the "pos" (positional/index-aware) variant study.
# Semantics follows docs/proof/main.tex Definition 1 for the baseline L.

ALPHA = "ab"

# ---------- Baseline L (paper Def. 1) ----------
def subst(A, B, C):
    """[A/B]C : replace every occurrence of B by A, leftmost-first,
    non-overlapping, never rescanning inserted text. B must be nonempty."""
    assert B != "", "[A/eps] is undefined"
    return C.replace(B, A)

# ---------- pos primitives ----------
def setAt(i, c, S):
    """Replace char at index i by single char c; identity if i out of range."""
    assert len(c) == 1
    if 0 <= i < len(S):
        return S[:i] + c + S[i+1:]
    return S

def occurrences(S, B):
    """Greedy leftmost-first non-overlapping occurrence start positions of B in S."""
    assert B != ""
    res, pos = [], 0
    while True:
        j = S.find(B, pos)
        if j < 0:
            return res
        res.append(j)
        pos = j + len(B)

def repOcc(k, B, A, S):
    """Replace the k-th (0-based, greedy leftmost-first) occurrence of B by A.
    Identity if fewer than k+1 occurrences."""
    assert B != "", "repOcc with empty pattern is undefined"
    occ = occurrences(S, B)
    if k < len(occ):
        j = occ[k]
        return S[:j] + A + S[j+len(B):]
    return S

# computed-index variants (index = length of computed index-string)
def setAtI(idx_str, c, S):
    return setAt(len(idx_str), c, S)

def repOccI(idx_str, k, B, A, S):
    return repOcc(len(idx_str), B, A, S)

# ---------- once_l ----------
def once_l(B, A, S):
    """Replace the leftmost occurrence of B by A (identity if none)."""
    return repOcc(0, B, A, S)

# ---------- pos expression AST + evaluator ----------
# ('var', i) | ('const', s) | ('cat', e1, e2)
# ('setat', i, r, e)        i literal int, r expr denoting a single char
# ('repocc', k, r, p, e)    k literal int
# ('setatI', ie, r, e)      index = |value(ie)|
# ('repoccI', ke, r, p, e)  index = |value(ke)|
class Undefined(Exception):
    pass

def ev(E, env):
    t = E[0]
    if t == 'var':
        return env[E[1]]
    if t == 'const':
        return E[1]
    if t == 'cat':
        return ev(E[1], env) + ev(E[2], env)
    if t == 'setat':
        r = ev(E[2], env)
        if len(r) != 1:
            raise Undefined("setAt char not single")
        return setAt(E[1], r, ev(E[3], env))
    if t == 'repocc':
        r, p = ev(E[2], env), ev(E[3], env)
        if p == "":
            raise Undefined("empty pattern")
        return repOcc(E[1], p, r, ev(E[4], env))
    if t == 'setatI':
        r = ev(E[2], env)
        if len(r) != 1:
            raise Undefined("setAt char not single")
        return setAt(len(ev(E[1], env)), r, ev(E[3], env))
    if t == 'repoccI':
        r, p = ev(E[3], env), ev(E[4], env)
        if p == "":
            raise Undefined("empty pattern")
        return repOcc(len(ev(E[1], env)), p, r, ev(E[5], env))
    raise ValueError(t)

X1 = ('var', 0)
X2 = ('var', 1)

# ---------- paper's L machinery (Section 2 of main.tex) ----------
def enc(S, b='a', x='b'):
    return subst(x+b, b, S)          # enc_{b,x} = [xb/b]
def dec(S, b='a', x='b'):
    return subst(b, x+b, S)          # dec_{b,x} = [b/xb]
def catL(X, Y, b='a', x='b'):
    # cat = dec([enc(X)/xb^2][enc(Y)/xb^3](xb^2 xb^3))
    T = subst(enc(X, b, x), x+b*2, subst(enc(Y, b, x), x+b*3, x+b*2 + x+b*3))
    return dec(T, b, x)
def headL(S, b='a', x='b'):
    # head(X) = dec([eps/enc(tail(X)) bb](enc(X) bb))
    tl = tailL(S, b, x)
    return dec(subst("", enc(tl, b, x) + b+b, enc(S, b, x) + b+b), b, x)
def tailL(S, b='a', x='b'):
    # tail(X) = dec([eps/bb][eps/bbx][eps/bbxb](bb enc(X)))   (N=2; general N adds [eps/bb si])
    T = b+b + enc(S, b, x)
    T = subst("", b+b+x+b, T)   # [eps/bbxb] runs first (rightmost)
    T = subst("", b+b+x, T)
    T = subst("", b+b, T)
    return dec(T, b, x)
def benc(W, b='a', x='b'):
    return x+b*2 + enc(W, b, x) + x+b*2
def eqL(A, B, b='a', x='b', tt='c', ff='d'):
    return subst(ff, benc(A, b, x), subst(tt, benc(B, b, x), benc(A, b, x)))
def ifL(C, A, B, b='a', x='b', tt='c', ff='d'):
    # if(C,X,Y) = dec([enc(Y)/bb]([enc(X)/top][bb/bot]C))
    T = subst(enc(A, b, x), tt, subst(b+b, ff, C))
    return dec(subst(enc(B, b, x), b+b, T), b, x)

def charL(j, S):
    """S[j] via head(tail^j) -- L-reachable."""
    for _ in range(j):
        S = tailL(S)
    return headL(S)

def setAtL(i, c, S):
    """setAt(i,c) in the baseline calculus:
    if(eq(tail^i S, eps), S, cat(prefix_i, c, tail^{i+1}))"""
    Ti = S
    for _ in range(i):
        Ti = tailL(Ti)
    if eqL(Ti, "") == 'c':
        return S
    pre = ""
    for j in range(i):
        pre = catL(pre, charL(j, S))
    return catL(catL(pre, c), tailL(Ti))

def edit_distance(a, b):
    m, n = len(a), len(b)
    dp = list(range(n+1))
    for i in range(1, m+1):
        prev, dp[0] = dp[0], i
        for j in range(1, n+1):
            cur = dp[j]
            dp[j] = min(dp[j]+1, dp[j-1]+1, prev + (a[i-1] != b[j-1]))
            prev = cur
    return dp[n]

if __name__ == "__main__":
    # sanity: Python replace == paper Def 1 examples
    assert subst("ab", "b", "b") == "ab"
    assert subst("aba", "ba", "baabba") == "abaababa"
    # pos sanity
    assert setAt(0, 'x', "abc") == "xbc"
    assert setAt(5, 'x', "abc") == "abc"
    assert repOcc(0, "b", "X", "abcb") == "aXcb"
    assert repOcc(1, "b", "X", "abcb") == "abcX"
    assert repOcc(2, "b", "X", "abcb") == "abcb"
    assert occurrences("aabaa", "aa") == [0, 3]
    print("poslib self-tests OK")

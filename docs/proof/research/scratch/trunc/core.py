"""trunc workspace: is tau -- the longest (ba|bb)*-prefix of a marked text --
computable in L on the marked world W0 = (ba|bb|baa)*?

tau(T) = T[:r-1] where r = position of the leftmost 'aa' (the first baa
token's 'aa'); tau = T when T has no mark.  By the (coordinator- and
independently-) verified pad reduction, tau in L on W0  ==>  the crux
[babba/baa]_1 in L on W0  ==>  ONCE sqsubset L over every alphabet.

Primitives reuse the once-workspace semantics (subst was cross-checked
there against str.replace, rec/lazy_pass, systems, 50k+ random cases).
"""
import itertools

# ---------------------------------------------------------------- world


def subst(A, B, C):
    """[A/B]C -- paper Def def:subst.  Greedy leftmost-first, disjoint,
    never rescans inserted text.  [A/eps] undefined."""
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


def once(A, B, C):
    """[A/B]_1 C -- Def def:once."""
    if not B:
        raise ValueError("[A/eps]_1 undefined")
    i = C.find(B)
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]


TOKENS = ('ba', 'bb', 'baa')
MARK = 'baa'


def marked_texts(maxlen):
    """All products of {ba,bb,baa} of total length <= maxlen, in a
    deterministic order (shortlex by token count then lex)."""
    out = ['']
    frontier = ['']
    while frontier:
        nxt = []
        for t in frontier:
            for tok in TOKENS:
                s = t + tok
                if len(s) <= maxlen:
                    nxt.append(s)
        out.extend(nxt)
        frontier = nxt
    return out


def is_marked(T):
    """T in (ba|bb|baa)* by greedy tokenization."""
    i = 0
    while i < len(T):
        if T.startswith('baa', i):
            i += 3
        elif T.startswith('ba', i) or T.startswith('bb', i):
            i += 2
        else:
            return False
    return True


# ---------------------------------------------------------------- oracles


def first_aa(T):
    """position of the leftmost 'aa', or -1."""
    return T.find('aa')


def tau(T):
    """THE TARGET: longest (ba|bb)*-prefix = T[:r-1], r = leftmost 'aa'
    (the first baa token starts one before its 'aa'); T if no mark."""
    r = first_aa(T)
    return T if r < 0 else T[:r - 1]


def tau_aa(T):
    """longest 'aa'-free prefix = tau(T)+'b' when a mark exists."""
    r = first_aa(T)
    return T if r < 0 else T[:r]


def zeta(T):
    """everything from the first mark's 'aa' on (T if no mark)."""
    r = first_aa(T)
    return T if r < 0 else T[r:]


def crux(T):
    """[babba/baa]_1 on W0 == replace the leftmost 'aa' by 'abba'."""
    return once('babba', 'baa', T)


# ---------------------------------------------------------------- encoding


def enc2(T, x='b'):
    """Comma code enc^2_x over {a,b} with comma x: every c ↦ block xc."""
    if x != 'b':
        raise ValueError("binary only, comma b")
    # doubling pass first (right-to-left product = first applied)
    S = subst('bb', 'b', T)
    S = subst('ba', 'a', S)
    return S


def dec2(S, x='b'):
    if x != 'b':
        raise ValueError("binary only, comma b")
    S = subst('a', 'ba', S)
    S = subst('b', 'bb', S)
    return S


def apply_pipeline(passes, T):
    """passes = [(A,B), ...] in RUN order (first applied first)."""
    for A, B in passes:
        T = subst(A, B, T)
    return T


# W from the paper (prop:del-leftmost), run order
W = [('aa', 'a'), ('ab', 'b'), ('b', 'ba'), ('ab', 'aa'), ('a', 'ab')]

# mirror of W (swap a<->b in every constant)
W_MIR = [('bb', 'b'), ('ba', 'a'), ('a', 'ab'), ('ba', 'bb'), ('b', 'ba')]


def battery(maxlen=12, extra=()):
    ts = marked_texts(maxlen)
    return ts + list(extra)


ADVERSARIAL = [
    '', 'ba', 'bb', 'baa', 'baba', 'bbba', 'babaa', 'baabaab',
    'bbbaababbaababbababbaabbbaa',   # random-ish longer
    'baabaabaabaabaa',               # marks dense
    'bbbbbbbbbbbaa',                  # long cell run then mark
    'baabababababababababa',          # mark early, cells after
    'bbabbabbaabbabbabaabbaabbabaa',
]

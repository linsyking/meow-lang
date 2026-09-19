"""The paper's Section 2 toolkit, implemented with a pluggable substitution
(l2r or r2l), so both directions can be tested on the same constructions.

Sigma is given as a list of characters [sigma_1, ..., sigma_N].
b = sigma_1 (escaped char), x = sigma_2 (backslash char), as in the paper.
"""


def compose(f, g):
    return lambda *a: f(g(*a))


def pipeline(sem, passes):
    """passes applied right-to-left, as in the paper's composition convention."""
    def h(S):
        for (R, P) in reversed(passes):
            S = sem(R, P, S)
        return S
    return h


def make_toolkit(sem, sigma):
    assert len(sigma) >= 2
    b, x = sigma[0], sigma[1]

    def enc(S):  # [xb/b]
        return sem(x + b, b, S)

    def dec(S):  # [b/xb]
        return sem(b, x + b, S)

    def cat(x_, y_):
        # dec([enc(X)/xb2][enc(Y)/xb3](xb2 xb3)), innermost (rightmost) pass first
        t = sem(enc(y_), x + b * 3, x + b * 2 + x + b * 3)
        t = sem(enc(x_), x + b * 2, t)
        return dec(t)

    def tail(x_):
        # dec([e/ss1][e/ss1s2][e/ss1s2s1](prod_i=3..N [e/ss1si])(ss1 enc(X)))
        # passes applied right-to-left; the product's last factor (i=N) first.
        passes = []
        for i in range(len(sigma), 2, -1):   # i = N down to 3
            passes.append(("", sigma[0] + sigma[0] + sigma[i - 1]))
        passes.append(("", sigma[0] + sigma[0] + sigma[1] + sigma[0]))
        passes.append(("", sigma[0] + sigma[0] + sigma[1]))
        passes.append(("", sigma[0] + sigma[0]))
        t = sigma[0] + sigma[0] + enc(x_)
        for (R, P) in passes:
            t = sem(R, P, t)
        return dec(t)

    def head(x_):
        # dec([e/enc(tail(X)) ss1](enc(X) ss1))
        t = enc(x_) + sigma[0] + sigma[0]
        t = sem("", enc(tail(x_)) + sigma[0] + sigma[0], t)
        return dec(t)

    def benc(x_):
        return x + b * 2 + enc(x_) + x + b * 2

    def bdec(s):
        return sem("", x + b * 2, s)

    def eq(x_, y_, top, bot):
        t = benc(x_)
        t = sem(top, benc(y_), t)
        t = sem(bot, benc(x_), t)
        return t

    def if_(c, x_, y_, top, bot):
        # dec([enc(Y)/bb]([enc(X)/top][bb/bot] C))
        t = sem(b + b, bot, c)
        t = sem(enc(x_), top, t)
        t = sem(enc(y_), b + b, t)
        return dec(t)

    return dict(enc=enc, dec=dec, cat=cat, tail=tail, head=head,
                benc=benc, bdec=bdec, eq=eq, if_=if_, b=b, x=x, sigma=sigma)


def make_rep(sem, sigma, n):
    """The paper's rep_n construction (Theorem `Multiple Substitution`).

    rep_n(S, X_1, Y_1, ..., X_n, Y_n) =
      dec( (prod_i [enc(Y_i)/xb^{i+1}])
           (prod_i from i=1 to n, applied i=1 first:
              [enc(X_i) b / xb^{i+2}] after [xb^{i+1} / enc(X_i)] )
           enc(S) )
    """
    b, x = sigma[0], sigma[1]

    def enc(S):
        return sem(x + b, b, S)

    def dec(S):
        return sem(b, x + b, S)

    def rep(S, pairs):
        assert len(pairs) == n
        t = enc(S)
        # renaming passes: i = 1, 2, ..., n (in this order)
        for i, (Xi, Yi) in enumerate(pairs, start=1):
            E = enc(Xi)
            m_i = x + b * (i + 1)
            m_next = x + b * (i + 2)
            t = sem(m_i, E, t)            # rename matches to markers
            t = sem(E + b, m_next, t)      # repair spurious markers
        # instantiation passes: i = n, ..., 1
        for i in range(n, 0, -1):
            Xi, Yi = pairs[i - 1]
            m_i = x + b * (i + 1)
            t = sem(enc(Yi), m_i, t)
        return dec(t)

    return rep


def make_rep_mirror(sem, sigma, n):
    """The fully mirrored rep_n construction for r2l (all constants reversed):
    enc' = [bx/b] (each b -> bx, so every b is FOLLOWED by x), markers b^{k} x,
    repair [b E' / b^{k} x], dec' = [b/bx].
    By the rev-duality this computes RIGHTMOST-freezing multiple substitution,
    under the mirrored hypothesis: |X_i| = 1 or X_i does not BEGIN with x.
    """
    b, x = sigma[0], sigma[1]

    def encp(S):
        return sem(b + x, b, S)

    def decp(S):
        return sem(b, b + x, S)

    def rep(S, pairs):
        assert len(pairs) == n
        t = encp(S)
        for i, (Xi, Yi) in enumerate(pairs, start=1):
            E = encp(Xi)
            m_i = b * (i + 1) + x
            t = sem(m_i, E, t)                      # rename: [m'_i / E']
            t = sem(b + E, b * (i + 2) + x, t)      # repair: [b E' / b m'_i]
        for i in range(n, 0, -1):
            Xi, Yi = pairs[i - 1]
            m_i = b * (i + 1) + x
            t = sem(encp(Yi), m_i, t)
        return decp(t)

    return rep


def freeze_rep(S, pairs, rightmost=False):
    """Freezing semantics of Definition `rep` (leftmost) and its mirror (rightmost).

    Round i: greedily freeze non-overlapping occurrences of X_i, each entirely
    in unfrozen positions, leftmost-first (or rightmost-first). Finally
    replace every frozen occurrence of X_i by Y_i simultaneously.
    """
    n = len(pairs)
    frozen = [False] * len(S)
    owner = [-1] * len(S)

    def admissible(Xi, s):
        return (s >= 0 and s + len(Xi) <= len(S) and S.startswith(Xi, s)
                and all(not frozen[q] for q in range(s, s + len(Xi))))

    for i in range(n):
        Xi = pairs[i][0]
        while True:
            occ = None
            rng = range(len(S) - len(Xi), -1, -1) if rightmost else range(0, len(S) - len(Xi) + 1)
            for s in rng:
                if admissible(Xi, s):
                    occ = s
                    break
            if occ is None:
                break
            for q in range(occ, occ + len(Xi)):
                frozen[q] = True
                owner[q] = i
    out = []
    i = 0
    while i < len(S):
        if frozen[i]:
            j = owner[i]
            out.append(pairs[j][1])
            i += len(pairs[j][0])
        else:
            out.append(S[i])
            i += 1
    return "".join(out)

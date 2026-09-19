"""Raw-L expression builders, transcribing the paper's Section 2 formulas.

Every builder returns an AST (core.py) that uses ONLY the nodes K/V/C/S --
i.e. a genuine expression of the paper's calculus (Def. def:exp).  These are
the pieces out of which the recursive definitions of later rounds are built.

Alphabet bookkeeping: a Sig carries
    sigma : list of characters (the alphabet Sigma)
    b, x  : the two encoding characters (paper: sigma_1, sigma_2), b != x
    top, bot : the two booleans for eq/if (top != bot, top != b)
All constructions in this file work over the binary alphabet {a,b} with
b='a', x='b', top='b', bot='a' (the paper's Prop. prop:instances notes
top = x is the |Sigma|=2 choice), so everything below is instantiated with
Sig(['a','b'], 'a', 'b', 'b', 'a') unless stated otherwise.

Composition convention (paper): [A1/B1][A2/B2]E applies [A2/B2] first
(right-to-left).  `comp(passes, E)` takes passes in PAPER ORDER and builds
the nested AST; `pipe(passes, E)` takes passes in RUN ORDER.
"""

from core import K, V, C, S, F, subst


def comp(passes, E):
    """passes = [(A1,B1),...,(Ak,Bk)] in paper order:  [A1/B1]...[Ak/Bk]E.
    The RIGHTMOST (last listed) runs FIRST."""
    acc = E
    for (A, B) in reversed(passes):
        acc = S(A if isinstance(A, tuple) else K(A),
                B if isinstance(B, tuple) else K(B), acc)
    return acc


def pipe(passes, E):
    """passes in RUN ORDER: passes[0] runs first."""
    return comp(list(reversed(passes)), E)


class Sig:
    def __init__(self, sigma, b, x, top, bot):
        assert b != x and top != bot and top != b
        self.sigma = list(sigma)
        self.b, self.x, self.top, self.bot = b, x, top, bot
        self.others = [c for c in self.sigma if c != x]   # c_1..c_M of enc2
        # markers of the lazy two-way gate (Section 3 of REPORT.md):
        # P, Q contain bb, are mutually non-occurring, and never occur inside
        # an enc^2-image (which has b-runs of length <= 1).
        self.P_GATE = self.b + self.b + self.x        # b b x
        self.Q_GATE = self.x + self.b + self.b        # x b b

    def m(self, k):
        """marker x b^k"""
        return self.x + self.b * k


BIN = Sig(['a', 'b'], 'a', 'b', 'b', 'a')     # the |Sigma|=2 instantiation


# ---------------------------------------------------------------- enc / dec

def enc(sg, E):      return comp([(sg.x + sg.b, sg.b)], E)          # [xb/b]E
def dec(sg, E):      return comp([(sg.b, sg.x + sg.b)], E)          # [b/xb]E


def benc(sg, E):
    """benc(X) = xb^2 enc(X) xb^2"""
    return C(C(K(sg.m(2)), enc(sg, E)), K(sg.m(2)))


def bdec(sg, E):
    """bdec(X) = [eps/xb^2]X"""
    return comp([(K(''), sg.m(2))], E)


# ---------------------------------------------------------------- comma code

def enc2(sg, E):
    """enc^2_x(S) = [xc_1/c_1]...[xc_M/c_M][xx/x] S  (the [xx/x] runs FIRST)"""
    passes = [(K(''), K(''))]  # placeholder, replaced below
    run = [(sg.x + sg.x, sg.x)]                                  # [xx/x]
    for c in reversed(sg.others):
        run.append((sg.x + c, c))                                # [xc/c]
    return pipe(run, E)


def dec2(sg, E):
    """dec^2_x(S) = [x/xx][c_M/xc_M]...[c_1/xc_1] S  (the [c_1/xc_1] runs
    FIRST, the halving [x/xx] runs LAST)."""
    run = []
    for c in sg.others:
        run.append((c, sg.x + c))                                # [c/xc]
    run.append((sg.x, sg.x + sg.x))                              # [x/xx]
    return pipe(run, E)


# ---------------------------------------------------------------- cat

def cat(sg, E1, E2):
    """cat(X,Y) = dec([enc(X)/xb^2][enc(Y)/xb^3](xb^2 xb^3))  (Thm thm:cat).
    The [enc(Y)/xb^3] pass runs FIRST."""
    T0 = K(sg.m(2) + sg.m(3))
    return dec(sg, comp([(enc(sg, E1), sg.m(2)), (enc(sg, E2), sg.m(3))], T0))


# ---------------------------------------------------------------- head / tail

def tail(sg, E):
    """tail(X) = dec( prod [eps/..] (b b enc(X)) ),  Thm thm:headtail.
    Paper order: [eps/bb][eps/bbx][eps/bbxb](bb enc X) with the rightmost
    running first; for general Sigma the product over i=3..N of [eps/bb c_i]
    runs before those."""
    # paper order (left-to-right in the theorem statement; rightmost runs
    # first):  [eps/bb][eps/bbx][eps/bbxb] (prod_i [eps/bb c_i]) (bb enc X)
    passes = [(K(''), sg.b + sg.b),                            # eps/bb (listed first, runs LAST)
              (K(''), sg.b + sg.b + sg.x)]                      # eps/bbx
    for c in reversed(sg.sigma[2:]):
        passes.append((K(''), sg.b + sg.b + c))                # prod eps/bb c_i
    passes.append((K(''), sg.b + sg.b + sg.x + sg.b))           # eps/bbxb (runs first)
    T0 = C(K(sg.b + sg.b), enc(sg, E))                         # bb enc(X)
    return dec(sg, comp(passes, T0))


def head(sg, E):
    """head(X) = dec([eps / enc(tail X) bb](enc(X) bb))"""
    pat = C(enc(sg, tail(sg, E)), K(sg.b + sg.b))
    return dec(sg, comp([(K(''), pat)], C(enc(sg, E), K(sg.b + sg.b))))


# ---------------------------------------------------------------- eq / if

def eq(sg, E1, E2):
    """eq(X,Y) = [bot/benc(X)][top/benc(Y)](benc(X))  (Thm Equality);
    the [top/benc(Y)] pass runs FIRST."""
    return comp([(sg.bot, benc(sg, E1)), (sg.top, benc(sg, E2))],
                benc(sg, E1))


def if_(sg, Cnd, X, Y):
    """if(C,X,Y) = dec([enc(Y)/bb]([enc(X)/top][bb/bot]C))  (Thm Selection).
    Run order: [bb/bot] first, then [enc(X)/top], then [enc(Y)/bb]."""
    return dec(sg, comp([(enc(sg, Y), sg.b + sg.b),
                         (enc(sg, X), sg.top),
                         (sg.b + sg.b, sg.bot)], Cnd))


def isne(sg, E):
    """isne(X) = top iff X != eps  (a total L-expression)."""
    return if_(sg, eq(sg, E, K('')), K(sg.bot), K(sg.top))


def contains(sg, E, B):
    """contains(X,B) = top iff B occurs in X, for CONSTANT B != eps.
    [M/B]X = X iff B does not occur in X, for any constant M != B
    (Substitution Elimination gives one direction; if the pass fires, the
    matched site is rewritten to M != B, so the string changes)."""
    assert B
    M = 'a' if B[0] != 'a' else 'b'
    assert M != B
    return if_(sg, eq(sg, E, comp([(M, B)], E)), K(sg.bot), K(sg.top))


# ---------------------------------------------------------------- the gates

def sel_body(sg):
    """The body of the two-way lazy selector sel (REPORT.md Sec. 3):

        sel(C,u,v) = dec2( [enc2(v)/Q][enc2(u)/P] if(C,P,Q) )

    with P = bbx, Q = xbb (both contain bb, P not< Q, Q not< P).  The run
    order is: the [enc2(u)/P] pass FIRST, then [enc2(v)/Q].

    Variables: X1 = condition, X2 = 'then' branch, X3 = 'else' branch.
    Forcing discipline (this is the whole point):
      - X1 is forced (it is the scrutinee of the if);
      - X2 is forced ONLY IF the gate is open  (P occurs);
      - X3 is forced ONLY IF the gate is closed (Q occurs);
      - the branch that IS forced is returned VERBATIM
        (dec2(enc2(t)) = t by the Comma Code Lemma).
    """
    Pp, Q = sg.P_GATE, sg.Q_GATE
    gate = if_(sg, V(0), K(Pp), K(Q))
    inner = comp([(enc2(sg, V(1)), Pp)], gate)     # [enc2(X2)/P] gate   (runs 1st)
    outer = comp([(enc2(sg, V(2)), Q)], inner)     # [enc2(X3)/Q] ...    (runs 2nd)
    return dec2(sg, outer)


def gate1_body(sg, step, base):
    """One-way gate (not needed given sel, kept for the report's discussion):

        F(X) = [ B(X, F(tail X)) / P ] if(isne X, P, base)
    is UNSOUND as a scheme in general (the base value may contain P); the
    sound one-way form is just sel.  This builder exists to DEMONSTRATE the
    unsoundness on a toy case in the verification sweep."""
    raise NotImplementedError("see verify_round2: demonstrated unsound directly")

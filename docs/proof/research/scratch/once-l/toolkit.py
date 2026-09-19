# Verify once-calculus constructions: cat, tail, head, iseps, eq, if.
# Expression AST per the paper's Definition (Substitution Expressions), once-flavored.
import itertools, sys

class Var:
    __slots__=("i",)
    def __init__(s,i): s.i=i
class Const:
    __slots__=("s",)
    def __init__(s,s_): s.s=s_
class Cat:
    __slots__=("a","b")
    def __init__(s,a,b): s.a, s.b = a, b
class Once:
    __slots__=("R","P","E")
    def __init__(s,R,P,E): s.R, s.P, s.E = R, P, E

def ev(e, args):
    if isinstance(e, Var): return args[e.i]
    if isinstance(e, Const): return e.s
    if isinstance(e, Cat): return ev(e.a,args) + ev(e.b,args)
    if isinstance(e, Once):
        R = ev(e.R,args); P = ev(e.P,args); T = ev(e.E,args)
        if P == "": raise ValueError("empty pattern")
        return T.replace(P, R, 1)
    raise Exception("?")

# ---------- constructions (all core: no Cat nodes used except inside Once args? NOTE:
# We allow Cat nodes for building patterns; cat itself is eliminable, cf. catE) ----------
def catE(i, j, a, b):   # cat(X_i, X_j) = [X_i/a]_1 [X_j/b]_1 (ab)
    return Once(Var(i), Const(a), Once(Var(j), Const(b), Const(a+b)))

def dbl_marker_check(SIG):
    """Lemma: if X != eps and XX*s in XXX then s == X[0]. Also: XX*X[0] occurs at 0."""
    bad = []
    for n in range(1, 8):
        for X in map("".join, itertools.product(SIG, repeat=n)):
            T = X*3
            for s in SIG:
                if X+X+s in T and s != X[0]:
                    bad.append((X, s))
            if X[0] and (X+X+X[0]) not in T[:len(X+X+X[0])]:
                bad.append(("no-match-at-0", X))
    return bad

def tailE(SIG):
    """tail(X) = prod_sigma [eps/XX*sigma]_1 (XXX). Patterns computed from input X."""
    T = catE(0,0,'a','b')            # will be composed; placeholder replaced below
    # build XXX via cat of cat
    XX = Cat(Var(0), Var(0))
    T3 = Cat(Cat(Var(0), Var(0)), Var(0))
    e = T3
    for s in SIG:
        pat = Cat(Cat(Var(0), Var(0)), Const(s))
        e = Once(Const(""), pat, e)
    return e

def headE(SIG, d):
    """head(X) = [eps / tail(X)*X*d]_1 (X*X*d)."""
    tail = tailE(SIG)
    pat = Cat(Cat(tail, Var(0)), Const(d))
    T = Cat(Cat(Var(0), Var(0)), Const(d))
    return Once(Const(""), pat, T)

def isepsE(top, bot, d):
    """iseps(X) = [bot/d]_1 [top/X*d]_1 (d)."""
    inner = Once(Const(top), Cat(Var(0), Const(d)), Const(d))
    return Once(Const(bot), Const(d), inner)

def eqE(top, bot, d):
    """eq(X,Y): eqind = [bot / X*YY*bot*d]_1 (Y*YY*bot*d); eq = [top/eqind]_1 (bot)."""
    eqind = Once(Const(bot),
                 Cat(Cat(Var(0), Cat(Var(1), Var(1))), Const(bot+d)),
                 Cat(Cat(Var(1), Cat(Var(1), Var(1))), Const(bot+d)))
    return Once(Const(top), eqind, Const(bot))

def ifE(top, bot, d):
    """if(C,X,Y) = [Y/(bot d X d Y d)]_1 [X/(top d X d Y d)]_1 (C d X d Y d)."""
    T = Cat(Cat(Var(0), Const(d)), Cat(Var(1), Const(d)))
    T = Cat(T, Cat(Var(2), Const(d)))
    p1 = Cat(Cat(Const(top), Const(d)), Cat(Var(1), Const(d)))
    p1 = Cat(p1, Cat(Var(2), Const(d)))
    p2 = Cat(Cat(Const(bot), Const(d)), Cat(Var(1), Const(d)))
    p2 = Cat(p2, Cat(Var(2), Const(d)))
    return Once(Var(2), p2, Once(Var(1), p1, T))

def domain(SIG, n):
    return ["".join(t) for k in range(n+1) for t in itertools.product(SIG, repeat=k)]

def run(SIG, tag):
    print(f"--- {tag}: SIGMA={SIG} ---")
    a, b = SIG[0], SIG[1]
    # cat
    D = domain(SIG, 3)
    bad = [(X,Y) for X in D for Y in D if ev(catE(0,1,a,b), (X,Y)) != X+Y]
    print("cat [X/a]_1[Y/b]_1(ab)      :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # doubled marker lemma
    bad = dbl_marker_check(SIG)
    print("Doubled-Marker Lemma          :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # tail
    D = domain(SIG, 6)
    bad = [(X, ev(tailE(SIG), (X,))) for X in D if ev(tailE(SIG), (X,)) != X[1:]]
    print("tail (XXX, del XX*sigma)      :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # order-independence of tail passes
    import itertools as it
    if len(SIG) <= 3:
        perms = list(it.permutations(SIG))
        bad2 = []
        for X in domain(SIG, 5):
            T3 = Cat(Cat(Var(0), Var(0)), Var(0))
            for perm in perms:
                e = T3
                for s in perm:
                    e = Once(Const(""), Cat(Cat(Var(0), Var(0)), Const(s)), e)
                if ev(e, (X,)) != X[1:]: bad2.append((X, perm))
        print("tail pass-order independence  :", "OK" if not bad2 else ("BAD " + str(bad2[:3])))
    # head
    for d in SIG:
        D = domain(SIG, 6)
        bad = [X for X in D if ev(headE(SIG, d), (X,)) != X[:1]]
        print(f"head (d={d})                  :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # whole-string self-match (used for doubling): [R/X]_1 X = R
    D = domain(SIG, 4)
    bad = [X for X in D if X and ev(Once(Cat(Var(0),Var(0)), Var(0), Var(0)), (X,)) != X+X]
    print("[XX/X]_1 X = XX (doubling)    :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # iseps
    top, bot, d = SIG[0], SIG[1], SIG[-1]
    D = domain(SIG, 6)
    bad = [X for X in D if ev(isepsE(top, bot, d), (X,)) != (top if X=="" else bot)]
    print(f"iseps (top={top},bot={bot},d={d}):", "OK" if not bad else ("BAD " + str(bad[:3])))
    # eq
    D = domain(SIG, 4)
    bad = [(X,Y) for X in D for Y in D if ev(eqE(top,bot,d), (X,Y)) != (top if X==Y else bot)]
    print("eq                            :", "OK" if not bad else ("BAD " + str(bad[:3])))
    # if
    bad = []
    for C in (top, bot):
        for X in D:
            for Y in domain(SIG,2):
                if ev(ifE(top,bot,d), (C,X,Y)) != (X if C==top else Y):
                    bad.append((C,X,Y,ev(ifE(top,bot,d),(C,X,Y))))
    print("if                            :", "OK" if not bad else ("BAD " + str(bad[:3])))

if __name__ == "__main__":
    run("ab", "2-char alphabet")
    run("abc", "3-char alphabet")

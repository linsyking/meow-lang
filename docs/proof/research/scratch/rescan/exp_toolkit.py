"""Experiment 3: the paper's toolkit under V = [A/B]^u.

Sigma = {sigma1, sigma2} = {b, x} with b='a', x='b' (2-letter alphabet).
Paper constructions, each node executed as an UNSAFE node:
  enc  = [x.b / b]        dec  = [b / x.b]
  cat  = dec [E_X/xb2][E_Y/xb3] (xb2 xb3)
  tail, head, eq, if: as in the paper (Section 2).
Census: for each, count ok / diverged / wrong on all inputs up to length 5-6.

Also: length bound |[A/B]^u C| <= |C|*(1+|A|) for B not-in A (verify).
"""
import itertools
from substlib import eq_unsafe, all_strings

CAP = 500
b, x = "a", "b"          # sigma1, sigma2
TOP, BOT = "b", "a"      # for eq/if we need distinct chars; over Sigma={a,b} use b,a


def U(A, B_, C):
    return eq_unsafe(A, B_, C, CAP)


def enc(S):
    return U(x + b, b, S)


def dec(S):
    return U(b, x + b, S)


def cat_paper(X, Y):
    xb2, xb3 = x + b + b, x + b + b + b
    s = xb2 + xb3
    s = U(enc(Y), xb3, s)
    if s == "DIVERGE":
        return "DIVERGE"
    s = U(enc(X), xb2, s)
    if s == "DIVERGE":
        return "DIVERGE"
    return dec(s)


def cat_direct(X, Y):
    """with-concat version: dec([enc(X)/xb2][enc(Y)/xb3](xb2 xb3)) -- same as above."""
    return cat_paper(X, Y)


def tail_paper(X):
    """tail(X) = dec( [e/ss1][e/ss1s2][e/ss1s2s1] (prod [e/ss1s1si]) (s1s1 enc(X)) )
    with s1=b='a', s2=x='b'; N=2 so the product over i=3..N is empty."""
    s1, s2 = b, x
    T = s1 + s1 + enc(X)
    if T == "DIVERGE":
        return "DIVERGE"
    for pat in [s1 + s1 + s2 + s1, s1 + s1 + s2, s1 + s1]:
        T = U("", pat, T)
        if T == "DIVERGE":
            return "DIVERGE"
    return dec(T)


def head_paper(X):
    """head(X) = dec( [e/(enc(tail(X)) s1s1)] (enc(X) s1s1) )"""
    s1 = b
    t = tail_paper(X)
    if t == "DIVERGE":
        return "DIVERGE"
    et = enc(t)
    if et == "DIVERGE":
        return "DIVERGE"
    ex = enc(X)
    if ex == "DIVERGE":
        return "DIVERGE"
    T = U("", et + s1 + s1, ex + s1 + s1)
    if T == "DIVERGE":
        return "DIVERGE"
    return dec(T)


def benc(X):
    xb2 = x + b + b
    e = enc(X)
    if e == "DIVERGE":
        return "DIVERGE"
    return xb2 + e + xb2


def eq_paper(X, Y):
    bx, by = benc(X), benc(Y)
    if bx == "DIVERGE" or by == "DIVERGE":
        return "DIVERGE"
    s = U(TOP, by, bx)
    if s == "DIVERGE":
        return "DIVERGE"
    return U(BOT, bx, s)


def if_paper(C, X, Y):
    """if(C,X,Y) = dec( [enc(Y)/bb] ([enc(X)/top][bb/bot] C) ), top != b required.
    top='b', bot='a', b='a'?? paper needs top != b: with Sigma={a,b}, b='a': top='b' ok, bot must
    differ from top: bot='a' = b. The paper's if has hypothesis top != b; bot can be anything
    distinct from top. Use top='b', bot='a'."""
    s = U(BOT + BOT, BOT, C)  # [bb/bot]
    if s == "DIVERGE":
        return "DIVERGE"
    s = U(enc(X), TOP, s)
    if s == "DIVERGE":
        return "DIVERGE"
    s = U(enc(Y), BOT + BOT, s)
    if s == "DIVERGE":
        return "DIVERGE"
    return dec(s)


def census(name, fn, argss, wanted):
    ok = div = wrong = 0
    ex = None
    for args in argss:
        r = fn(*args)
        w = wanted(*args)
        if r == "DIVERGE":
            div += 1
            if ex is None:
                ex = ("DIV", args)
        elif r != w:
            wrong += 1
            if ex is None:
                ex = ("WRONG", args, r, w)
        else:
            ok += 1
    print(f"{name}: ok={ok} diverged={div} wrong={wrong} first-failure={ex}")
    return ok, div, wrong


if __name__ == "__main__":
    Cs = all_strings("ab", 5)
    Pairs = [(X, Y) for X in Cs for Y in Cs if len(X) + len(Y) <= 6]

    census("enc alone (should be: DIVERGE iff b in S, else S)", enc, [(s,) for s in Cs],
           lambda s: "DIVERGE" if b in s else s)
    census("dec alone (= safe dec)", dec, [(s,) for s in Cs], lambda s: __import__("substlib").subst_safe(b, x + b, s))

    census("cat (paper Thm) = XY", cat_paper, Pairs, lambda X, Y: X + Y)

    census("tail (paper) = X minus head", [(s,) for s in Cs if s], lambda s: s[1:], ) if False else None
    census("tail (paper)", tail_paper, [(s,) for s in Cs], lambda s: ("" if not s else s[1:]))
    census("head (paper)", head_paper, [(s,) for s in Cs], lambda s: ("" if not s else s[0]))
    census("eq (paper)", eq_paper, Pairs, lambda X, Y: TOP if X == Y else BOT)
    census("if (paper)", if_paper, [(c, X, Y) for c in [TOP, BOT] for X, Y in Pairs],
           lambda c, X, Y: X if c == TOP else Y)

    # length bound check: for B notin A, |[A/B]^u C| <= |C|*(1+|A|)
    viol = []
    for A in ["".join(p) for n in range(0, 4) for p in itertools.product("ab", repeat=n)]:
        for B_ in ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]:
            if B_ in A:
                continue
            for C in all_strings("ab", 6):
                r = U(A, B_, C)
                if r == "DIVERGE":
                    viol.append(("DIVERGE despite B notin A", A, B_, C))
                    continue
                if len(r) > len(C) * (1 + len(A)):
                    viol.append((A, B_, C, len(r)))
    print(f"length bound |out| <= |C|(1+|A|) for B notin A: {'OK' if not viol else viol[:5]}")

    # also check the sharper step-derived bound |out| <= |C| + (|C|+1-|B|)*(|A|-|B|)^+
    viol2 = []
    for A in ["".join(p) for n in range(0, 4) for p in itertools.product("ab", repeat=n)]:
        for B_ in ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]:
            if B_ in A:
                continue
            for C in all_strings("ab", 6):
                r = U(A, B_, C)
                if r == "DIVERGE":
                    continue
                bound = len(C) + max(0, len(C) + 1 - len(B_)) * max(0, len(A) - len(B_))
                if len(r) > bound:
                    viol2.append((A, B_, C, len(r), bound))
    print(f"sharper bound |out| <= |C|+(|C|+1-|B|)(|A|-|B|)^+: {'OK' if not viol2 else str(len(viol2)) + ' violations e.g. ' + str(viol2[:5])}")

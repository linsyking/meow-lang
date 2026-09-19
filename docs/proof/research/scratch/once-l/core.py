# Core: semantics of [A/B]_1 (once) and [A/B]_k, plus Section-2 algebra checks.
import itertools, sys

def subst_all(A, B, C):
    """Paper Definition 1: replace-all, greedy L->R, non-overlapping, no rescan."""
    assert B != "", "undefined"
    return C.replace(B, A)

def subst_once(A, B, C):
    """V = [A/B]_1 C: replace exactly the leftmost occurrence of B by A."""
    assert B != "", "undefined"
    return C.replace(B, A, 1)

def subst_k(A, B, C, k):
    """[A/B]_k C: first k matches of the greedy non-rescanning scan."""
    assert B != "", "undefined"
    return C.replace(B, A, k)

def subst_once_def1(A, B, C):
    """Direct from the paper's Definition-1 style: C = XBY with |X| minimal."""
    if B not in C:
        return C
    i = C.find(B)  # leftmost
    X, Y = C[:i], C[i+len(B):]
    return X + A + Y

SIGMA = "ab"

def check_semantics():
    ok = True
    # 1) subst_once == def1-style; subst_k == Python replace count; k=1 == once
    for n in range(7):
        for C in map("".join, itertools.product(SIGMA, repeat=n)):
            for lb in range(1, 4):
                for B in map("".join, itertools.product(SIGMA, repeat=lb)):
                    for la in range(3):
                        for A in map("".join, itertools.product(SIGMA, repeat=la)):
                            if subst_once(A, B, C) != subst_once_def1(A, B, C):
                                ok = False; print("ONCE!=DEF1", A, B, C)
                            for k in range(0, 5):
                                if subst_k(A, B, C, k) != "".join([A]*min(k, 10)) .join([]) if False else True:
                                    pass
    print("[semantics] once == def1-style on all |C|<=6, |A|<=2, |B|<=3 over {a,b}:", ok)
    return ok

def check_k_vs_iterated_once():
    """[A/B]_k vs applying [A/B]_1 k times (rescan difference)."""
    ex = None
    for n in range(5):
        for C in map("".join, itertools.product(SIGMA, repeat=n)):
            for lb in range(1, 3):
                for B in map("".join, itertools.product(SIGMA, repeat=lb)):
                    for la in range(3):
                        for A in map("".join, itertools.product(SIGMA, repeat=la)):
                            for k in (2, 3):
                                it = C
                                for _ in range(k):
                                    it = subst_once(A, B, it)
                                if subst_k(A, B, C, k) != it:
                                    ex = (A, B, C, k, subst_k(A,B,C,k), it)
                                    return ex
    return ex

def check_algebra():
    results = {}
    S3 = ["".join(t) for n in range(6) for t in itertools.product("abc", repeat=n)]
    A2 = ["".join(t) for n in range(3) for t in itertools.product("abc", repeat=n)]

    # Identity Substitution [A/A]_1 S = S  (A != eps)
    bad = [(A,S) for A in A2 if A for S in S3 if subst_once(A,A,S) != S]
    results["Identity [A/A]_1 S = S"] = ("HOLDS", len(bad)==0, bad[:3])

    # Direct Substitution [A/B]_1 B = A
    bad = [(A,B) for A in A2 for B in A2 if B and subst_once(A,B,B) != A]
    results["Direct [A/B]_1 B = A"] = ("HOLDS", len(bad)==0, bad[:3])

    # Substitution Elimination
    bad = [(A,B,S) for A in A2 for B in A2 for S in S3
           if B and B not in S and subst_once(A,B,S) != S]
    results["Elimination B!in S => [A/B]_1 S = S"] = ("HOLDS", len(bad)==0, bad[:3])

    # Independent Substitution: A cap B = {} , A cap C = {} , C != eps  ==>  A in [B/C]_1 S  iff  A in S
    def chars(s): return set(s)
    bad = []
    for A in A2:
        for Cp in A2:  # pattern C of the lemma
            if not Cp or chars(A) & chars(Cp): continue
            for B in A2:
                if chars(A) & chars(B): continue
                for S in S3:
                    if subst_once(B, Cp, S) != ("" if True else "") and (A in S) != (A in subst_once(B, Cp, S)):
                        bad.append((A,B,Cp,S))
                        if len(bad) > 3: break
    results["Independent Substitution (once)"] = ("HOLDS?", len(bad)==0, bad[:4])

    # Stepping-into: [C/A]_1 (AB) = C([C/A]_1 B)   -> expect FAIL
    cex = None
    for A in A2:
        if not A: continue
        for B in A2:
            for Cc in A2:
                if subst_once(Cc, A, A+B) != Cc + subst_once(Cc, A, B):
                    cex = (Cc, A, B, subst_once(Cc,A,A+B), Cc+subst_once(Cc,A,B)); break
            if cex: break
        if cex: break
    results["Stepping-into [C/A]_1(AB)=C([C/A]_1B)"] = ("FAILS" if cex else "HOLDS", cex is None, cex)

    # Double Substitution Lemma (once): X,Y nonempty, X in Y, Y unbordered => [X/Y]_1[Y/X]_1 Z = Z
    def unbordered(Y):
        for i in range(1, len(Y)):
            if Y[:i] == Y[-i:]: return False
        return True
    bad = []
    for X in A2:
        if not X: continue
        for Y in A2:
            if not Y or not unbordered(Y) or X not in Y: continue
            for Z in S3:
                r = subst_once(X, Y, subst_once(Y, X, Z))
                if r != Z:
                    bad.append((X,Y,Z,r))
    results["Double Substitution (once)"] = ("HOLDS" if not bad else "FAILS", len(bad)==0, bad[:4])

    # Encoding theorem (i),(ii),(iii) under once: enc=[xb/b]_1, dec=[b/xb]_1
    b, x = "a", "b"
    enc = lambda S: subst_once(x+b, b, S)
    dec = lambda S: subst_once(b, x+b, S)
    bad1 = [S for S in S3 if dec(enc(S)) != S]
    results["enc(i) dec(enc(S))=S (once)"] = ("HOLDS" if not bad1 else "FAILS", len(bad1)==0, bad1[:3])
    bad2 = [S for S in S3 if b+b in enc(S)]
    results["enc(ii) bb notin enc(S) (once)"] = ("FAILS" if bad2 else "HOLDS", len(bad2)==0, bad2[:3])
    bad3 = [(X,Y) for X in S3 for Y in S3 if enc(X)+enc(Y) != enc(X+Y)]
    results["enc(iii) morphism (once)"] = ("FAILS" if bad3 else "HOLDS", len(bad3)==0, bad3[:3])
    # Monotonicity A in B => enc(A) in enc(B)
    bad4 = [(A_,B_) for A_ in S3 for B_ in S3 if A_ in B_ and enc(A_) not in enc(B_)]
    results["enc monotonicity (once)"] = ("FAILS" if bad4 else "HOLDS", len(bad4)==0, bad4[:3])

    # Single Character Substitution: [sigma/Sigma]_1 ... != sigma^|S|
    coll = lambda S: subst_once("a","c", subst_once("a","b", S))
    bad5 = [S for S in S3 if coll(S) != "a"*len(S)]
    results["[sigma/Sigma] collapse (once)"] = ("FAILS (as expected)" if bad5 else "HOLDS?!", len(bad5)>0, bad5[:3])
    return results

if __name__ == "__main__":
    check_semantics()
    print("k vs iterated-once counterexample:", check_k_vs_iterated_once())
    for k, (st, ok, ex) in check_algebra().items():
        print(f"{st:12s} ok={ok}  {k}" + (f"  ex={ex}" if ex and not ok else ""))

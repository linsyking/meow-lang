# verify_constructions.py -- verify every claimed PROVEN construction, exhaustively
# on small domains.
import itertools, sys
sys.path.insert(0, '.')
from poslib import *

def allstr(alf, maxlen):
    for n in range(maxlen+1):
        for tup in itertools.product(alf, repeat=n):
            yield "".join(tup)

fails = []
def check(name, cond, detail=""):
    if not cond:
        fails.append((name, detail))
        print("FAIL:", name, detail)

# ============ 1. paper's L machinery sanity (needed for the setAt-in-L claim) ============
for S in allstr("abc", 4):
    check("enc/dec roundtrip", dec(enc(S)) == S, S)
for S in allstr("abc", 4):
    for T in allstr("abc", 3):
        check("cat", catL(S, T) == S+T, (S,T))
        check("eq", eqL(S, T) == ('c' if S==T else 'd'), (S,T))
for S in allstr("ab", 5):
    check("tailL", tailL(S) == S[1:], S)
    check("headL", headL(S) == S[:1], S)
for C in "cd":
    for A in allstr("ab",2):
        for B in allstr("ab",2):
            check("ifL", ifL(C, A, B) == (A if C=='c' else B), (C,A,B))

# ============ 2. setAt(i,c) in the baseline L (Theorem: construction) ============
for i in range(4):
    for S in allstr("ab", 5):
        check("setAtL", setAtL(i, 'a', S) == setAt(i, 'a', S), (i, S))

# ============ 3. pos-side constructions ============
# tail: 2 LITERAL nodes, total on every alphabet (c = any char of the alphabet)
def tailE(c):
    return ('repocc', 0, ('const',''), ('const',c), ('setat', 0, ('const',c), X1))
for alf, mx in [("ab", 6), ("abc", 5), ("a", 8), ("abcd", 4)]:
    for c in alf:
        for S in allstr(alf, mx):
            check("tail_pos", ev(tailE(c), (S,)) == S[1:], (alf, c, S))

# head in pos WITH CONCAT, total:
#   T = repOcc(0, eps, tail(X.S), X.S)              [S = "dwd", gives X[0] or residue]
#   E = repOcc(0, eps, tail(tail(X.S)), T)
def headE(S="dwd"):
    XS = ('cat', X1, ('const', S))
    T  = ('repocc', 0, ('const',''), ('repocc',0,('const',''),('const','b'),
                         ('setat',0,('const','b'),XS)), XS)   # repOcc(0,eps,tail(XS),XS)
    P2 = ('repocc',0,('const',''),('const','b'),
          ('setat',0,('const','b'),('repocc',0,('const',''),('const','b'),
           ('setat',0,('const','b'),XS))))                     # tail(tail(XS))
    return ('repocc', 0, ('const',''), P2, T)
for alf, mx in [("ab", 6), ("abc", 5), ("a", 8), ("abcd", 4), ("d", 8)]:
    for S in allstr(alf, mx):
        check("head_pos_cat", ev(headE(), (S,)) == S[:1], (alf, S))

# join two computed single chars via 2-char scaffold (pos_lit_core)
def join2(R1, R2):
    return ('setat', 0, R1, ('setat', 1, R2, ('const',"uv")))
for c1 in "pq":
    for c2 in "pq":
        check("join2", ev(join2(('const',c1), ('const',c2)), ()) == c1+c2)

# char_j / prefix_j / truncate_j in pos WITH concat (uses headE, tailE, cat)
def headV(V):   # head of arbitrary sub-expression V (as expression)
    return None
def tailx(e):   # tail as expression
    return ('repocc', 0, ('const',''), ('const','b'), ('setat', 0, ('const','b'), e))
def headx(e):   # head as expression (pos_concat construction, scaffold "dwd")
    eS = ('cat', e, ('const', "dwd"))
    T  = ('repocc', 0, ('const',''), tailx(eS), eS)
    P2 = tailx(tailx(eS))
    return ('repocc', 0, ('const',''), P2, T)
def charx(j, e):
    for _ in range(j):
        e = tailx(e)
    return headx(e)
def prefixx(j):
    e = ('const','')
    for t in range(j):
        e = ('cat', e, charx(t, X1))
    return e
for j in range(4):
    for S in allstr("ab", 5):
        check("charj", ev(charx(j, X1), (S,)) == (S[j] if j < len(S) else ""), (j,S))
        check("prefixj", ev(prefixx(j), (S,)) == S[:j], (j,S))

# setAt-last via computed index |tail(X)| = |X|-1  (pos_idx)
setat_last = ('setatI', tailE('b'), ('const','z'), X1)
for S in allstr("ab", 6):
    check("setAt-last", ev(setat_last, (S,)) == (S[:-1]+'z' if S else S), S)

# ============ 4. repOcc(k,B,A) == once_l-marker composition (2k+1 nodes) ============
def repocc_via_once(k, B, A, S, M="ZZ"):
    T = S
    for _ in range(k):
        T = once_l(B, M, T)
    T = once_l(B, A, T)
    for _ in range(k):
        T = once_l(M, B, T)
    return T
for k in range(4):
    for B in ["a","b","ab","ba","aa","bb","aba"]:
        for A in ["", "X", "ab", "bbb"]:
            for S in allstr("ab", 5):
                if "ZZ" in S or "ZZ" in A or "ZZ" in B:
                    continue
                check("repocc<=once", repocc_via_once(k,B,A,S) == repOcc(k,B,A,S), (k,B,A,S))

# repOcc(0,A,B)^m = replace-first-m  when B not substring of A
def firstm(S, B, A, m):
    out, p, c = "", 0, 0
    while c < m:
        j = S.find(B, p)
        if j < 0: break
        out += S[p:j] + A
        p = j + len(B)
        c += 1
    return out + S[p:]
for m in range(4):
    for B in ["a","b","ab","ba"]:
        for A in ["X","XY","QW","XYZW"]:
            if set(B) & set(A): continue      # disjoint alphabets
            if len(A) < len(B): continue      # |A| >= |B| blocks C0.C1 merging
            for S in allstr("ab",5):
                T = S
                for _ in range(m):
                    T = repOcc(0, B, A, T)
                check("repfirst-m", T == firstm(S,B,A,m), (m,B,A,S))

# ============ 5. pos_idx simulation of f(X,Y)=replace the (|Y|+1)-th 'a' on unary X
def f_sim(X, Y):
    # step1: repOcc(0, Y.a, Y.M.a, X);  step2: repOcc(0, M.a, M, .)
    T = repOcc(0, Y + "a", Y + "M" + "a", X)
    return repOcc(0, "Ma", "M", T)
for n in range(9):
    for m in range(9):
        X, Y = "a"*n, "a"*m
        want = X
        occ = occurrences(X, "a")
        if m < len(occ):
            j = occ[m]
            want = X[:j] + "M" + X[j+1:]
        check("f-sim unary", f_sim(X,Y) == want, (n,m))

# ============ 6. stepping-in / rank-shift lemma ============
# repOcc(k, R, P, P.E) = P . repOcc(k-1, R, P, E) for k>=1 ; = R.E for k=0
for k in range(3):
    for P in ["a","ab","ba"]:
        for R in ["","X","ab"]:
            for E in allstr("ab",3):
                S = P + E
                lhs = repOcc(k, P, R, S)
                rhs = (P + repOcc(k-1, P, R, E)) if k >= 1 else (R + E)
                check("stepping-in", lhs == rhs, (k,P,R,E))

print("FAILURES:", len(fails))

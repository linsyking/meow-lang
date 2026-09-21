"""R1b: THE REDUCTION CLUSTER around 'delete the leftmost b', machine-verified
with ORACLE nodes.

Definitions (b = the character being deleted; over {a,b} we take b='b'):
  P(X)    = the longest b-free prefix        (takeWhile != b)
  Cut(X)  = X[i:] with i = first b           (everything from the first b on;
            eps when X has no b)
  D(X)    = X with the leftmost b deleted    (THE probe, = [eps/b]_1 X)

Claims verified here (all with P/Cut as ORACLE leaves -- i.e. these are
implications 'if the oracle function is L-reachable then so is the target'):

  R1  P   in L  ==>  D   in L     (anchored needle: A.enc2(P).B unique at 0)
  R2  Cut in L  ==>  P   in L      (Cut occurs exactly once in X: starts with
                                    b forces j >= i, suffix-length forces
                                    j <= i; empty-Cut guarded by pattern-guard
                                    junk, paper rem:total-rep style)
  R3  P   in L  ==>  Cut in L      (dec2([eps/A.enc2(P)](A.enc2(X))); needs
                                    no guard: no-b case degenerates to eps)
  R4  the TIE OBSTRUCTION, documented: the naive un-anchored P-needle
      [P/P.b] computes D on a^i b a^j b a^k EXACTLY when j < i (the second
      gap is shorter); it fails on every tie j >= i -- even with P as an
      oracle.  The anchor A is what breaks ties; the anchor needs P.

Oracle AST node: ('O', fn) evaluates fn(X).  Everything else is a genuine
L-expression over K/V/C/S with the rec/lazy_pass toolkit builders.
"""
import sys

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/rec/lazy_pass')

from core import K, V, C, S
import toolkit as LPTK
from oncecore import subst, binstrings, ternstrings, del1b

# ------------------------------------------------------------ oracle nodes


def O(fn):
    return ('O', fn)


def evalO(e, X):
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return X
    if t == 'O':
        return e[1](X)
    if t == 'C':
        return evalO(e[1], X) + evalO(e[2], X)
    if t == 'S':
        T = evalO(e[3], X)
        B = evalO(e[2], X)
        assert B != '', 'empty pattern'
        A = evalO(e[1], X)
        return subst(A, B, T)
    raise ValueError(t)


# ------------------------------------------------------------ the oracles

DELCHAR = 'b'          # the character whose leftmost occurrence we delete


def P_oracle(X):
    return X[:X.find(DELCHAR)] if DELCHAR in X else X


def Cut_oracle(X):
    return X[X.find(DELCHAR):] if DELCHAR in X else ''


def D_oracle(X):
    return del1b(X)


# ------------------------------------------------- binary construction setup
# comma char x = 'a', deleted char b = 'b':  enc2 blocks are 'a'+c; images
# have b-runs <= 1 (data 'b' always followed by comma 'a'); anchor A = 'bb'
# is therefore fresh in every enc2 image.  B = enc2('b') = 'ab'.

BIN = LPTK.Sig(['a', 'b'], 'b', 'a', 'a', 'b')    # sg.b='b' (DELCHAR), sg.x='a'
A_ANCH = BIN.b + BIN.b                             # 'bb'
B_BLK = BIN.x + DELCHAR                           # 'ab' = enc2 block of 'b'


def enc2(e):
    return LPTK.enc2(BIN, e)


def dec2(e):
    return LPTK.dec2(BIN, e)


def D_via_P():
    """D(X) = dec2( [eps/A]( [A.enc2(P) / A.enc2(P).B]( A.enc2(X) ) ) )."""
    Pat = C(C(K(A_ANCH), enc2(O(P_oracle))), K(B_BLK))
    Rep = C(K(A_ANCH), enc2(O(P_oracle)))
    scrut = C(K(A_ANCH), enc2(V(0)))
    return dec2(S(comp_pass(K(''), A_ANCH), S(Rep, Pat, scrut)))


def comp_pass(R, P):
    return S(R, P, None)  # placeholder, replaced below


# rebuild without helper (pass = S(Rep, Pat, scrut) then cleanup S(K(''), K(A)))
def D_via_P_expr():
    Pat = C(C(K(A_ANCH), enc2(O(P_oracle))), K(B_BLK))
    Rep = C(K(A_ANCH), enc2(O(P_oracle)))
    scrut = C(K(A_ANCH), enc2(V(0)))
    edited = S(Rep, Pat, scrut)                 # [Rep/Pat] scrut
    cleaned = S(K(''), K(A_ANCH), edited)       # [eps/A] edited
    return dec2(cleaned)


def Cut_via_P_expr():
    """Cut(X) = dec2( [eps/A.enc2(P)]( A.enc2(X) ) )."""
    Pat = C(K(A_ANCH), enc2(O(P_oracle)))
    scrut = C(K(A_ANCH), enc2(V(0)))
    return dec2(S(K(''), Pat, scrut))


def P_via_Cut_expr():
    """P(X) = [eps / Cut.if(eq(Cut,eps),'bb',eps)] X  (pattern-guarded).

    If X has a b: pattern = Cut (unique occurrence in X -> deletes it -> P).
    If not: Cut = eps, X in a*, pattern = 'bb' (occurs nowhere in a*) -> X.
    """
    G = LPTK.if_(BIN, LPTK.eq(BIN, O(Cut_oracle), K('')), K('bb'), K(''))
    Pat = C(O(Cut_oracle), G)
    return S(K(''), Pat, V(0))


# ------------------------------------------------------------------ checks

def check(name, expr, target, domain):
    bad = []
    for X in domain:
        got = evalO(expr, X)
        if got != target(X):
            bad.append((X, got, target(X)))
    print(f"{name}: {'OK' if not bad else 'FAIL'} on {len(domain)} inputs"
          + (f"; first fails: {bad[:5]}" if bad else ""))
    return not bad


if __name__ == '__main__':
    dom2 = binstrings(8)                       # 511 binary strings <= 8
    dom3 = ternstrings(6)                      # 1093 ternary strings <= 6
    ok = True
    ok &= check("R1  P |= D    (binary <=8)", D_via_P_expr(), D_oracle, dom2)
    ok &= check("R1  P |= D    (ternary <=6)", D_via_P_expr(), D_oracle, dom3)
    ok &= check("R3  P |= Cut  (binary <=8)", Cut_via_P_expr(), Cut_oracle, dom2)
    ok &= check("R3  P |= Cut  (ternary <=6)", Cut_via_P_expr(), Cut_oracle, dom3)
    ok &= check("R2  Cut |= P  (binary <=8)", P_via_Cut_expr(), P_oracle, dom2)
    ok &= check("R2  Cut |= P  (ternary <=6)", P_via_Cut_expr(), P_oracle, dom3)

    # R4: the tie obstruction on the 2-b family.
    fails, ties, total = [], 0, 0
    for i in range(0, 7):
        for j in range(0, 7):
            for k in range(0, 4):
                X = 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
                P = P_oracle(X)
                got = subst(P, P + 'b', X)         # [P/P.b]X, the naive needle
                want = del1b(X)
                total += 1
                if got != want:
                    fails.append((i, j, k))
                    if j >= i:
                        ties += 1
    print(f"R4  naive needle [P/P.b] on a^i b a^j b a^k ({total} inputs): "
          f"{len(fails)} failures, of which {ties} have j >= i "
          f"(ties-or-longer second gap)")
    if fails:
        bad_no_tie = [f for f in fails if f[1] < f[0]]
        print(f"    failures with j < i (should be NONE): {bad_no_tie}")
    print("ALL OK" if ok and not [f for f in fails if f[1] < f[0]] else "CHECK FAILURES")

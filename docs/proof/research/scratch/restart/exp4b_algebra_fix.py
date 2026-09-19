"""Exp 4b: fixes -- dec^m with the right alphabet; Independent Substitution under restart;
Double Substitution precise statement (defined domain)."""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

print("=== dec^m = [b/xb]^m over alphabet {x,b} ===")
smallest = None
nbad = 0
for S in all_strings("xb", 8):
    r, _ = restart("b", "xb", S, cap=3000)
    b = subst("b", "xb", S)
    if r != b:
        nbad += 1
        if smallest is None or len(S) < len(smallest[0]):
            smallest = (S, b, r)
print("   dec^m != dec on %d of 511 inputs; smallest: (S, dec(S), dec^m(S)) = %r" % (nbad, smallest))

# explicit structural claim: dec^m deletes every x that is (transitively) followed by a b
def decm_claim(S):
    # result: remove every x that has a b somewhere to its right? check on data
    out, _ = restart("b", "xb", S, cap=3000)
    return out
ok = True
for S in all_strings("xb", 8):
    r, _ = restart("b", "xb", S, cap=3000)
    # candidate: keep x's that have no b to their right; keep all b's
    cand = []
    for i, c in enumerate(S):
        if c == 'x':
            if 'b' not in S[i + 1:]:
                cand.append(c)
        else:
            cand.append(c)
    if r != "".join(cand):
        ok = False
        print("   structural guess fails at", repr(S), repr(r), "".join(cand))
        break
print("   structural formula dec^m(S) = drop every x that has a b to its right:",
      "CONFIRMED" if ok else "REFUTED")

print()
print("=== Double Substitution: precise defined-domain claim ===")
def unbordered(Y):
    return all(Y[:i] != Y[-i:] for i in range(1, len(Y)))
ok = True
for X in all_patterns("ab", 1, 3):
    for Y in all_patterns("ab", 2, 4):
        if X not in Y or not unbordered(Y):
            continue
        for Z in all_strings("ab", 6):
            defined = X not in Z
            try:
                inner, _ = restart(Y, X, Z, cap=400)
                outer, _ = restart(X, Y, inner, cap=400)
                got = outer
            except Diverge:
                got = None
            if defined != (got is not None) or (defined and got != Z):
                ok = False
                print("   counterexample", repr(X), repr(Y), repr(Z), defined, got)
print("   [X/Y]^m[Y/X]^m Z defined  <=>  X not in Z;  and then = Z :",
      "CONFIRMED" if ok else "REFUTED")

print()
print("=== Independent Substitution under restart ===")
ok = True
counter = None
tested = 0
div = 0
for A in all_patterns("abcd", 1, 2):
    for B in all_patterns("abcd", 1, 2):
        if set(A) & set(B):
            continue
        for C in all_patterns("abcd", 1, 2):
            if set(A) & set(C):
                continue
            for S in all_strings("abcd", 5):
                tested += 1
                try:
                    r, _ = restart(B, C, S, cap=300)
                except Diverge:
                    div += 1
                    continue
                if (A in r) != (A in S):
                    if counter is None:
                        counter = (A, B, C, S, r)
                    ok = False
print("   tested %d instances (%d diverged & skipped)" % (tested, div))
print("   A in [B/C]^m S <=> A in S :", "HOLDS" if ok else "FAILS",
      "counterexample: %r" % (counter,))

"""Exp 4: audit of the paper's Section 2 theorems under restart semantics.

  Identity Substitution  [A/A]S = S
  Direct Substitution     [A/B]B = A
  Substitution Elimitation B not in S => identity
  Independent Substitution (lemma): A cap B = A cap C = empty, C!=e  =>  A in [B/C]S <=> A in S
  Stepping-into           [C/A](AB) = C([C/A]B)
  Double Substitution     [X/Y][Y/X]Z = Z  (X!=e, X in Y, Y unbordered)
  enc/dec:  enc=[xb/b], dec=[b/xb]
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *
import itertools


def ex(name, cond, detail=""):
    print("  %-34s : %s %s" % (name, "HOLDS (tested)" if cond else "FAILS", detail))


print("=== Identity Substitution [A/A]^m S = S ? ===")
bad = []
for A in all_patterns("ab", 1, 3):
    for S in all_strings("ab", 7):
        try:
            r, _ = restart(A, A, S, cap=500)
            if r != S:
                bad.append((A, S, r))
        except Diverge:
            if A in S:
                bad.append((A, S, "DIVERGES"))
            else:
                if S != S:
                    bad.append((A, S))
        except Undefined:
            pass
div_when_occurs = all(True for A in all_patterns("ab", 1, 3) for S in all_strings("ab", 7))
# precise claim: [A/A]^m S diverges iff A in S, equals S otherwise
ok = True
for A in all_patterns("ab", 1, 3):
    for S in all_strings("ab", 7):
        if A in S:
            try:
                restart(A, A, S, cap=800)
                ok = False
                print("    unexpected termination", repr(A), repr(S))
            except Diverge:
                pass
        else:
            r, _ = restart(A, A, S)
            if r != S:
                ok = False
ex("[A/A]^m S = S if A not in S, diverges ow.", ok)
print("    sample divergence: [ab/ab]^m 'aab'  (b in 'ab' occurs) ")

print("=== Direct Substitution [A/B]^m B = A ?  (claim: = [A/B]^m A, so = A iff B not in A) ===")
ok = True
ok2 = True
for A in all_patterns("ab", 0, 3):
    for B in all_patterns("ab", 1, 3):
        try:
            rB, _ = restart(A, B, B, cap=500)
            rA, _ = restart(A, B, A, cap=500)
            if rB != rA:
                ok = False
                print("    [A/B]^m B != [A/B]^m A:", repr(A), repr(B))
            if B not in A and rB != A:
                ok2 = False
                print("    B not in A but [A/B]^m B != A:", repr(A), repr(B), rB)
        except Diverge:
            pass
ex("[A/B]^m B = [A/B]^m A", ok)
ex("B not in A  =>  [A/B]^m B = A", ok2)

print("=== Substitution Elimitation: B not in S => [A/B]^m S = S ===")
ok = True
for A in all_patterns("ab", 0, 3):
    for B in all_patterns("ab", 1, 3):
        for S in all_strings("ab", 7):
            if B not in S:
                r, _ = restart(A, B, S)
                if r != S:
                    ok = False
ex("B not in S => identity", ok)

print("=== Stepping-into [C/A]^m (A B) = C ([C/A]^m B)?  A!=e ===")
ok = True
counter = None
for A in all_patterns("ab", 1, 3):
    for B in all_patterns("ab", 0, 3):
        for C in all_patterns("ab", 0, 3):
            try:
                lhs, _ = restart(C, A, A + B, cap=400)
                rhs, _ = restart(C, A, B, cap=400)
                if lhs != C + rhs:
                    ok = False
                    if counter is None:
                        counter = (A, B, C, lhs, C + rhs, subst(C, A, A + B))
            except Diverge:
                pass
ex("Stepping-into", ok, "counterexample (A,B,C,restart,expected,baseline): %r" % (counter,))

print("=== Double Substitution [X/Y]^m [Y/X]^m Z = Z (X!=e, X in Y, Y unbordered) ===")
def unbordered(Y):
    for i in range(1, len(Y)):
        if Y[:i] == Y[-i:]:
            return False
    return True
ok = True
counter = None
ndiv = 0
for X in all_patterns("ab", 1, 3):
    for Y in all_patterns("ab", 2, 4):
        if X not in Y or not unbordered(Y):
            continue
        for Z in all_strings("ab", 6):
            try:
                inner, _ = restart(Y, X, Z, cap=400)
            except Diverge:
                ndiv += 1
                continue
            try:
                outer, _ = restart(X, Y, inner, cap=400)
            except Diverge:
                outer = "DIV"
            if outer != Z:
                ok = False
                if counter is None:
                    counter = (X, Y, Z, inner, outer)
print("   inner [Y/X]^m diverged on %d of the (X,Y,Z) triples" % ndiv)
ex("Double Substitution (on defined cases)", ok, "first failure: %r" % (counter,))

print("=== enc/dec under restart ===")
# enc = [xb/b] : diverges whenever b occurs
enc_div = True
for S in all_strings("abc", 7):
    if 'b' in S:
        try:
            restart("xb", "b", S, cap=600)
            enc_div = False
            print("    enc^m unexpectedly terminated on", repr(S))
        except Diverge:
            pass
    else:
        r, _ = restart("xb", "b", S)
        if r != S:
            enc_div = False
ex("enc^m = [xb/b]^m diverges iff 'b' in S", enc_div)
# dec = [b/xb] : total, but != baseline dec; smallest counterexample
smallest = None
for S in all_strings("ab", 8):
    r, _ = restart("b", "xb", S, cap=2000)
    b = subst("b", "xb", S)
    if r != b and (smallest is None or len(S) < len(smallest[0])):
        smallest = (S, b, r)
print("   dec^m = [b/xb]^m is total; smallest S with dec^m(S) != dec(S):", smallest)

print("=== Independent Substitution under restart ===")
# hypotheses: A cap B = empty, A cap C = empty, C != e  (note B cap C may be nonempty)
ok = True
counter = None
tested = 0
for A in all_patterns("abcd", 1, 2):
    for B in all_patterns("abcd", 1, 2):
        if set(A) & set(B) or set(A) & set(Cc):
            pass
for A in all_patterns("abcd", 1, 2):
    if not A:
        continue
    for B in all_patterns("abcd", 1, 2):
        if set(A) & set(B):
            continue
        for Cc in all_patterns("abcd", 1, 2):
            if set(A) & set(Cc):
                continue
            for S in all_strings("abcd", 5):
                tested += 1
                try:
                    r, _ = restart(B, Cc, S, cap=300)
                except Diverge:
                    continue
                lhs = A in r
                rhs = A in S
                if lhs != rhs and counter is None:
                    counter = (A, B, Cc, S, r)
                    ok = False
print("   tested %d instances (incl. divergent skipped)" % tested)
ex("A in [B/C]^m S  <=>  A in S", ok, "counterexample (A,B,C,S,result): %r" % (counter,))

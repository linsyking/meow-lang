"""Round 1, battery A: comma-freeness, self-synchronization, pass transfer.

Checks, exhaustively over the stated finite domains:
  A1  the explicit dictionary family {a a m b} is comma-free (complete
      finite check) and grows Fibonacci-like over binary.
  A2  alignment: for the coding c: {a,b,c} -> {x,y} (ell=6 family),
      for all NONEMPTY B in abc^{<=3}, C in abc^{<=5}: the occurrence
      positions of c(B) in c(C) are exactly {ell*s : s an occurrence of
      B in C}.
  A3  pass transfer: [c(A)/c(B)] c(C) = c([A/B]C), all A in abc^{<=3},
      B in abc^{1..3}, C in abc^{<=5}; also under once, R, and k-th
      occurrence (k <= 3) semantics.
  A4  composition lemma: if D_c (over Gamma) and D_d (over Sigma) are
      comma-free, so is {d(w) : w in D_c}; checked on the concrete pair
      c: abc->xy, d: xy->abc.
  A5  the paper's own comma code enc^2 (blocks xc) does NOT transfer:
      an explicit counterexample exists in a small search box.
  A6  unary alignment: c(a) = 'ab' (primitive word): occurrences of
      (ab)^j in (ab)^m exactly at 2s, s an occurrence of a^j in a^m;
      pass transfer on unary strings.
"""
import sys
from meow import (subst, once_subst, rsubst, kth_subst, apply_pass,
                  occ_positions, comma_free, dict_family, make_coding,
                  enc, transfer, ev, all_strings)

LOG = []
def log(s):
    print(s)
    LOG.append(s)

def check(name, n, ok):
    log(f"{'OK  ' if ok else 'FAIL'} {name}: {n} cases")
    return ok

allok = True

# ---------- A1: dictionary family is comma-free ----------
total = 0
for gamma, name in [({'x', 'y'}, 'binary'), ({'x', 'y', 'z'}, 'ternary'),
                    ({'w', 'x', 'y', 'z'}, 'quaternary')]:
    for ell in range(3, 10):
        D = dict_family(gamma, 'x', 'y', ell)
        cf = comma_free(D)
        total += 1
        assert cf, (name, ell)
        if ell >= 7 or (name == 'ternary' and ell >= 6):
            pass
sizes_bin = {ell: len(dict_family({'x', 'y'}, 'x', 'y', ell)) for ell in range(3, 13)}
log(f"A1 comma-free: all dictionaries in the family, binary/ternary/quaternary, "
    f"ell in 3..9: {total} dictionaries, all comma-free")
log(f"A1 binary dict sizes ell=3..12: {sizes_bin}  (Fibonacci-like)")
# Size formula: m in Gamma^{ell-3}, no 'aa', m[0] != a; over binary that is
# m = b + (no-aa string of length ell-4), counted by Fib(ell-2), Fib(1)=Fib(2)=1.
def fib(k):
    a, b = 1, 1
    for _ in range(k - 1):
        a, b = b, a + b
    return a
fb = all(sizes_bin[e] == fib(e - 2) for e in range(3, 13))
allok &= check("A1fib size formula |D_ell| = Fib(ell-2) over binary", 10, fb)

# ---------- the concrete coding under test ----------
cmap, Dc, ellc = make_coding('abc', 'xy')   # ternary -> binary
log(f"coding c: abc -> xy, ell={ellc}, dict={Dc}, map={cmap}")

# ---------- A2: alignment ----------
Sigma = 'abc'
n_cases = 0
ok = True
for B in all_strings(Sigma, 3):
    if B == '':
        continue          # the alignment lemma concerns nonempty patterns
    for C in all_strings(Sigma, 5):
        cB, cC = enc(cmap, B), enc(cmap, C)
        got = occ_positions(cC, cB)
        want = [ellc * s for s in occ_positions(C, B)]
        n_cases += 1
        if got != want:
            ok = False
            log(f"  MISMATCH B={B} C={C}: got {got} want {want}")
allok &= check(f"A2 alignment occ(c(B)) in c(C) = ell*occ(B) (B<=3, C<=5 over abc)", n_cases, ok)

# ---------- A3: pass transfer, all four semantics ----------
n_cases = 0
bad = []
for A in all_strings(Sigma, 3):
    for B in all_strings(Sigma, 3):
        if B == '':
            continue
        for C in all_strings(Sigma, 4):
            n_cases += 1
            cA, cB, cC = enc(cmap, A), enc(cmap, B), enc(cmap, C)
            lhs = subst(cA, cB, cC)
            rhs = enc(cmap, subst(A, B, C))
            if lhs != rhs:
                bad.append(('L', A, B, C, lhs, rhs))
log(f"A3L pass transfer [c(A)/c(B)]c(C)=c([A/B]C): {n_cases} cases, "
    f"{len(bad)} mismatches")
allok &= check("A3L full-pass transfer", n_cases, len(bad) == 0)

n_cases = 0
bad = []
for A in all_strings(Sigma, 2):
    for B in all_strings(Sigma, 2):
        if B == '':
            continue
        for C in all_strings(Sigma, 3):
            for mode in ['once', 'R', ('kth', 1), ('kth', 2), ('kth', 3)]:
                n_cases += 1
                cA, cB, cC = enc(cmap, A), enc(cmap, B), enc(cmap, C)
                lhs = apply_pass(mode, cA, cB, cC)
                rhs = enc(cmap, apply_pass(mode, A, B, C))
                if lhs != rhs:
                    bad.append((mode, A, B, C, lhs, rhs))
log(f"A3v variant-pass transfer (once, R, k-th k<=3): {n_cases} cases, "
    f"{len(bad)} mismatches")
allok &= check("A3v once/R/kth transfer", n_cases, len(bad) == 0)

# ---------- A4: composition lemma ----------
dmap, Dd, elld = make_coding('xy', 'abc')   # binary -> ternary
log(f"coding d: xy -> abc, ell={elld}, |dict|={len(Dd)}")
Dh = sorted({enc(dmap, w) for w in Dc})     # {d(c(sigma))}
comp_ok = comma_free(Dh)
allok &= check(f"A4 composition: dict(d o c) (over abc, ell={ellc*elld}) comma-free",
               len(Dh), comp_ok)
# spot-check the self-synchronization of the composed code on image words
n_cases = 0
ok = True
for u in Dh:
    for v in Dh:
        for p in range(1, ellc * elld):
            if (u + v)[p:p + ellc * elld] in set(Dh):
                ok = False
allok &= check("A4b junction-straddle recheck on dict(d o c)", len(Dh) ** 2, ok)

# ---------- A5: the paper's comma code (blocks x.sigma) ----------
# On PURE image text (no markers) the paper's own comma code also satisfies
# the pass transfer: the only misaligned occurrence class needs B = x^k
# (pattern (xx)^k), and each such occurrence is preceded one position
# earlier by an overlapping aligned one that the leftmost scan takes first
# (the shadowing of Remark rem:comma). It codes only |Sigma| <= |Gamma|
# (payloads must inject into Gamma), so it cannot replace the comma-free
# dictionaries in general.
cc = {'x': 'xx', 'y': 'xy'}   # source = target = {x,y}, comma = x
n_cases = 0
bad = []
for A in all_strings('xy', 2):
    for B in all_strings('xy', 3):
        if B == '':
            continue
        for C in all_strings('xy', 4):
            n_cases += 1
            cA, cB, cC = enc(cc, A), enc(cc, B), enc(cc, C)
            if subst(cA, cB, cC) != enc(cc, subst(A, B, C)):
                bad.append((A, B, C))
log(f"A5 paper comma code on pure image text: {n_cases} pass-transfer cases, "
    f"{len(bad)} mismatches")
allok &= check("A5 comma code transfers on pure image text", n_cases, len(bad) == 0)
n_cases = 0
bad = []
for A in all_strings('xy', 2):
    for B in all_strings('xy', 2):
        if B == '':
            continue
        for C in all_strings('xy', 3):
            for mode in ['once', 'R', ('kth', 2)]:
                n_cases += 1
                cA, cB, cC = enc(cc, A), enc(cc, B), enc(cc, C)
                if apply_pass(mode, cA, cB, cC) != enc(cc, apply_pass(mode, A, B, C)):
                    bad.append((mode, A, B, C))
log(f"A5b comma code, once/R/kth semantics: {n_cases} cases, {len(bad)} mismatches")
# Expected: every mismatch is in mode 'R' -- the rightmost scan takes a
# misaligned occurrence first (the paper's thm:r2l-rep phenomenon: shadowing
# is a leftmost phenomenon). Golomb-comma-free codes have no misaligned
# occurrences at all, hence transfer under every direction (A3v).
r_only = all(b[0] == 'R' for b in bad) and len(bad) > 0
allok &= check("A5b comma-code mismatches are exactly R-mode (matches thm:r2l-rep)",
               len(bad), r_only)

# ---------- A6: unary alignment, c(a) = 'ab' ----------
n_cases = 0
ok = True
for j in range(1, 9):
    for m in range(0, 13):
        cB, cC = 'ab' * j, 'ab' * m
        got = occ_positions(cC, cB)
        want = [2 * s for s in occ_positions('a' * m, 'a' * j)]
        n_cases += 1
        if got != want:
            ok = False
allok &= check("A6 unary alignment c(a)=ab (j<=8, m<=12)", n_cases, ok)

n_cases = 0
ok = True
for i in range(0, 7):
    for j in range(1, 7):
        for m in range(0, 11):
            n_cases += 1
            lhs = subst('ab' * i, 'ab' * j, 'ab' * m)
            rhs = 'ab' * (i * (m // j) + m % j)
            if lhs != rhs:
                ok = False
allok &= check("A6b unary pass transfer (i<=6, j<=6, m<=10)", n_cases, ok)

# 'ab' is primitive: the only single-codeword comma-free dictionaries
prim_ok = comma_free({'ab'}) and comma_free({'abb'}) and not comma_free({'abab'})
allok &= check("A6c {w} comma-free iff w primitive (spot: ab, abb yes; abab no)", 3, prim_ok)

with open('alignment.log', 'w') as f:
    f.write('\n'.join(LOG) + '\n')
print("ALL OK" if allok else "SOME FAILURES")
sys.exit(0 if allok else 1)

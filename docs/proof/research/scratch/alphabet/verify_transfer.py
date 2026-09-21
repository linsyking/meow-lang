"""Round 1, battery T: end-to-end transfer of expressions, both directions.

  T0   sanity: our expression implementation of rep_n (thm:multiple
       substitution) computes the freezing semantics of def:rep.
  T1   Direction 1: for every expression E over the ternary alphabet
       (depth <= 1, constants <= 2; plus random depth <= 3), the transferred
       expression E^c over binary satisfies  [[E^c]](c(S)) = c([[E]](S))
       with matching definedness, on all inputs of length <= 4 (resp. 3).
  T2   the same under once and R semantics (variant calculi transfer).
  T3   unary -> binary: transfer of all depth <= 1 unary expressions
       (constants a^0..a^4) on inputs a^0..a^24, plus random depth <= 3.
  T4   Direction 2 roundtrip: E over ternary -> E' = E^c over binary ->
       E_final = H_h(E'_d(h(X))) over ternary; [[E_final]] = [[E]] exactly
       (values and definedness) on all inputs of length <= 3.
  T5   retraction machinery over Gamma: q = c o e as a rep-based expression:
       q decodable (H_q(q(T)) = T), every variant pass equivariant under q,
       and the reversal retraction via a PALINDROMIC comma-free e (the
       naive identity c(rev S) = rev(c(S)) is FALSE unless codewords are
       palindromes; the machine caught this in an earlier round).
  T6   payoff end-to-end: the coding-equivariant functions double (cat(X,X)),
       the right pass r, the once pass and the 2nd-occurrence pass, built
       over the ternary alphabet, transferred to binary and retracted:
       the resulting binary expression computes the native binary function.
  T7   bookkeeping: deg(E^c) = deg(E), Safe(E) => Safe(E^c), size blowup.
"""
import random
import sys
from itertools import product
from meow import (subst, once_subst, rsubst, kth_subst, apply_pass, ev, enc,
                  transfer, make_coding, all_strings, deg, safe, size, depth,
                  rep_sem, rep_apply_expr, comma_free, dict_family, subst_ast)

random.seed(20260921)
LOG = []
def log(s):
    print(s)
    LOG.append(s)

def check(name, n, ok):
    log(f"{'OK  ' if ok else 'FAIL'} {name}: {n} cases")
    return ok

allok = True

# ---------- the codings ----------
SIG, GAM = 'abc', 'xy'          # ternary source, binary target
cmap, Dc, ellc = make_coding(SIG, GAM)          # c: abc -> xy (comma-free)
dmap, Dd, elld = make_coding(GAM, SIG)          # d: xy -> abc (comma-free)
log(f"c: {SIG}->{GAM} ell={ellc} map={cmap}")
log(f"d: {GAM}->{SIG} ell={elld} map={dmap}")

# rep-based coding over an alphabet: patterns = single chars, replacements =
# codewords (constants). h_codes[chr] = codeword.
def coding_expr(alphabet, codes, b, x):
    """rep-based total expression for the character-wise coding T |-> prod codes[T[i]]."""
    al = sorted(alphabet)
    return rep_apply_expr(len(al), b, x, [c for c in al if c != x],
                          ('var', 0),
                          [('const', ch) for ch in al],
                          [('const', codes[ch]) for ch in al])

def decoding_expr(alphabet, codes, b, x):
    """rep-based decoder: patterns = codewords, replacements = characters."""
    al = sorted(alphabet)
    return rep_apply_expr(len(al), b, x, [c for c in al if c != x],
                          ('var', 0),
                          [('const', codes[ch]) for ch in al],
                          [('const', ch) for ch in al])

# ---------- T0: rep expression vs freezing semantics ----------
n_cases = 0
ok = True
al3 = 'abc'
for _ in range(300):
    S = ''.join(random.choice('ab') for _ in range(random.randint(0, 6)))
    n = random.randint(1, 3)
    pairs = []
    for i in range(n):
        X = ''.join(random.choice('ab') for _ in range(random.randint(1, 2)))
        Y = ''.join(random.choice('ab') for _ in range(random.randint(0, 2)))
        pairs.append((X, Y))
    E = rep_apply_expr(n, 'b', 'x', ['a', 'b'] if 'x' not in 'ab' else ['a'],
                       ('var', 0),
                       [('const', p[0]) for p in pairs],
                       [('const', p[1]) for p in pairs])
    got = ev(E, [S])
    want = rep_sem(S, pairs)
    n_cases += 1
    if got != want:
        ok = False
        log(f"  rep mismatch S={S} pairs={pairs}: {got} vs {want}")
allok &= check("T0 rep expression = freezing semantics (300 random, n<=3)", n_cases, ok)

# ---------- expression spaces ----------
def leaves(maxconst):
    ls = [('var', 0)] + [('const', w) for w in all_strings(SIG, maxconst)]
    return ls

def space_depth1(maxconst):
    ls = leaves(maxconst)
    res = list(ls)
    for R in ls:
        for P in ls:
            for E in ls:
                res.append(('pass', R, P, E))
    for E1 in ls:
        for E2 in ls:
            res.append(('cat', E1, E2))
    return res

def rand_expr(d, maxconst):
    if d == 0:
        if random.random() < 0.5:
            return ('var', 0)
        return ('const', ''.join(random.choice(SIG) for _ in range(random.randint(0, maxconst))))
    r = random.random()
    if r < 0.6:
        return ('pass', rand_expr(d - 1, maxconst), rand_expr(d - 1, maxconst),
                rand_expr(d - 1, maxconst))
    if r < 0.8:
        return ('cat', rand_expr(d - 1, maxconst), rand_expr(d - 1, maxconst))
    return rand_expr(0, maxconst)

SP1 = space_depth1(2)
log(f"expression space: depth<=1, constants<=2 over {SIG}: {len(SP1)} expressions")

# ---------- T1: Direction 1, full pass semantics ----------
def check_dir1(exprs, inputs, mode='L', label=''):
    n = 0
    bad = 0
    und = 0
    for E in exprs:
        Ec = transfer(E, cmap)
        for S in inputs:
            n += 1
            v1 = ev(E, [S], mode)
            v2 = ev(Ec, [enc(cmap, S)], mode)
            if (v1 is None) != (v2 is None):
                bad += 1
                if bad < 4:
                    log(f"  definedness mismatch {label} {E} on {S}")
                continue
            if v1 is None:
                und += 1
                continue
            if v2 != enc(cmap, v1):
                bad += 1
                if bad < 4:
                    log(f"  value mismatch {label} {E} on {S}: {v2} vs c({v1})")
    return n, bad, und

IN4 = all_strings(SIG, 4)
n, bad, und = check_dir1(SP1, IN4, 'L', 'T1')
log(f"T1 Dir-1 (all {len(SP1)} depth<=1 exprs, |S|<=4, {len(IN4)} inputs): "
    f"{n} evaluations, {bad} mismatches, {und} undefined (matching)")
allok &= check("T1 Direction 1 transfer, full pass", n, bad == 0)

rnd3 = [rand_expr(3, 2) for _ in range(1200)]
IN3 = all_strings(SIG, 3)
n, bad, und = check_dir1(rnd3, IN3, 'L', 'T1b')
log(f"T1b Dir-1 (1200 random depth<=3 exprs, |S|<=3, {len(IN3)} inputs): "
    f"{n} evaluations, {bad} mismatches")
allok &= check("T1b Direction 1, random deeper", n, bad == 0)

# ---------- T2: variant semantics ----------
for mode in ['once', 'R']:
    sub = [E for E in SP1 if depth(E) <= 1]
    n, bad, und = check_dir1(sub, IN3, mode, f'T2-{mode}')
    log(f"T2 Dir-1 under {mode}: {n} evaluations, {bad} mismatches")
    allok &= check(f"T2 {mode} transfer", n, bad == 0)

# ---------- T3: unary -> binary ----------
def unary_leaves():
    return [('var', 0)] + [('const', 'a' * k) for k in range(5)]

US = unary_leaves()
U1 = list(US)
for R in US:
    for P in US:
        for E in US:
            U1.append(('pass', R, P, E))
for E1 in US:
    for E2 in US:
        U1.append(('cat', E1, E2))
cmap1 = {'a': 'ab'}
UIN = ['a' * m for m in range(25)]
n = bad = und = 0
for E in U1:
    Ec = transfer(E, cmap1)
    for S in UIN:
        n += 1
        v1 = ev(E, [S])
        v2 = ev(Ec, [enc(cmap1, S)])
        if (v1 is None) != (v2 is None):
            bad += 1
        elif v1 is not None and v2 != enc(cmap1, v1):
            bad += 1
        else:
            und += v1 is None
log(f"T3 unary->binary (all {len(U1)} depth<=1 unary exprs, a^0..a^24): "
    f"{n} evaluations, {bad} mismatches, {und} undefined")
allok &= check("T3 unary source transfer", n, bad == 0)

def rand_unary(d):
    if d == 0:
        return random.choice([('var', 0), ('const', 'a' * random.randint(0, 3))])
    if random.random() < 0.7:
        return ('pass', rand_unary(d - 1), rand_unary(d - 1), rand_unary(d - 1))
    return ('cat', rand_unary(d - 1), rand_unary(d - 1))

UR = [rand_unary(3) for _ in range(800)]
n = bad = 0
for E in UR:
    Ec = transfer(E, cmap1)
    for m in range(0, 15):
        S = 'a' * m
        v1 = ev(E, [S])
        v2 = ev(Ec, [enc(cmap1, S)])
        n += 1
        if (v1 is None) != (v2 is None) or (v1 is not None and v2 != enc(cmap1, v1)):
            bad += 1
log(f"T3b unary->binary (800 random depth<=3, a^0..a^14): {n} evaluations, {bad} mismatches")
allok &= check("T3b unary source, random deeper", n, bad == 0)

# ---------- Direction 2 machinery ----------
# h = d o c : ternary -> ternary; its codewords h(sigma) = d(c(sigma)).
h_codes = {s: enc(dmap, cmap[s]) for s in SIG}
log(f"h = d o c codewords: {h_codes}")
bX, xX = 'a', 'b'   # (b, x) roles inside the ternary alphabet for enc^2/dec^2

def h_expr():
    return coding_expr(SIG, h_codes, bX, xX)

def H_expr():
    return decoding_expr(SIG, h_codes, bX, xX)

def dir2(Eprime, arity):
    """E' over Gamma (binary) -> expression over Sigma computing the conjugate."""
    Ed = transfer(Eprime, dmap)          # over ternary
    hE = h_expr()
    Ed = subst_ast(Ed, {i: subst_ast(hE, {0: ('var', i)}) for i in range(arity)})
    H = H_expr()
    return subst_ast(H, {0: Ed})

# roundtrip: E0 over ternary -> E' = transfer(E0, c) over binary -> E_final.
def roundtrip(E0, arity):
    return dir2(transfer(E0, cmap), arity)

# quick sanity of h/H as functions (via direct rep semantics, cheap)
n = bad = 0
for S in all_strings(SIG, 3):
    n += 1
    hv = ev(h_expr(), [S])
    if hv != enc(h_codes, S):
        bad += 1
    if ev(H_expr(), [hv]) != S:
        bad += 1
log(f"T4a h/H expressions: {n} inputs |S|<=3, {bad} failures")
allok &= check("T4a h expression codes, H decodes", n, bad == 0)

# ---------- T4: roundtrip ----------
# use the constants<=1 subspace for speed
ls1 = [('var', 0)] + [('const', w) for w in all_strings(SIG, 1)]
SPc = list(ls1)
for R in ls1:
    for P in ls1:
        for E in ls1:
            SPc.append(('pass', R, P, E))
for E1 in ls1:
    for E2 in ls1:
        SPc.append(('cat', E1, E2))
log(f"T4 roundtrip space (constants<=1): {len(SPc)} expressions")

n = bad = und = 0
for E0 in SPc:
    Ef = roundtrip(E0, 1)
    for S in IN3:
        n += 1
        v1 = ev(E0, [S])
        v2 = ev(Ef, [S])
        if (v1 is None) != (v2 is None) or (v1 is not None and v1 != v2):
            bad += 1
            if bad < 4:
                log(f"  roundtrip mismatch {E0} on {S}: {v1} vs {v2}")
        else:
            und += v1 is None
log(f"T4 Dir-2 roundtrip (E -> E^c -> H(E'_d(h(.)))): {n} evaluations, "
    f"{bad} mismatches, {und} undefined (matching)")
allok &= check("T4 Direction 2 roundtrip", n, bad == 0)

# ---------- T5: retraction machinery over Gamma ----------
# e: xy -> abc (comma-free), q = c o e : binary -> binary
emap, De, elle = make_coding(GAM, SIG)
q_codes = {g: enc(cmap, emap[g]) for g in GAM}
bG, xG = 'x', 'y'   # (b, x) roles inside the binary alphabet
def q_expr():
    return coding_expr(GAM, q_codes, bG, xG)
def Hq_expr():
    return decoding_expr(GAM, q_codes, bG, xG)

TIN = all_strings(GAM, 4)
n = bad = 0
for T in TIN:
    qT = ev(q_expr(), [T])
    n += 1
    if qT != enc(q_codes, T):
        bad += 1
        log(f"  q expr mismatch on {T}")
    if ev(Hq_expr(), [qT]) != T:
        bad += 1
        log(f"  H(q(T)) != T on {T}")
log(f"T5a q = c o e as expression, H_q its decoder: {n} inputs |T|<=4, {bad} failures")
allok &= check("T5a retraction q decodable", n, bad == 0)

# ---------- T5b: the reversal retraction via a PALINDROMIC e ----------
# Character-wise codings do NOT commute with reversal: c(rev S) = rev(c(S))
# iff every codeword is a palindrome.  The reversal payoff therefore uses a
# retraction q = c o e whose e has palindromic comma-free codewords:
#   [[E']](q(T)) = c(rev e(T)) = c(e(rev T)) = q(rev T)
# (e(rev T) = rev(e(T)) because each codeword reverses to itself), hence
#   rev_Gamma = H_q o [[E']] o q.
# We machine-check every link that does not presuppose rev in L:
#   (i) e palindromic, comma-free; (ii) dict(c o e) comma-free (L3);
#   (iii) e(rev T) = rev(e(T)); (iv) with D = c o rev o c^{-1} the oracle
#   standing in for [[E']], H_q(D(q(T))) = rev T with q, H_q as EXPRESSIONS.
e3 = {'x': 'bab', 'y': 'cac'}        # middle-marker family over {a,b,c}, mu='a'
assert all(w == w[::-1] for w in e3.values())
assert comma_free(list(e3.values()))
q_rev = {g: enc(cmap, e3[g]) for g in GAM}
assert comma_free(list(q_rev.values()))

def q_rev_expr():
    return coding_expr(GAM, q_rev, bG, xG)

def Hq_rev_expr():
    return decoding_expr(GAM, q_rev, bG, xG)

cinv = {v: k for k, v in cmap.items()}
def decode_c(W):
    return ''.join(cinv[W[i:i + ellc]] for i in range(0, len(W), ellc))
def D_rev(W):
    """Oracle for [[E']] on image(c): c(rev(c^{-1}(W)))."""
    return enc(cmap, decode_c(W)[::-1])

n = bad = 0
for T in all_strings(GAM, 5):
    n += 1
    if enc(e3, T[::-1]) != enc(e3, T)[::-1]:          # (iii)
        bad += 1
    got = ev(Hq_rev_expr(), [D_rev(ev(q_rev_expr(), [T]))])   # (iv)
    if got != T[::-1]:
        bad += 1
log(f"T5b reversal retraction: e = {{x:bab, y:cac}} (palindromic, comma-free), "
    f"q = c o e; H_q(D(q(T))) = rev T on {n} inputs |T|<=5, {bad} failures")
allok &= check("T5b rev_Gamma = H_q o D o q, D = c o rev o c^-1 (oracle)", n, bad == 0)

# equivariance of the variant passes under q
n = bad = 0
for A in all_strings(GAM, 2):
    for B in all_strings(GAM, 2):
        if B == '':
            continue
        for C in all_strings(GAM, 2):
            for mode in ['L', 'once', 'R', ('kth', 2)]:
                qA, qB, qC = enc(q_codes, A), enc(q_codes, B), enc(q_codes, C)
                lhs = apply_pass(mode, qA, qB, qC)
                rhs = enc(q_codes, apply_pass(mode, A, B, C))
                n += 1
                if lhs != rhs:
                    bad += 1
log(f"T5c pass equivariance under q (L/once/R/kth): {n} cases, {bad} mismatches")
allok &= check("T5c passes equivariant under the retraction coding", n, bad == 0)

# ---------- T6: payoff end-to-end ----------
def payoff(E0, arity):
    """E0 over ternary (a coding-equivariant function) -> binary expression
    computing the native binary function:
       E_pay = H_q(E'(q(X_1),...,q(X_n)))   with E' = transfer(E0, c)
    applied DIRECTLY to the q-wrapped inputs (image(q) is inside image(c),
    and [[E']] is exactly the transfer of E0 there)."""
    Ep = transfer(E0, cmap)
    qE = q_expr()
    Ep = subst_ast(Ep, {i: subst_ast(qE, {0: ('var', i)}) for i in range(arity)})
    return subst_ast(Hq_expr(), {0: Ep})

n = bad = 0
E0 = ('cat', ('var', 0), ('var', 0))    # double
Ef = payoff(E0, 1)
for T in TIN:
    n += 1
    if ev(Ef, [T]) != T + T:
        bad += 1
log(f"T6a double over ternary -> native double over binary: {n} inputs, {bad} failures")
allok &= check("T6a payoff: doubling is alphabet-uniform", n, bad == 0)

# equivariance of the pass under e (= d) itself, all four modes
n = bad = 0
for A in all_strings(GAM, 2):
    for B in all_strings(GAM, 2):
        if B == '':
            continue
        for C in all_strings(GAM, 2):
            for mode in ['L', 'once', 'R', ('kth', 2)]:
                eA, eB, eC = enc(dmap, A), enc(dmap, B), enc(dmap, C)
                n += 1
                if apply_pass(mode, eA, eB, eC) != enc(dmap, apply_pass(mode, A, B, C)):
                    bad += 1
log(f"T6b-0 pass equivariance under e (= d: xy->abc, comma-free, all modes): "
    f"{n} cases, {bad} mismatches")
allok &= check("T6b-0 passes equivariant under e itself", n, bad == 0)

# L mode: the full end-to-end expression H_q([qX0/qX1]qX2)
n = bad = 0
Er = ('pass', ('var', 0), ('var', 1), ('var', 2))   # the pass node
Ef = payoff(Er, 3)
for A in all_strings(GAM, 2):
    for B in all_strings(GAM, 2):
        if B == '':
            continue
        for C in all_strings(GAM, 2):
            n += 1
            if ev(Ef, [A, B, C]) != subst(A, B, C):
                bad += 1
log(f"T6b pass node, L mode, full expression H_q(E'(q(X))): {n} evaluations, "
    f"{bad} mismatches")
allok &= check("T6b payoff: pass node alphabet-uniform (L, full expression)", n, bad == 0)

# variant modes: q and H_q are L-expressions, so the composition is checked
# with the variant pass evaluated as [[E']]_m on the q-wrapped inputs
# ([[E']](c(S)) = c(F0(S)) with S = e(T), and F0 o e = e o F by T6b-0).
n = bad = 0
for A in all_strings(GAM, 2):
    for B in all_strings(GAM, 2):
        if B == '':
            continue
        for C in all_strings(GAM, 2):
            for mode in ['once', 'R', ('kth', 2)]:
                n += 1
                qA, qB, qC = enc(q_codes, A), enc(q_codes, B), enc(q_codes, C)
                mid = ev(Er, [qA, qB, qC], mode)      # [[E']]_m(q(T))
                got = ev(Hq_expr(), [mid])            # H_q, an L-expression
                want = apply_pass(mode, A, B, C)
                if got != want:
                    bad += 1
log(f"T6b pass node, once/R/kth: H_q([[E']]_m(q(T))) = native pass: "
    f"{n} evaluations, {bad} mismatches")
allok &= check("T6b payoff: pass node alphabet-uniform (once/R/kth, semantic composition)",
               n, bad == 0)

# ---------- T7: bookkeeping ----------
n = bad = 0
for E in SP1:
    n += 1
    if deg(transfer(E, cmap)) != deg(E):
        bad += 1
    if safe(E) and not safe(transfer(E, cmap)):
        bad += 1
log(f"T7 deg(E^c)=deg(E) and Safe transfer, over the depth<=1 space: {n} expressions, "
    f"{bad} violations")
allok &= check("T7 degree and safety transfer", n, bad == 0)

szs = [size(transfer(E, cmap)) for E in SP1]
maxfac = max((s / max(1, size(E)) for s, E in zip(szs, SP1)))
log(f"T7b size blowup of the transfer over the space: max |E^c|/|E| = {maxfac:.2f}, "
    f"codeword length {ellc}")

with open('transfer.log', 'w') as f:
    f.write('\n'.join(LOG) + '\n')
print("ALL OK" if allok else "SOME FAILURES")
sys.exit(0 if allok else 1)

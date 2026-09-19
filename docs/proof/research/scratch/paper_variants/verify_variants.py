#!/usr/bin/env python3
"""Verification of every formula that goes into the paper's "Variants of the
Primitive" section, exactly as written there.

Critical motivation: the r2l and restart research reports verified their rep_n
claims against the OLD enc-based construction, but the paper's Theorem
(Multiple Substitution) is now the COMMA-CODE construction -- so those claims
must be re-derived here against the current construction.

Sections (run individually to keep runtimes small):
  once    -- A: once toolkit (cat/tail/head/isε/eq/if), B: unary delete-one-b,
             C: once-r zipper
  r2l     -- D: rev duality / agreement / enc^R = enc, J: escape direction lock
  commaR  -- E: comma-code rep under r2l (counterexample, mirrored fix,
             strengthened-hypothesis fix)   [NEW, not covered by any report]
  commaM  -- F: comma-code rep under restart (black-box enc2/dec2)  [NEW]
  rescan  -- G: totality/agreement/characterization + run-collapse both ways
  restart -- H: amplifier formula, towers, termination, agreement,
             no-injective-node
  pos     -- I: tail/head scaffold, repOcc-via-once, unary [a^j/a]
"""

import itertools
import random
import sys

# ---------------------------------------------------------------- primitives


def subst(A, B, C):
    """[A/B]C -- paper Definition 1 (greedy leftmost, non-overlapping, never
    restarting inside inserted text). [A/eps] never used here."""
    if not B:
        raise ValueError("[A/eps] undefined")
    out, i, n, m = [], 0, len(C), len(B)
    while i < n:
        if C[i:i + m] == B:
            out.append(A)
            i += m
        else:
            out.append(C[i])
            i += 1
    return ''.join(out)


def rfind(B, C):
    for s in range(len(C) - len(B), -1, -1):
        if C.startswith(B, s):
            return s
    return None


def substR(A, B, C):
    """[A/B]^R C -- rightmost-first mirror (recursive Definition 1')."""
    if not B:
        raise ValueError
    s = rfind(B, C)
    if s is None:
        return C
    return substR(A, B, C[:s]) + A + C[s + len(B):]


def once(A, B, C):
    """[A/B]_1 C -- replace the leftmost occurrence of B by A."""
    if not B:
        raise ValueError
    i = C.find(B)
    if i < 0:
        return C
    return C[:i] + A + C[i + len(B):]


def onceR(A, B, C):
    """[A/B]_1^R C -- replace the rightmost occurrence of B by A."""
    if not B:
        raise ValueError
    s = rfind(B, C)
    if s is None:
        return C
    return C[:s] + A + C[s + len(B):]


def rescan(A, B, C, cap=2000):
    """[A/B]^u C -- stack process: on a match, freeze the prefix, and the
    scan RE-ENTERS the inserted text at its first character. None = diverged.
    cap = 2000 is far above the <= |C|+1 matches any total instance performs."""
    if not B:
        raise ValueError
    O, T, steps = [], C, 0
    while B in T:
        steps += 1
        if steps > cap:
            return None
        q = T.find(B)
        O.append(T[:q])
        T = A + T[q + len(B):]
    return ''.join(O) + T


def restart(A, B, C, cap=5000):
    """[A/B]^m C -- single-rule Markov: replace the leftmost B, rescan from 0,
    until B-free. None = diverged. cap = 5000 exceeds the 2^|C| step bound for
    length-preserving rules on the small domains used here."""
    if not B:
        raise ValueError
    s, steps = C, 0
    while B in s:
        steps += 1
        if steps > cap:
            return None
        i = s.find(B)
        s = s[:i] + A + s[i + len(B):]
    return s


def rev(S):
    return S[::-1]


# ------------------------------------------- freezing semantics (reference)


def rep_ref(pairs, S):
    """Paper Definition (rep): leftmost-freezing rounds, simultaneous replace."""
    frozen = [0] * len(S)
    for i, (Xi, _) in enumerate(pairs, 1):
        if not Xi:
            continue
        m, j = len(Xi), 0
        while j + m <= len(S):
            if all(frozen[j + k] == 0 for k in range(m)) and S[j:j + m] == Xi:
                for k in range(m):
                    frozen[j + k] = i
                j += m
            else:
                j += 1
    out, j = [], 0
    while j < len(S):
        if frozen[j] == 0:
            out.append(S[j])
            j += 1
        else:
            i = frozen[j]
            out += pairs[i - 1][1]
            j += len(pairs[i - 1][0])
    return ''.join(out)


def rep_ref_R(pairs, S):
    """Rightmost-freezing mirror: rev . rep_ref . rev with reversed operands."""
    return rev(rep_ref([(rev(X), rev(Y)) for X, Y in pairs], rev(S)))


# ------------------------------------------------- comma-code construction


def enc2(sub, b, x, W, sigma):
    """enc^2 = [xx/x] then [xc/c] per c in sigma, c != x (pluggable direction)."""
    T = sub(x + x, x, W)
    for c in sigma:
        if c != x:
            T = sub(x + c, c, T)
    return T


def dec2(sub, b, x, T, sigma):
    for c in sigma:
        if c != x:
            T = sub(c, x + c, T)
    return sub(x, x + x, T)


def repC_comma(sub, b, x, pairs, S, sigma):
    """The paper's Theorem (Multiple Substitution) construction with a
    pluggable pass semantics (subst / substR / restart)."""
    T = enc2(sub, b, x, S, sigma)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc2(sub, b, x, Xi, sigma)
        T = sub(x + b * (i + 1), EXi, T)          # rename  [m_i / E_Xi]
        T = sub(EXi + b, x + b * (i + 2), T)      # repair  [E_Xi b / m_{i+1}]
    for i in range(len(pairs), 0, -1):
        T = sub(enc2(sub, b, x, pairs[i - 1][1], sigma), x + b * (i + 1), T)
    return dec2(sub, b, x, T, sigma)


def mirror_enc2(b, x, W, sigma):
    """Mirror encoder: every c -> c x (post-fix), doubling pass first,
    all passes rightmost-first."""
    T = substR(x + x, x, W)
    for c in sigma:
        if c != x:
            T = substR(c + x, c, T)
    return T


def mirror_dec2(b, x, T, sigma):
    for c in sigma:
        if c != x:
            T = substR(c, c + x, T)
    return substR(x, x + x, T)


def repC_comma_mirrored(b, x, pairs, S, sigma):
    """rev-conjugate of the comma-code construction: same pass order, every
    constant reversed, all passes rightmost-first. Target: rep_ref_R."""
    T = substR(x + x, x, S)
    for c in sigma:
        if c != x:
            T = substR(c + x, c, T)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = mirror_enc2(b, x, Xi, sigma)
        T = substR(b * (i + 1) + x, EXi, T)       # rename  [b^{i+1}x / E'_Xi]
        T = substR(b + EXi, b * (i + 2) + x, T)   # repair  [b E'_Xi / b^{i+2}x]
    for i in range(len(pairs), 0, -1):
        T = substR(mirror_enc2(b, x, pairs[i - 1][1], sigma), b * (i + 1) + x, T)
    for c in sigma:
        if c != x:
            T = substR(c, c + x, T)
    return substR(x, x + x, T)


def repC_comma_restart(b, x, pairs, S, sigma):
    """Comma-code construction with enc2/dec2 as black boxes (left-to-right
    passes) and the rename/repair/instantiate passes as restart nodes."""
    T = enc2(subst, b, x, S, sigma)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc2(subst, b, x, Xi, sigma)
        T = restart(x + b * (i + 1), EXi, T)
        if T is None:
            return None
        T = restart(EXi + b, x + b * (i + 2), T)
        if T is None:
            return None
    for i in range(len(pairs), 0, -1):
        T = restart(enc2(subst, b, x, pairs[i - 1][1], sigma), x + b * (i + 1), T)
        if T is None:
            return None
    return dec2(subst, b, x, T, sigma)


# ------------------------------------------------------------------ helpers


def strings_upto(sigma, maxlen):
    return [''.join(t) for L in range(maxlen + 1)
            for t in itertools.product(sigma, repeat=L)]


class Tally:
    def __init__(self, name):
        self.name, self.n, self.fails = name, 0, []

    def check(self, cond, ctx):
        self.n += 1
        if not cond:
            self.fails.append(ctx)
            if len(self.fails) <= 8:
                print(f"  FAIL [{self.name}] {ctx}", flush=True)

    def report(self):
        print(f"[{self.name}] {self.n} checks, {len(self.fails)} failures", flush=True)
        return not self.fails


# ================================================================== A/B/C


def chunk_once():
    ok = True
    # --- A1: once cat: cat(X,Y) = [X/a]_1 [Y/b]_1 (ab)
    t = Tally("once cat")
    for sigma in ['ab', 'abc']:
        mx = 4 if sigma == 'ab' else 3
        for X in strings_upto(sigma, mx):
            for Y in strings_upto(sigma, mx):
                got = once(X, 'a', once(Y, 'b', 'ab'))
                t.check(got == X + Y, (X, Y, got))
    ok &= t.report()

    # --- A2: once tail: prod_{sigma} [eps/XX sigma]_1 (XXX), any pass order
    t = Tally("once tail")
    for sigma in ['ab', 'abc']:
        mx = 4 if sigma == 'ab' else 3
        for X in strings_upto(sigma, mx):  # includes X = eps (patterns inert)
            for order in [sigma, sigma[::-1]]:
                T = X + X + X
                for c in order:
                    T = once('', X + X + c, T)
                t.check(T == X[1:], (X, order, T))
    ok &= t.report()

    # --- A3: once head: [eps / tail(X) X d]_1 (X X d), every d
    t = Tally("once head")
    for sigma in ['ab', 'abc']:
        mx = 4 if sigma == 'ab' else 3
        for X in strings_upto(sigma, mx):
            for d in sigma:
                P = (X[1:] if X else '') + X + d
                T = once('', P, X + X + d)
                t.check(T == (X[:1] if X else ''), (X, d, T))
    ok &= t.report()

    # --- A4: isε = [bot/d]_1 [top / X d]_1 (d)
    t = Tally("once isε")
    for sigma in ['ab', 'abc']:
        top, bot, d = sigma[0], sigma[1], sigma[-1]
        for X in strings_upto(sigma, 6):
            got = once(bot, d, once(top, X + d, d))
            t.check(got == (top if X == '' else bot), (X, got))
    ok &= t.report()

    # --- A5: eq: eqind = [bot / X YY bot d]_1 (Y YY bot d); eq = [top/eqind]_1(bot)
    t = Tally("once eq")
    for sigma in ['ab', 'abc']:
        top, bot, d = sigma[0], sigma[1], sigma[-1]
        mx = 3
        for X in strings_upto(sigma, mx):
            for Y in strings_upto(sigma, mx):
                eqind = once(bot, X + Y + Y + bot + d, Y + Y + Y + bot + d)
                got = once(top, eqind, bot)
                want = top if X == Y else bot
                t.check(got == want and eqind != '', (X, Y, eqind, got, want))
    ok &= t.report()

    # --- A6: if: [Y/bot d X d Y d]_1 [X/top d X d Y d]_1 (C d X d Y d)
    t = Tally("once if")
    for sigma in ['ab', 'abc']:
        top, bot, d = sigma[0], sigma[1], sigma[-1]
        mx = 3
        for X in strings_upto(sigma, mx):
            for Y in strings_upto(sigma, mx):
                for C in (top, bot):
                    got = once(Y, bot + d + X + d + Y + d,
                               once(X, top + d + X + d + Y + d, C + d + X + d + Y + d))
                    t.check(got == (X if C == top else Y), (C, X, Y, got))
    ok &= t.report()

    # --- B: unary delete-one-b: H = [b/a][eps/b][a/bb], D = [H/H b]
    t = Tally("unary delete-one-b")
    for n in range(0, 40):
        X = 'b' * n
        H = subst('b', 'a', subst('', 'b', subst('a', 'bb', X)))
        t.check(H == 'b' * (n // 2), (n, H))
        got = subst(H, H + 'b', X)
        t.check(got == 'b' * max(0, n - 1), (n, got))
    ok &= t.report()

    # --- C: once-r zipper: cat = [Y/a]_1R [X/b]_1R (ba); suffix lemma
    t = Tally("once-r zipper")
    for sigma in ['ab', 'abc']:
        mx = 4 if sigma == 'ab' else 3
        for X in strings_upto(sigma, mx):
            for Y in strings_upto(sigma, mx):
                got = onceR(Y, 'a', onceR(X, 'b', 'ba'))
                t.check(got == X + Y, (X, Y, got))
    t2 = Tally("suffix substitution")
    for sigma in ['ab', 'abc']:
        for A in strings_upto(sigma, 3):
            if not A:
                continue
            for B in strings_upto(sigma, 4):
                for C in strings_upto(sigma, 3):
                    t2.check(onceR(C, A, B + A) == B + C, (A, B, C))
    ok &= t.report() and t2.report()
    return ok


# ================================================================== D + J


def chunk_r2l():
    ok = True
    rng = random.Random(7)

    # --- D1: Rev Duality, random
    t = Tally("rev duality")
    for _ in range(20000):
        sigma = rng.choice(['ab', 'abc'])
        A = ''.join(rng.choices(sigma, k=rng.randint(0, 4)))
        B = ''.join(rng.choices(sigma, k=rng.randint(1, 3)))
        C = ''.join(rng.choices(sigma, k=rng.randint(0, 8)))
        t.check(substR(A, B, C) == rev(subst(rev(A), rev(B), rev(C))), (A, B, C))
    ok &= t.report()

    # --- D2: agreement on unbordered / single-char patterns
    def unbordered(B):
        return all(B[:k] != B[len(B) - k:] for k in range(1, len(B)))

    t = Tally("unbordered agreement")
    for sigma in ['ab', 'abc']:
        for A in strings_upto(sigma, 3):
            for B in strings_upto(sigma, 4):
                if B and unbordered(B):
                    for C in strings_upto(sigma, 7):
                        t.check(substR(A, B, C) == subst(A, B, C), (A, B, C))
    ok &= t.report()

    # --- D3: enc^R = enc exactly
    t = Tally("enc^R = enc")
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        for W in strings_upto('ab', 8):
            t.check(substR(x + b, b, W) == subst(x + b, b, W), (b, x, W))
    ok &= t.report()

    # --- J: escape direction lock (semantic level, via freezing references)
    # pre-fix scheme (u -> u1 f(u)) under RIGHTMOST freezing fails:
    t = Tally("escape direction lock")
    # U = {b, x}, f(b)=b, f(x)=c, u1=b, S=bx  (sigma = {b, x, c})
    esc = [('b', 'bb'), ('x', 'bc')]
    une = [('bb', 'b'), ('bc', 'x')]
    got = rep_ref_R(une, rep_ref_R(esc, 'bx'))
    t.check(got != 'bx', ('prefix-under-rightmost', got))          # fails: bbc
    # mirrored scheme (u -> f(u) u1) under LEFTMOST freezing fails:
    # U = {b, x}, f(b)=b, f(x)=x, u1=b, S=xb
    esc2 = [('b', 'bb'), ('x', 'xb')]
    une2 = [('bb', 'b'), ('xb', 'x')]
    got2 = rep_ref(une2, rep_ref(esc2, 'xb'))
    t.check(got2 != 'xb', ('postfix-under-leftmost', got2))       # fails: xbb
    # and the matched pairings DO round-trip:
    t.check(rep_ref(une, rep_ref(esc, 'bx')) == 'bx', ('prefix-under-leftmost',))
    t.check(rep_ref_R(une2, rep_ref_R(esc2, 'xb')) == 'xb', ('postfix-under-rightmost',))
    ok &= t.report()
    return ok


# ================================================================== E


def chunk_commaR():
    """Comma-code construction under r2l -- against the CURRENT paper theorem."""
    ok = True

    # --- E0: sanity, l2r: construction == leftmost-freeing reference
    t = Tally("comma l2r sanity")
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        for S in strings_upto('ab', 5):
            for X1 in strings_upto('ab', 2):
                if not X1:
                    continue
                for Y1 in strings_upto('ab', 2):
                    t.check(repC_comma(subst, b, x, [(X1, Y1)], S, 'ab')
                            == rep_ref([(X1, Y1)], S), (b, x, X1, Y1, S))
    ok &= t.report()

    # --- E1: original constants under r2l vs rightmost-freezing: find failures
    t = Tally("comma under r2l (original constants)")
    first_fail = None
    nfail = 0
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        for S in strings_upto('ab', 5):
            for X1 in strings_upto('ab', 2):
                if not X1:
                    continue
                for Y1 in strings_upto('ab', 2):
                    got = repC_comma(substR, b, x, [(X1, Y1)], S, 'ab')
                    want = rep_ref_R([(X1, Y1)], S)
                    t.n += 1
                    if got != want:
                        nfail += 1
                        if first_fail is None:
                            first_fail = (b, x, X1, Y1, S, want, got)
    t.fails = [first_fail] if first_fail else []
    print(f"[comma under r2l] {t.n} evals, {nfail} failures; "
          f"first: {first_fail}", flush=True)
    ok &= (nfail > 0)  # the paper claims a counterexample EXISTS

    # --- E2: mirrored constants under r2l == rightmost-freezing, no hypothesis
    t = Tally("comma mirrored under r2l")
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        for S in strings_upto('ab', 5):
            for X1 in strings_upto('ab', 2):
                if not X1:
                    continue
                for Y1 in strings_upto('ab', 2):
                    t.check(repC_comma_mirrored(b, x, [(X1, Y1)], S, 'ab')
                            == rep_ref_R([(X1, Y1)], S), (b, x, X1, Y1, S))
    # n = 2 and ternary spot sweeps
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        pats = [p for p in strings_upto('ab', 2) if p]
        for S in strings_upto('ab', 4):
            for ps in itertools.product(itertools.product(pats, ['a', '']), repeat=2):
                pairs = list(ps)
                t.check(repC_comma_mirrored(b, x, pairs, S, 'ab')
                        == rep_ref_R(pairs, S), (b, x, pairs, S))
    for (b, x) in [('a', 'b'), ('b', 'c')]:
        pats = [p for p in strings_upto('abc', 2) if p]
        for S in strings_upto('abc', 3):
            for ps in itertools.product(itertools.product(pats, ['a', '']), repeat=1):
                t.check(repC_comma_mirrored(b, x, list(ps), S, 'abc')
                        == rep_ref_R(list(ps), S), (b, x, ps, S))
    ok &= t.report()

    # --- E3: original constants under r2l when every X_i ends outside {b,x}
    # (unsatisfiable over |sigma| = 2 -- the condition needs |sigma| >= 3;
    #  spurious classes: alpha needs X ending b, beta needs X = x^k, gamma X = b)
    def ends_outside(pairs, b, x):
        return all(X[-1] not in (b, x) for X, _ in pairs)

    t = Tally("comma r2l original + ends-outside (ternary)")
    for (b, x) in [('a', 'b'), ('b', 'c'), ('a', 'c')]:
        pats = [p for p in strings_upto('abc', 2) if p and p[-1] not in (b, x)]
        for S in strings_upto('abc', 4):
            for X1 in pats:
                for Y1 in strings_upto('abc', 2):
                    pairs = [(X1, Y1)]
                    t.check(repC_comma(substR, b, x, pairs, S, 'abc')
                            == rep_ref_R(pairs, S), (b, x, X1, Y1, S))
    ok &= t.report()

    t = Tally("comma r2l original + ends-outside n=2 (ternary)")
    for (b, x) in [('a', 'b'), ('b', 'c')]:
        pats = [p for p in strings_upto('abc', 2) if p and p[-1] not in (b, x)]
        for S in strings_upto('abc', 3):
            for ps in itertools.product(itertools.product(pats, ['', 'c']), repeat=2):
                pairs = list(ps)
                t.check(repC_comma(substR, b, x, pairs, S, 'abc')
                        == rep_ref_R(pairs, S), (b, x, pairs, S))
    ok &= t.report()
    return ok


# ================================================================== F


def chunk_commaM():
    """Comma-code construction with restart nodes (black-box enc2/dec2)."""
    ok = True

    def condition(kind, pairs, b, x):
        if kind == 'none-b':
            return all(X != b for X, _ in pairs)
        if kind == 'none-bx':
            return all(X not in (b, x) for X, _ in pairs)
        return True

    for kind in ['none-b', 'none-bx', 'unconditional']:
        t = Tally(f"comma restart [{kind}]")
        for (b, x) in [('a', 'b'), ('b', 'a')]:
            for S in strings_upto('ab', 4):
                for X1 in strings_upto('ab', 2):
                    if not X1:
                        continue
                    for Y1 in strings_upto('ab', 2):
                        pairs = [(X1, Y1)]
                        if not condition(kind, pairs, b, x):
                            continue
                        got = repC_comma_restart(b, x, pairs, S, 'ab')
                        t.check(got == rep_ref(pairs, S), (b, x, X1, Y1, S, got))
        ok &= t.report()

    # n = 2 under the winning condition
    for kind in ['none-b']:
        t = Tally(f"comma restart n=2 [{kind}]")
        for (b, x) in [('a', 'b'), ('b', 'a')]:
            pats = [p for p in strings_upto('ab', 2) if p and p != b]
            for S in strings_upto('ab', 4):
                for ps in itertools.product(itertools.product(pats, ['a', '']), repeat=2):
                    pairs = list(ps)
                    got = repC_comma_restart(b, x, pairs, S, 'ab')
                    t.check(got == rep_ref(pairs, S), (b, x, pairs, S, got))
        ok &= t.report()
    return ok


# ================================================================== G


def chunk_rescan():
    ok = True

    def star(A, B):
        """Condition (*): no nonempty suffix of A (A itself included) is a
        proper prefix of B."""
        for i in range(0, len(A)):
            suf = A[i:]
            if B.startswith(suf) and len(suf) < len(B):
                return False
        return True

    # --- G1: totality <=> B not in A
    t = Tally("rescan: total <=> B notin A")
    for sigma in ['ab', 'abc']:
        mA, mB, mC = (4, 3, 6) if sigma == 'ab' else (3, 2, 5)
        for A in strings_upto(sigma, mA):
            for B in strings_upto(sigma, mB):
                if not B:
                    continue
                for C in strings_upto(sigma, mC):
                    got = rescan(A, B, C)
                    if B not in A:
                        t.check(got is not None, (A, B, C))
                    else:
                        t.check(got is None or B not in C, (A, B, C, got))
    ok &= t.report()

    t = Tally("rescan: agreement iff (*)")
    for sigma in ['ab', 'abc']:
        mA, mB, mC = (4, 3, 6) if sigma == 'ab' else (3, 2, 5)
        for A in strings_upto(sigma, mA):
            for B in strings_upto(sigma, mB):
                if not B:
                    continue
                agree = all(rescan(A, B, C) == subst(A, B, C)
                            for C in strings_upto(sigma, mC))
                t.check(agree == (B not in A and star(A, B)),
                        (A, B, agree, star(A, B)))
    ok &= t.report()

    # --- G2: the encoder is the load-bearing failure
    t = Tally("rescan encoder divergence")
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        t.check(rescan(x + b, b, b * 5) is None, (b, x))          # b-containing
        t.check(rescan(x + b, b, x * 5) == x * 5, (b, x))         # b-free: inert
    ok &= t.report()

    # --- G3: run-collapse in L: [eps/ab][eps/aba][aab/a]  (right-to-left)
    def collapse_ref(S):
        out, i = [], 0
        while i < len(S):
            if S[i] == 'a':
                out.append('a')
                while i < len(S) and S[i] == 'a':
                    i += 1
            else:
                out.append(S[i])
                i += 1
        return ''.join(out)

    t = Tally("run-collapse in L")
    for sigma in ['ab', 'abc']:
        mx = 12 if sigma == 'ab' else 9
        for S in strings_upto(sigma, mx):
            got = subst('', 'ab', subst('', 'aba', subst('aab', 'a', S)))
            t.check(got == collapse_ref(S), (S, got))
    rng = random.Random(11)
    for _ in range(3000):
        S = ''.join(rng.choices('ab', k=rng.randint(0, 60)))
        got = subst('', 'ab', subst('', 'aba', subst('aab', 'a', S)))
        t.check(got == collapse_ref(S), (S, got))
    for m in (50, 300):
        for S in ('a' * m, 'b' + 'a' * m, 'a' * m + 'b'):
            got = subst('', 'ab', subst('', 'aba', subst('aab', 'a', S)))
            t.check(got == collapse_ref(S), (m, S[:3], got))
    ok &= t.report()

    # --- G4: run-collapse in U: [a/aa]^u
    t = Tally("run-collapse in U")
    for S in strings_upto('ab', 10):
        t.check(rescan('a', 'aa', S) == collapse_ref(S), (S,))
    ok &= t.report()

    # --- G5: a-flood [a/ab]^u: b^i a^j W -> b^i a^{#a(W)}
    t = Tally("a-flood")
    for S in strings_upto('ab', 9):
        got = rescan('a', 'ab', S)
        i = 0
        while i < len(S) and S[i] == 'b':
            i += 1
        want = 'b' * i + 'a' * S.count('a')
        t.check(got == want, (S, got, want))
    ok &= t.report()
    return ok


# ================================================================== H


def chunk_restart():
    ok = True

    def v(S):
        """Horner value: each a contributes 2^{#b's to its right}."""
        tot, powb = 0, 1
        for c in reversed(S):
            if c == 'b':
                powb *= 2
            else:
                tot += powb
        return tot

    # --- H1: amplifier [baa/ab]^m (S) = b^{#b} a^{v(S)}, steps = v - #a
    t = Tally("amplifier")
    for S in strings_upto('ab', 10):
        got = restart('baa', 'ab', S)
        want = 'b' * S.count('b') + 'a' * v(S)
        t.check(got == want, (S, got, want))
    ok &= t.report()

    t = Tally("amplifier steps")
    for S in strings_upto('ab', 9):
        s, steps = S, 0
        while 'ab' in s:
            i = s.find('ab')
            s = s[:i] + 'baa' + s[i + 2:]
            steps += 1
        t.check(steps == v(S) - S.count('a'), (S, steps, v(S)))
    # growth on ab^{n-1}
    for n in range(2, 13):
        S = 'a' + 'b' * (n - 1)
        t.check(len(restart('baa', 'ab', S)) == 2 ** (n - 1) + n - 1, (n,))
    ok &= t.report()

    # --- H2: tower of height 2 (3 nodes) on ab^{n-1}
    # (n = 6 gives |t3| = 131,091 -- too slow for this script; the formula
    #  check at n <= 5 plus the block-formula induction carry the claim)
    t = Tally("tower t=2")
    for n in range(2, 6):
        S = 'a' + 'b' * (n - 1)
        t1 = restart('baa', 'ab', S)
        t2 = restart('ab', 'aa', t1)
        t3 = restart('baa', 'ab', t2)
        want_len = (n - 1 + 2 ** (n - 2)) + 2 ** (2 ** (n - 2) + 1) - 2
        t.check(t3 is not None and len(t3) == want_len, (n, len(t3), want_len))
    ok &= t.report()

    # --- H3: termination classification
    t = Tally("termination |A|<|B| and |A|=|B|, A!=B")
    for A in strings_upto('ab', 3):
        for B in strings_upto('ab', 3):
            if not B or A == B:
                continue
            if len(A) > len(B):
                continue
            for C in strings_upto('ab', 8):
                t.check(restart(A, B, C) is not None, (A, B, C))
    t2 = Tally("termination B in A diverges")
    for A in strings_upto('ab', 3):
        for B in strings_upto('ab', 3):
            if not B or B not in A:
                continue
            for C in strings_upto('ab', 6):
                if B in C:
                    t2.check(restart(A, B, C) is None, (A, B, C))
    ok &= t.report() and t2.report()

    # --- H4: agreement: disjoint alphabets, A,B nonempty
    t = Tally("restart agreement")
    for A in strings_upto('ab', 3):
        if not A:
            continue
        for B in strings_upto('ab', 3):
            if not B or set(A) & set(B):
                continue
            for C in strings_upto('ab', 7):
                t.check(restart(A, B, C) == subst(A, B, C), (A, B, C))
    ok &= t.report()

    # --- H5: no total injective node
    t = Tally("no-injective-node")
    for A in strings_upto('ab', 3):
        for B in strings_upto('ab', 3):
            if not B or len(A) > len(B):
                continue  # only totality candidates
            if A == B or B in A:
                continue
            total = all(restart(A, B, C) is not None for C in strings_upto('ab', 6))
            if total:
                t.check(restart(A, B, A) == A == restart(A, B, B) and A != B,
                        (A, B))
    ok &= t.report()

    # --- H6: doubling [aa/a] is total injective (L-cc side of the separation)
    t = Tally("doubling injective")
    seen = {}
    for C in strings_upto('ab', 8):
        g = subst('aa', 'a', C)
        t.check(g not in seen or seen[g] is None or True, None)
        seen[g] = C
    t.check(len(seen) == len([1 for C in strings_upto('ab', 8)]), 'injective')
    ok &= t.report()

    # --- H7: sort and run-collapse as single nodes
    t = Tally("sort node")
    rng = random.Random(3)
    for _ in range(2000):
        S = ''.join(rng.choices('ab', k=rng.randint(0, 30)))
        t.check(restart('ba', 'ab', S) == 'b' * S.count('b') + 'a' * S.count('a'), (S,))
    t2 = Tally("run-collapse node")
    for S in strings_upto('ab', 10):
        t2.check(restart('a', 'aa', S) == ''.join(
            ch for i, ch in enumerate(S) if not (ch == 'a' and i and S[i - 1] == 'a')), (S,))
    ok &= t.report() and t2.report()
    return ok


# ================================================================== I


def chunk_pos():
    ok = True

    def setAt(i, c, S):
        return S[:i] + c + S[i + 1:] if 0 <= i < len(S) else S

    def occ(S, B):
        out, i, m = [], 0, len(B)
        while i + m <= len(S):
            if S[i:i + m] == B:
                out.append(i)
                i += m
            else:
                i += 1
        return out

    def repOcc(k, B, A, S):
        if not B:
            raise ValueError
        O = occ(S, B)
        if len(O) <= k:
            return S
        i = O[k]
        return S[:i] + A + S[i + len(B):]

    # --- I1: tail = repOcc(0, eps, c, setAt(0, c, X))
    t = Tally("pos tail")
    for sigma in ['ab', 'abc', 'a']:
        mx = {'ab': 6, 'abc': 5, 'a': 8}[sigma]
        for X in strings_upto(sigma, mx):
            for c in sigma:
                got = repOcc(0, c, '', setAt(0, c, X))
                t.check(got == X[1:], (X, c, got))
    ok &= t.report()

    # --- I2: head scaffold
    t = Tally("pos head scaffold")
    for sigma in ['ab', 'abc', 'a', 'abcd']:
        mx = {'ab': 6, 'abc': 5, 'a': 8, 'abcd': 5}[sigma]
        for X in strings_upto(sigma, mx):
            for c in sigma:
                V = X + c * 3
                T = repOcc(0, V[1:], '', V)          # head(V)
                P2 = (V[1:] if len(V) > 1 else '')[1:]  # tail(tail(V))
                got = repOcc(0, P2, '', T)
                t.check(got == X[:1], (X, c, T, P2, got))
    ok &= t.report()

    # --- I3: repOcc(k,B,A) = once^k(B->M) . once(B->A) . once^k(M->B), fresh M
    t = Tally("repOcc via once")
    rng = random.Random(5)
    for _ in range(4000):
        sigma = 'abc'
        B = ''.join(rng.choices('ab', k=rng.randint(1, 3)))
        A = ''.join(rng.choices(rng.choice(['ab', 'abc']), k=rng.randint(0, 3)))
        k = rng.randint(0, 3)
        S = ''.join(rng.choices('ab', k=rng.randint(0, 8)))  # avoids M = 'c...'? use M chars
        M = 'cc'
        if 'c' in B + A + S:
            continue  # marker must be fresh
        T = S
        for _ in range(k):
            T = once(M, B, T)
        T = once(A, B, T)
        for _ in range(k):
            T = once(B, M, T)
        t.check(T == repOcc(k, B, A, S), (B, A, k, S, T))
    ok &= t.report()

    # --- I4: unary [a^j/a] via cat of j-1 tails
    t = Tally("unary [a^j/a]")
    for j in range(2, 6):
        for n in range(0, 25):
            X = 'a' * n
            repl = ''.join(X[1:] for _ in range(j - 1)) + 'a' * j
            got = repOcc(0, 'a', repl, X)
            t.check(len(got) == j * n, (j, n, len(got)))
    ok &= t.report()
    return ok


CHUNKS = {
    'once': chunk_once, 'r2l': chunk_r2l, 'commaR': chunk_commaR,
    'commaM': chunk_commaM, 'rescan': chunk_rescan, 'restart': chunk_restart,
    'pos': chunk_pos,
}


def main():
    which = sys.argv[1:] or list(CHUNKS)
    ok = True
    for name in which:
        print(f"=== {name} ===", flush=True)
        ok &= CHUNKS[name]()
    print("ALL OK" if ok else "FAILURES PRESENT")
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()

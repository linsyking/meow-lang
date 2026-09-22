"""THE MARKING REDUCTION (once lane, round 5).

Claim under test (Theorem A of REPORT.md):
  If the constant-block once-op  [A/B]_1  is L-reachable (all constant
  A, B, on all strings), then the 3-argument once node
  g(X,Y,Z) = [X/Y]_1 Z  is L-reachable, over the same alphabet.

Construction (Sigma = {a,b}, comma x = b, cells ba/bb):
    N  = enc2(Y)          X' = enc2(X)
    g  = dec2( [X'/A0] [N/M] ORACLE([A0/M]_1) [M/N] enc2(Z) )
where M (marker) and A0 (edited-site tag) are fixed constants that are
FRESH in the comma-coded world (found structurally below).  Every pass
except the ORACLE is plain L (replace-all with computed pattern /
replacement -- legal nodes of L); the oracle is the hypothesis.

This script:
  (0) picks valid (M, A0) by a structural triple-junction freshness test;
  (1) verifies the reduction against the true once semantics on a large
      random battery over Sigma = {a,b} (and, with its own constants,
      Sigma = {a,b,c});
  (2) gold-checks the same reduction as a genuine AST with V-nodes and an
      oracle node, via lcore.den + oracle handling;
  (3) verifies Lemma (pass transfer, once primitive) for a concrete good
      binary coding: [c(A)/c(B)]_1 c(C) = c([A/B]_1 C).
Run: /usr/bin/python3 -W ignore verify_marking.py
"""
import itertools
import random
import sys

sys.path.insert(0, '.')
from lcore import K, V, C, S, den, Undefined  # noqa: E402

# --------------------------------------------------------------------------
# primitives (string level).  subst == paper def:subst for constant patterns
# (cross-checked in R1: == core.subst == str.replace).


def subst(A, B, T):
    return T.replace(B, A) if B else (_ for _ in ()).throw(ValueError("empty pattern"))


def once(A, B, C):
    """[A/B]_1 C  (B nonempty)."""
    i = C.find(B)
    return C if i < 0 else C[:i] + A + C[i + len(B):]


# --------------------------------------------------------------------------
# comma code enc2_x / dec2_x as pass pipelines (string level).
# enc2_x(S) = prod_{c != x} [xc/c] . [xx/x] S   (rightmost runs first)
# dec2_x(S) = [x/xx] . prod_{c != x} [c/xc] S


def enc2(x, sigma, S):
    T = subst(x + x, x, S)                       # [xx/x]: double the x's
    for c in [s for s in sigma if s != x]:
        T = subst(x + c, c, T)                   # [xc/c]: escape c
    return T


def dec2(x, sigma, S):
    T = S
    for c in [s for s in sigma if s != x]:        # run order: c_1 first
        T = subst(c, x + c, T)                   # [c/xc]: unescape c
    T = subst(x, x + x, T)                        # [x/xx]: halve x-runs
    return T


def enc2_ast(x, sigma, E):
    """AST: E -> enc2(x)(E)."""
    acc = E
    acc = S(K(x + x), K(x), acc)                  # runs FIRST
    for c in [s for s in sigma if s != x]:
        acc = S(K(x + c), K(c), acc)
    return acc


def dec2_ast(x, sigma, E):
    acc = E
    for c in [s for s in sigma if s != x]:
        acc = S(K(c), K(x + c), acc)
    acc = S(K(x), K(x + x), acc)                  # runs LAST
    return acc


# --------------------------------------------------------------------------
# structural freshness of (M, A0) in the comma-coded world.
# Tokens: cells (x d, d in sigma\{x} -- data letters), M, A0.
# Valid iff: in every product of <= 3 tokens, every occurrence of M (resp.
# A0) starts exactly at an M-token (resp. A0-token).  (Markers of length
# <= 5 cannot span 4+ tokens: they would contain 2 full cells = 4 chars
# plus 2 boundary chars > 5; longer markers are checked over 4 tokens.)


def token_fresh(M, A0, cells, ntok=4):
    toks = cells + [M, A0]
    for k in range(1, ntok + 1):
        for prod_t in itertools.product(toks, repeat=k):
            T = ''.join(prod_t)
            for marker in (M, A0):
                lm = len(marker)
                start = 0
                while True:
                    i = T.find(marker, start)
                    if i < 0:
                        break
                    # position i must be a token start of an equal token
                    pos, ok = 0, False
                    for t in prod_t:
                        if pos == i and t == marker:
                            ok = True
                        pos += len(t)
                    if not ok:
                        return False, (T, marker, i)
                    start = i + 1
    # also: markers must not occur in pure cell products (k = ntok covers)
    return True, None


def find_constants(sigma, x, maxlen=5):
    # cell set = {x*d : d in sigma}  -- INCLUDING the xx cell produced by
    # the doubling pass for the comma letter x itself.
    cells = [x + c for c in sigma]
    cand = []
    letters = sorted(set(sigma))
    for lm in range(2, maxlen + 1):
        for M in (''.join(t) for t in itertools.product(letters, repeat=lm)):
            if M in cells:
                continue
            for la in range(2, maxlen + 1):
                for A0 in (''.join(t) for t in itertools.product(letters, repeat=la)):
                    if A0 == M or A0 in cells:
                        continue
                    ok, _ = token_fresh(M, A0, cells)
                    if ok:
                        cand.append((M, A0))
        if cand:
            return cand
    return cand


# --------------------------------------------------------------------------
# THE REDUCTION (string level; oracle = once for the crux).


def once_node_via_marking(X, Y, Z, sigma, x, M, A0):
    """g(X,Y,Z) = [X/Y]_1 Z  built from L-passes + the constant-block oracle."""
    N = enc2(x, sigma, Y)      # needle image (computed pattern)
    Xp = enc2(x, sigma, X)     # replacement image (computed replacement)
    T0 = enc2(x, sigma, Z)
    T1 = T0.replace(N, M)       # [M/N]: mark all disjoint needle occurrences
    T2 = once(A0, M, T1)        # ORACLE: [A0/M]_1 -- the crux
    T3 = T2.replace(M, N)       # [N/M]: unmark the surviving sites
    T4 = T3.replace(A0, Xp)     # [X'/A0]: the edited site -> replacement
    return dec2(x, sigma, T4)


def once_node_via_marking_ast(Xv, Yv, Zv, sigma, x, M, A0):
    """Genuine AST with V-nodes; the crux is the oracle node ('O',)."""
    Nast = enc2_ast(x, sigma, Yv)
    Xast = enc2_ast(x, sigma, Xv)
    T0 = enc2_ast(x, sigma, Zv)
    T1 = S(K(M), Nast, T0)              # [M/N]
    T2 = ('O', M, A0, T1)               # oracle node: [A0/M]_1
    T3 = S(Nast, K(M), T2)              # [N/M]
    T4 = S(Xast, K(A0), T3)             # [X'/A0]
    return dec2_ast(x, sigma, T4)


def oden(e, args, oracle):
    """den with oracle nodes ('O', pat, repl, scrut)."""
    t = e[0]
    if t == 'O':
        T = oden(e[3], args, oracle)
        return oracle(e[2], e[1], T)
    if t == 'K':
        return e[1]
    if t == 'V':
        return args[e[1]]
    if t == 'C':
        return oden(e[1], args, oracle) + oden(e[2], args, oracle)
    if t == 'S':
        R, P, E = e[1], e[2], e[3]
        T = oden(E, args, oracle)
        B = oden(P, args, oracle)
        if B == '':
            raise Undefined()
        A = oden(R, args, oracle)
        return T.replace(B, A)
    raise ValueError(t)


# --------------------------------------------------------------------------
# battery


def battery(sigma, ntr, maxlen, seed):
    rng = random.Random(seed)
    out = []
    for _ in range(ntr):
        X = ''.join(rng.choice(sigma) for _ in range(rng.randrange(0, maxlen)))
        Y = ''.join(rng.choice(sigma) for _ in range(rng.randrange(1, maxlen)))
        Z = ''.join(rng.choice(sigma) for _ in range(rng.randrange(0, maxlen + 2)))
        out.append((X, Y, Z))
    # add adversarial shapes: overlaps, repeats, Y spanning Z, etc.
    for (X, Y, Z) in [
        ('', 'a', 'aaa'), ('', 'b', 'bbb'), ('a', 'ab', 'abab'),
        ('ab', 'a', 'aaaa'), ('b', 'ab', 'ba'), ('a', 'b', 'abababab'),
        ('aa', 'aba', 'ababa'), ('b', 'bb', 'bbb'), ('a', 'bb', 'abba'),
        ('ba', 'ab', 'aabb'), ('', 'ab', 'abab'), ('ab', 'ab', 'ab'),
        ('aab', 'aab', 'aabaabaab'), ('b', 'ab', 'aabbaabb'),
        ('a', 'a', 'a'), ('b', 'b', 'b'), ('ab', 'b', 'abbab'),
        ('a', 'ba', 'aabbaa'), ('bb', 'bab', 'bababbab'),
    ]:
        if all(c in sigma for c in X + Y + Z):
            out.append((X, Y, Z))
    return out


def run_case(sigma, x, M, A0, ntr, maxlen, seed, tag):
    ok = 0
    bad = []
    for (X, Y, Z) in battery(sigma, ntr, maxlen, seed):
        want = once(X, Y, Z)
        got = once_node_via_marking(X, Y, Z, sigma, x, M, A0)
        if got == want:
            ok += 1
        else:
            bad.append((X, Y, Z, want, got))
    print(f"[{tag}] string-level reduction: {ok} ok, {len(bad)} FAIL"
          f"  (M={M!r}, A0={A0!r}, x={x!r}, sigma={''.join(sigma)})")
    for b in bad[:5]:
        print("   FAIL:", b)
    return not bad


def run_gold(sigma, x, M, A0, ntr, maxlen, seed, tag):
    """AST-level gold check with oracle node, via oden (den + oracle)."""
    rng = random.Random(seed + 1)
    ok = 0
    bad = []
    cases = battery(sigma, ntr // 2, maxlen, seed)
    for _ in range(ntr // 2):
        X = ''.join(rng.choice(sigma) for _ in range(rng.randrange(0, maxlen)))
        Y = ''.join(rng.choice(sigma) for _ in range(rng.randrange(1, maxlen)))
        Z = ''.join(rng.choice(sigma) for _ in range(rng.randrange(0, maxlen + 2)))
        cases.append((X, Y, Z))
    for (X, Y, Z) in cases:
        ast = once_node_via_marking_ast(V(0), V(1), V(2), sigma, x, M, A0)
        try:
            got = oden(ast, (X, Y, Z), once)
        except Undefined:
            got = None
        want = once(X, Y, Z)
        if got == want:
            ok += 1
        else:
            bad.append((X, Y, Z, want, got))
    print(f"[{tag}] AST-level (V-nodes + oracle): {ok} ok, {len(bad)} FAIL")
    for b in bad[:5]:
        print("   FAIL:", b)
    return not bad


# --------------------------------------------------------------------------
# Lemma: pass transfer for the once primitive, on a concrete good coding.
# Good coding binary->binary: the double-a family D_5 = {aabab, aabbb}.


def is_comma_free(D):
    ell = len(D[0])
    for u, v in itertools.product(D, repeat=2):
        T = u + v
        for w in D:
            for p in range(1, ell):
                if w in T[p:p + ell]:
                    return False, (u, v, w, p)
    return True, None


def run_transfer():
    D = {'a': 'aabab', 'b': 'aabbb'}
    okcf, wit = is_comma_free(list(D.values()))
    print(f"[transfer] D5 comma-free: {okcf} {wit if not okcf else ''}")
    rng = random.Random(7)
    ok, bad = 0, 0
    for _ in range(3000):
        A = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 4)))
        B = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 4)))
        C = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 9)))
        c = lambda s: ''.join(D[ch] for ch in s)
        lhs = once(c(A), c(B), c(C))
        rhs = c(once(A, B, C))
        if lhs == rhs:
            ok += 1
        else:
            bad += 1
            if bad < 3:
                print("   transfer FAIL:", A, B, C, lhs, rhs)
    print(f"[transfer] once-primitive pass transfer on D5: {ok} ok, {bad} FAIL")
    return okcf and not bad


def main():
    random.seed()
    all_ok = True
    # binary: comma x = b, cells ba/bb
    cands = find_constants(list('ab'), 'b')
    print(f"[consts] binary candidate (M,A0) pairs (first 3): {cands[:3]} "
          f"(total {len(cands)})")
    M, A0 = cands[0]
    all_ok &= run_case(list('ab'), 'b', M, A0, 4000, 7, 11, 'bin')
    all_ok &= run_gold(list('ab'), 'b', M, A0, 1500, 6, 11, 'bin')
    # ternary: comma x = c, cells ca/cb
    cands3 = find_constants(list('abc'), 'c')
    print(f"[consts] ternary candidates (first 3): {cands3[:3]} "
          f"(total {len(cands3)})")
    M3, A03 = cands3[0]
    all_ok &= run_case(list('abc'), 'c', M3, A03, 4000, 6, 12, 'tern')
    all_ok &= run_gold(list('abc'), 'c', M3, A03, 1500, 5, 12, 'tern')
    all_ok &= run_transfer()
    print("ALL GREEN" if all_ok else "FAILURES PRESENT")
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main())

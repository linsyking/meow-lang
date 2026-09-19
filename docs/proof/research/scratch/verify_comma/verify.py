#!/usr/bin/env python3
"""Independent verification of the comma-code construction (research/multi.md §4.2).

Everything here is reimplemented from the report's specification and the paper's
definitions only -- none of the research agents' scripts are used. Checks:

  1. Anchors against the Lean development's #eval outputs (subst, repRef, repC).
  2. The explicit 10-pass pipeline of multi.md §4.5 (pass list must match).
  3. Exhaustive agreement repC_comma == rep_ref on small domains.
  4. The escape round trip without hypothesis (H2) (multi.md §4.3 corollary).

Usage: verify.py <chunk>   with chunk in {base, n2a, n2b, n3, tri, adv}
"""

import itertools
import random
import sys


def subst(A, B, C):
    """[A/B]C -- paper Definition 1 (greedy leftmost, non-overlapping, never
    restarting inside inserted text). Empty pattern never matches (identity)."""
    if not B:
        return C
    out, i, n, m = [], 0, len(C), len(B)
    while i < n:
        if C[i:i + m] == B:
            out.append(A)
            i += m
        else:
            out.append(C[i])
            i += 1
    return ''.join(out)


# ---- The paper's original construction (for anchors / failure cross-check) ----

def enc_p(b, x, W):
    return subst(x + b, b, W)


def dec_p(b, x, T):
    return subst(b, x + b, T)


def repC_paper(b, x, pairs, S):
    T = enc_p(b, x, S)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc_p(b, x, Xi)
        T = subst(x + b * (i + 1), EXi, T)
        T = subst(EXi + b, x + b * (i + 2), T)
    for i in range(len(pairs), 0, -1):
        T = subst(enc_p(b, x, pairs[i - 1][1]), x + b * (i + 1), T)
    return dec_p(b, x, T)


# ---- The comma-code construction (multi.md §4.2), as baseline passes ----

def enc2(b, x, W, sigma):
    """enc2 = [xx/x] then [xc/c] for every c in sigma, c != x."""
    T = subst(x + x, x, W)
    for c in sigma:
        if c != x:
            T = subst(x + c, c, T)
    return T


def dec2(b, x, T, sigma):
    """dec2 = [c/xc] for every c in sigma, c != x, then [x/xx]."""
    for c in sigma:
        if c != x:
            T = subst(c, x + c, T)
    return subst(x, x + x, T)


def repC_comma(b, x, pairs, S, sigma):
    """dec2 o instantiate(n..1) o renameRepair(1..n) o enc2 -- all via subst."""
    T = enc2(b, x, S, sigma)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc2(b, x, Xi, sigma)
        T = subst(x + b * (i + 1), EXi, T)           # rename  [m_i / E_Xi]
        T = subst(EXi + b, x + b * (i + 2), T)        # repair  [E_Xi·b / m_{i+1}]
    for i in range(len(pairs), 0, -1):
        T = subst(enc2(b, x, pairs[i - 1][1], sigma), x + b * (i + 1), T)  # instantiate
    return dec2(b, x, T, sigma)


def comma_pipeline(b, x, pairs, sigma):
    """The pass list of repC_comma, in application order (A, B) = [A/B]."""
    passes = [(x + x, x)]
    for c in sigma:
        if c != x:
            passes.append((x + c, c))
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc2(b, x, Xi, sigma)
        passes.append((x + b * (i + 1), EXi))
        passes.append((EXi + b, x + b * (i + 2)))
    for i in range(len(pairs), 0, -1):
        passes.append((enc2(b, x, pairs[i - 1][1], sigma), x + b * (i + 1)))
    for c in sigma:
        if c != x:
            passes.append((c, x + c))
    passes.append((x, x + x))
    return passes


# ---- The freezing semantics (paper Definition rep), independent implementation ----

def rep_ref(pairs, S):
    frozen = [0] * len(S)  # 0 = unfrozen, else round tag
    for i, (Xi, _) in enumerate(pairs, 1):
        if not Xi:
            continue  # X = ε is undefined; excluded from all domains here
        m = len(Xi)
        j = 0
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


# ---- Domain helpers ----

def strings_upto(sigma, maxlen):
    return [''.join(t) for L in range(maxlen + 1)
            for t in itertools.product(sigma, repeat=L)]


def nonempty_upto(sigma, maxlen):
    return [s for s in strings_upto(sigma, maxlen) if s]


FAILURES = []
EVALS = 0


def check(b, x, pairs, S, sigma):
    global EVALS
    EVALS += 1
    got = repC_comma(b, x, pairs, S, sigma)
    want = rep_ref(pairs, S)
    if got != want:
        FAILURES.append((b, x, pairs, S, sigma, want, got))
        if len(FAILURES) <= 10:
            print(f"FAIL b={b} x={x} pairs={pairs} S={S!r} sigma={sigma} "
                  f"want={want!r} got={got!r}", flush=True)


def sweep(sigma, b, x, npairs, patmax, repmax, strmax, progress_every=200_000):
    pats = nonempty_upto(sigma, patmax)
    reps = strings_upto(sigma, repmax)
    strs = strings_upto(sigma, strmax)
    pairsets = list(itertools.product(itertools.product(pats, reps), repeat=npairs))
    n = 0
    for pairset in pairsets:
        pairs = list(pairset)
        for S in strs:
            check(b, x, pairs, S, sigma)
            n += 1
            if progress_every and n % progress_every == 0:
                print(f"  ... {n}/{len(pairsets) * len(strs)} evals, "
                      f"{len(FAILURES)} failures", flush=True)
    print(f"sweep sigma={sigma} (b,x)=({b},{x}) n={npairs} pat<={patmax} "
          f"rep<={repmax} str<={strmax}: {n} evals, {len(FAILURES)} failures "
          f"(cumulative)", flush=True)


# ---- Escape functions (paper Definition, escaping charset) ----

def escaping_functions(sigma):
    """Yield (U_enumerated_with_fixed_point_first, f) for every bijection
    f: U -> V (some V) with f(u1) = u1, u1 first in the enumeration."""
    for r in range(1, len(sigma) + 1):
        for U in itertools.combinations(sigma, r):
            for u1 in U:
                rest = [c for c in U if c != u1]
                Uen = [u1] + rest
                others = [c for c in sigma if c != u1]
                for img in itertools.permutations(others, r - 1):
                    f = {Uen[i]: (u1 if i == 0 else img[i - 1]) for i in range(r)}
                    yield Uen, f


# ---- Chunks ----

def chunk_base():
    # 1. Anchors against Lean #eval outputs (Subst.lean, run 2026-09-19).
    assert subst('ab', 'b', 'b') == 'ab'
    assert subst('ab', 'b', 'ab') == 'aab'
    assert subst('a', 'a', 'aa') == 'aa'
    assert subst('xy', 'x', 'yx') == 'yxy'
    assert subst('aa', 'aba', 'aba') == 'aa'
    assert subst('', 'a', 'baa') == 'b'
    assert rep_ref([('a', 'ba')], 'aba') == 'babba'
    assert rep_ref([('ab', 'c'), ('ba', 'aa')], 'aba') == 'ca'
    assert rep_ref([('ab', 'bbba'), ('bbb', 'aa')], 'abaab') == 'bbbaabbba'
    assert repC_paper('a', 'b', [('ab', 'bbba'), ('bbb', 'aa')], 'abaab') == 'bbbaaab'
    print("anchors vs Lean: OK", flush=True)

    # 2. The §4.5 pipeline: pass list and end-to-end equality.
    pairs = [('ab', 'bbba'), ('bbb', 'aa')]
    expected = [
        ("bb", "b"), ("ba", "a"),
        ("baa", "babb"), ("babba", "baaa"),
        ("baaa", "bbbbbb"), ("bbbbbba", "baaaa"),
        ("baba", "baaa"),
        ("bbbbbbba", "baa"),
        ("a", "ba"), ("b", "bb"),
    ]
    pl = comma_pipeline('a', 'b', pairs, 'ab')
    assert pl == expected, pl
    T = 'abaab'
    for (A, B) in pl:
        T = subst(A, B, T)
    assert T == repC_comma('a', 'b', pairs, 'abaab', 'ab') == 'bbbaabbba'
    print("section 4.5 pipeline: OK (10 passes, end-to-end = freezing result)",
          flush=True)

    # 3. n=1 exhaustive over {a,b}, both (b,x).
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        sweep('ab', b, x, 1, 3, 3, 6)

    # 4. Escape round trip without (H2), and construction agreement on escape pairs.
    sigma = 'abc'
    strs6 = strings_upto(sigma, 6)
    strs5 = strings_upto(sigma, 5)
    nfs = 0
    for Uen, f in escaping_functions(sigma):
        nfs += 1
        u1 = Uen[0]
        esc = [(u, u1 + f[u]) for u in Uen]
        une = [(u1 + f[u], u) for u in Uen]
        for S in strs6:
            global EVALS
            EVALS += 1
            if rep_ref(une, rep_ref(esc, S)) != S:
                FAILURES.append(('escape-roundtrip', Uen, f, S))
                print(f"FAIL escape round trip U={Uen} f={f} S={S!r}", flush=True)
        for (b, x) in [('a', 'b'), ('b', 'a'), ('a', 'c'), ('c', 'a'), ('b', 'c'), ('c', 'b')]:
            for S in strs5:
                check(b, x, esc, S, sigma)
                check(b, x, une, S, sigma)
    print(f"escape: {nfs} escaping functions, round trips + construction "
          f"agreement over all 6 (b,x): {len(FAILURES)} failures (cumulative)",
          flush=True)


def chunk_n2a():
    sweep('ab', 'a', 'b', 2, 3, 2, 4)


def chunk_n2b():
    sweep('ab', 'b', 'a', 2, 3, 2, 4)


def chunk_n3():
    sweep('ab', 'a', 'b', 3, 2, 1, 4)


def chunk_tri():
    for (b, x) in [('a', 'b'), ('b', 'c')]:
        sweep('abc', b, x, 1, 2, 2, 4)
    sweep('abc', 'a', 'b', 2, 2, 1, 3)
    sweep('abc', 'b', 'c', 2, 2, 1, 3)


def chunk_adv():
    # Shadowing instance: every string over {a,b} up to length 8, both (b,x).
    pairs = [('ab', 'bbba'), ('bbb', 'aa')]
    for S in strings_upto('ab', 8):
        for (b, x) in [('a', 'b'), ('b', 'a')]:
            check(b, x, pairs, S, 'ab')
    print(f"shadowing-instance sweep: cumulative {EVALS} evals, "
          f"{len(FAILURES)} failures", flush=True)

    # Marker-shaped / escape-colliding patterns, n=2.
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        pats = ['b', 'baa', 'baaa', 'ab', 'bb']
        reps = ['', 'a', 'ba']
        strs = strings_upto('ab', 6)
        for pset in itertools.product(itertools.product(pats, reps), repeat=2):
            pairs = list(pset)
            for S in strs:
                check(b, x, pairs, S, 'ab')
    print(f"marker-shaped sweep: cumulative {EVALS} evals, "
          f"{len(FAILURES)} failures", flush=True)

    # Randomized stress.
    rng = random.Random(20260919)
    for t in range(30_000):
        sigma = ''.join(rng.sample('abcd', rng.choice([2, 3, 4])))
        b, x = rng.sample(sigma, 2)
        n = rng.randint(1, 4)
        pairs = [(''.join(rng.choices(sigma, k=rng.randint(1, 4))),
                  ''.join(rng.choices(sigma, k=rng.randint(0, 3))))
                 for _ in range(n)]
        S = ''.join(rng.choices(sigma, k=rng.randint(0, 20)))
        check(b, x, pairs, S, sigma)
    print(f"randomized stress: cumulative {EVALS} evals, "
          f"{len(FAILURES)} failures", flush=True)


CHUNKS = {
    'base': chunk_base,
    'n2a': chunk_n2a,
    'n2b': chunk_n2b,
    'n3': chunk_n3,
    'tri': chunk_tri,
    'adv': chunk_adv,
}


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in CHUNKS:
        print(__doc__)
        sys.exit(2)
    CHUNKS[sys.argv[1]]()
    print(f"RESULT chunk={sys.argv[1]} evals={EVALS} failures={len(FAILURES)}")
    sys.exit(1 if FAILURES else 0)


if __name__ == '__main__':
    main()

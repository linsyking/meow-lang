"""Randomized stress test of the comma-code construction + edge cases.

Also: escape/unescape round trip without the paper's (H2) [x notin V],
in the freezing semantics (which the comma construction computes).
"""
import sys, random, itertools
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import rep_ref, repC_paper, repC_comma, all_strings

random.seed(20260919)

fails = 0
tests = 0

# ---- randomized stress: bigger patterns, longer strings, n up to 5 ---------
for trial in range(400):
    alph = random.choice(["ab", "abc"])
    n = random.randint(1, 5)
    pairs = []
    for _ in range(n):
        XL = random.randint(1, 4)
        YL = random.randint(0, 4)
        X = "".join(random.choice(alph) for _ in range(XL))
        Y = "".join(random.choice(alph + "de") for _ in range(YL))
        pairs.append((X, Y))
    SL = random.randint(0, 24)
    S = "".join(random.choice(alph) for _ in range(SL))
    tests += 1
    if repC_comma("a", "b", pairs, S, alph) != rep_ref(pairs, S):
        fails += 1
        print("COMMA FAIL:", pairs, S, rep_ref(pairs, S), repC_comma("a", "b", pairs, S, alph))
        if fails > 5:
            break
print(f"randomized stress: {tests} trials, {fails} failures")

# ---- adversarial hand-picked cases ----------------------------------------
adversarial = [
    # (alphabet, pairs, strings)  -- marker-shaped patterns, deletions,
    # patterns equal to markers, replacements shaped like markers...
    ("ab", [("b", "a"), ("a", "b")], all_strings("ab", 7)),          # swap
    ("ab", [("b", ""), ("bb", "a")], all_strings("ab", 7)),           # deletion + (H)-violating
    ("ab", [("baa", "x"), ("a", "baa")], all_strings("ab", 6)),       # marker-shaped text
    ("ab", [("ab", "bbba"), ("bbb", "aa")], all_strings("ab", 8)),    # the shadowing instance
    ("ab", [("b", "baa"), ("ba", "aa")], all_strings("ab", 6)),       # replacements make markers
    ("ab", [("bb", "a"), ("a", "bb"), ("ab", "")], all_strings("ab", 6)),
    ("abc", [("b", ""), ("ca", "b"), ("ab", "bb")], all_strings("abc", 5)),
    ("ab", [("ab", "b"), ("b", "ab")], all_strings("ab", 7)),         # self-referential
    ("ab", [("a", ""), ("", None)][:1] + [("b", "")], all_strings("ab", 7)),  # delete everything
]
for alph, pairs, strings in adversarial:
    bad = [(S, rep_ref(pairs, S), repC_comma("a", "b", pairs, S, alph))
           for S in strings if repC_comma("a", "b", pairs, S, alph) != rep_ref(pairs, S)]
    tests += len(strings)
    fails += len(bad)
    tag = "OK " if not bad else "FAIL"
    print(f"[{tag}] adversarial pairs={pairs} over {len(strings)} strings", bad[:2])

# same with the other construction char order (b,x) = (b,a): swap roles
def swap(s):
    return s.replace("a", "A").replace("b", "a").replace("A", "b")
for alph, pairs, strings in adversarial:
    pairs_sw = [(swap(X), swap(Y)) for X, Y in pairs]
    bad = 0
    for S in strings:
        Ssw = swap(S)
        if repC_comma("b", "a", pairs_sw, Ssw, alph) != rep_ref(pairs_sw, Ssw):
            bad += 1
    tests += len(strings)
    fails += bad
    print(f"[{'OK ' if not bad else 'FAIL'}] adversarial (swapped b,x) pairs={pairs_sw}", )

print(f"\nTOTAL: {tests} tests, {fails} failures")

# ---------------------------------------------------------------------------
# Escape/unescape without (H2): the paper's Character Escaping theorem
# assumed x notin V only to apply its rep_n construction.  Semantically, does
# the round trip unescape(escape(S)) = S hold without it?  Test ALL escaping
# functions on small alphabets with the fixed point enumerated first (H1).
# ---------------------------------------------------------------------------
print("\n--- escape/unescape round trip, dropping (H2) ---")
bad_esc = 0
tot_esc = 0
for Sigma in ["abc", "abcd"]:
    chars = list(Sigma)
    # all nonempty U subsetof Sigma, all bijections f: U -> V subsetof Sigma
    # with a fixed point; enumerate small cases only.
    from itertools import combinations, permutations
    for r in range(1, min(len(chars), 3) + 1):
        for U in combinations(chars, r):
            fixed = [u for u in U if u in chars]
            # choose the fixed point u_k and V with f(U) = V, f injective
            for uk in U:
                rest = [u for u in U if u != uk]
                # V must contain f(uk)=uk; images of rest: any injective choice
                others = [c for c in chars]
                for perm in permutations([c for c in chars if c != uk], len(rest)):
                    V = set([uk]) | set(perm)
                    f = dict(zip(rest, perm)); f[uk] = uk
                    if f[uk] != uk:
                        continue
                    # H1: enumerate u_1 = u_k first
                    Us = [uk] + rest
                    tot_esc += 1
                    def esc(S):
                        return rep_ref([(u, uk + f[u]) for u in Us], S)
                    def unesc(T):
                        return rep_ref([(uk + f[u], u) for u in Us], T)
                    for S in all_strings(Sigma, 6):
                        if unesc(esc(S)) != S:
                            bad_esc += 1
                            if bad_esc < 6:
                                print("  ESC FAIL:", Sigma, Us, f, S,
                                      esc(S), unesc(esc(S)))
                            break
print(f"escape round trip without (H2): {tot_esc} escaping functions tested, "
      f"{bad_esc} failures")

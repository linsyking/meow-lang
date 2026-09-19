"""Extended verification of the comma-code construction:
  - larger randomized sweep (patterns <= 5, strings <= 40, n <= 6)
  - marker-shaped patterns with many rounds (n up to 6): patterns chosen
    among the markers m_i themselves and near-markers
  - alphabets of size 2..5 with several construction-char choices
"""
import sys, random, itertools
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import rep_ref, repC_comma, all_strings

random.seed(777)
fails = 0

# 1. big randomized sweep
t = 0
for trial in range(3000):
    alph = random.choice(["ab", "abc", "abcd", "abcde"])
    n = random.randint(1, 6)
    pairs = []
    for _ in range(n):
        X = "".join(random.choice(alph) for _ in range(random.randint(1, 5)))
        Y = "".join(random.choice(alph + "WXYZ") for _ in range(random.randint(0, 5)))
        pairs.append((X, Y))
    S = "".join(random.choice(alph) for _ in range(random.randint(0, 40)))
    t += 1
    if repC_comma("a", "b", pairs, S, alph) != rep_ref(pairs, S):
        fails += 1
        print("FAIL rand:", pairs, S)
        if fails > 3: break
print(f"randomized (n<=6, |X|<=5, |S|<=40, |Sigma|<=5): {t} trials, {fails} failures")

# 2. marker-shaped patterns with many rounds: construction (b,x)=(a,b), so
#    m_i = b a^{i+1}: "baa", "baaa", ..., plus near-markers.
pairs_set = []
for extra in ["", "b", "ab", "bb"]:
    pats = ["ba" + "a" * i + extra for i in range(1, 7)]   # markers + suffix
    pats = [p for p in pats if p]
    pairs = [(p, "Z" + str(i)) for i, p in enumerate(pats)]
    pairs_set.append(pairs)
    bad = 0
    for S in all_strings("ab", 7):
        if repC_comma("a", "b", pairs, S, "ab") != rep_ref(pairs, S):
            bad += 1
    print(f"marker-shaped rounds (n={len(pairs)}, extra={extra!r}): "
          f"{'OK' if not bad else f'{bad} FAILURES'} over 255 strings")

# 3. construction chars in other positions for a ternary alphabet
for (bc, xc) in [("a", "b"), ("a", "c"), ("b", "a"), ("b", "c"), ("c", "a"), ("c", "b")]:
    alph = "abc"
    pats = ["a", "b", "c", "ab", "bc", xc + bc, xc + xc]
    bad = 0
    tot = 0
    for X1, X2 in itertools.product(pats, repeat=2):
        for Y1, Y2 in [("", "a"), (xc, ""), (bc + xc, "b")]:
            pairs = [(X1, Y1), (X2, Y2)]
            tot += 1
            for S in all_strings(alph, 6):
                if repC_comma(bc, xc, pairs, S, alph) != rep_ref(pairs, S):
                    bad += 1
                    if bad < 3:
                        print(f"  FAIL (b,x)=({bc},{xc}):", pairs, S)
    print(f"ternary with (b,x)=({bc},{xc}): {tot} pattern-set families, "
          f"all strings len<=6: {'OK' if not bad else str(bad)+' FAILURES'}")

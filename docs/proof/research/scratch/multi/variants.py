"""Secondary question: one-pass multi-pattern variants vs round-by-round
freezing.

  freezing  (F): the paper's Definition (Multiple Substitution, Semantics)
  onepass-L (L): one left-to-right pass, at each position take the LONGEST
                 matching pattern
  onepass-R (R): one pass, at each position take the FIRST (lowest-index)
                 matching pattern
In both one-pass variants the scan resumes after the replacement text.
"""
import sys, itertools
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import rep_ref, rep_onepass, all_strings

def F(pairs, S): return rep_ref(pairs, S)
def L(pairs, S): return rep_onepass(pairs, S, "longest")
def R(pairs, S): return rep_onepass(pairs, S, "first")

D = all_strings("ab", 7)  # 255

def agree(f, g, pairs):
    return all(f(pairs, S) == g(pairs, S) for S in D)

# ---- 1. minimal separating examples ---------------------------------------
print("--- separating examples (verified on the stated instance) ---")
ex1 = [("a", "1"), ("ab", "2")]           # X1=a->1, X2=ab->2
S = "ab"
print(f"freezing  vs onepass-L: pairs={ex1}, S={S!r}: "
      f"F={F(ex1,S)!r} L={L(ex1,S)!r} -> "
      f"{'DIFFER' if F(ex1,S)!=L(ex1,S) else 'same'}")
ex2 = [("bc", "1"), ("ab", "2")]
S = "abc"
print(f"freezing  vs onepass-R: pairs={ex2}, S={S!r}: "
      f"F={F(ex2,S)!r} R={R(ex2,S)!r} -> "
      f"{'DIFFER' if F(ex2,S)!=R(ex2,S) else 'same'}")
ex3 = [("a", "1"), ("ab", "2")]
S = "ab"
print(f"onepass-L vs onepass-R: pairs={ex3}, S={S!r}: "
      f"L={L(ex3,S)!r} R={R(ex3,S)!r} -> "
      f"{'DIFFER' if L(ex3,S)!=R(ex3,S) else 'same'}")

# ---- 2. does a permutation of the pattern list turn freezing into an
#         onepass variant? ----------------------------------------------------
print("\n--- freezing vs onepass under permutation of the pattern list ---")
pats = ["a", "b", "aa", "ab", "ba", "bb", "aba", "bab"]
reps = {"1": None, "2": None}
n_perm_L = n_perm_R = n_tot = 0
no_L, no_R = [], []
for Xs in itertools.product(pats, repeat=2):
    pairs = [(Xs[0], "1"), (Xs[1], "2")]
    n_tot += 1
    okL = agree(F, L, pairs) or agree(F, L, pairs[::-1])
    okR = agree(F, R, pairs) or agree(F, R, pairs[::-1])
    n_perm_L += okL
    n_perm_R += okR
    if not okL and len(no_L) < 3: no_L.append(Xs)
    if not okR and len(no_R) < 3: no_R.append(Xs)
print(f"n=2 pattern pairs: {n_tot}; freezing == onepass-L (possibly reversed) "
      f"on {n_perm_L}/{n_tot}; == onepass-R on {n_perm_R}/{n_tot}")
print("  e.g. not captured by reversal (L):", no_L)
print("  e.g. not captured by reversal (R):", no_R)

# ---- 3. class-level comparison on a small function space --------------------
# Function f_P : S |-> P(S) with P drawn from: ordered pattern lists of length
# 1..3 over a pool, replacements fixed distinct markers.  Compare the SET of
# functions induced by each semantics (as functions on D).
print("\n--- class-level comparison (functions on strings over {a,b} len<=7) ---")
pool = ["a", "b", "ab", "ba", "aa", "bb", "aab", "bba"]
def funcs(sem, maxn):
    res = {}
    for n in range(1, maxn + 1):
        for Xs in itertools.product(pool, repeat=n):
            if len(set(Xs)) < n:
                continue
            pairs = [(X, str(i)) for i, X in enumerate(Xs)]
            sig = tuple(sem(pairs, S) for S in D)
            res.setdefault(sig, pairs)
    return res

FF = funcs(F, 3)
LL = funcs(L, 2)
RR = funcs(R, 2)
print(f"|freezing class| = {len(FF)}  (pattern lists of len 1..3 from pool of {len(pool)})")
print(f"|onepass-L class| = {len(LL)}  (len 1..2)")
print(f"|onepass-R class| = {len(RR)}  (len 1..2)")
only_L = [v for k, v in LL.items() if k not in FF]
only_R = [v for k, v in RR.items() if k not in FF]
print(f"onepass-L functions NOT expressible as freezing over the same pool: {len(only_L)}; e.g. {only_L[:2]}")
print(f"onepass-R functions NOT expressible as freezing over the same pool: {len(only_R)}; e.g. {only_R[:2]}")
only_F = [v for k, v in FF.items() if k not in LL and k not in RR]
print(f"freezing functions NOT expressible as either onepass variant: {len(only_F)}; e.g. {only_F[:2]}")
common_LR = set(LL) & set(RR)
print(f"onepass-L and onepass-R classes share {len(common_LR)} functions; "
      f"L-only: {len(set(LL)-set(RR))}, R-only: {len(set(RR)-set(LL))}")

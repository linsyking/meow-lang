"""Minimize the flat pipeline for the shadowing instance, and run a bounded
exhaustive search for shorter constant pipelines.

f(S) = rep_2(S; ab->bbba; bbb->aa) over Sigma={a,b}.
"""
import sys, itertools, time
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import subst, rep_ref, enc2, all_strings

pairs = [("ab", "bbba"), ("bbb", "aa")]
b, x, alphabet = "a", "b", "ab"
TARGET = lambda S: rep_ref(pairs, S)

def build(keep_repair=True, keep_rename2=True):
    flat = [(x + x, x)] + [(x + c, c) for c in alphabet if c != x]
    for i, (X, _) in enumerate(pairs, start=1):
        flat.append((x + b * (i + 1), enc2(b, x, X, alphabet)))
        if keep_repair:
            flat.append((enc2(b, x, X, alphabet) + b, x + b * (i + 2)))
    for i in range(len(pairs), 0, -1):
        Y = pairs[i - 1][1]
        flat.append((enc2(b, x, Y, alphabet), x + b * (i + 1)))
    flat += [(c, x + c) for c in alphabet if c != x] + [(x, x + x)]
    return flat

def run(flat, S):
    T = S
    for R, P in flat:
        T = subst(R, P, T)
    return T

D = all_strings("ab", 10)  # 2047 strings
full = build()
bad = [S for S in D if run(full, S) != TARGET(S)]
print(f"full construction pipeline ({len(full)} passes): {'OK' if not bad else bad[:3]}")

# Greedy pass-elimination: drop each pass, see if still correct on D.
def correct(flat):
    return all(run(flat, S) == TARGET(S) for S in D)

flat = full[:]
i = 0
while i < len(flat):
    cand = flat[:i] + flat[i + 1:]
    if correct(cand):
        print(f"  pass {i+1} ({flat[i]}) is redundant -> removed")
        flat = cand
    else:
        i += 1
print(f"minimized pipeline: {len(flat)} passes")
for i, (R, P) in enumerate(flat):
    print(f"  {i+1:2d}. [{R}/{P}]")

# Also: does the PAPER's construction on this instance fail? (sanity)
from core import repC_paper
badp = [S for S in D if repC_paper("a", "b", pairs, S) != TARGET(S)]
print(f"paper construction fails on {len(badp)} of {len(D)} strings, e.g. {badp[:4]}")

# ---------------------------------------------------------------------------
# Bounded exhaustive search for constant pipelines computing f.
# Passes [R/P]: P nonempty over {a,b}, |P|<=plen; R over {a,b}, |R|<=rlen.
# Pipelines of depth <= depth, tested on all strings len<=6 (127), candidates
# re-verified on len<=10 (2047).
# ---------------------------------------------------------------------------
def search(depth, plen, rlen, domain, label):
    pats = ["".join(t) for L in range(1, plen + 1)
            for t in itertools.product("ab", repeat=L)]
    reps = ["".join(t) for L in range(0, rlen + 1)
            for t in itertools.product("ab", repeat=L)]
    passes = [(R, P) for P in pats for R in reps]
    t0 = time.time()
    # BFS with signature dedup
    ident = tuple(domain)
    seen = {ident: []}
    frontier = dict(seen)
    found = None
    for d in range(depth):
        nxt = {}
        for sig, pl in frontier.items():
            for R, P in passes:
                newsig = tuple(subst(R, P, s) for s in sig)
                if newsig in seen or newsig in nxt:
                    continue
                newpl = pl + [(R, P)]
                if newsig == tuple(TARGET(s) for s in domain):
                    # candidate: verify on the full domain
                    if all(run(newpl, S) == TARGET(S) for S in D):
                        found = newpl
                        break
                nxt[newsig] = newpl
            if found: break
        seen.update(nxt)
        frontier = nxt
        print(f"  [{label}] depth {d+1}: {len(seen)} distinct signatures "
              f"({time.time()-t0:.0f}s)")
        if found or not frontier: break
    if found:
        print(f"  [{label}] FOUND a pipeline of {len(found)} passes:")
        for i, (R, P) in enumerate(found):
            print(f"     {i+1}. [{R}/{P}]")
    else:
        print(f"  [{label}] no pipeline of <= {depth} passes with "
              f"|P|<={plen}, |R|<={rlen} computes f (searched "
              f"{len(seen)} distinct signatures).")
    return found

print("\n--- bounded search for short constant pipelines computing f ---")
# Lean searches (domain len<=6 for BFS; candidates re-verified on len<=10):
search(4, 2, 2, all_strings("ab", 6), "A: depth<=4, |P|<=2, |R|<=2")
search(3, 3, 3, all_strings("ab", 5), "B: depth<=3, |P|<=3, |R|<=3")

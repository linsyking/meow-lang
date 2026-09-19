"""Extract concrete witnesses for the report."""
import sys, itertools
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import rep_ref, rep_onepass, subst, all_strings

D = all_strings("ab", 7)

# Witness: pattern set ("ab","ba") where NO order of freezing equals
# onepass-first (and onepass-longest).
pairs = [("ab", "1"), ("ba", "2")]
wit = []
for S in D:
    f12 = rep_ref(pairs, S)
    f21 = rep_ref(pairs[::-1], S)
    r = rep_onepass(pairs, S, "first")
    l = rep_onepass(pairs, S, "longest")
    if r != f12 and r != f21:
        wit.append((S, f12, f21, r, l))
print("freezing orders vs onepass-first for patterns (ab->1, ba->2):")
for S, f12, f21, r, l in wit[:6]:
    print(f"  S={S!r}: F(ab,ba)={f12!r} F(ba,ab)={f21!r} onepass-first={r!r} "
          f"onepass-longest={l!r}")
print(f"total witnesses among strings len<=7: {len(wit)}")

# Also: is onepass-first(ab,ba) equal to onepass-longest(ab,ba)?
same = all(rep_onepass(pairs, S, "first") == rep_onepass(pairs, S, "longest")
           for S in D)
print(f"onepass-first == onepass-longest for (ab,ba) on all len<=7: {same}")

# Can freezing with a LONGER pattern list over {a,b} capture
# onepass-first(ab,ba)?  Try all lists of length 1..4 from a small pool.
pool = ["a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "baa", "bba"]
target = lambda S: rep_onepass(pairs, S, "first")
found = None
cnt = 0
for n in range(1, 5):
    for Xs in itertools.product(pool, repeat=n):
        if len(set(Xs)) < n:
            continue
        cnt += 1
        cand = [(X, str(i) + "Z") for i, X in enumerate(Xs)]
        if all(rep_ref(cand, S) == target(S) for S in D):
            found = cand
            break
    if found: break
print(f"freezing pattern-lists of length 1..4 over pool of 10 (distinct, "
      f"markers iZ): {cnt} tried; capture onepass-first(ab,ba): "
      f"{'YES: ' + str(found) if found else 'NO'}")

# Same question with pure deletion/insertion style replacements from {a,b}:
found2 = None
for n in range(1, 4):
    for Xs in itertools.product(pool, repeat=n):
        if len(set(Xs)) < n:
            continue
        for Ys in itertools.product(["a", "b", "", "ab", "ba"], repeat=n):
            cand = list(zip(Xs, Ys))
            if all(rep_ref(cand, S) == target(S) for S in D):
                found2 = cand
                break
        if found2: break
    if found2: break
print(f"freezing lists with replacements from {{a,b,eps}}: "
      f"{'YES: ' + str(found2) if found2 else 'NO'}")

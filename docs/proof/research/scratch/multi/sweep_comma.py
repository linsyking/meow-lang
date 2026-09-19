"""Exhaustive sweep: comma-code construction vs freezing semantics.

Stages (each states its finite domain):
  A. binary Sigma={a,b}, n=1..3, all pattern sets from a stated pool, all
     replacement tuples from a stated pool, all strings up to a stated length,
     construction chars (b,x) in both orders.
  B. ternary Sigma={a,b,c}, n=1..2 similarly.
Also collects statistics on the paper's construction (fails when (H) is
violated; regression: must agree when (H) holds).
"""
import sys, itertools, time
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import rep_ref, repC_paper, repC_comma, all_strings

def H_ok(pairs, x):
    """The paper's hypothesis: every pattern is a single char or doesn't end with x."""
    return all(len(X) == 1 or X[-1] != x for X, _ in pairs)

def sweep(name, alphabet, n, pat_pool, rep_pool, maxlen, b, x, strings):
    t0 = time.time()
    combos = 0
    comma_bad = []
    paper_bad_under_H = []
    paper_fail_count = 0
    paper_total = 0
    for Xs in itertools.product(pat_pool, repeat=n):
        if len(set(Xs)) < n and n > 1:
            pass  # duplicate patterns allowed, still a valid pattern set
        for Ys in itertools.product(rep_pool, repeat=n):
            pairs = list(zip(Xs, Ys))
            combos += 1
            h = H_ok(pairs, x)
            for S in strings:
                want = rep_ref(pairs, S)
                got = repC_comma(b, x, pairs, S, alphabet)
                if got != want:
                    comma_bad.append((pairs, S, want, got))
                    if len(comma_bad) > 5:
                        break
            if len(comma_bad) > 5:
                break
            # paper construction statistics
            paper_total += 1
            if h:
                for S in strings:
                    if repC_paper(b, x, pairs, S) != rep_ref(pairs, S):
                        paper_bad_under_H.append((pairs, S))
                        break
            else:
                failed = False
                for S in strings:
                    if repC_paper(b, x, pairs, S) != rep_ref(pairs, S):
                        failed = True
                        break
                if failed:
                    paper_fail_count += 1
        if len(comma_bad) > 5:
            break
    dt = time.time() - t0
    print(f"[{name}] domain: Sigma={alphabet}, n={n}, |pat|={len(pat_pool)}, "
          f"|rep|={len(rep_pool)}, strings len<={maxlen} ({len(strings)} strs), "
          f"(b,x)=({b},{x})")
    print(f"    combos tested: {combos}, time {dt:.1f}s")
    if comma_bad:
        print("    COMMA CONSTRUCTION FAILURES (first few):")
        for pairs, S, want, got in comma_bad[:6]:
            print(f"      pairs={pairs} S={S!r} want={want!r} got={got!r}")
    else:
        print("    comma construction == freezing on the whole domain  [OK]")
    if paper_bad_under_H:
        print("    !! paper construction failed UNDER (H):", paper_bad_under_H[:3])
    print(f"    paper construction: {paper_fail_count}/{paper_total} pattern sets "
          f"disagree with freezing (all of them violate (H): "
          f"{paper_fail_count == 0 or 'see counts'})")
    return comma_bad

# ---------------- Stage A: binary ----------------
AB = "ab"
strings8 = all_strings(AB, 8)   # 511
strings6 = all_strings(AB, 6)   # 127
strings5 = all_strings(AB, 5)   # 63

# n=1: every pattern len 1..3, every replacement len 0..3
pats1 = [s for L in range(1, 4) for s in map("".join, itertools.product(AB, repeat=L))]
reps1 = [""] + pats1
bad = []
bad += sweep("A1", AB, 1, pats1, reps1, 8, "a", "b", strings8)

# n=2: every ordered pair of patterns len 1..3 (14^2=196), replacements len 0..2 (7)
reps2 = [s for L in range(0, 3) for s in map("".join, itertools.product(AB, repeat=L))]
bad += sweep("A2", AB, 2, pats1, reps2, 6, "a", "b", strings6)

# n=2 with the other construction char order (b,x) = (b,a)
pats_sw = [p.replace("a", "A").replace("b", "a").replace("A", "b") for p in pats1]
reps_sw = [r.replace("a", "A").replace("b", "a").replace("A", "b") for r in reps2]
bad += sweep("A2sw", AB, 2, pats_sw, reps_sw, 6, "b", "a", strings6)

# n=3: spurious-prone pattern shapes, small replacement pool, short strings
pats3 = ["a", "b", "ab", "ba", "bb", "bbb", "abb", "aab"]
reps3 = ["", "a", "bb"]
bad += sweep("A3", AB, 3, pats3, reps3, 5, "a", "b", strings5)

# ---------------- Stage B: ternary ----------------
ABC = "abc"
stringsABC = all_strings(ABC, 6)  # 364
pats_abc = ["a", "b", "c", "ab", "bc", "cb", "ba", "ca", "cab", "bca"]
reps_abc = ["", "a", "c", "bc", "cab"]
bad += sweep("B2", ABC, 2, pats_abc, reps_abc, 6, "a", "b", stringsABC)
bad += sweep("B3", ABC, 3, ["a", "b", "ab", "bc", "bb"], ["", "a", "c"], 5,
             "a", "b", all_strings(ABC, 5))

print("\n" + ("ALL SWEEPS CLEAN: comma construction == freezing everywhere tested"
              if not bad else f"TOTAL FAILURES: {len(bad)}"))

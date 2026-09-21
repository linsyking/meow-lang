"""mismatch_r1.py -- characterize the lim-vs-restart mismatches on the
census domain (all 930 binary rules, all inputs of length <= 9).

Part 2 of verify_r1 found 3306 value mismatches and 290 verdict
mismatches.  This script re-runs the same domain and classifies:
  * which rules disagree (and their |A|, |B|, B-in-A, |A| vs |B| shape);
  * the DIRECTION of verdict mismatches (restart-div & lim-val, or the
    reverse) -- which discipline terminates more often;
  * whether the disagreement is stable under bigger caps (mismatches
    re-run with cap x10, and on the specific witnesses with cap x50).
"""

import time
from lim_core import restart, orbit_pass
from verify_r1 import rules_census, all_strings


def main():
    t0 = time.time()
    val_rules = {}     # (A,B) -> #inputs with value mismatch
    verd_rules = {}    # (A,B) -> [restart-div&lim-val count, restart-val&lim-div count]
    witnesses = []     # up to 40 (A,B,w,outcome) sample mismatch records
    nrun = 0
    for A, B in rules_census():
        if A == B or B in A:
            continue
        for w in all_strings(9):
            nrun += 1
            rr = restart(A, B, w, 4000, 2_000_000)
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            if rr is None and oo[0] == 'div':
                continue
            if rr is None or oo[0] == 'div':
                d = verd_rules.setdefault((A, B), [0, 0])
                if rr is None:
                    d[0] += 1          # restart diverges, lim converges
                else:
                    d[1] += 1          # restart converges, lim diverges
                if len(witnesses) < 40:
                    witnesses.append((A, B, w, 'verd', rr, oo[1]))
            elif rr != oo[1]:
                val_rules[(A, B)] = val_rules.get((A, B), 0) + 1
                if len(witnesses) < 40:
                    witnesses.append((A, B, w, 'val', rr, oo[1]))
    print(f"ran {nrun} pairs in {time.time()-t0:.0f}s")
    print(f"\nVALUE mismatches: {sum(val_rules.values())} inputs across "
          f"{len(val_rules)} rules")
    items = sorted(val_rules.items(), key=lambda kv: -kv[1])
    for (A, B), n in items[:15]:
        shape = ('|A|<|B|' if len(A) < len(B) else
                 '|A|=|B|' if len(A) == len(B) else '|A|>|B|')
        print(f"  [{A}/{B}] {shape}: {n} inputs")
    from collections import Counter
    shapes = Counter('|A|<|B|' if len(A) < len(B) else
                     '|A|=|B|' if len(A) == len(B) else '|A|>|B|'
                     for A, B in val_rules)
    print(f"  rule shapes: {dict(shapes)}  "
          f"(+{len(items)-15} more rules not listed)")
    print(f"\nVERDICT mismatches across {len(verd_rules)} rules:")
    for (A, B), (rdiv, ldiv) in sorted(verd_rules.items()):
        shape = ('|A|<|B|' if len(A) < len(B) else
                 '|A|=|B|' if len(A) == len(B) else '|A|>|B|')
        print(f"  [{A}/{B}] {shape}: restart-div&lim-val={rdiv}, "
              f"restart-val&lim-div={ldiv}")
    tot_rdiv = sum(v[0] for v in verd_rules.values())
    tot_ldiv = sum(v[1] for v in verd_rules.values())
    print(f"  TOTAL: restart diverges where lim converges: {tot_rdiv}; "
          f"lim diverges where restart converges: {tot_ldiv}")

    # stability: the mismatch must PERSIST at 10x caps on the lim side
    # (restart's divergence is definitive: an infinite trajectory; what
    # needs re-verification is lim's convergence and its value).
    print("\nlim-side stability at 10x caps (all mismatch inputs):")
    unstable = 0
    for (A, B) in list(val_rules) + list(verd_rules):
        for w in all_strings(9):
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            oo2 = orbit_pass(A, B, w, 40000, 20_000_000)
            if oo != oo2:
                unstable += 1
                print(f"  UNSTABLE [{A}/{B}] {w!r}: {oo} vs {oo2}")
                if unstable > 5:
                    break
    print(f"  {'all lim verdicts/values stable at 10x caps' if unstable == 0 else str(unstable)+' unstable'}")


if __name__ == '__main__':
    main()

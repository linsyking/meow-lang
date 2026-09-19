"""Exp 1 (v2): baseline vs restart -- agreement theorems, smallest counterexamples.

Checks:
  (a) A cap B = empty AND A != e  =>  restart == baseline on all tested C (Agreement Thm, non-deletion).
  (a') deletion case A = e, A cap B = e: can differ; record smallest counterexample.
  (b) Exact Agreement Thm: restart==baseline everywhere  <=>  baseline result always B-free. (all A incl. e)
  (d) restart result is always B-free whenever it halts.
  (e) three smallest restart != baseline instances with A != e.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/scratch/".replace("/proof/scratch/", "/proof/research/scratch/restart"))
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

SIG2 = "ab"
SIG3 = "abc"


def run(sigma, maxlenA, maxlenB, maxlenC, cap=3000):
    strs = list(all_strings(sigma, maxlenC))
    pairs = [(A, B) for A in all_patterns(sigma, 0, maxlenA)
             for B in all_patterns(sigma, 1, maxlenB)]
    nonempty_disjoint_ok = True
    exact_ok = True
    bfree_out_fail = []
    diffs = []  # (key, A, B, C, base, rest)
    n_defined = 0
    for (A, B) in pairs:
        bfree = all(B not in subst(A, B, C) for C in strs)
        agree = True
        div_on = []
        for C in strs:
            try:
                r, st = restart(A, B, C, cap)
            except Diverge:
                div_on.append(C)
                continue
            n_defined += 1
            if r != subst(A, B, C):
                agree = False
                diffs.append((len(A) + len(B) + len(C), len(A), len(B), len(C), A, B, C,
                              subst(A, B, C), r))
            if B in r:
                bfree_out_fail.append((A, B, C, r))
        if disjoint(A, B) and A != "":
            if not agree or div_on:
                nonempty_disjoint_ok = False
                print("NONEMPTY-DISJOINT-FAILURE", repr(A), repr(B), div_on[:3])
        lhs = agree and not div_on
        if lhs != bfree:
            exact_ok = False
            print("EXACT-MISMATCH", repr(A), repr(B), "lhs:", lhs, "bfree:", bfree)
    diffs.sort()
    print("sigma=%s |A|<=%d |B|<=%d |C|<=%d  pairs=%d  defined-runs=%d" %
          (sigma, maxlenA, maxlenB, maxlenC, len(pairs), n_defined))
    print("  (a) char-disjoint & A!=e => agreement+termination :",
          "OK" if nonempty_disjoint_ok else "FAILED")
    print("  (b) exact agreement <=> baseline-always-B-free    :",
          "OK" if exact_ok else "FAILED")
    print("  (d) restart outputs always B-free                :",
          "OK" if not bfree_out_fail else ("FAILED" + str(bfree_out_fail[:3])))
    print("  6 smallest restart!=baseline (key,|A|,|B|,|C|,A,B,C,base,restart):")
    for d in diffs[:6]:
        print("    ", d)
    nd = [d for d in diffs if d[4] != ""]
    print("  6 smallest with A!=e:")
    for d in nd[:6]:
        print("    ", d)
    del_ = [d for d in diffs if d[4] == ""]
    print("  3 smallest with A=e (deletion):")
    for d in del_[:3]:
        print("    ", d)


print("=== binary alphabet ===")
run(SIG2, 3, 3, 8)
print()
print("=== ternary alphabet ===")
run(SIG3, 2, 2, 6)

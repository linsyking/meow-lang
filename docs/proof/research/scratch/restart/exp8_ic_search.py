"""Exp 8: search for an injective-and-growing 1-variable restart expression with
VARIABLE patterns (the IC question). Bounded search over node libraries.

Library F of 1-variable V-computable parameter functions (values depend on X1):
  id, constants, del_c, collapse_c, sort, spread-ish, doublers via disjoint pairs etc.
Expressions tested:  E = [R/P]^m X1  and E = [R2/P2]^m [R1/P1]^m X1
Criteria on all inputs of length <= 7 (255 strings):
  total, injective, and grows somewhere (|f(S)| > |S|).
Theory predicts: with CONSTANT patterns this is impossible (Theorem no-injective-node).
Variable patterns evade the theorem's collision argument; this search probes them.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *
import itertools

SIG = "ab"
STRS = list(all_strings(SIG, 7))


def lib_functions():
    """name -> function S -> value (computed by V-legal sub-pipelines where possible)"""
    F = {}
    F["id"] = lambda s: s
    for w in ["", "a", "b", "aa", "ab", "ba", "bb"]:
        F["const:%r" % w] = (lambda w: (lambda s: w))(w)
    # deletion nodes (total)
    F["del_a"] = lambda s: restart("", "a", s, cap=500)[0]
    F["del_b"] = lambda s: restart("", "b", s, cap=500)[0]
    F["del_aa"] = lambda s: restart("", "aa", s, cap=500)[0]
    F["del_ab"] = lambda s: restart("", "ab", s, cap=500)[0]
    # collapse nodes (total)
    F["col_a"] = lambda s: restart("a", "aa", s, cap=500)[0]
    F["col_b"] = lambda s: restart("b", "bb", s, cap=500)[0]
    # sort (total)
    F["sort"] = lambda s: restart("ba", "ab", s, cap=500)[0]
    # disjoint replace-all (baseline-safe)
    F["rep_b_to_aa"] = lambda s: restart("aa", "b", s, cap=800)[0]
    F["rep_a_to_bb"] = lambda s: restart("bb", "a", s, cap=800)[0]
    # double via disjoint: replace b by ba? (b->ab has overlap; ba is disjoint from b? 'b' in 'ba'? yes char overlap)
    F["rep_b_to_ab"] = lambda s: restart("ab", "b", s, cap=800)[0]   # may diverge; catch
    return F


F = lib_functions()
NAMES = list(F.keys())
print("library size:", len(NAMES))

# evaluate all library functions on STRS (catch divergence in the parameter computation)
vals = {}
for n in NAMES:
    vs = []
    ok = True
    for s in STRS:
        try:
            vs.append(F[n](s))
        except Diverge:
            vs.append(None)
    vals[n] = vs
print("library evaluated.", flush=True)


def run_node(repv, patv, s):
    """one restart node with runtime replacement/parameter values"""
    if patv is None or repv is None or patv == "":
        return None
    try:
        return restart(repv, patv, s, cap=1500)[0]
    except Diverge:
        return None


# 1-node expressions E = [R/P]^m X1
print("=== 1-node variable-pattern expressions: total+injective+growing ===", flush=True)
hits = []
tested = 0
for Rn in NAMES:
    for Pn in NAMES:
        outs = {}
        total = True
        grows = False
        for i, s in enumerate(STRS):
            r = run_node(vals[Rn][i], vals[Pn][i], s)
            if r is None:
                total = False
                break
            outs[s] = r
            if len(r) > len(s):
                grows = True
        tested += 1
        if total and grows and len(set(outs.values())) == len(STRS):
            hits.append((Rn, Pn))
print("   tested %d expressions; total+injective+growing: %d" % (tested, len(hits)))
for h in hits[:20]:
    print("      ", h)

# 2-node expressions, reduced library (skip constants of length>1 for speed)
RED = [n for n in NAMES if not n.startswith("const") or len(n) <= 9]
print("=== 2-node expressions over reduced library (%d fns) ===" % len(RED), flush=True)
hits2 = []
tested2 = 0
import time
t0 = time.time()
for R1n in RED:
    for P1n in RED:
        # first node map (may be partial)
        m1 = {}
        ok1 = True
        for i, s in enumerate(STRS):
            r = run_node(vals[R1n][i], vals[P1n][i], s)
            if r is None:
                ok1 = False
                break
            m1[s] = r
        if not ok1:
            continue
        if len(set(m1.values())) != len(STRS):
            continue  # first node must be injective to have any chance
        for R2n in RED:
            for P2n in RED:
                outs = []
                total = True
                grows = False
                for i, s in enumerate(STRS):
                    r = run_node(vals[R2n][i], vals[P2n][i], m1[s])
                    if r is None:
                        total = False
                        break
                    outs.append(r)
                    if len(r) > len(s):
                        grows = True
                tested2 += 1
                if total and grows and len(set(outs)) == len(STRS):
                    hits2.append((R1n, P1n, R2n, P2n))
        if time.time() - t0 > 200:
            print("   (time guard hit)")
            break
    if time.time() - t0 > 200:
        break
print("   tested %d two-node expressions; total+injective+growing: %d" % (tested2, len(hits2)))
for h in hits2[:20]:
    print("      ", h)

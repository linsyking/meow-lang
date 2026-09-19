"""Exp 5: (i) Independent Substitution with B = e (paper erratum check, both semantics);
        (ii) injectivity search over constant-pattern restart pipelines (depth<=2)."""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

print("=== (i) Independent Substitution with B = epsilon ===")
print("   hypotheses: A cap B = e (vacuous), A cap C = e, C != e")
found_base = found_rest = None
for A in all_patterns("abcd", 1, 2):
    for C in all_patterns("abcd", 1, 2):
        if set(A) & set(C):
            continue
        for S in all_strings("abcd", 6):
            base = subst("", C, S)
            try:
                r, _ = restart("", C, S, cap=200)
            except Diverge:
                r = None
            if (A in base) != (A in S) and found_base is None:
                found_base = (A, "", C, S, base)
            if r is not None and (A in r) != (A in S) and found_rest is None:
                found_rest = (A, "", C, S, r)
print("   BASELINE  counterexample (A,B,C,S,[B/C]S):", found_base)
print("   RESTART   counterexample (A,B,C,S,[B/C]^m S):", found_rest)
print("   -> the paper's lemma as stated (no B!=e hypothesis) fails for BOTH semantics.")

print()
print("=== (ii) injectivity of constant-pattern restart pipelines ===")
SIG = "ab"
STRS = list(all_strings(SIG, 8))  # 511 inputs
NODES = [(A, B) for A in all_patterns(SIG, 0, 3) for B in all_patterns(SIG, 1, 3)]

# precompute each node's action as a dict on STRS; mark total nodes
maps = {}
total_nodes = []
for (A, B) in NODES:
    m = {}
    tot = True
    for s in STRS:
        try:
            r, _ = restart(A, B, s, cap=4000)
            m[s] = r
        except Diverge:
            m[s] = None
            tot = False
    maps[(A, B)] = m
    if tot:
        total_nodes.append((A, B))
print("   nodes: %d total, %d non-total (on inputs len<=8)" %
      (len(total_nodes), len(NODES) - len(total_nodes)))

# single-node injectivity (on total nodes)
inj1 = []
for (A, B) in total_nodes:
    m = maps[(A, B)]
    if len(set(m.values())) == len(STRS):
        inj1.append((A, B))
print("   total single nodes that are injective on the 511 inputs:", inj1)

# depth-2 pipelines h2 o h1 (h1 applied first)
inj2 = []
n_checked = 0
for (A1, B1) in total_nodes:
    m1 = maps[(A1, B1)]
    if len(set(m1.values())) != len(STRS):
        continue  # h1 not injective => pipeline not injective (necessary)
    for (A2, B2) in total_nodes:
        m2 = maps[(A2, B2)]
        vals = [m2.get(m1[s]) for s in STRS]
        if None in vals:
            continue
        n_checked += 1
        if len(set(vals)) == len(STRS):
            inj2.append(((A1, B1), (A2, B2)))
print("   depth-2 total pipelines checked: %d; injective ones: %d" % (n_checked, len(inj2)))
for p in inj2[:10]:
    print("      ", p)
print("   (theory: NO node with >=1 substitution is injective on ALL of Sigma*,")
print("    so no constant-pattern pipeline of depth>=1 is injective anywhere.)")

# growth: any total single node that grows somewhere?
growers = []
for (A, B) in total_nodes:
    m = maps[(A, B)]
    if any(len(m[s]) > len(s) for s in STRS):
        growers.append((A, B))
print("   total growing single nodes (|out|>|in| somewhere):", len(growers))
for g in growers[:15]:
    print("      ", g)

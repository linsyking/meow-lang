"""Exp 2: termination classification of [A/B]^m (single-rule, leftmost-restart strategy).

Hypotheses:
  (T1) |A| < |B|  => total.
  (T2) A cap B = empty, A != e => total.
  (T3) B in A (occurs) => diverges on input B itself (so not total).
  (T4) CONJECTURE to test: "B not-in A => total"?  Look for counterexamples (e.g. [bbaa/ab]).
  (T5) leftmost-restart totality  vs  full system termination (any strategy),
       exact for |A| <= |B| via finite graph of reachable strings.
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

SIG2 = "ab"


def leftmost_total(A, B, strs, cap=4000):
    """total on all inputs in strs? returns (True,) or (False, witness)"""
    for C in strs:
        try:
            restart(A, B, C, cap)
        except Diverge:
            return (False, C)
    return (True, None)


def all_positions(C, B):
    return [i for i in range(len(C) - len(B) + 1) if C.startswith(B, i)]


def system_terminates(A, B, maxstates=200000):
    """Full-system termination from all starts up to some length bound.
    Exact when |A| <= |B| (length never grows): explore reachable closure from
    every string up to length LMAX; the state space is finite (all strings of
    length <= LMAX + slack).  Returns ('yes'|'no'|'unknown', witness)."""
    if len(A) > len(B):
        return ("unknown", None)  # length grows; not decidable by this closure
    # closure from all starts up to LMAX
    LMAX = 7
    seen = set()
    frontier = list(all_strings(SIG2, LMAX))
    for s in frontier:
        seen.add(s)
    while frontier:
        s = frontier.pop()
        for i in all_positions(s, B):
            t = s[:i] + A + s[i + len(B):]
            if len(t) > LMAX:
                return ("no", s)  # only possible if len(A)==len(B) impossible; sanity
            if t not in seen:
                if len(seen) > maxstates:
                    return ("unknown", None)
                seen.add(t)
                frontier.append(t)
                if t == s:
                    return ("no", s)
    return ("yes", None)


def main():
    strs = list(all_strings(SIG2, 9))  # 1023 inputs
    pairs = [(A, B) for A in all_patterns(SIG2, 0, 4)
             for B in all_patterns(SIG2, 1, 4)]
    print("total pairs to classify:", len(pairs))
    cats = {"total": [], "div": [], "unknown": []}
    for (A, B) in pairs:
        if len(A) < len(B):
            pred = "total"
        elif B in A:
            pred = "div"
        elif disjoint(A, B) and A != "":
            pred = "total"
        else:
            pred = "?"
        ok, wit = leftmost_total(A, B, strs, cap=4000)
        actual = "total" if ok else "div"
        if actual == "total" and pred == "div":
            print("MISMATCH predicted div but total:", repr(A), repr(B))
        if actual == "div" and pred == "total":
            print("MISMATCH predicted total but diverges:", repr(A), repr(B), wit)
        cats[actual].append((A, B))
    print("total:", len(cats["total"]), " div:", len(cats["div"]))
    # Focus: divergent pairs with B not a substring of A  (would refute T4)
    t4_counter = [(A, B) for (A, B) in cats["div"] if B not in A]
    print("divergent pairs with B NOT substring of A:", len(t4_counter))
    for (A, B) in t4_counter[:20]:
        print("   ", repr(A), repr(B))
    # divergent pairs with |A| <= |B| but B not in A:
    sub = [(A, B) for (A, B) in t4_counter if len(A) <= len(B)]
    print("   ...of those with |A|<=|B|:", len(sub))
    for (A, B) in sub[:20]:
        print("   ", repr(A), repr(B))
    # total pairs with |A| > |B| (growing total rules):
    grow = [(A, B) for (A, B) in cats["total"] if len(A) > len(B)]
    print("total & growing (|A|>|B|):", len(grow))
    for (A, B) in grow[:40]:
        print("   ", repr(A), repr(B))


main()

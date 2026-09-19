"""Bounded searches for expressibility within constant-pattern pipeline fragments.

g = [b/aa]^R (rightmost pairing) and h = [b/aa] (leftmost pairing), over Sigma={a,b}.

Search 1 (sanity + evidence): is g computable by any l2r pipeline of <= DEPTH
passes with constant patterns (|A|,|B| <= 3) on all inputs |C| <= 8?
Theory says NO (g is not left-subsequential). Mirror search for h in r2l.

Search 2: same but allowing a few simple VARIABLE patterns/replacements
(X1, aX1, X1a, aaX1, ...), depth <= 2.
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


ALPHA = ("a", "b")
INPUTS = all_strings(ALPHA, 6)
G = tuple(subst_r2l("b", "aa", C) for C in INPUTS)     # rightmost pairing
H = tuple(subst_l2r("b", "aa", C) for C in INPUTS)     # leftmost pairing


def apply_pipeline(sem, passes, inputs):
    """passes applied right-to-left to the variable's value (start = input)."""
    outs = list(inputs)
    for (R, P) in reversed(passes):
        outs = [sem(R, P, s) if P else s for s in outs]
    return tuple(outs)


def const_passes(maxlen, maxpat=None):
    As = all_strings(ALPHA, maxlen)
    Bs = [s for s in all_strings(ALPHA, maxpat or maxlen) if s]
    return [(A, B) for B in Bs for A in As]


def search_constant(depth, target, sem, maxlen=3, maxpat=None):
    cps = const_passes(maxlen, maxpat)
    inputs = tuple(INPUTS)
    # BFS over functions represented by output tuples
    frontier = {inputs: ()}
    seen = {inputs}
    for d in range(1, depth + 1):
        new = {}
        for fvals, passes in frontier.items():
            for (A, B) in cps:
                nv = tuple(sem(A, B, s) for s in fvals)
                if nv in seen:
                    continue
                np = passes + ((A, B),)
                if nv == target:
                    return np, d
                seen.add(nv)
                new[nv] = np
        frontier = new
        print(f"  depth {d}: frontier={len(frontier)} total-visited={len(seen)}")
        if not frontier:
            break
    return None, depth


def var_passes():
    """Small schema of patterns/replacements mixing the variable X1 and constants."""
    opts = ["", "a", "b", "aa", "bb", "ab", "ba", "X", "aX", "Xa", "bX", "Xb",
            "aaX", "Xaa", "abX", "Xba", "aXa", "bXb"]
    def sub(t, v):
        return t.replace("X", v)
    passes = []
    for P in opts:
        if P == "":
            continue
        for R in opts:
            if P == R:
                continue
            passes.append((R, P))
    return passes, sub


def search_var(depth, target, sem):
    vp, sub = var_passes()
    inputs = tuple(INPUTS)
    # a pass depends on the variable's value; we must track it per input
    # function repr: for each input, current string; pass: for input C with
    # current value s, new value = sem(sub(R, C), sub(P, C), s)
    def step(fvals, A, B):
        out = []
        for C, s in zip(INPUTS, fvals):
            pat = sub(B, C)
            if pat == "":
                return None  # [A/eps] undefined -> partial function, not our target
            out.append(sem(sub(A, C), pat, s))
        return tuple(out)
    frontier = {inputs: ()}
    seen = {inputs}
    for d in range(1, depth + 1):
        new = {}
        for fvals, passes in frontier.items():
            for (A, B) in vp:
                nv = step(fvals, A, B)
                if nv is None or nv in seen:
                    continue
                np = passes + ((A, B),)
                if nv == target:
                    return np, d
                seen.add(nv)
                new[nv] = np
        frontier = new
        print(f"  depth {d}: frontier={len(frontier)} total-visited={len(seen)}")
        if not frontier:
            break
    return None, depth


if __name__ == "__main__":
    print("Search 1a: l2r constant pipelines for g=[b/aa]^R (expect NOT FOUND):")
    p, d = search_constant(2, G, subst_l2r, maxlen=3)
    print("  ->", "FOUND " + repr(p) if p else f"not found (depth<=2, |A|<=3, |B|<=3)")
    p, d = search_constant(3, G, subst_l2r, maxlen=3, maxpat=2)
    print("  ->", "FOUND " + repr(p) if p else f"not found (depth<=3, |A|<=3, |B|<=2)")
    print("Search 1b: r2l constant pipelines for h=[b/aa] (expect NOT FOUND):")
    p, d = search_constant(2, H, subst_r2l, maxlen=3)
    print("  ->", "FOUND " + repr(p) if p else f"not found (depth<=2, |A|<=3, |B|<=3)")
    p, d = search_constant(3, H, subst_r2l, maxlen=3, maxpat=2)
    print("  ->", "FOUND " + repr(p) if p else f"not found (depth<=3, |A|<=3, |B|<=2)")
    print("Search 1c: r2l constant pipelines for g (expect FOUND at depth 1):")
    p, d = search_constant(1, G, subst_r2l, maxlen=3)
    print("  ->", "FOUND " + repr(p) if p else f"not found up to depth {d}")
    print("Search 2a: l2r variable-schema pipelines for g (depth<=2):")
    p, d = search_var(2, G, subst_l2r)
    print("  ->", "FOUND " + repr(p) if p else f"not found up to depth {d}")
    print("Search 2b: r2l variable-schema pipelines for h (depth<=2):")
    p, d = search_var(2, H, subst_r2l)
    print("  ->", "FOUND " + repr(p) if p else f"not found up to depth {d}")

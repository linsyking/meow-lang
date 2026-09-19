"""Deep constant-only pipeline search for once-r: all patterns and
replacements are CONSTANTS (strings over {a,b} of length <= 3, incl. empty
replacement), spine = the input. Depth <= 6, domain = all strings over {a,b}
of length <= 8 (511 points). Signature-deduped frontier.

Which toolkit functions are constant-pattern-reachable, and which are absent
even at depth 6?
"""
import itertools, sys, time
from core import subst_once_r, subst_once_l, subst_L, subst_R2L

SIG = "ab"
DOM = ["".join(t) for L in range(7) for t in itertools.product(SIG, repeat=L)]
RCONS = ["".join(t) for L in range(3) for t in itertools.product(SIG, repeat=L)]
PCONS = [w for w in RCONS if w != ""]
RVALS = {w: [w] * len(DOM) for w in RCONS}  # constants: same for all inputs

def t_delrb(x):
    i = x.rfind("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_dellb(x):
    i = x.find("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_head(x): return x[:1]
def t_tail(x): return x[1:]
def t_last(x): return x[-1:]
def t_droplast(x): return x[:-1]
def t_rev(x): return x[::-1]
def t_id(x): return x
def t_delalla(x): return x.replace("a", "")

TARGETS = {
    "delete-rightmost-b": t_delrb,
    "delete-leftmost-b": t_dellb,
    "head": t_head,
    "tail": t_tail,
    "lastchar": t_last,
    "droplast": t_droplast,
    "reverse": t_rev,
    "identity": t_id,
    "delete-all-a": t_delalla,
}
TVALS = {n: tuple(f(x) for x in DOM) for n, f in TARGETS.items()}

def extend(sem, sig2passes):
    out = {}
    n = len(DOM)
    for A in RCONS:
        for B in PCONS:
            for sig in sig2passes:
                ns = tuple(sem(A, B, s) for s in sig)
                cur = out.get(ns)
                if cur is None:
                    out[ns] = sig2passes[sig] + ((A, B),)
    return out

def search(sem, name, depth):
    t0 = time.time()
    frontier = {tuple(DOM): ()}
    print(f"=== {name}: constant-only pipelines, depth<={depth}, "
          f"R:{len(RCONS)} P:{len(PCONS)}, |DOM|={len(DOM)} ===")
    for d in range(depth):
        frontier = extend(sem, frontier)
        hits = [(tn, frontier[tv]) for tn, tv in TVALS.items() if tv in frontier]
        print(f"  depth {d+1}: {len(frontier)} distinct functions ({time.time()-t0:.0f}s)")
        for tn, ps in hits:
            print(f"    FOUND  {tn}: {' '.join(f'[{A}/{B}]' for A, B in ps)}")
        sys.stdout.flush()
    absent = [tn for tn, tv in TVALS.items() if tv not in frontier]
    print("  ABSENT:", ", ".join(absent))
    return frontier

if __name__ == "__main__":
    import sys as _s
    depth = int(_s.argv[1]) if len(_s.argv) > 1 else 6
    search(subst_once_r, "once-r", depth)

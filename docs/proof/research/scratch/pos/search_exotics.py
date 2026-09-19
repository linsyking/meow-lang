# search_exotics.py -- computed-pattern pos searches (2 variables):
#  cat in pos_CORE (no concat nodes, computed patterns)?  expect NO
#  eq in pos_concat (computed patterns incl. cat-args)?    expect NO
#  L(a,b) in pos_concat?                                   expect NO (proven anyway)
# once-calculus search: tail/head/setAt(0,b) in once_l+concat-with-const?  expect NO
import itertools, sys
sys.path.insert(0, '.')
from poslib import *
from search_pos import bfs, allstr

PAIRS = [(x,y) for x in allstr("ab",2) for y in allstr("ab",2)]

def try_run(fn):
    def g(st):
        try:
            r = fn(st)
            if any(s is None for s in r): return None
            return r
        except Exception:
            return None
    return g

def mk_pool_nodes(pool, with_cat=False, ks=(0,1)):
    """nodes over states = tuples of (S,X,Y). Undefined on any point -> None."""
    items = list(pool.items())
    nodes = []
    for k in ks:
        for rn, rf in items:
            for pn, pf in items:
                nodes.append((f"repOcc({k},{rn}/{pn})",
                    try_run((lambda k, rf, pf: lambda st: tuple(
                        (repOcc(k, pf(X,Y), rf(X,Y), S), X, Y) for (S,X,Y) in st))(k, rf, pf))))
    for i in (0,1):
        for c in "ab":
            nodes.append((f"setAt({i},{c})",
                try_run((lambda i,c: lambda st: tuple(setAt(i,c,S) for (S,X,Y) in st))(i,c))))
    if with_cat:
        for rn, rf in items:
            nodes.append((f"cat(.,{rn})",
                try_run((lambda rf: lambda st: tuple(
                    (S + rf(X,Y), X, Y) for (S,X,Y) in st))(rf))))
            nodes.append((f"cat({rn},.)",
                try_run((lambda rf: lambda st: tuple(
                    (rf(X,Y) + S, X, Y) for (S,X,Y) in st))(rf))))
    return nodes

def start_pairs(dom): return tuple((x, x, y) for (x,y) in PAIRS)

# ---------- (A) cat in pos_core: no concat anywhere ----------
POOL_CORE = {
    "eps":  (lambda X,Y: ""),
    "a":    (lambda X,Y: "a"),
    "b":    (lambda X,Y: "b"),
    "X":    (lambda X,Y: X),
    "Y":    (lambda X,Y: Y),
    "tailX":(lambda X,Y: X[1:]),
    "tailY":(lambda X,Y: Y[1:]),
    "s0bX": (lambda X,Y: setAt(0,'b',X)),
    "s0aX": (lambda X,Y: setAt(0,'a',X)),
}
CORE_NODES = mk_pool_nodes(POOL_CORE, with_cat=False)
print(f"pos_core 2-var nodes: {len(CORE_NODES)}")
ctargets = {
    "cat(X,Y)=XY": [ (x+y, x, y) for (x,y) in PAIRS],
    "head(X)":      [ (x[:1], x, y) for (x,y) in PAIRS],
    "setAt(0,b)":   [ (setAt(0,'b',x), x, y) for (x,y) in PAIRS],
}
bfs("pos_core-2var<=3", PAIRS, CORE_NODES, ctargets, 3, start=start_pairs)

# ---------- (B) eq / L in pos_concat ----------
POOL_CAT = dict(POOL_CORE)
POOL_CAT.update({
    "XY":  (lambda X,Y: X+Y),  "YX":  (lambda X,Y: Y+X),
    "Xa":  (lambda X,Y: X+"a"), "aX":  (lambda X,Y: "a"+X),
    "Ya":  (lambda X,Y: Y+"a"), "aY":  (lambda X,Y: "a"+Y),
    "Xb":  (lambda X,Y: X+"b"), "bX":  (lambda X,Y: "b"+X),
})
CAT_NODES = mk_pool_nodes(POOL_CAT, with_cat=True, ks=(0,))
print(f"pos_concat 2-var nodes: {len(CAT_NODES)}")
etargets = {
    "eq(X,Y)=aa/bb": [ ("aa" if x==y else "bb", x, y) for (x,y) in PAIRS],
    "L(a,b) on X":   [ (x.replace("a","b"), x, y) for (x,y) in PAIRS],
    "cat(X,Y)=XY":   [ (x+y, x, y) for (x,y) in PAIRS],   # control: FOUND via cat(.,Y)
}
bfs("pos_concat-2var<=2", PAIRS, CAT_NODES, etargets, 2, start=start_pairs)

# ---------- (C) once-calculus: tail/head/setAt(0,b) reachable? ----------
# domain of strings up to length 6: replace-all would need 7 once-nodes on
# aaaaaa, so depth<=4 cannot confuse single-edit semantics with replace-all.
DOM = allstr("ab", 6)
OPOOL = {
    "eps": (lambda X: ""),  "a":   (lambda X: "a"),   "b": (lambda X: "b"),
    "ab":  (lambda X: "ab"), "ba":  (lambda X: "ba"),  "X": (lambda X: X),
}
OITEMS = list(OPOOL.items())
ONCE_NODES = []
for rn, rf in OITEMS:
    for pn, pf in OITEMS:
        ONCE_NODES.append((f"once({rn}/{pn})",
            try_run((lambda rf, pf: lambda st: tuple(
                (once_l(pf(x), rf(x), s), x) for (s,x) in st))(rf, pf))))
for c in "ab":
    ONCE_NODES.append((f"prepend({c})",
        (lambda c: lambda st: tuple((c+s, x) for (s,x) in st))(c)))
    ONCE_NODES.append((f"append({c})",
        (lambda c: lambda st: tuple((s+c, x) for (s,x) in st))(c)))
print(f"once-calculus nodes: {len(ONCE_NODES)}")
def ostart(dom): return tuple((s,s) for s in DOM)
otargets = {
    "tail":   [ (s[1:], s) for s in DOM],
    "head":   [ (s[:1], s) for s in DOM],
    "setAt(0,b)": [ (setAt(0,'b',s), s) for s in DOM],
    "once_l(a->b) itself": [ (repOcc(0,'a','b',s), s) for s in DOM],  # control: FOUND
    "L(a,b)": [ (s.replace('a','b'), s) for s in DOM],
}
bfs("once<=4", DOM, ONCE_NODES, otargets, 4, start=ostart)

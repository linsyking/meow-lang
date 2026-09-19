# search_L.py -- searches on the BASELINE side:
#  (1) L with literal patterns (depth<=4)
#  (2) L with literal patterns + enc/dec/head/tail macros (depth<=3)
#  (3) L on the unary alphabet (a^n, computed pattern X allowed)
import itertools, sys
sys.path.insert(0, '.')
from poslib import *
from search_pos import bfs, allstr

DOM = allstr("ab", 4)
A2 = ["a","b","ab","ba","aa","bb"]
R2 = ["","a","b","aa","ab","ba","bb"]

# ---------- (1) L-lit ----------
L_LIT = []
for B in A2:
    for A in R2:
        L_LIT.append((f"[{A}/{B}]",
            lambda st, A=A, B=B: tuple(subst(A,B,s) for s in st)))
print(f"L-lit nodes: {len(L_LIT)}")
targets = {
    "once_l(a->X)": [repOcc(0,"a","X",s) for s in DOM],
    "once_l(b->X)": [repOcc(0,"b","X",s) for s in DOM],
    "once_l(ab->)": [repOcc(0,"ab","",s) for s in DOM],
    "repOcc(1,a->X)": [repOcc(1,"a","X",s) for s in DOM],
    "repOcc(2,a->X)": [repOcc(2,"a","X",s) for s in DOM],
    "setAt(1,a)": [setAt(1,"a",s) for s in DOM],
    "setAt(0,b)": [setAt(0,"b",s) for s in DOM],
    "L(a,b)":     [s.replace("a","b") for s in DOM],   # control: FOUND
    "reverse":    [s[::-1] for s in DOM],
    "truncate2":  [s[:2] for s in DOM],
}
bfs("L-lit<=4", DOM, L_LIT, targets, 4)

# ---------- (2) L with macros ----------
L_MAC = L_LIT + [
    ("enc", lambda st: tuple(enc(s) for s in st)),
    ("dec", lambda st: tuple(dec(s) for s in st)),
    ("headL", lambda st: tuple(headL(s) for s in st)),
    ("tailL", lambda st: tuple(tailL(s) for s in st)),
    ("catL(c,.)", lambda st: tuple("c"+s for s in st)),   # concat w/ const
    ("catL(.,c)", lambda st: tuple(s+"c" for s in st)),
]
print(f"L-macro nodes: {len(L_MAC)}")
targets2 = {
    "once_l(a->X)": [repOcc(0,"a","X",s) for s in DOM],
    "once_l(b->X)": [repOcc(0,"b","X",s) for s in DOM],
    "repOcc(1,a->X)": [repOcc(1,"a","X",s) for s in DOM],
    "setAt(1,a)": [setAt(1,"a",s) for s in DOM],
    "tail":       [s[1:] for s in DOM],   # control: FOUND via tailL
    "head":       [s[:1] for s in DOM],   # control: FOUND via headL
    "L(a,b)":     [s.replace("a","b") for s in DOM],   # control: FOUND
}
bfs("L-macro<=3", DOM, L_MAC, targets2, 3)

# ---------- (3) L on the unary alphabet ----------
# NOTE: computed-pattern nodes are partial (undefined on eps); a candidate
# expression for a TOTAL function must be defined on the whole domain, so
# states where any node is undefined are simply not generated (bfs skips None).
UDOM = ["a"*n for n in range(9)]
def total_subst(A, B):
    def f(st):
        try:
            return tuple(subst(A(s), B(s), s) for s in st)
        except Exception:
            return None
    return f
U_NODES = []
for i in range(1,4):        # pattern a^i
    for j in range(0,4):    # replacement a^j
        U_NODES.append((f"[a^{j}/a^{i}]",
            (lambda i=i, j=j: lambda st: tuple(subst("a"*j, "a"*i, s) for s in st))()))
for j in range(0,3):       # computed pattern = X (whole input), replacement a^j
    U_NODES.append((f"[a^{j}/X]",
        (lambda j=j: total_subst(lambda s: "a"*j, lambda s: s))()))
print(f"L-unary nodes: {len(U_NODES)}")
utargets = {
    "head (n->min(n,1))": [ "a"*min(len(s),1) for s in UDOM],
    "tail (n->n-1)":      [ "a"*max(len(s)-1,0) for s in UDOM],
    "replace-all (n->0)": [ "" for s in UDOM],          # control: FOUND
    "half (n->ceil n/2)": [ "a"*((len(s)+1)//2) for s in UDOM],
}
bfs("L-unary<=3", UDOM, U_NODES, utargets, 3)

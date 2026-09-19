# search_pos_lit_main.py -- pos_lit pipelines, depth<=3, domain |s|<=5 (kills
# short-domain replace-all artifacts: a^5 needs 5 single-edit nodes).
import sys
sys.path.insert(0,'.')
from poslib import *
from search_pos import bfs, allstr

DOM = allstr("ab", 5)
A2 = ["a","b","ab","ba","aa","bb"]
R2 = ["","a","b","aa","ab","ba","bb"]
NODES = []
for i in range(4):
    for c in "ab":
        NODES.append((f"setAt({i},{c})",
            (lambda i=i,c=c: lambda st: tuple(setAt(i,c,s) for s in st))()))
for k in range(3):
    for B in A2:
        for A in R2:
            NODES.append((f"repOcc({k},{B}->{A})",
                (lambda k=k,B=B,A=A: lambda st: tuple(repOcc(k,B,A,s) for s in st))()))
print(f"nodes: {len(NODES)}, domain: {len(DOM)}")
t = {
  "head":     [s[:1] for s in DOM],
  "tail":     [s[1:] for s in DOM],
  "L(a,b)":   [s.replace("a","b") for s in DOM],
  "once_l(a->X)": [repOcc(0,"a","X",s) for s in DOM],
  "repOcc(1,a->X)": [repOcc(1,"a","X",s) for s in DOM],
  "truncate2": [s[:2] for s in DOM],
  "droplast": [s[:-1] for s in DOM],
  "reverse":  [s[::-1] for s in DOM],
}
bfs("pos_lit<=3 (|s|<=5)", DOM, NODES, t, 3)

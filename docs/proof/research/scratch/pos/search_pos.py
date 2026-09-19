# search_pos.py -- BFS reachability searches in function space (dedup on states).
# Answers: which target functions are reachable by small pos pipelines?
import itertools, sys
from collections import deque
sys.path.insert(0, '.')
from poslib import *

def allstr(alf, mx):
    out = []
    for n in range(mx+1):
        out += ["".join(t) for t in itertools.product(alf, repeat=n)]
    return out

def bfs(name, domain, nodes, targets, depth, start=None, extra_report=None):
    """domain: list of input strings; nodes: list of (label, fn: tuple->tuple);
    targets: dict label -> list of expected values."""
    s0 = start(domain) if start else tuple(x for x in domain)
    visited = {s0: 0}
    frontier = [s0]
    found = {}
    for tgt, want in targets.items():
        if list(s0) == list(want):
            found[tgt] = 0
    for d in range(1, depth+1):
        newf = []
        for st in frontier:
            for lbl, fn in nodes:
                ns = fn(st)
                if ns is None or any(s is None for s in ns): continue
                if ns in visited: continue
                visited[ns] = d
                newf.append(ns)
                for tgt, want in targets.items():
                    if list(ns) == list(want):
                        found.setdefault(tgt, (d, lbl))
        frontier = newf
        print(f"  [{name}] depth {d}: states {len(visited)}")
        if extra_report: extra_report(visited)
    for tgt in targets:
        if tgt not in found:
            print(f"  [{name}] NOT FOUND (depth<={depth}): {tgt}")
    for tgt, info in found.items():
        print(f"  [{name}] FOUND: {tgt} at {info}")
    return found, visited

if __name__ == "__main__":
    DOM = allstr("ab", 4)          # 31 strings
    A2 = ["a","b","ab","ba","aa","bb"]
    R2 = ["","a","b","aa","ab","ba","bb"]
    POSLIT_NODES = []
    for i in range(4):
        for c in "ab":
            POSLIT_NODES.append((f"setAt({i},{c})",
                lambda st, i=i, c=c: tuple(setAt(i,c,s) for s in st)))
    for k in range(3):
        for B in A2:
            for A in R2:
                POSLIT_NODES.append((f"repOcc({k},{B}->{A})",
                    lambda st, k=k, B=B, A=A: tuple(repOcc(k,B,A,s) for s in st)))
    print(f"pos_lit nodes: {len(POSLIT_NODES)}")

    targets = {
        "head":     [s[:1] for s in DOM],
        "tail":     [s[1:] for s in DOM],
        "L(a,b)":   [s.replace("a","b") for s in DOM],
        "L(b,a)":   [s.replace("b","a") for s in DOM],
        "once_l(a->X)": [repOcc(0,"a","X",s) for s in DOM],
        "repOcc(1,a->X)": [repOcc(1,"a","X",s) for s in DOM],
        "setAt(1,a)": [setAt(1,"a",s) for s in DOM],
        "truncate2": [s[:2] for s in DOM],
        "droplast": [s[:-1] for s in DOM],
        "reverse":  [s[::-1] for s in DOM],
        "norm(a^n->b^n)": [s.replace("a","b") for s in DOM],  # same as L(a,b) on unary
    }
    def report_bcount(visited):
        # sanity: b-count invariant on unary inputs a^3, a^4 (in domain)
        worst = 0
        for st in visited:
            for idx, s in enumerate(DOM):
                if s in ("aaa","aaaa"):
                    worst = max(worst, st[idx].count('b'))
        assert worst <= 12, worst   # 4 nodes * maxA_b=2 -> <=8; loose bound
    found, visited = bfs("pos_lit<=4", DOM, POSLIT_NODES, targets, 4,
                         extra_report=report_bcount)
    print("b-count sanity worst:", max(st[DOM.index('aaaa')].count('b') for st in visited))

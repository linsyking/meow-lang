"""Minimum total interval count: Y as a shuffle of t interval-subsequences of X
plus C free chars, minimizing the total number of X-contiguous segments
(each read's contributions split whenever consecutive contributions jump).

This is the quantity bounded by (T2):  sum <= #leaves + 2*#Subst.
"""
from functools import lru_cache
import sys
sys.setrecursionlimit(500000)

def min_intervals(Y, X, t, C):
    n = len(X); Xlist = list(X); m = len(Y)
    INF = float('inf')
    # precompute next occurrence positions
    nxt = {}
    for ch in set(Y):
        lst = []
        j = -1
        while True:
            j = X.find(ch, j + 1)
            if j < 0: break
            lst.append(j)
        nxt[ch] = lst

    @lru_cache(maxsize=None)
    def go(i, lasts, c):
        # lasts: tuple of last used position per read (-1 if unused)
        if i == m:
            return 0
        ch = Y[i]
        best = INF
        for r in range(t):
            base = lasts[r] + 1
            for j in nxt.get(ch, ()):
                if j < base: continue
                add = 0 if j == base else 1  # extending vs new segment
                if lasts[r] < 0: add = 1  # first segment
                nl = lasts[:r] + (j,) + lasts[r+1:]
                v = go(i+1, nl, c)
                if v < INF:
                    best = min(best, add + v)
            # NOTE: to be exact we must consider all j, done above
        if c > 0:
            v = go(i+1, lasts, c-1)
            if v < INF:
                best = min(best, v)
        return best
    return go(0, tuple([-1]*t), C)

def runstr(ns):
    return "".join("a"*n + "b" for n in ns)

print("min intervals for reverse (t=4 reads, C=0), runs superincreasing:")
for k in range(1, 6):
    ns = [1]
    for _ in range(k-1): ns.append(4*ns[-1]+1)
    X = runstr(ns)
    Y = X[::-1]
    v = min_intervals(Y, X, 4, 0)
    print(f"  k={k} |X|={len(X)} min_intervals={v}")

print("min intervals for reverse (t=2 reads, C=0):")
for k in range(1, 6):
    ns = [1]
    for _ in range(k-1): ns.append(4*ns[-1]+1)
    X = runstr(ns)
    Y = X[::-1]
    print(f"  k={k} min_intervals(t=2)={min_intervals(Y, X, 2, 0)}")

print("min intervals for double (t=2, C=0):")
for k in range(1, 4):
    ns = [1]
    for _ in range(k-1): ns.append(4*ns[-1]+1)
    X = runstr(ns)
    Y = "".join(ch+ch for ch in X)
    print(f"  k={k} min_intervals(t=2)={min_intervals(Y, X, 2, 0)}")

print("sanity: identity min_intervals(t=1):", min_intervals("aabba", "aabba", 1, 0))
print("sanity: XX min_intervals(t=2):", min_intervals("aabbaaabba", "aabba", 2, 0))

"""Exact feasibility check: is Y a shuffle of t interval-subsequences of X,
optionally interleaved with up to C free characters (modelling bounded
constant-leaf material)?

A read is a copy of X; reading positions must be strictly increasing within a
read.  Different reads are separate copies (may reuse the same X position).
State: (index into Y, tuple of next-allowed X position per read, free budget).
"""
from functools import lru_cache
import sys
sys.setrecursionlimit(100000)

def feasible(Y, X, t, C):
    n = len(X)
    Xlist = list(X)

    from functools import lru_cache
    @lru_cache(maxsize=None)
    def go(i, qs, c):
        if i == len(Y):
            return True
        ch = Y[i]
        # option 1: take from a read
        for r in range(t):
            q = qs[r]
            # try every position q' >= q with X[q'] == ch
            # precompute next occurrence lists
            start = q
            while True:
                # find next occurrence of ch in X at >= start
                j = Xlist.index(ch, start) if ch in Xlist[start:] else -1
                if j < 0:
                    break
                nqs = qs[:r] + (j + 1,) + qs[r + 1:]
                if go(i + 1, nqs, c):
                    return True
                start = j + 1
                if start >= n:
                    break
        # option 2: free char (constant material)
        if c > 0 and go(i + 1, qs, c - 1):
            return True
        return False

    return go(0, tuple([0] * t), C)

def min_reads(Y, X, C=0, tmax=6):
    for t in range(1, tmax + 1):
        if feasible(Y, X, t, C):
            return t
    return None

# run family: X_k = a^{n_1} b a^{n_2} b ... a^{n_k} b, n superincreasing
def runstr(ns):
    return "b".join("a" * n for n in ns) + "b" if False else \
        ("a" * ns[0] + "".join("b" + "a" * n for n in ns[1:]) + "b")

def super(n0, k, factor=4):
    ns, s = [n0], n0
    for _ in range(k - 1):
        s = factor * s + 1
        ns.append(s)
    return ns

print("=== REVERSE lower bound (C=0) ===")
for k in range(1, 5):
    ns = super(1, k)
    X = "".join("a" * n + "b" for n in ns)
    Y = X[::-1]
    t = min_reads(Y, X, 0, tmax=8)
    print(f"k={k} ns={ns} |X|={len(X)} min_reads={t} (expect >= k)")

print("=== REVERSE with free budget C=3 ===")
for k in range(1, 5):
    ns = super(1, k)
    X = "".join("a" * n + "b" for n in ns)
    Y = X[::-1]
    t = min_reads(Y, X, 3, tmax=8)
    print(f"k={k} min_reads(C=3)={t}")

print("=== DOUBLE (every character doubled) lower bound (C=0) ===")
for k in range(1, 4):
    ns = super(1, k)
    X = "".join("a" * n + "b" for n in ns)
    Y = "".join(ch + ch for ch in X)
    t = min_reads(Y, X, 0, tmax=8)
    print(f"k={k} ns={ns} |X|={len(X)} min_reads={t} (expect grows with k)")

print("=== sanity: identity needs 1 read ===")
X = "aabaabab"
print("identity:", min_reads(X, X, 0, 4))
print("=== sanity: XX needs 2 reads ===")
print("XX:", min_reads(X + X, X, 0, 4))
print("=== sanity: delete-all-b (a-runs concatenated) needs 1 read ===")
print("no-b:", min_reads(X.replace("b", ""), X, 0, 4))

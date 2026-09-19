# Search: can L (baseline replace-all) pipelines express [A/B]_1 C?
# Part A: constant-pattern pipelines (BFS with behavior dedup).
# Part B: variable-pattern pipelines (small grammar).
# Part C: unary trick verification ([b^h/b^(h+1)] replaces only first match, h>n/2).
import itertools, sys, time

def rall(A, B, C): return C.replace(B, A)

TEST = ["".join(t) for n in range(7) for t in itertools.product("ab", repeat=n)]  # 254 strings

def delete_first_b(C):
    i = C.find("b"); return C if i < 0 else C[:i] + C[i+1:]

def replace_first_b(C):
    i = C.find("b"); return C if i < 0 else C[:i] + "a" + C[i+1:]

TARGETS = {"del1b": tuple(delete_first_b(s) for s in TEST),
           "rep1b": tuple(replace_first_b(s) for s in TEST),
           "delallb": tuple(s.replace("b","") for s in TEST)}  # control: must be found

def bfs(maxlevel, pat_len, rep_len, pass_alpha="abc", target_sigs=TARGETS, verbose=True):
    pats = ["".join(t) for k in range(1, pat_len+1)
            for t in itertools.product(pass_alpha, repeat=k)]
    repls = [""] + ["".join(t) for k in range(1, rep_len+1)
            for t in itertools.product(pass_alpha, repeat=k)]
    passes = [(P, R) for P in pats for R in repls]
    ident = tuple(TEST)
    seen = {ident: None}
    frontier = [ident]
    found = {}
    if ident in target_sigs.values(): pass
    for level in range(1, maxlevel+1):
        t0 = time.time(); newf = []
        for sig in frontier:
            for (P, R) in passes:
                ns = tuple(s.replace(P, R) for s in sig)
                if ns not in seen:
                    seen[ns] = (sig, (P, R))
                    newf.append(ns)
        frontier = newf
        if verbose:
            print(f"  level {level}: frontier {len(newf)}, total behaviors {len(seen)}, "
                  f"{time.time()-t0:.1f}s", flush=True)
        for name, tsig in target_sigs.items():
            if tsig in seen and name not in found:
                pipeline = []; node = tsig
                while seen[node] is not None:
                    pre, last = seen[node]; pipeline.append(last); node = pre
                found[name] = list(reversed(pipeline))
                print(f"  FOUND {name}: passes (applied leftmost first) {found[name]}")
        if "del1b" in found or "rep1b" in found:
            return found
    return found

print("=== Part A: constant-pattern L-pipelines, patterns<=2 repls<=2, alphabet {a,b,c} ===")
res = bfs(3, 2, 2)
print("  control delallb found:", "delallb" in res)
if "del1b" not in res and "rep1b" not in res:
    print("  -> NO witness for del1b/rep1b with <=3 passes (patterns<=2, repls<=2, alpha=abc)")

print("=== Part A2: patterns<=3 repls<=2, 2 passes (wider nets) ===")
res2 = bfs(2, 3, 2)
if not res2: print("  -> no witness with 2 wide passes")

print("=== Part B: variable-pattern L-pipelines (1-ary, X = input) ===")
# patterns and replacements built from X via cat with constants (incl. computed halves)
def apply_vpass(P, R, C):
    p, r = P(C), R(C)
    if p == "": raise ValueError
    return C.replace(p, r)

def halve(C):  # b^n-balanced halving on unary b-runs; general def: replace bb->a, a->b
    T = C.replace("bb", "a").replace("a", "b")
    return T

var_pats = {
    "X": lambda C: C,
    "XX": lambda C: C + C,
    "aX": lambda C: "a" + C, "bX": lambda C: "b" + C, "cX": lambda C: "c" + C,
    "Xa": lambda C: C + "a", "Xb": lambda C: C + "b", "Xc": lambda C: C + "c",
    "a": lambda C: "a", "b": lambda C: "b", "c": lambda C: "c",
    "halve+b": lambda C: halve(C) + "b",
}
var_repls = {
    "eps": lambda C: "", "X": lambda C: C, "XX": lambda C: C + C,
    "a": lambda C: "a", "b": lambda C: "b", "c": lambda C: "c",
    "aX": lambda C: "a" + C, "Xa": lambda C: C + "a",
    "halve": lambda C: halve(C),
}
vp = [(pn, rn) for pn in var_pats for rn in var_repls]
sig0 = tuple(TEST); seen = {sig0: None}; frontier = [sig0]; found = {}
for level in range(1, 4):
    t0=time.time(); newf=[]
    for sig in frontier:
        for (pn, rn) in vp:
            try:
                ns = tuple(apply_vpass(var_pats[pn], var_repls[rn], s) for s in sig)
            except ValueError:
                continue
            if ns not in seen:
                seen[ns] = (sig, (pn, rn)); newf.append(ns)
    frontier = newf
    print(f"  level {level}: frontier {len(newf)}, total {len(seen)}, {time.time()-t0:.1f}s", flush=True)
    for name, tsig in TARGETS.items():
        if tsig in seen:
            node=tsig; pl=[]
            while seen[node] is not None:
                pre,last=seen[node]; pl.append(last); node=pre
            found[name]=list(reversed(pl))
    for n_,p_ in found.items(): print("  FOUND", n_, p_)
    if "del1b" in found or "rep1b" in found:
        break
if not found: print("  -> no witness with 3 variable-pattern passes")

print("=== Part C: unary trick: [floorhalve(X) / floorhalve(X)*b] (X), h=|floor(n/2)|+1 ===")
def floorhalve(C):  # b^n -> b^floor(n/2):  [b/a][eps/b][a/bb] (rightmost first)
    return C.replace("bb","a").replace("b","").replace("a","b")
ok = True
for n in range(0, 201):
    C = "b"*n
    H = floorhalve(C)          # b^floor(n/2)
    P, R = H + "b", H          # pattern b^(floor(n/2)+1), replacement b^floor(n/2)
    out = rall(R, P, C)
    want = "b"*max(0, n-1)
    if out != want or (n >= 1 and C.count(P) * 1 != 1):
        ok = False; print("  unary FAIL at n =", n, repr(out), repr(want)); break
    if n >= 1 and C.replace(P, "X").count("X") != 1:
        ok = False; print("  not-1-match at n =", n); break
print("  unary: [floorhalve / floorhalve*b](b^n) = b^(n-1) for n=0..200, exactly 1 match:", ok)
C = "bbbabb"; H = floorhalve(C); P, R = H+"b", H
print("  same expression on non-unary 'bbbabb':", rall(R, P, C), " (want 'bbabb' for del-first-b)")
print("  floorhalve sanity b^0..b^9 ->", [floorhalve("b"*n) for n in range(10)])

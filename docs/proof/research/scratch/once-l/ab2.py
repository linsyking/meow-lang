# Full-domain check: is [ab/b]_2 once-expressible over the WHOLE Sigma*?
import itertools, random

TEST = ["".join(t) for n in range(5) for t in itertools.product("abc", repeat=n)]  # 121 strings
def ab2(C): return C.replace("b","ab",2)

# 1) sanity: restricted-domain witness on longer {b,c}* strings
rng = random.Random(1)
def wit(C):
    T = C.replace("b","a",1)     # [a/b]_1
    T = T.replace("b","ab",1)    # [ab/b]_1
    T = T.replace("a","ab",1)    # [ab/a]_1
    return T
ok = all(wit(C) == ab2(C) for C in ("".join(rng.choice("bc") for _ in range(rng.randrange(0,15))) for _ in range(20000)))
print("witness [a/b]_1,[ab/b]_1,[ab/a]_1 == [ab/b]_2 on random {b,c}* strings (len<=14):", ok)
# 2) it fails on inputs containing 'a':
for C in ["ab", "abbb", "aabb"]:
    print(f"  witness on {C!r}: {wit(C)!r}  vs [ab/b]_2: {ab2(C)!r}")

# 3) full-domain once-BFS, <=3 passes, patterns<=2, repls<=2, alpha={a,b,c}
pats = ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
repls = [""] + ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
passes = [(P,R) for P in pats for R in repls]
TSIG = tuple(ab2(s) for s in TEST)
ident = tuple(TEST); seen = {ident: None}; frontier=[ident]; found=None
for level in range(1,4):
    newf=[]
    for sig in frontier:
        for (P,R) in passes:
            ns = tuple(s.replace(P,R,1) for s in sig)
            if ns not in seen: seen[ns]=(sig,(P,R)); newf.append(ns)
    frontier=newf
    print(f"  full-domain once-BFS level {level}: behaviors {len(seen)}")
    if TSIG in seen:
        node=TSIG; pl=[]
        while seen[node] is not None:
            pre,last=seen[node]; pl.append(last); node=pre
        found=list(reversed(pl)); print("  FOUND full-domain [ab/b]_2 pipeline:", found); break
if not found:
    print("  -> NO full-domain once-pipeline (<=3 passes, pat<=2, repl<=2) computes [ab/b]_2 on {a,b,c}*<=4")

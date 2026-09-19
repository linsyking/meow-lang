# k-family: [A/B]_k vs k-fold once; once-expressibility of [A/B]_2.
import itertools, random

def rall(A,B,C): return C.replace(B,A)
def ronce(A,B,C): return C.replace(B,A,1)
def rk(A,B,C,k): return C.replace(B,A,k)

# 1) Distinction [A/B]_k vs iterating once k times (rescan sensitivity)
print("counterexample [ab/b]_2 'bb' =", repr(rk("ab","b","bb",2)),
      " vs twice-once:", repr(ronce("ab","b", ronce("ab","b","bb"))))
print("counterexample [aa/a]_2 'a' =", repr(rk("aa","a","aa",2)),
      " vs twice-once:", repr(ronce("aa","a", ronce("aa","a","aa"))))

# 2) When A contains no B (no rescan issue), k-fold once == [A/B]_k?
rng = random.Random(7)
bad = []
for _ in range(20000):
    SIG = "abc"
    B = "".join(rng.choice("b") for _ in range(rng.randrange(1,3)))  # b, bb
    A = "".join(rng.choice("ac") for _ in range(rng.randrange(0,3)))  # A avoids 'b'
    C = "".join(rng.choice("abc") for _ in range(rng.randrange(0,9)))
    k = rng.randrange(0,5)
    it = C
    for _ in range(k): it = ronce(A,B,it)
    if rk(A,B,C,k) != it: bad.append((A,B,C,k,rk(A,B,C,k),it))
print("A-disjoint-from-B: k-fold once == [A/B]_k on 20000 random cases:", not bad, bad[:2])

# 3) Is [ab/b]_2 (rescan-sensitive) once-expressible by constant-pattern once-pipelines?
TEST = ["".join(t) for n in range(6) for t in itertools.product("bc", repeat=n)]  # 63 strings
def ab2(C): return C.replace("b","ab",2)
TSIG = tuple(ab2(s) for s in TEST)
TSIG_allb = tuple(s.replace("b","") for s in TEST)

pats = ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
repls = [""] + ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
passes = [(P,R) for P in pats for R in repls]
ident = tuple(TEST); seen = {ident: None}; frontier=[ident]; found=None
for level in range(1,5):
    newf=[]
    for sig in frontier:
        for (P,R) in passes:
            ns = tuple(s.replace(P,R,1) for s in sig)
            if ns not in seen: seen[ns]=(sig,(P,R)); newf.append(ns)
    frontier=newf
    print(f"  once-BFS level {level}: behaviors {len(seen)}")
    if TSIG in seen:
        node=TSIG; pl=[]
        while seen[node] is not None:
            pre,last=seen[node]; pl.append(last); node=pre
        found=list(reversed(pl)); print("  FOUND [ab/b]_2 once-pipeline:", found); break
if not found: print("  -> no constant-pattern once-pipeline (<=4 passes, pat<=2, repl<=2) computes [ab/b]_2 on {b,c}*<=5")

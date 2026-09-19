# Verify the three potential lemmas (fresh-char, max-run, balance) as STATEMENTS
# on random small once-expressions, and the linear growth lemma.
import itertools, random

class Var:
    __slots__=("i",)
    def __init__(s,i): s.i=i
class Const:
    __slots__=("s",)
    def __init__(s,s_): s.s=s_
class Cat:
    __slots__=("a","b")
    def __init__(s,a,b): s.a, s.b = a, b
class Once:
    __slots__=("R","P","E")
    def __init__(s,R,P,E): s.R, s.P, s.E = R, P, E

def ev(e, args):
    if isinstance(e, Var): return args[e.i]
    if isinstance(e, Const): return e.s
    if isinstance(e, Cat): return ev(e.a,args) + ev(e.b,args)
    P = ev(e.P,args)
    if P == "": raise ValueError("undef")
    return ev(e.E,args).replace(P, ev(e.R,args), 1)

SIG = "abc"
RNG = random.Random(42)

def rand_expr(depth, nvars):
    r = RNG.random()
    if depth == 0 or r < 0.25:
        if RNG.random() < 0.5: return Var(RNG.randrange(nvars))
        return Const("".join(RNG.choice(SIG) for _ in range(RNG.randrange(3))))
    if r < 0.6:
        return Cat(rand_expr(depth-1,nvars), rand_expr(depth-1,nvars))
    return Once(rand_expr(depth-1,nvars), rand_expr(depth-1,nvars), rand_expr(depth-1,nvars))

# --- coefficients -------------------------------------------------------------
def fc_vc(e, c):   # fresh-char: #c(out) <= fc + sum_i vc_i * #c(S_i)
    if isinstance(e, Var):
        d = {i:0 for i in range(3)}; d[e.i]=1; return 0, d
    if isinstance(e, Const): return e.s.count(c), {}
    if isinstance(e, Cat):
        f1,v1 = fc_vc(e.a,c); f2,v2 = fc_vc(e.b,c)
        return f1+f2, {k: v1.get(k,0)+v2.get(k,0) for k in set(v1)|set(v2)}
    fE,vE = fc_vc(e.E,c); fR,vR = fc_vc(e.R,c); fP,vP = fc_vc(e.P,c)
    return fE+fR+fP, {k: vE.get(k,0)+vR.get(k,0)+vP.get(k,0) for k in set(vE)|set(vR)|set(vP)}

def mr_ab(e):      # max-run: mr(out) <= a + sum_i b_i * mr(S_i)
    if isinstance(e, Var):
        d = {i:0 for i in range(3)}; d[e.i]=1; return 0, d
    if isinstance(e, Const):
        best=cur=0
        for ch in e.s:
            cur = cur+1 if False else (cur+1)
            best=max(best,cur)
        # recompute properly
        best=cur=0; prev=None
        for ch in e.s:
            cur = cur+1 if ch==prev else 1; prev=ch; best=max(best,cur)
        return best, {}
    if isinstance(e, Cat):
        a1,b1 = mr_ab(e.a); a2,b2 = mr_ab(e.b)
        return a1+a2, {k: b1.get(k,0)+b2.get(k,0) for k in set(b1)|set(b2)}
    aE,bE = mr_ab(e.E); aR,bR = mr_ab(e.R)
    m = {k: 2*bE.get(k,0)+bR.get(k,0) for k in set(bE)|set(bR)}
    return 2*aE+aR, m

def bal_kv(e, x, y):   # |Psi(out)| <= K + sum_i v_i * |Psi(S_i)|, Psi = #x - #y
    if isinstance(e, Var):
        d = {i:0 for i in range(3)}; d[e.i]=1; return 0, d
    if isinstance(e, Const): return abs(e.s.count(x)-e.s.count(y)), {}
    if isinstance(e, Cat):
        K1,v1 = bal_kv(e.a,x,y); K2,v2 = bal_kv(e.b,x,y)
        return K1+K2, {k: v1.get(k,0)+v2.get(k,0) for k in set(v1)|set(v2)}
    KE,vE = bal_kv(e.E,x,y); KP,vP = bal_kv(e.P,x,y); KR,vR = bal_kv(e.R,x,y)
    return KE+KP+KR, {k: vE.get(k,0)+vP.get(k,0)+vR.get(k,0) for k in set(vE)|set(vP)|set(vR)}

def w_growth(e):  # |out| <= C + w * max(1,|S_i|)
    if isinstance(e, Var): return 1,0
    if isinstance(e, Const): return 0,len(e.s)
    if isinstance(e, Cat): return (lambda t: (t[0][0]+t[1][0], t[0][1]+t[1][1]))([w_growth(e.a), w_growth(e.b)])
    wE,cE = w_growth(e.E); wR,cR = w_growth(e.R); wP,cP = w_growth(e.P)
    return wE+wR+wP, cE+cR+cP+1

def mr(T):
    best=cur=0; prev=None
    for ch in T:
        cur = cur+1 if ch==prev else 1; prev=ch; best=max(best,cur)
    return best if T else 0

DOM1 = ["".join(t) for n in range(7) for t in itertools.product("ab", repeat=n)]
DOM2 = [(x,y) for x in DOM1 if len(x)<=4 for y in DOM1 if len(y)<=3]

nfail = 0; nchk = 0
for trial in range(3000):
    nv = RNG.choice([1,1,2]); d = RNG.choice([2,3])
    e = rand_expr(d, nv)
    for raw in (DOM1 if nv==1 else DOM2):
        args = raw if nv==2 else (raw,)
        try: out = ev(e, args)
        except ValueError: continue
        S = args
        M = max(1, max(len(s) for s in S))
        # growth
        w, C = w_growth(e)
        if len(out) > C + w*M: print("GROWTH FAIL", args, out); nfail+=1
        nchk += 1
        # fresh-char for each c in SIG
        for c in SIG:
            f, v = fc_vc(e, c)
            if out.count(c) > f + sum(v.get(i,0)*s.count(c) for i,s in enumerate(S)):
                print("FRESH FAIL", c, args, out); nfail+=1
        # max-run
        a_, b_ = mr_ab(e)
        if mr(out) > a_ + sum(b_.get(i,0)*mr(s) for i,s in enumerate(S)):
            print("MAXRUN FAIL", args, out); nfail+=1
        # balance
        for x,y in [("a","b"),("a","c"),("b","c")]:
            K, v = bal_kv(e, x, y)
            if abs(out.count(x)-out.count(y)) > K + sum(v.get(i,0)*abs(s.count(x)-s.count(y)) for i,s in enumerate(S)):
                print("BAL FAIL", x, y, args, out); nfail+=1
print(f"[potentials] checked {nchk} evaluations, failures: {nfail}")

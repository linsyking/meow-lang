"""Cross-family pipeline searches: can the OTHER semantics (baseline L,
r2l, once-l) compute once-r's native function delete-rightmost-b (etc.)?

Model: a k-pass pipeline = core expression
    [R_k/P_k] ... [R_1/P_1] X
where each R_i, P_i is drawn from a restricted leaf vocabulary
{constants |w|<=2, X, Xc, cX} evaluated against the ORIGINAL input.
Sequences are enumerated with signature dedup; a pipeline is kept if
defined on every nonempty input (patterns nonempty there).

Domain: all nonempty strings over {a,b} of length <= 7 (254 points).
"""
import itertools, sys, time
from core import subst_L, subst_R2L, subst_once_l, subst_once_r

SIG = "ab"
DOM = ["".join(t) for L in range(1, 8) for t in itertools.product(SIG, repeat=L)]

CONSTS = ["", "a", "b", "aa", "ab", "ba", "bb"]
def mk_forms():
    F = {}
    for w in CONSTS:
        F[w] = (lambda w: lambda x: w)(w)
    F["X"] = lambda x: x
    F["Xa"] = lambda x: x + "a"
    F["aX"] = lambda x: "a" + x
    F["Xb"] = lambda x: x + "b"
    F["bX"] = lambda x: "b" + x
    return F
FORMS = mk_forms()
RKEYS = list(FORMS)               # 12 forms usable as replacement
PKEYS = [k for k in FORMS if k != ""]  # 11 forms (pattern must be nonempty;
# "X" is fine since domain is nonempty)

# precompute per-domain-point values for each form key
VALS = {k: [FORMS[k](x) for x in DOM] for k in FORMS}

def t_delrb(x):
    i = x.rfind("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_dellb(x):
    i = x.find("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_head(x): return x[:1]
def t_tail(x): return x[1:]
def t_last(x): return x[-1:]
def t_droplast(x): return x[:-1]
def t_repall(x): return x.replace("b", "a")
def t_delallb(x): return x.replace("b", "")
def t_rev(x): return x[::-1]
def t_swap(x): return x.replace("a", "c").replace("b", "a").replace("c", "b")
def t_id(x): return x

TARGETS = {
    "delete-rightmost-b": t_delrb,
    "delete-leftmost-b": t_dellb,
    "head": t_head,
    "tail": t_tail,
    "lastchar": t_last,
    "droplast": t_droplast,
    "replace-all-b->a": t_repall,
    "delete-all-b": t_delallb,
    "reverse": t_rev,
    "swap-a-b": t_swap,
    "identity": t_id,
}
TVALS = {n: tuple(f(x) for x in DOM) for n, f in TARGETS.items()}

def extend(sem, sig2passes):
    """one more pass; returns dict signature-tuple -> example pass seq"""
    out = {}
    n = len(DOM)
    for rk in RKEYS:
        Rv = VALS[rk]
        for pk in PKEYS:
            Pv = VALS[pk]
            for sig in sig2passes:
                ns = []
                ok = True
                for i in range(n):
                    P = Pv[i]
                    if P == "":
                        ok = False; break
                    ns.append(sem(Rv[i], P, sig[i]))
                if not ok:
                    continue
                ns = tuple(ns)
                cur = out.get(ns)
                if cur is None:
                    out[ns] = sig2passes[sig] + ((rk, pk),)
    return out

def search_family(sem, name, depth):
    t0 = time.time()
    frontier = {tuple(DOM): ()}   # identity signature
    print(f"=== {name} pipelines (depth<={depth}, forms=R:{len(RKEYS)},P:{len(PKEYS)}) ===")
    for d in range(depth):
        frontier = extend(sem, frontier)
        hits = []
        for tn, tv in TVALS.items():
            if tv in frontier:
                hits.append((tn, frontier[tv]))
        print(f"  depth {d+1}: {len(frontier)} distinct functions "
              f"({time.time()-t0:.0f}s)")
        for tn, ps in hits:
            print(f"    FOUND  {tn}: {' '.join(f'[{rk}/{pk}]' for rk, pk in ps)}")
        sys.stdout.flush()
    for tn in TVALS:
        if tn not in [h[0] for h in []]:
            pass
    absent = [tn for tn in TVALS if TVALS[tn] not in frontier]
    print("  ABSENT:", ", ".join(absent))
    sys.stdout.flush()
    return frontier

if __name__ == "__main__":
    fams = {"L": subst_L, "R2L": subst_R2L, "once-l": subst_once_l,
            "once-r": subst_once_r}
    want = sys.argv[1:] or list(fams)
    for nm in want:
        search_family(fams[nm], nm, 3)

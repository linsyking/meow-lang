"""Exhaustive search of small once-r expressions for toolkit functions.

Enumerates CORE expressions (Subst/Var/Const) of sizes 1,4,7 (unary: ~99k)
and with-concat expressions of size <= 7, then tests each total expression
against a battery of target functions on a full domain.

Sigma = {a,b}; constants from the 7 strings of length <= 2.
"""
import itertools, sys, time
from core import Var, Const, Subst, Cat, evalE, show
from core import subst_once_r

SIG = "ab"
CONSTS = ["", "a", "b", "aa", "ab", "ba", "bb"]

def gen_core(n, nvars):
    """all core expressions of size exactly n"""
    if n == 1:
        out = [Var(i) for i in range(nvars)]
        out += [Const(w) for w in CONSTS]
        return out
    if n < 4:
        return []
    out = []
    for a in range(1, n - 2):
        b = n - 1 - a
        c0 = 1
        # sizes (a, b, c0) with a+b+c0 = n-1, each >= 1
        pass
    for a in range(1, n - 1):
        for b in range(1, n - a):
            c0 = n - 1 - a - b
            if c0 < 1: continue
            for R in gen_core(a, nvars):
                for P in gen_core(b, nvars):
                    for E in gen_core(c0, nvars):
                        out.append(Subst(R, P, E))
    return out

def gen_all(n, nvars):
    """all expressions (incl Cat) of size exactly n"""
    if n == 1:
        out = [Var(i) for i in range(nvars)]
        out += [Const(w) for w in CONSTS]
        return out
    if n < 3:
        return []
    out = []
    # Subst
    if n >= 4:
        for a in range(1, n - 1):
            for b in range(1, n - a):
                c0 = n - 1 - a - b
                if c0 < 1: continue
                for R in gen_all(a, nvars):
                    for P in gen_all(b, nvars):
                        for E in gen_all(c0, nvars):
                            out.append(Subst(R, P, E))
    # Cat
    for a in range(1, n - 1):
        b = n - 1 - a
        for E1 in gen_all(a, nvars):
            for E2 in gen_all(b, nvars):
                out.append(Cat(E1, E2))
    return out

# ---------------- domains ----------------
UNI = ["".join(t) for L in range(6) for t in itertools.product(SIG, repeat=L)]
BIN = [(x, y) for x in UNI[:16] for y in UNI[:16]]

# ---------------- targets ----------------
def t_id(x): return x
def t_head(x): return x[:1]
def t_tail(x): return x[1:]
def t_last(x): return x[-1:]
def t_droplast(x): return x[:-1]
def t_dup(x): return x + x
def t_double(x): return "".join(c + c for c in x)
def t_rev(x): return x[::-1]
def t_repall(x): return x.replace("b", "a")
def t_enc(x): return x.replace("b", "ab")
def t_len(x): return "a" * len(x)
def t_delrb(x): return x[:x.rfind("b")] + x[x.rfind("b") + 1:] if "b" in x else x
def t_append(x): return x + "b"
def t_prepend(x): return "b" + x
def t_unidouble(x): return "a" * (2 * x.count("a")) if set(x) <= {"a"} else None

UNARY_TARGETS = {
    "identity": t_id,
    "append-b": t_append,
    "prepend-b": t_prepend,
    "head": t_head,
    "tail": t_tail,
    "lastchar": t_last,
    "droplast": t_droplast,
    "XX (dup)": t_dup,
    "double-each-char": t_double,
    "reverse": t_rev,
    "replace-all-[a/b]": t_repall,
    "enc(b->ab)": t_enc,
    "length-unary": t_len,
    "delete-rightmost-b": t_delrb,
}

def t_cat(x, y): return x + y
def t_eq(x, y): return "a" if x == y else "b"

BINARY_TARGETS = {"cat": t_cat, "eq(a/b)": t_eq}

def search(exprs, nvars, targets, domain, label):
    t0 = time.time()
    found = {}
    tested = 0
    for E in exprs:
        ok = True
        vals = []
        for pt in domain:
            inputs = list(pt) if isinstance(pt, tuple) else [pt]
            v = evalE(E, subst_once_r, inputs)
            if v is None:
                ok = False; break
            vals.append(v)
        if not ok:
            continue
        tested += 1
        for name, f in targets.items():
            exps = [f(pt) if not isinstance(pt, tuple) else f(*pt) for pt in domain]
            if any(e is None for e in exps):
                continue
            if vals == exps:
                found.setdefault(name, []).append(show(E))
    print(f"[{label}] {len(exprs)} exprs, {tested} total, {time.time()-t0:.1f}s")
    for name in targets:
        if name in found:
            print(f"   FOUND  {name}: {found[name][:3]}{' ...' if len(found[name])>3 else ''} ({len(found[name])} exprs)")
        else:
            print(f"   absent {name}")
    return found

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "core7"
    if mode == "core7":
        exprs = []
        for n in (1, 4, 7):
            exprs += gen_core(n, 1)
        # remove the size-1 non-total trivialities implicitly (they get filtered)
        search(exprs, 1, UNARY_TARGETS, UNI, "unary core size<=7")
    elif mode == "all7":
        exprs = []
        for n in range(1, 8):
            exprs += gen_all(n, 1)
        search(exprs, 1, UNARY_TARGETS, UNI, "unary with-concat size<=7")
    elif mode == "bin":
        exprs = []
        for n in (1, 4, 7):
            exprs += gen_core(n, 2)
        search(exprs, 2, BINARY_TARGETS, BIN, "binary core size<=7")

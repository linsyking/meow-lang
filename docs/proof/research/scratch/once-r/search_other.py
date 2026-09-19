"""Exhaustive small-expression search for the OTHER semantics (L, R2L,
once-l) against once-r's native functions.

Reuses the generators from search_oncer (all core expressions of size
1,4,7 / with-concat <= 7 over Sigma={a,b}, constants <= 2) but evaluates
under a chosen semantics. Targets include once-r's one-node function
delete-rightmost-b and once-l's delete-leftmost-b, plus controls
(replace-all for L, delete-leftmost-b for once-l, identity for all).
"""
import sys
from search_oncer import gen_core, gen_all, UNI, BIN
from core import evalE, show
from core import subst_L, subst_R2L, subst_once_l, subst_once_r

def t_id(x): return x
def t_head(x): return x[:1]
def t_tail(x): return x[1:]
def t_last(x): return x[-1:]
def t_droplast(x): return x[:-1]
def t_repall(x): return x.replace("b", "a")
def t_delallb(x): return x.replace("b", "")
def t_delrb(x):
    i = x.rfind("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_dellb(x):
    i = x.find("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_swap(x): return x.replace("a", "c").replace("b", "a").replace("c", "b")

UNARY_TARGETS = {
    "identity": t_id,
    "delete-rightmost-b": t_delrb,
    "delete-leftmost-b": t_dellb,
    "head": t_head,
    "tail": t_tail,
    "lastchar": t_last,
    "droplast": t_droplast,
    "replace-all-b->a": t_repall,
    "delete-all-b": t_delallb,
    "swap-a-b": t_swap,
}

def t_cat(x, y): return x + y
def t_eq(x, y): return "a" if x == y else "b"
BINARY_TARGETS = {"cat": t_cat, "eq(a/b)": t_eq}

def search(exprs, sem, targets, domain, label):
    found = {}
    tested = 0
    for E in exprs:
        vals = []
        ok = True
        for pt in domain:
            inputs = list(pt) if isinstance(pt, tuple) else [pt]
            v = evalE(E, sem, inputs)
            if v is None:
                ok = False; break
            vals.append(v)
        if not ok:
            continue
        tested += 1
        for name, f in targets.items():
            exps = [f(pt) if not isinstance(pt, tuple) else f(*pt) for pt in domain]
            if vals == exps:
                found.setdefault(name, []).append(show(E))
    print(f"[{label}] {len(exprs)} exprs, {tested} total, FOUND:")
    for name in targets:
        if name in found:
            print(f"    FOUND  {name}: {found[name][:2]} ({len(found[name])} exprs)")
        else:
            print(f"    absent {name}")
    sys.stdout.flush()

if __name__ == "__main__":
    fams = {"L": subst_L, "R2L": subst_R2L, "once-l": subst_once_l}
    want = sys.argv[1:] or list(fams)
    for nm in want:
        sem = fams[nm]
        core_u = []
        for n in (1, 4, 7):
            core_u += gen_core(n, 1)
        search(core_u, sem, UNARY_TARGETS, UNI, f"{nm} unary core size<=7")
        all_u = []
        for n in range(1, 8):
            all_u += gen_all(n, 1)
        search(all_u, sem, UNARY_TARGETS, UNI, f"{nm} unary with-concat size<=7")
        core_b = []
        for n in (1, 4, 7):
            core_b += gen_core(n, 2)
        search(core_b, sem, BINARY_TARGETS, BIN, f"{nm} binary core size<=7")

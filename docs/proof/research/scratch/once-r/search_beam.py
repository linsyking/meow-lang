"""Beam search for larger once-r expressions targeting the open toolkit
functions, plus cross-family pipeline searches (L, R2L, once-l) against
once-r's native functions.

Beam: pool of expressions; each round wraps them in one more Subst with
pattern/replacement drawn from a candidate pool (leaves, constants, and the
current best-scoring expressions). Score = number of matching domain points.
"""
import itertools, random, sys
from core import Var, Const, Subst, Cat, evalE, show
from core import subst_once_r, subst_L, subst_once_l, subst_R2L

SIG = "ab"
CONSTS = ["", "a", "b", "aa", "ab", "ba", "bb"]
UNI = ["".join(t) for L in range(6) for t in itertools.product(SIG, repeat=L)]
BIN = [(x, y) for x in UNI[:16] for y in UNI[:16]]

def t_head(x): return x[:1]
def t_tail(x): return x[1:]
def t_last(x): return x[-1:]
def t_droplast(x): return x[:-1]
def t_delrb(x): return x[:x.rfind("b")] + x[x.rfind("b")+1:] if "b" in x else x
def t_dellb(x):
    i = x.find("b")
    return x[:i] + x[i+1:] if i >= 0 else x
def t_eq(x, y): return "a" if x == y else "b"

def score_un(E, f, dom=UNI):
    s = 0
    for x in dom:
        v = evalE(E, subst_once_r, [x])
        if v is None:
            return -1
        if v == f(x):
            s += 1
    return s

def score_bin(E, f, dom=BIN):
    s = 0
    for pt in dom:
        v = evalE(E, subst_once_r, list(pt))
        if v is None:
            return -1
        if v == f(*pt):
            s += 1
    return s

def beam_unary(target, rounds=6, poolsize=2500, seed=1):
    random.seed(seed)
    f = target[1]
    pool = [Var(0)] + [Const(w) for w in CONSTS]
    # seed with size<=4 core expressions
    pool += [Subst(Const(r), Const(p), e)
             for r in CONSTS for p in ["a", "b", "aa", "ab", "ba", "bb"]
             for e in [Var(0)] + [Const(w) for w in CONSTS]]
    best = (None, -1)
    for rnd in range(rounds):
        scored = []
        for E in pool:
            s = score_un(E, f)
            if s > best[1]:
                best = (E, s)
            scored.append((s, E))
        scored.sort(key=lambda t: -t[0])
        print(f"  round {rnd}: pool {len(pool)}, best {best[1]}/{len(UNI)}")
        if best[1] == len(UNI):
            break
        top = [E for s, E in scored[:poolsize // 4]]
        # candidate patterns/replacements: constants + vars + top performers
        cands = [Var(0)] + [Const(w) for w in CONSTS] + top[:40]
        newpool = set()
        for E in top:
            for P in cands:
                for R in cands:
                    newpool.add(Subst(R, P, E))
        pool = list(newpool)[:poolsize * 6]
    return best

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "tail"
    targets = {
        "tail": t_tail, "head": t_head, "lastchar": t_last,
        "droplast": t_droplast,
    }
    if which == "eq":
        f = t_eq
        # binary beam
        pool0 = [Var(0), Var(1)] + [Const(w) for w in CONSTS]
        best = (None, -1)
        pool = list(pool0)
        for rnd in range(5):
            scored = []
            for E in pool:
                s = score_bin(E, f)
                if s > best[1]: best = (E, s)
                scored.append((s, E))
            scored.sort(key=lambda t: -t[0])
            print(f"  round {rnd}: pool {len(pool)}, best {best[1]}/{len(BIN)}")
            if best[1] == len(BIN): break
            top = [E for s, E in scored[:600]]
            cands = [Var(0), Var(1)] + [Const(w) for w in CONSTS] + top[:30]
            newpool = set()
            for E in top[:150]:
                for P in cands:
                    for R in cands:
                        newpool.add(Subst(R, P, E))
            pool = list(newpool)[:20000]
        print("eq best:", show(best[0]) if best[0] else None, best[1])
    else:
        E, s = beam_unary((which, targets[which]))
        print(f"{which} best: {show(E) if E else None} score {s}/{len(UNI)}")

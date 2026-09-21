"""R4 part C: the EXPLICIT COLLAPSE TRANSLATION  flat-lazy -> eager L.

Construction (derived this round; see REPORT Sec. 9):
  g(X)     = if(eq(X, eps), 'a', X)                    coerce a pattern nonempty
  Phi(E)   = totalized value-part: patterns coerced by g, recursively
  O(u,v)   = occurrence test for TOTAL computed u,v (garbage allowed at u=eps)
             if(eq(u,'b'), [bb/b]v != v, [b/g(u)]v != v)
  F(E)     = TOP/BOT indicator of dom(lazy-E):
             K,V: TOP;  C(E,G): and(F E, F G);
             S(R,P,T): and3(F T, F P, isne(Phi P)) => or(NOT O(Phi P, Phi T), F R)
  TR(E)    = [a / if(F E, 'a', eps)] Phi(E)            the guard node
Theorem to machine-verify:  run_eager(TR(E)) == ev_lazy(E) as PARTIAL
functions, on stated finite domains.  (Guard: on-domain F='a' and [a/a] is
the identity; off-domain F=eps and the eps-pattern is undefined.)
"""
import sys, os, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'rec', 'lazy_pass'))
sys.setrecursionlimit(200000)
import core
import toolkit as tk
from verify_r4 import ev, all_exprs, strings, census

sg = tk.BIN
TOP, BOT = sg.top, sg.bot            # 'b', 'a'

# ---------------- small helpers ----------------
def g(X):
    """coerce: eps -> 'a', else identity (total; X must be total)."""
    return tk.if_(sg, tk.eq(sg, X, tk.K('')), tk.K('a'), X)

def and2(x, y):
    return tk.if_(sg, tk.eq(sg, tk.cat(sg, x, y), tk.K(TOP + TOP)),
                  tk.K(TOP), tk.K(BOT))
def and3(x, y, z):
    return tk.if_(sg, tk.eq(sg, tk.cat(sg, x, tk.cat(sg, y, z)),
                            tk.K(TOP * 3)), tk.K(TOP), tk.K(BOT))
def or2(x, y):
    return tk.if_(sg, tk.eq(sg, tk.cat(sg, x, y), tk.K(BOT + BOT)),
                  tk.K(BOT), tk.K(TOP))
def notb(x):
    return tk.if_(sg, x, tk.K(BOT), tk.K(TOP))

def O(u, v):
    """TOP iff u occurs in v (u, v TOTAL expressions).  Value free at u=eps
    (garbage slice: the g-coercion makes the pass total)."""
    doubled = tk.comp([(tk.K('bb'), tk.K('b'))], v)     # [bb/b]v
    naive = tk.comp([(tk.K('b'), g(u))], v)             # [b/g(u)]v
    return tk.if_(sg, tk.eq(sg, u, tk.K('b')),
                  tk.if_(sg, tk.eq(sg, doubled, v), tk.K(BOT), tk.K(TOP)),
                  tk.if_(sg, tk.eq(sg, naive, v), tk.K(BOT), tk.K(TOP)))

# ---------------- the translation ----------------
def PHI(e):
    t = e[0]
    if t == 'K': return tk.K(e[1])
    if t == 'V': return core.V(0)
    if t == 'C': return core.C(PHI(e[1]), PHI(e[2]))
    R, P, T = e[1], e[2], e[3]
    return core.S(PHI(R), g(PHI(P)), PHI(T))

def F(e):
    t = e[0]
    if t in ('K', 'V'): return tk.K(TOP)
    if t == 'C': return and2(F(e[1]), F(e[2]))
    R, P, T = e[1], e[2], e[3]
    cond = and3(F(T), F(P), tk.isne(sg, PHI(P)))
    rest = or2(notb(O(PHI(P), PHI(T))), F(R))
    return tk.if_(sg, cond, rest, tk.K(BOT))

def TR(e):
    Fp = tk.if_(sg, F(e), tk.K('a'), tk.K(''))
    return core.S(tk.K('a'), Fp, PHI(e))

# ---------------- evaluation ----------------
_MEM = {}
def ev_core(e, S):
    """memoized evaluator for core-grammar (V(0) only) expressions."""
    key = (e, S)
    if key in _MEM: return _MEM[key]
    t = e[0]
    if t == 'K': r = ('val', e[1])
    elif t == 'V': r = ('val', S)
    elif t == 'C':
        a = ev_core(e[1], S)
        r = a if a[0] == 'undef' else (lambda b: b if b[0] == 'undef'
                else ('val', a[1] + b[1]))(ev_core(e[2], S))
    else:
        T = ev_core(e[3], S)
        if T[0] == 'undef': r = T
        else:
            B = ev_core(e[2], S)
            if B[0] == 'undef': r = B
            elif B[1] == '': r = ('undef',)
            else:
                R = ev_core(e[1], S)
                if R[0] == 'undef': r = R
                else: r = ('val', core.subst(R[1], B[1], T[1]))
    _MEM[key] = r
    return r

def ev_lazy_flat(e, S):
    return ev(e, S, True)

# ---------------- verification ----------------
def size(e):
    if e[0] in 'KV': return 1
    if e[0] == 'C': return 1 + size(e[1]) + size(e[2])
    return 1 + size(e[1]) + size(e[2]) + size(e[3])

def verify(exprs, IN, tag, escalate=None):
    bad = tot_bad = 0
    for e in exprs:
        tre = TR(e)
        for S in IN:
            le = ev_lazy_flat(e, S)
            ee = ev_core(tre, S)
            if le != ee:
                bad += 1
                if bad <= 5:
                    print(f"  MISMATCH {tag}: E size {size(e)}, S={S!r}: "
                          f"lazy={le} eager_TR={ee}")
        # Phi totality sanity
        phi = PHI(e)
        for S in IN:
            if ev_core(phi, S)[0] == 'undef':
                tot_bad += 1
                if tot_bad <= 3:
                    print(f"  PHI NOT TOTAL on E size {size(e)}, S={S!r}")
    print(f"{tag}: {len(exprs)} expressions x {len(IN)} inputs: "
          f"{bad} mismatches (expect 0), {tot_bad} Phi-undefinedness "
          f"(expect 0)")
    return bad, tot_bad

def cross_TR(exprs, IN, n=25):
    """TR vs the paper's own run_eager machine."""
    bad = 0
    for e in exprs[:n]:
        tre = TR(e)
        prog = {'main': (1, tre)}
        for S in IN:
            mine = ev_core(tre, S)
            r = core.run_eager(prog, 'main', [S])
            theirs = ('val', r[1]) if r[0] == core.HALT_VAL else ('undef',)
            if mine != theirs:
                bad += 1
                if bad <= 3:
                    print("  TR cross MISMATCH", size(e), S, mine, theirs)
    print(f"TR vs paper machine: {n} exprs x {len(IN)} inputs: {bad} "
          f"mismatches (expect 0)")
    return bad

if __name__ == '__main__':
    IN4 = strings(4)
    # canonical witness + a few hand cases first
    canon = [[('K', ''), ('K', ''), ('K', '')], None, None]
    hand = [('S', ('S', ('K', ''), ('K', ''), ('K', '')), ('K', 'a'), ('V',)),
            ('S', ('S', ('K', ''), ('K', ''), ('K', '')), ('K', 'b'), ('V',)),
            ('S', ('V',), ('K', 'a'), ('V',)),
            ('C', ('V',), ('V',))]
    verify(hand, IN4, "hand cases")
    cross_TR(hand, IN4)
    # the 193 lazy-only witnesses
    IN, lazyD, eagerD = census(2, 4)
    lazy_only = [t for t in lazyD if t not in eagerD]
    wit = []
    for t in lazy_only:
        wit.append(min(lazyD[t], key=lambda e: (size(e), str(e))))
    print(f"verifying all {len(wit)} lazy-only witnesses ...")
    verify(wit, IN4, "lazy-only witnesses")
    # random sample
    rng = random.Random(4)
    pool = all_exprs(2)
    sample = rng.sample(pool, 250)
    verify(sample, IN4, "random depth<=2 sample")
    # escalation: 25 witnesses on |S| <= 6
    IN6 = strings(6)
    verify(wit[:25], IN6, "escalation |S|<=6 (25 witnesses)")
    print("verify_r4b done")

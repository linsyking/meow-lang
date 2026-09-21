"""R4 part A: the FLAT LAZY-PASS calculus.

Semantics (paper sec:rec-lazy, machine in ../rec/lazy_pass/core.py):
  node [R/P]E: force scrutinee E -> T; force pattern P -> B;
    B = eps   -> UNDEFINED (both runtimes);
    B not in T -> value T   (R discarded -- LAZY ONLY; eager forces R anyway);
    B in T     -> force R -> r; value subst(r, B, T).
Eager forces R always.  Concatenation and leaves strict in both.

Part A: (1) cross-check my flat evaluator against the paper's machines
(run_lazy / run_eager) on random call-free expressions; (2) lpcons
re-verification on an EXHAUSTIVE small space.
"""
import sys, os, itertools, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'rec', 'lazy_pass'))
import core

# ---------------- flat evaluator ----------------
def ev(e, S, lazy, depth=0):
    """('val', w) | ('undef',).  e: ('K',w)|('V',)|('C',a,b)|('S',R,P,E)."""
    t = e[0]
    if t == 'K': return ('val', e[1])
    if t == 'V': return ('val', S)
    if t == 'C':
        a = ev(e[1], S, lazy)
        if a[0] == 'undef': return a
        b = ev(e[2], S, lazy)
        if b[0] == 'undef': return b
        return ('val', a[1] + b[1])
    # ('S', R, P, E)
    T = ev(e[3], S, lazy)
    if T[0] == 'undef': return T
    B = ev(e[2], S, lazy)
    if B[0] == 'undef': return B
    if B[1] == '': return ('undef',)
    if lazy and B[1] not in T[1]:
        return T                                    # discard R
    R = ev(e[1], S, lazy)
    if R[0] == 'undef': return R
    return ('val', core.subst(R[1], B[1], T[1]))

def ev_eager_reason(e, S):
    """eager with undefinedness reason: ('undef','R',node)|('undef','P',node)|
    ('undef','E',node) -- which slot caused it (innermost first)."""
    t = e[0]
    if t == 'K': return ('val', e[1])
    if t == 'V': return ('val', S)
    if t == 'C':
        a = ev_eager_reason(e[1], S)
        if a[0] == 'undef': return a
        b = ev_eager_reason(e[2], S)
        if b[0] == 'undef': return b
        return ('val', a[1] + b[1])
    T = ev_eager_reason(e[3], S)
    if T[0] == 'undef':
        return ('undef', 'E', e) if T[1] == 'root' else T
    B = ev_eager_reason(e[2], S)
    if B[0] == 'undef':
        return ('undef', 'P', e) if B[1] == 'root' else B
    if B[1] == '': return ('undef', 'P', e)
    R = ev_eager_reason(e[1], S)
    if R[0] == 'undef':
        return ('undef', 'R', e) if R[1] == 'root' else R
    return ('val', core.subst(R[1], B[1], T[1]))

def fix(e):
    """tag undefined-from-leaf so ev_eager_reason reports the right node."""
    return e

def ev_reason(e, S):
    r = ev_eager_reason(e, S)
    if r[0] == 'undef' and len(r) == 2:   # from a sub-node
        return r
    if r[0] == 'undef':
        return (r[0], r[1], r[2])
    return r

# ---------------- grammar ----------------
def leaves():
    return [('K', ''), ('K', 'a'), ('K', 'b'), ('V',)]

def all_exprs(maxdepth):
    """all flat expressions depth <= maxdepth over {eps,a,b,X,C,S}."""
    lv = {0: leaves()}
    for d in range(1, maxdepth + 1):
        cur = []
        for x in lv[d - 1]:
            for y in lv[d - 1]:
                cur.append(('C', x, y))
        for x in lv[d - 1]:
            for y in lv[d - 1]:
                for z in lv[d - 1]:
                    cur.append(('S', x, y, z))
        lv[d] = lv[d - 1] + cur
    return lv[maxdepth]

def strings(maxlen):
    out = []
    for L in range(maxlen + 1):
        for t in itertools.product('ab', repeat=L):
            out.append(''.join(t))
    return out

# ---------------- part A1: cross-check vs paper machines ----------------
def to_core(e):
    t = e[0]
    if t == 'K': return core.K(e[1])
    if t == 'V': return core.V(0)
    if t == 'C': return core.C(to_core(e[1]), to_core(e[2]))
    return core.S(to_core(e[1]), to_core(e[2]), to_core(e[3]))

def rand_expr(rng, maxdepth):
    """random flat expression, depth <= maxdepth."""
    if maxdepth == 0 or rng.random() < 0.25:
        return rng.choice(leaves())
    t = rng.random()
    if t < 0.3:
        return ('C', rand_expr(rng, maxdepth - 1), rand_expr(rng, maxdepth - 1))
    return ('S', rand_expr(rng, maxdepth - 1), rand_expr(rng, maxdepth - 1),
            rand_expr(rng, maxdepth - 1))

def crosscheck(n=3000, seed=1):
    rng = random.Random(seed)
    IN = strings(3)
    bad = 0
    for _ in range(n):
        e = rand_expr(rng, 3)
        ce = to_core(e)
        prog = {'main': (1, ce)}
        for S in IN:
            mine_l = ev(e, S, True)
            mine_e = ev(e, S, False)
            r = core.run_lazy(prog, 'main', [S])
            theirs_l = ('val', r[1]) if r[0] == core.HALT_VAL else ('undef',)
            r2 = core.run_eager(prog, 'main', [S])
            theirs_e = ('val', r2[1]) if r2[0] == core.HALT_VAL else ('undef',)
            if mine_l != theirs_l or mine_e != theirs_e:
                bad += 1
                if bad <= 5:
                    print("MISMATCH", e, S, mine_l, theirs_l, mine_e, theirs_e)
    print(f"A1 cross-check: {n} exprs x {len(IN)} inputs x 2 runtimes: "
          f"{bad} mismatches (expect 0)")
    return bad

# ---------------- part A2: lpcons on an exhaustive space ----------------
def lpcons(maxdepth=2, maxlen=4):
    IN = strings(maxlen)
    exprs = all_exprs(maxdepth)
    print(f"A2 space: {len(exprs)} expressions depth <= {maxdepth}, "
          f"{len(IN)} inputs |S| <= {maxlen}")
    agree = 0; extra = 0; und_both = 0
    mech_bad = 0; mismatches = 0
    for e in exprs:
        for S in IN:
            le = ev(e, S, True)
            ee = ev(e, S, False)
            if ee[0] == 'val':
                if le != ee:
                    mismatches += 1
                    if mismatches <= 5:
                        print("LPCONS VIOLATION", e, S, ee, le)
                else:
                    agree += 1
            else:
                if le[0] == 'val':
                    extra += 1
                    # mechanism: eager undefined through an R slot whose
                    # pass did not fire?
                    r = ev_eager_reason(e, S)
                    if not (r[0] == 'undef' and r[1] == 'R'
                            and r[2][2] is not None):
                        mech_bad += 1
                        if mech_bad <= 5:
                            print("MECHANISM?", e, S, r)
                else:
                    und_both += 1
    print(f"A2 lpcons: eager-defined {agree} (all in exact agreement: "
          f"{mismatches == 0}); undefined-both {und_both}; "
          f"LAZY-ONLY definedness points {extra}; "
          f"non-R-slot mechanisms {mech_bad} (expect 0)")
    return mismatches, extra, mech_bad

if __name__ == '__main__':
    crosscheck(1500, seed=1)
    lpcons(2, 4)

# ---------------- part A2b: faithful mechanism check ----------------
def ev_trace(e, S, lazy, disc):
    """like ev but records SUBTREES discarded (lazy) in disc (node ids)."""
    t = e[0]
    if t == 'K': return ('val', e[1])
    if t == 'V': return ('val', S)
    if t == 'C':
        a = ev_trace(e[1], S, lazy, disc)
        if a[0] == 'undef': return a
        b = ev_trace(e[2], S, lazy, disc)
        if b[0] == 'undef': return b
        return ('val', a[1] + b[1])
    T = ev_trace(e[3], S, lazy, disc)
    if T[0] == 'undef': return T
    B = ev_trace(e[2], S, lazy, disc)
    if B[0] == 'undef': return B
    if B[1] == '': return ('undef',)
    if lazy and B[1] not in T[1]:
        disc.append(e[1])                          # R discarded here
        return T
    R = ev_trace(e[1], S, lazy, disc)
    if R[0] == 'undef': return R
    return ('val', core.subst(R[1], B[1], T[1]))

def undef_node(e, S):
    """(slot, subtree) of the eager-undefined node; subtree is a node of e."""
    r = ev_eager_reason(e, S)
    return r

def contains(sub, node):
    if sub is node: return True
    if sub[0] == 'C':
        return contains(sub[1], node) or contains(sub[2], node)
    if sub[0] == 'S':
        return (contains(sub[1], node) or contains(sub[2], node)
                or contains(sub[3], node))
    return False

def mech_check(maxdepth=2, maxlen=4, sample=200000, seed=7):
    """On lazy-only definedness points: is the eager-undefined node inside
    some subtree the lazy run DISCARDED?  (lpcons mechanism, faithful)."""
    rng = random.Random(seed)
    IN = strings(maxlen)
    exprs = all_exprs(maxdepth)
    checked = bad = 0
    for e in rng.sample(exprs, min(sample, len(exprs))):
        for S in IN:
            le = ev(e, S, True)
            ee = ev(e, S, False)
            if ee[0] == 'val' or le[0] == 'undef':
                continue
            checked += 1
            disc = []
            ev_trace(e, S, True, disc)
            r = ev_eager_reason(e, S)
            node = r[2] if r[0] == 'undef' else None
            ok = node is not None and any(contains(d, node) for d in disc)
            if not ok:
                bad += 1
                if bad <= 3:
                    print("MECH FAIL", e, S, r, "discards:", len(disc))
    print(f"A2b mechanism (sampled {sample}): {checked} lazy-only points, "
          f"{bad} not through a discarded replacement (expect 0)")

# ---------------- part B: denotation spaces ----------------
def census(maxdepth=2, maxlen=4):
    IN = strings(maxlen)
    exprs = all_exprs(maxdepth)
    lazyD, eagerD = {}, {}
    for e in exprs:
        tl = []
        for S in IN:
            r = ev(e, S, True)
            tl.append(r[1] if r[0] == 'val' else None)
        lazyD.setdefault(tuple(tl), []).append(e)
        te = []
        for S in IN:
            r = ev(e, S, False)
            te.append(r[1] if r[0] == 'val' else None)
        eagerD.setdefault(tuple(te), []).append(e)
    return IN, lazyD, eagerD

def partB(maxdepth=2, maxlen=4):
    IN, lazyD, eagerD = census(maxdepth, maxlen)
    print(f"B1 depth <= {maxdepth}: {len(lazyD)} distinct LAZY denotations, "
          f"{len(eagerD)} distinct EAGER denotations "
          f"(from {len(all_exprs(maxdepth))} expressions)")
    # eager denotations always have lazy counterparts?
    eager_only = [t for t in eagerD if t not in lazyD]
    print(f"   eager-only denotations: {len(eager_only)} (expect 0: "
          f"every eager denotation is also lazy -- same syntax!)")
    lazy_only = [t for t in lazyD if t not in eagerD]
    print(f"   LAZY-ONLY denotations: {len(lazy_only)}")
    # classify: for each, its domain and whether the domain is an eager
    # domain (identity-on-D eager-realizable at this depth) and whether
    # some eager denotation agrees on the domain
    eager_doms = set()
    for t in eagerD:
        eager_doms.add(tuple(x is not None for x in t))
    dom_ok = val_ok = neither = 0
    for t in lazy_only:
        dom = tuple(x is not None for x in t)
        if dom in eager_doms:
            dom_ok += 1
        # value agreement: exists eager s with s[i] == t[i] wherever t[i]
        # is not None?  (eager may be defined off dom too -- weak check)
        agree = False
        for s in eagerD:
            if all((t[i] is None) or (s[i] == t[i]) for i in range(len(t))):
                agree = True; break
        if agree: val_ok += 1
        if (dom not in eager_doms) and not agree: neither += 1
    print(f"   of the lazy-only: domain-is-eager-domain {dom_ok}; "
          f"value-extends-some-eager {val_ok}; "
          f"neither (new domain AND no value-extension) {neither}")
    return IN, lazyD, eagerD, lazy_only

if __name__ == '__main__':
    import sys as _s
    if 'A2B' in _s.argv:
        mech_check()
        partB()

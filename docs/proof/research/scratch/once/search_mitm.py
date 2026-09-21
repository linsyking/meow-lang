"""Exhaustive MITM (meet-in-the-middle) search: does ANY constant-pattern
pipeline of depth <= 4 / <= 5 (paper vocabulary: patterns, replacements of
length <= 2 over abc) compute del1b on the test domain -- or del1b
restricted to the classes C_2 / C_3 (strings with <= 2 / <= 3 b's)?

MITM: depth <= 4 = f o g with f, g each <= 2 passes; depth <= 5 = f o g
with g <= 3 passes (first) and f <= 2 passes (last).  Behaviors (deduped)
suffice: f o g depends only on the behaviors of f and g.  Dedup on the
full test-domain signature is exact for constant passes (pass = function).

Also: Part C -- variable-pattern exhaustive depth-3 search ON THE CLASS C_2
(do computed needles at least handle two-b strings?).
"""
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
from oncecore import binstrings, const_passes, del1b, VOCAB

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def apply_pipeline(pl, s):
    for (P, R) in pl:
        s = s.replace(P, R)
    return s


def sig_of(pl, test):
    return tuple(apply_pipeline(pl, s) for s in test)


def build_levels(test, passes, maxlevel):
    """BFS over full signatures; returns list of levels (level 0..maxlevel),
    each a list of (pipeline, signature)."""
    root = tuple(test)
    seen = {root}
    levels = [[((), root)]]
    frontier = [root]
    for lev in range(1, maxlevel + 1):
        newf, newp = [], []
        t0 = time.time()
        for sig in frontier:
            # find a witness pipeline for sig (stored alongside)
            pass
        # (rebuild with pipelines attached)
        break
    return levels


def build_levels2(test, passes, maxlevel):
    """BFS storing (pipeline, signature) pairs, dedup on signature."""
    root = tuple(test)
    seen = {root: ()}
    levels = [[((), root)]]
    frontier = [((), root)]
    for lev in range(1, maxlevel + 1):
        t0 = time.time()
        newf = []
        seenn = seen
        for (pl, sig) in frontier:
            for p in passes:
                P, R = p
                ns = tuple(s.replace(P, R) for s in sig)
                if ns not in seenn:
                    seenn[ns] = pl + (p,)
                    newf.append((pl + (p,), ns))
        frontier = newf
        levels.append(newf)
        log(f"    level {lev}: +{len(newf)} (cum {len(seen)}), {time.time()-t0:.0f}s")
    return levels


# --------------------------------------------------------------- MITM parts

_G = None      # global for workers: (S_g list of (pipeline, sig?), U list, ...)


def mitm(test, passes, depth_g, depth_f, tsig):
    """Search for f o g = tsig with g in S_{<=depth_g}, f in S_{<=depth_f}.
    Returns list of (f_pipeline, g_pipeline) witnesses (possibly none)."""
    log(f"  building g-side levels <= {depth_g} ...")
    lv_g = build_levels2(test, passes, depth_g)
    S_g = [pl for lvl in lv_g for (pl, _) in lvl]
    log(f"  building f-side levels <= {depth_f} ...")
    lv_f = build_levels2(test, passes, depth_f)
    S_f = [pl for lvl in lv_f for (pl, _) in lvl]
    log(f"  |S_g| = {len(S_g)}, |S_f| = {len(S_f)}")
    s1 = 'abab' if 'abab' in test else test[len(test) // 2]   # probe strings
    t1 = tsig[test.index(s1)]
    s2 = 'abba' if 'abba' in test else test[-1]
    t2 = tsig[test.index(s2)]
    # index g's by image of s1
    u_map = {}
    for pl in S_g:
        u_map.setdefault(apply_pipeline(pl, s1), []).append(
            (pl, apply_pipeline(pl, s2)))
    global _U, _T1
    _U = list(u_map.keys())
    _T1 = t1
    log(f"  distinct probe images |U| = {len(_U)}")

    t0 = time.time()
    cand = []
    with Pool(30, initializer=_init_worker, initargs=(_U, _T1)) as pool:
        for fpl, hits in pool.imap_unordered(_do_f_star, S_f, chunksize=4):
            if hits:
                cand.append((fpl, hits))
    log(f"  probe filter done in {time.time()-t0:.0f}s; "
        f"{len(cand)} f's with >=1 probe hit")
    # full verification of candidate (f, g) pairs (2nd probe, then full)
    witnesses = []
    nfull = 0
    for fpl, hits in cand:
        for u in hits:
            for (gpl, u2) in u_map[u]:
                if apply_pipeline(fpl, u2) != t2:
                    continue
                nfull += 1
                if sig_of(fpl, [apply_pipeline(gpl, s) for s in test]) == tsig:
                    witnesses.append((fpl, gpl))
                    log(f"  WITNESS depth {len(fpl)+len(gpl)}: g={gpl} f={fpl}")
    log(f"  full checks: {nfull}, witnesses: {len(witnesses)}")
    return witnesses


def _init_worker(U, t1):
    global _U, _T1
    _U = U
    _T1 = t1


def _do_f_star(fpl):
    hits = []
    for u in _U:
        if apply_pipeline(fpl, u) == _T1:
            hits.append(u)
    return fpl, hits


# --------------------------------------------------------------- main parts

def part_full():
    test = binstrings(6)
    tsig = tuple(del1b(s) for s in test)
    passes = const_passes('abc', 2, 2)
    log(f"A: full domain (127 binary strings <=6), paper vocab "
        f"({len(passes)} passes)")
    log(" A1: depth <= 4 (2+2 MITM)")
    mitm(test, passes, 2, 2, tsig)
    log(" A2: depth <= 5 (3+2 MITM)")
    mitm(test, passes, 3, 2, tsig)


def part_class():
    test_all = binstrings(6)
    passes = const_passes('abc', 2, 2)
    for nb in (2, 3):
        cls = [s for s in test_all if s.count('b') <= nb]
        tsig = tuple(del1b(s) for s in cls)
        log(f"B: class C_{nb} ({len(cls)} strings), paper vocab")
        log(f" B1: depth <= 4")
        mitm(cls, passes, 2, 2, tsig)
        log(f" B2: depth <= 5")
        mitm(cls, passes, 3, 2, tsig)


VAR_PAT = ['a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len', 'enc',
           'tail', 'init', 'aXb']
VAR_REP = ['eps', 'a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len',
           'enc', 'tail', 'init', 'aXb']


def part_varclass():
    """Exhaustive depth-3 VARIABLE-pattern search restricted to C_2."""
    from oncecore import subst
    test_all = binstrings(6)
    cls = [s for s in test_all if s.count('b') <= 2]
    tsig = tuple(del1b(s) for s in cls)
    passes = [(r, p) for p in VAR_PAT for r in VAR_REP]
    root = tuple(cls)
    seen = {root: ()}
    frontier = [((), root)]
    hit = None
    for lev in range(1, 4):
        newf = []
        for (pl, sig) in frontier:
            for (rn, pn) in passes:
                ns = []
                ok = True
                for orig, cur in zip(cls, sig):
                    P = VOCAB[pn](orig)
                    if P == '':
                        ok = False
                        break
                    ns.append(cur.replace(P, VOCAB[rn](orig)))
                if not ok:
                    continue
                ns = tuple(ns)
                if ns not in seen:
                    seen[ns] = pl + ((rn, pn),)
                    newf.append((pl + ((rn, pn),), ns))
                    if ns == tsig:
                        hit = seen[ns]
                        break
            if hit:
                break
        frontier = newf
        log(f"  varclass level {lev}: cum {len(seen)}")
        if hit:
            break
    log(f"C: variable-pattern depth-3 on C_2 ({len(cls)} strings): "
        f"{'FOUND ' + str(hit) if hit else 'ABSENT'}")


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('full', 'all'):
        part_full()
    if which in ('class', 'all'):
        part_class()
    if which in ('varclass', 'all'):
        part_varclass()
    log(f"total {time.time()-t0:.0f}s")
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/mitm.log', 'w') as f:
        f.write('\n'.join(LOG))

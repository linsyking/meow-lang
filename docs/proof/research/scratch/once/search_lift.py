"""R4: the |Sigma| >= 3 lift -- search for a ternary rep1b/del1b witness.

The binary cascade (verify_r3.py) breaks on c's: stage 3 [ba->b] cannot
delete a c after a b, and stage 4's [aa->ab] pairing misaligns across c's.
Two searches here:

  mitm3   exhaustive MITM (depth <= 4, then 5) over the PAPER vocabulary
          const_passes('abc', 2, 2) for rep1b on the C-SPLICED domain:
          every binary string <= 5 with ONE c inserted at every position
          (plus the pure-binary strings) -- the tightest domain that
          still forces c-handling.  Any candidate is then verified on the
          full ternary domain <= 7 + random.
  stage   structured search over the CASCADE-SHAPED vocabulary (my
          hand-designed stages: per-char doubling [s->ss], halving
          [ss->s], the binary witness passes, sentinel sandwiches
          [b->aba] / [b->aab] / [b->ba], junction swaps [ba->ab]) at
          depth <= 6 MITM -- the vocabulary is small (~40 passes) so
          depth 6 = 3+3 is feasible.

Run:  python3 search_lift.py mitm3 | stage
"""
import itertools
import random
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
from oncecore import del1b, rep1b, const_passes

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def apply_pipeline(pl, s):
    for (P, R) in pl:
        s = s.replace(P, R)
    return s


def c_spliced(maxlen=5):
    """binary strings <= maxlen, each with one c spliced at every
    position, deduped, plus the pure binary strings."""
    out = []
    seen = set()
    for L in range(maxlen + 1):
        for t in itertools.product('ab', repeat=L):
            w = ''.join(t)
            for i in range(len(w) + 1):
                u = w[:i] + 'c' + w[i:]
                if u not in seen:
                    seen.add(u)
                    out.append(u)
            if w not in seen:
                seen.add(w)
                out.append(w)
    return out


# ------------------------------------------------------------- shared MITM
def build_levels(test, passes, maxlevel):
    root = tuple(test)
    seen = {root: ()}
    levels = [[((), root)]]
    frontier = [((), root)]
    for lev in range(1, maxlevel + 1):
        t0 = time.time()
        newf = []
        for (pl, sig) in frontier:
            for p in passes:
                P, R = p
                ns = tuple(s.replace(P, R) for s in sig)
                if ns not in seen:
                    seen[ns] = pl + (p,)
                    newf.append((pl + (p,), ns))
        frontier = newf
        levels.append(newf)
        log(f"    level {lev}: +{len(newf)} (cum {len(seen)}), {time.time()-t0:.0f}s")
    return levels, seen


_U = None
_T1 = None


def _init_worker(U, t1):
    global _U, _T1
    _U = U
    _T1 = t1


def _do_f(fpl):
    hits = [u for u in _U if apply_pipeline(fpl, u) == _T1]
    return fpl, hits


def mitm(test, passes, dg, df, target, name):
    tsig = tuple(target(s) for s in test)
    log(f"  building g-side (first {dg} passes) ...")
    lv_g, _ = build_levels(test, passes, dg)
    S_g = [pl for lvl in lv_g for (pl, _) in lvl]
    log(f"  building f-side (last {df} passes) ...")
    lv_f, _ = build_levels(test, passes, df)
    S_f = [pl for lvl in lv_f for (pl, _) in lvl]
    log(f"  |S_g|={len(S_g)} |S_f|={len(S_f)}")
    s1 = test[len(test) // 3]
    t1 = tsig[test.index(s1)]
    s2 = test[-1]
    t2 = tsig[test.index(s2)]
    umap = {}
    for pl in S_g:
        umap.setdefault(apply_pipeline(pl, s1), []).append(
            (pl, apply_pipeline(pl, s2)))
    U = list(umap.keys())
    global _U, _T1
    _U, _T1 = U, t1
    log(f"  probe images |U|={len(U)}")
    t0 = time.time()
    cand = []
    with Pool(30, initializer=_init_worker, initargs=(U, t1)) as pool:
        for fpl, hits in pool.imap_unordered(_do_f, S_f, chunksize=8):
            if hits:
                cand.append((fpl, hits))
    log(f"  probe filter: {len(cand)} f-candidates, {time.time()-t0:.0f}s")
    nfull = 0
    for fpl, hits in cand:
        for u in hits:
            for (gpl, u2) in umap[u]:
                if apply_pipeline(fpl, u2) != t2:
                    continue
                nfull += 1
                mid = [apply_pipeline(gpl, s) for s in test]
                got = tuple(apply_pipeline(fpl, m) for m in mid)
                if got == tsig:
                    log(f"  WITNESS {name} depth {len(fpl)+len(gpl)}: "
                        f"g={gpl} f={fpl}")
                    return (gpl, fpl)
                if nfull % 50000 == 0:
                    log(f"    ... {nfull} full checks")
    log(f"  full checks {nfull}: no witness for {name} at depth <= {dg+df}")
    return None


def full_verify(pl, target, name):
    """verify a candidate pipeline on the FULL ternary domain."""
    for ml, alpha in ((7, 'abc'), (6, 'abcd')):
        bad = 0
        n = 0
        for L in range(ml + 1):
            for t in itertools.product(alpha, repeat=L):
                X = ''.join(t)
                n += 1
                if apply_pipeline(pl, X) != target(X):
                    bad += 1
        log(f"  verify {name} over {alpha} <= {ml}: {bad}/{n} fail")
        if bad:
            return False
    rng = random.Random(5)
    bad = 0
    for _ in range(200000):
        X = ''.join(rng.choice('abc') for _ in range(rng.randrange(0, 40)))
        if apply_pipeline(pl, X) != target(X):
            bad += 1
    log(f"  verify {name} random abc <= 39: {bad}/200000 fail")
    return bad == 0


# =================================================================== mitm3
def part_mitm3():
    test = c_spliced(5)
    log(f"mitm3: c-spliced domain: {len(test)} strings "
        f"(binary <=5 with one c at each position)")
    passes = const_passes('abc', 2, 2)
    log(f"  vocabulary: {len(passes)} passes (patterns/repls <= 2 over abc)")
    w = mitm(test, passes, 2, 2, rep1b, "rep1b@c-spliced")
    if w:
        full_verify(list(w[0]) + list(w[1]), rep1b, "rep1b")
        return
    w = mitm(test, passes, 3, 2, rep1b, "rep1b@c-spliced")
    if w:
        full_verify(list(w[0]) + list(w[1]), rep1b, "rep1b")


# =================================================================== stage
def cascade_vocab():
    """The cascade-shaped vocabulary: every stage from the binary witness,
    its per-char generalizations, and the sentinel/swap variants."""
    V = []
    # binary witness passes
    V += [('a', 'aa'), ('b', 'ab'), ('ba', 'b'), ('aa', 'ab'), ('ab', 'a')]
    # per-char doubling (a, c) and halving
    V += [('a', 'aa'), ('c', 'cc'), ('aa', 'a'), ('cc', 'c')]
    # mark insertions around b
    V += [('b', 'ba'), ('b', 'ab'), ('b', 'aba'), ('b', 'aab'),
          ('b', 'abb'), ('b', 'bab'), ('b', 'b'), ('b', 'cc'),
          ('b', 'bcc'), ('b', 'ccb')]
    # junction deletions / swaps
    V += [('ab', 'b'), ('ba', 'a'), ('ba', 'ab'), ('ab', 'ba'),
          ('bb', 'b'), ('ca', 'a'), ('ac', 'a'), ('bc', 'b'),
          ('cb', 'b'), ('ca', 'c'), ('ac', 'c')]
    # pairing encodings
    V += [('aa', 'ab'), ('cc', 'ac'), ('aa', 'ba'), ('cc', 'ca'),
          ('aa', 'aac'), ('cc', 'aac')]
    # collapses
    V += [('ab', 'a'), ('ac', 'a'), ('ba', 'a'), ('ca', 'a'),
          ('aac', 'a'), ('aca', 'a'), ('aab', 'a')]
    # dedupe, drop identity passes and empty patterns
    out = []
    seen = set()
    for p in V:
        if p[0] == '' or p[0] == p[1]:
            continue
        if p in seen:
            continue
        seen.add(p)
        out.append(p)
    return out


def part_stage():
    test = c_spliced(5)
    log(f"stage: cascade-shaped vocabulary on c-spliced domain "
        f"({len(test)} strings)")
    V = cascade_vocab()
    log(f"  vocabulary: {len(V)} passes: {V}")
    for (dg, df) in ((3, 3), (4, 3), (4, 4)):
        w = mitm(test, V, dg, df, rep1b, f"rep1b@stages{dg}+{df}")
        if w:
            full_verify(list(w[0]) + list(w[1]), rep1b, "rep1b")
            return


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('mitm3', 'all'):
        part_mitm3()
    if which in ('stage', 'all'):
        part_stage()
    log(f"total {time.time()-t0:.0f}s")
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/lift.log',
              'w') as f:
        f.write('\n'.join(LOG))

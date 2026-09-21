"""R1 battery for HINGE 1 (once in L?): reproduce + escalate the paper's
failed searches for 'delete the leftmost b', and characterize the misses.

Parts (argv):  x  cross-checks           r  reproduce paper BFS depth 3
               rc restricted classes    nm near-miss census (needs r)
               v  vocabulary escalation  var variable-pattern searches
               rand randomized deep     all everything in order

Every search prints its exact space + domain so the run is reproducible.
"""
import hashlib
import heapq
import itertools
import random
import sys
import time
from collections import defaultdict

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/rec/lazy_pass')
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/systems')

from oncecore import (subst, once, del1b, rep1b, delallb, evalL, PatternEmpty,
                      binstrings, ternstrings, const_passes, VOCAB, VarBFS)

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


# ===================================================================== Part x
def part_x():
    """Cross-checks: my subst vs str.replace vs rec/lazy_pass vs systems;
    once vs systems; evalL vs rec/lazy_pass ev_eager; VOCAB vs real ASTs."""
    import core as LPCORE            # rec/lazy_pass
    import toolkit as LPTK
    import systems
    rng = random.Random(20260921)
    ALPHA = 'abc'

    # x1: subst == str.replace (constant patterns), random
    bad = 0
    for _ in range(30000):
        A = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 4)))
        B = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(1, 4)))
        C = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 9)))
        if subst(A, B, C) != C.replace(B, A):
            bad += 1
    log(f"x1 subst == str.replace on 30000 random (|A|<=3,|B|<=3,|C|<=8, abc): {bad} mismatches")

    # x2: subst == rec/lazy_pass core.subst == systems.subst
    bad = 0
    for _ in range(20000):
        A = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 4)))
        B = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(1, 4)))
        C = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 9)))
        if subst(A, B, C) != LPCORE.subst(A, B, C) or subst(A, B, C) != systems.subst(A, B, C):
            bad += 1
    log(f"x2 subst == lazy_pass core.subst == systems.subst on 20000 random: {bad} mismatches")

    # x3: once == systems.once
    bad = 0
    for _ in range(20000):
        A = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 4)))
        B = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(1, 4)))
        C = ''.join(rng.choice(ALPHA) for _ in range(rng.randrange(0, 9)))
        if once(A, B, C) != systems.once(A, B, C):
            bad += 1
    log(f"x3 once == systems.once on 20000 random: {bad} mismatches")

    # x4: evalL == ev_eager(defs={}) on random ASTs
    def rand_ast(d, rng):
        if d == 0 or rng.random() < 0.3:
            return (rng.choice([('K', rng.choice(['', 'a', 'b', 'ab', 'ba', 'aa', 'bb'])),
                                ('V', 0)]))
        r = rng.random()
        if r < 0.5:
            return ('S', rand_ast(d - 1, rng), rand_ast(d - 1, rng), rand_ast(d - 1, rng))
        return ('C', rand_ast(d - 1, rng), rand_ast(d - 1, rng))

    agree = undef_match = 0
    for _ in range(4000):
        e = rand_ast(3, rng)
        X = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 6)))
        try:
            v1 = evalL(e, X); u1 = False
        except PatternEmpty:
            v1, u1 = None, True
        try:
            v2 = LPCORE.ev_eager({}, e, (X,)); u2 = False
        except LPCORE.Undefined:
            v2, u2 = None, True
        if u1 != u2 or (not u1 and v1 != v2):
            log("  x4 MISMATCH", e, X, v1, v2)
            break
        agree += 1
        undef_match += (u1 is True)
    else:
        log(f"x4 evalL == lazy_pass ev_eager on 4000 random ASTs x inputs: all agree "
            f"({undef_match} both-undefined)")

    # x5: VOCAB entries vs real L-ASTs (toolkit builders)
    sg = LPTK.Sig(['a', 'b'], 'a', 'b', 'b', 'a')      # b='a', x='b'
    A_ANCH = sg.b + sg.b                                # 'aa'
    def T_last():  return LPTK.C(LPTK.enc2(sg, LPTK.V(0)), LPTK.K(A_ANCH))
    PA = sg.x + 'a' + A_ANCH
    PB = sg.x + 'b' + A_ANCH
    asts = {
        'enc': LPTK.enc(sg, LPTK.V(0)),
        'dec': LPTK.dec(sg, LPTK.V(0)),
        'tail': LPTK.tail(sg, LPTK.V(0)),
        'head': LPTK.head(sg, LPTK.V(0)),
        'len': LPTK.comp([(sg.x, c) for c in 'ab'], LPTK.V(0)),   # [b/a][b/b]X = b^|X|
        'H': LPTK.comp([('b', 'a'), ('', 'b'), ('a', 'bb')], LPTK.V(0)),
        'last': LPTK.if_(sg, LPTK.eq(sg, LPTK.V(0), LPTK.K('')), LPTK.K(''),
                    LPTK.if_(sg, LPTK.contains(sg, T_last(), PA), LPTK.K('a'), LPTK.K('b'))),
        'init': LPTK.if_(sg, LPTK.eq(sg, LPTK.V(0), LPTK.K('')), LPTK.K(''),
                     LPTK.if_(sg, LPTK.contains(sg, T_last(), PA),
                              LPTK.dec2(sg, LPTK.comp([('', PA)], T_last())),
                              LPTK.dec2(sg, LPTK.comp([('', PB)], T_last())))),
    }
    test = binstrings(5)
    for name, ast in asts.items():
        bad = 0
        for X in test:
            try:
                v = evalL(ast, X)
            except PatternEmpty:
                v = None
            if v != VOCAB[name](X):
                bad += 1
        log(f"x5 VOCAB['{name}'] == real L-AST on {len(test)} strings: {bad} mismatches")

    # x6: del1b == once('','b',.) (the probe's definition)
    bad = sum(1 for X in binstrings(7) if del1b(X) != once('', 'b', X))
    log(f"x6 del1b == [eps/b]_1 on all 508 strings <=7: {bad} mismatches")


# ===================================================================== Part r
class FastBFS:
    """Constant-pattern BFS with digest dedup (memory-safe for big levels).
    Tracks streaming distance to a target signature."""

    def __init__(self, testset, passes, targetsig=None):
        self.test = list(testset)
        self.sig0 = tuple(self.test)
        self.passes = passes
        self.seen = {}                      # digest -> (parent digest | None, pass)
        self.root = self._dig(self.sig0)
        self.seen[self.root] = (None, None)
        self.frontier = [self.sig0]
        self.targetdig = self._dig(targetsig) if targetsig is not None else None
        self.best = []                      # heap of (-dist, digest, pipeline)
        self.targetsig = targetsig

    def _dig(self, sig):
        h = hashlib.blake2b(digest_size=16)
        for s in sig:
            h.update(s.encode())
            h.update(b'\x00')
        return h.digest()

    def _dist(self, sig):
        return sum(1 for a, b in zip(sig, self.targetsig) if a != b)

    def run_level(self, keep_best=8):
        newf = []
        nb = 0
        for sig in self.frontier:
            for p in self.passes:
                P, R = p
                ns = tuple(s.replace(P, R) for s in sig)
                d = self._dig(ns)
                if d in self.seen:
                    continue
                self.seen[d] = (self._dig(sig), p)
                newf.append(ns)
                nb += 1
                if self.targetdig is not None and self.targetdig == d:
                    return ns, newf
                if self.targetsig is not None:
                    dist = self._dist(ns)
                    if len(self.best) < keep_best:
                        heapq.heappush(self.best, (-dist, d, p, self._dig(sig)))
                    elif -self.best[0][0] > dist:
                        heapq.heapreplace(self.best, (-dist, d, p, self._dig(sig)))
        self.frontier = newf
        return None, newf

    def hit(self):
        return self.targetdig in self.seen


def part_r():
    """Reproduce the paper's search: constant patterns, |P|,|R| <= 2 over abc,
    depth 3, behavior dedup on all 254 binary strings <= 6."""
    test = binstrings(6)
    passes = const_passes('abc', 2, 2)
    log(f"r: paper space: {len(passes)} passes (pats<=2, repls<=2, abc), "
        f"domain {len(test)} binary strings <=6, depth 3")
    tsigs = {'del1b': tuple(del1b(s) for s in test),
             'rep1b': tuple(rep1b(s) for s in test),
             'delallb': tuple(delallb(s) for s in test)}
    for name, ts in tsigs.items():
        bfs = FastBFS(test, passes, ts)
        for lev in range(1, 4):
            hit, _ = bfs.run_level()
            if hit is not None:
                break
        log(f"  target {name}: {'FOUND depth ' + str(lev) if bfs.hit() else 'ABSENT at depth 3'}"
            f"   [behaviors seen: {len(bfs.seen)}]")
    return test, passes


# ==================================================================== Part rc
def part_rc():
    """Restricted-class exhaustive search: is del1b restricted to
    C_n = {strings with <= n b's} reachable by constant-pattern pipelines?
    (dedup on class signatures is exact for constant passes)."""
    test_all = binstrings(6)
    passes = const_passes('abc', 2, 2)
    for nb_max in (1, 2, 3):
        cls = [s for s in test_all if s.count('b') <= nb_max]
        tsig = tuple(del1b(s) for s in cls)
        bfs = FastBFS(cls, passes, tsig)
        found = None
        for lev in range(1, 5):
            hit, _ = bfs.run_level()
            if hit is not None:
                found = lev
                break
            if len(bfs.seen) > 3_000_000:
                log(f"  C_{nb_max}: aborted, >3M behaviors at level {lev}")
                break
        log(f"rc: C_{nb_max} ({len(cls)} strings): del1b|C_{nb_max} "
            f"{'FOUND at depth ' + str(found) if found is not None else 'ABSENT at depth 4'}"
            f"   [behaviors: {len(bfs.seen)}]")


# ==================================================================== Part nm
def part_nm():
    """Near-miss census from the depth-3 exhaustive space (paper vocab):
    distance distribution vs del1b, closest behaviors, failure-shape
    classification."""
    test = binstrings(6)
    passes = const_passes('abc', 2, 2)
    tsig = tuple(del1b(s) for s in test)
    bfs = FastBFS(test, passes, tsig)
    for _ in range(3):
        bfs.run_level()
    # distance histogram over ALL seen behaviors (recompute from frontier+
    # seen is impossible without sigs -> recompute by re-walking: instead we
    # collected best-8 streaming; for the full histogram do a fresh pass
    # storing distances per level)
    # (cheap alternative: rerun levels storing dist only)
    hist = defaultdict(int)
    seen = {}
    root = tuple(test)
    seen[root] = 0
    frontier = [root]
    for lev in range(1, 4):
        newf = []
        for sig in frontier:
            for (P, R) in passes:
                ns = tuple(s.replace(P, R) for s in sig)
                if ns in seen:
                    continue
                seen[ns] = lev
                d = sum(1 for a, b in zip(ns, tsig) if a != b)
                hist[d] += 1
                newf.append(ns)
        frontier = newf
        log(f"  nm level {lev}: {len(newf)} new, cum {len(seen)}")
    tot = sum(hist.values())
    log(f"nm: distance-to-del1b histogram over {tot} depth<=3 behaviors "
        f"(254 strings): min={min(hist)}, #d<=5: {sum(v for k,v in hist.items() if k<=5)}")
    log(f"    counts d=0..8: {[hist.get(d,0) for d in range(9)]}")
    # closest behaviors with pipelines (recompute best by scanning)
    best = []
    for sig, lev in seen.items():
        d = sum(1 for a, b in zip(sig, tsig) if a != b)
        best.append((d, lev, sig))
    best.sort(key=lambda t: t[0])
    shown = 0
    for d, lev, sig in best:
        if shown >= 6:
            break
        # reconstruct pipeline by reverse search from sig
        pl = _reconstruct(seen_all=None, target=sig, test=test, passes=passes, maxd=lev)
        fails = [s for s, a, b in zip(test, sig, tsig) if a != b]
        log(f"  miss d={d} depth={lev} pipeline={pl}")
        log(f"      fails on {len(fails)}/{len(test)}: e.g. {fails[:8]}")
        shown += 1
    return best


def _reconstruct(seen_all, target, test, passes, maxd):
    """greedy reconstruction of a pipeline reaching signature `target`
    (used only for reporting near misses; small search)."""
    # BFS storing full sigs up to maxd
    root = tuple(test)
    par = {root: None}
    frontier = [root]
    for _ in range(maxd):
        newf = []
        for sig in frontier:
            for p in passes:
                P, R = p
                ns = tuple(s.replace(P, R) for s in sig)
                if ns not in par:
                    par[ns] = (sig, p)
                    newf.append(ns)
                    if ns == target:
                        pl = []
                        node = ns
                        while par[node]:
                            prev, last = par[node]
                            pl.append(last)
                            node = prev
                        return list(reversed(pl))
        frontier = newf
    return None


# ===================================================================== Part v
def part_v():
    """Vocabulary escalations of the constant-pattern BFS."""
    test = binstrings(6)
    tsig = tuple(del1b(s) for s in test)

    # v1: binary alphabet, patterns<=3, repls<=3, depth 3
    passes = const_passes('ab', 3, 3)
    log(f"v1: binary patterns<=3 repls<=3 ({len(passes)} passes), depth 3, "
        f"254 strings <=6")
    bfs = FastBFS(test, passes, tsig)
    for lev in range(1, 4):
        hit, _ = bfs.run_level()
        if hit is not None:
            break
    log(f"  del1b: {'FOUND d' + str(lev) if bfs.hit() else 'ABSENT at depth 3'}"
        f" [behaviors {len(bfs.seen)}]")

    # v2: quaternary alphabet, patterns<=2 repls<=2, depth 3
    passes = const_passes('abcd', 2, 2)
    log(f"v2: quaternary patterns<=2 repls<=2 ({len(passes)} passes), depth 3, "
        f"254 strings <=6")
    bfs = FastBFS(test, passes, tsig)
    for lev in range(1, 4):
        hit, _ = bfs.run_level()
        if hit is not None:
            break
    log(f"  del1b: {'FOUND d' + str(lev) if bfs.hit() else 'ABSENT at depth 3'}"
        f" [behaviors {len(bfs.seen)}]")

    # v3: ternary patterns<=3 repls<=2, depth 3 (both wider)
    passes = const_passes('abc', 3, 2)
    log(f"v3: ternary patterns<=3 repls<=2 ({len(passes)} passes), depth 3")
    bfs = FastBFS(test, passes, tsig)
    for lev in range(1, 4):
        hit, _ = bfs.run_level()
        if hit is not None:
            break
    log(f"  del1b: {'FOUND d' + str(lev) if bfs.hit() else 'ABSENT at depth 3'}"
        f" [behaviors {len(bfs.seen)}]")


# =================================================================== Part var
VAR_PAT = ['a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len', 'enc',
           'tail', 'init', 'aXb']
VAR_REP = ['eps', 'a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len',
           'enc', 'tail', 'init', 'aXb']


def part_var():
    """Variable-pattern search: patterns/replacements computed from the
    ORIGINAL input by L-computable vocab functions.  Exhaustive depth 2,
    then depth 3 on a reduced vocabulary, then randomized depth 4-7."""
    test = binstrings(6)
    tsig = tuple(del1b(s) for s in test)
    passes = [(r, p) for p in VAR_PAT for r in VAR_REP]
    log(f"var: {len(passes)} variable passes (patterns from {VAR_PAT}, "
        f"replacements from {VAR_REP}), patterns computed from original input")

    # exhaustive depth 3
    vb = VarBFS(test, passes)
    hit = None
    for lev in range(1, 4):
        n = vb.run_level()
        log(f"  var level {lev}: +{n} new (cum {len(vb.seen)})")
        if tsig in vb.seen:
            hit = lev
            break
    log(f"  del1b: {'FOUND var-pipeline depth ' + str(hit) if hit else 'ABSENT at depth 3'}")

    # closest misses of the variable space
    best = []
    for sig in vb.seen:
        d = sum(1 for a, b in zip(sig, tsig) if a != b)
        best.append((d, sig))
    best.sort(key=lambda t: t[0])
    for d, sig in best[:4]:
        pl = vb.pipeline_of(sig)
        fails = [s for s, a, b in zip(test, sig, tsig) if a != b]
        log(f"  var-miss d={d} pipeline={pl}")
        log(f"      fails on {len(fails)}/{len(test)}: {fails[:8]}")

    # randomized depth 4-7, full-distance tracking
    rng = random.Random(987654321)
    t_end = time.time() + 240
    tried = 0
    bestd = 10 ** 9
    bestpl = None
    while time.time() < t_end:
        k = rng.randrange(4, 8)
        pl = [rng.choice(passes) for _ in range(k)]
        d = 0
        for orig, want in zip(test, tsig):
            cur = orig
            for (rn, pn) in pl:
                P = VOCAB[pn](orig)
                if P == '':
                    d = 10 ** 9
                    break
                cur = cur.replace(P, VOCAB[rn](orig))
            if cur != want:
                d += 1
        tried += 1
        if d < bestd:
            bestd, bestpl = d, pl
            log(f"  var-rand new best d={d}: {pl}")
        if d == 0:
            log(f"  VAR WITNESS: {pl}")
            break
    log(f"var-rand: {tried} pipelines of 4-7 passes in 240s, best distance {bestd}")


# =================================================================== Part rand
def part_rand():
    """Randomized deep CONSTANT search with full-domain distance tracking
    (the paper tracked only the first failing string)."""
    test = binstrings(7)
    tsig = tuple(del1b(s) for s in test)
    passes = const_passes('abc', 2, 2) + const_passes('ab', 3, 3)
    rng = random.Random(42)
    t_end = time.time() + 300
    tried = 0
    dists = defaultdict(int)
    bestd, bestpl = 10 ** 9, None
    while time.time() < t_end:
        k = rng.randrange(3, 9)
        pl = [rng.choice(passes) for _ in range(k)]
        d = 0
        for s, w in zip(test, tsig):
            t = s
            for (P, R) in pl:
                t = t.replace(P, R)
            if t != w:
                d += 1
        tried += 1
        dists[d] += 1
        if d < bestd:
            bestd, bestpl = d, pl
        if d == 0:
            log(f"rand WITNESS: {pl}")
            break
    log(f"rand: {tried} pipelines of 3-8 passes (vocab abc<=2 + ab<=3), "
        f"best full-domain distance {bestd} on 508 strings <=7")
    log(f"     best pipeline: {bestpl}")
    log(f"     distance histogram (0..10): {[dists.get(i,0) for i in range(11)]}")


# ======================================================================== main
if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('x', 'all'):
        log("=== Part x: cross-checks ===")
        part_x()
    if which in ('r', 'all'):
        log("=== Part r: reproduce paper's BFS (depth 3) ===")
        part_r()
    if which in ('rc', 'all'):
        log("=== Part rc: restricted classes ===")
        part_rc()
    if which in ('nm', 'all'):
        log("=== Part nm: near-miss census ===")
        part_nm()
    if which in ('v', 'all'):
        log("=== Part v: vocabulary escalation ===")
        part_v()
    if which in ('var', 'all'):
        log("=== Part var: variable-pattern search ===")
        part_var()
    if which in ('rand', 'all'):
        log("=== Part rand: randomized deep ===")
        part_rand()
    log(f"total time {time.time()-t0:.1f}s")
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/r1.log', 'w') as f:
        f.write('\n'.join(LOG))

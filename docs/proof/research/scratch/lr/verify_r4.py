"""ROUND 4: collapse vs strictness + the landscape row for L+R.

  E0   W's closed forms: W = [a/bb]^L ; [b/aa]^R ; [a/bb]^L (run order).
       W fixes every alternating string; W(b^n) has the derived 2-block formula.
  E1a  Constant passes with a SINGLE-LETTER pattern are direction-independent
       (L = R): they are exactly the letter-substitution homomorphisms
       (sigma -> A), because inserted text is never rescanned.
  E1b  Orientation Lemma (the formal residue-end heuristic): for cross-letter
       letter-power passes [tau^q/sigma^p], sigma != tau, p >= 2, on a
       sigma-run of length l (bare or sentinel-delimited with an inert third
       letter c, so nothing merges):
         L : sigma^l -> (tau^q)^{l div p} . sigma^{l mod p}   (produced left,
                                                                residue right)
         R : sigma^l -> sigma^{l mod p} . (tau^q)^{l div p}   (= rev of L)
  E2   COMPLETE two-block impossibility (the R2 D2b upgrade: block length was
       budget-limited <= 6 there; here saturated = ALL lengths).  All passes
       of the universe U are length-non-increasing, so D_N = all binary
       strings of length <= N is closed under U, and each pipeline restricts
       to a function D_N -> D_N.  Tables are byte-vectors over D_N indices
       (N = 7: 255 strings, exactly one byte per entry), a pass is a byte
       translation table, so closures saturate exactly (dedup by table).
       Saturate S_L (pure-L words, any length) and S_R, then the two-block
       composites L-closure(S_R) (= f o g, f pure-L, g pure-R, all lengths)
       and R-closure(S_L).  Test: are the 4 >=2-alternation survivor tables
       among them?  Universe ladder U_min (4 cross-letter halvings),
       U2 (all 24 length-non-increasing |pattern| = 2 passes),
       U36 (U2 + the 12 direction-independent single-letter passes).
       Sanity plants: 1-alternation pipelines ARE in the two-block closures.
  E3   The NR2L invariant candidate (aligned with the ONCE agent's
       "junction-local bounded left-context" / "no right-to-left flow of
       unbounded information"):  probe pairs = (x, x with ONE run lengthened
       by 1) -- a parity flip of a single run.  Classify (f(x), f(x')):
         PREFIX  = parity material surfaced at the RIGHT flank (natural L
                   flow), SUFFIX = at the LEFT flank (R-to-L routing).
       E3a: complete closures (pure-L, pure-R, two-blocks) -- suffix-freedom
            of the pure-L side would be the separation.
       E3b: toolkit slices (enc/dec/enc2/dec2/head/tail/cat/eq/if/contains,
            last/init/rotate from prop:last -- the computed-needle class).
       E3c: random 1-ary L-expressions with arbitrary sub-expression patterns
            (the rep_n / spanning-needle escape-hatch class) -- falsification
            hunt; random mixed expressions as positive control.
       E3d: rho-slices X |-> [A/B]^R X (the violation side).
  E4   Growth transfer: mixed pipelines obey the same length bound
       |f(x)| <= |x| * prod(max(1, |A_i|/|B_i|)) (landscape row: the L+R
       growth class equals the L growth class).
"""

import itertools
import random
import sys
import os
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrcore import (subst, substR, K, V, C, S, SR, run)
import toolkit as tk

AB = 'ab'
sg = tk.BIN


class Tally:
    def __init__(self, name):
        self.name, self.bad = name, 0

    def check(self, ok, msg):
        if not ok:
            self.bad += 1
            print(f'    FAIL [{self.name}] {msg}')

    def done(self):
        print(f'    [{self.name}] ' + ('ALL GREEN' if self.bad == 0
                                       else f'{self.bad} FAILURES'))
        return self.bad == 0


# --------------------------------------------------------------- domain

def domain(n):
    dom = ['']
    for k in range(1, n + 1):
        dom += [''.join(p) for p in itertools.product(AB, repeat=k)]
    return dom


def gen_map(gen, dom, idx):
    """Byte translation table realizing one pass on D_N indices."""
    A, B, d = gen
    f = subst if d == 'L' else substR
    m = bytearray(256)
    for i, s in enumerate(dom):
        t = f(A, B, s)
        j = idx.get(t)
        if j is None:
            raise RuntimeError(f'pass {gen}: output {t!r} escapes the domain')
        m[i] = j
    return bytes(m)


def closure(gen_maps, seeds, cap, name, note=''):
    """BFS to saturation (dedup by table).  Returns (set, False) if the
    closure saturated before the cap (COMPLETE), (set, None) if the cap was
    hit (INCOMPLETE)."""
    t0 = time.time()
    seen = set(seeds)
    frontier = list(seeds)
    while frontier:
        new = []
        for tab in frontier:
            for gm in gen_maps:
                t2 = tab.translate(gm)
                if t2 not in seen:
                    seen.add(t2)
                    new.append(t2)
        frontier = new
        if len(seen) > cap:
            print(f'    [{name}] CAP HIT at {len(seen)} tables '
                  f'({time.time()-t0:.0f}s) -- INCOMPLETE{note}')
            return seen, None
    print(f'    [{name}] saturated: {len(seen)} tables '
          f'({time.time()-t0:.0f}s){note}')
    return seen, False


# --------------------------------------------------------------- universes

CROSS = [('a', 'bb'), ('b', 'aa')]
U_MIN = [(A, B, d) for (A, B) in CROSS for d in 'LR']            # 4
P2 = ['aa', 'ab', 'ba', 'bb']
R2 = ['', 'a', 'b']
U2 = [(A, B, d) for B in P2 for A in R2 for d in 'LR']           # 24
P1 = ['a', 'b']
U36 = U2 + [(A, B, d) for B in P1 for A in R2 for d in 'LR']     # 36

SURVIVORS = {                                            # run order
    'W_LRL': [('a', 'bb', 'L'), ('b', 'aa', 'R'), ('a', 'bb', 'L')],
    'W_RLR': [('a', 'bb', 'R'), ('b', 'aa', 'L'), ('a', 'bb', 'R')],
    'W_bLRL': [('b', 'aa', 'L'), ('a', 'bb', 'R'), ('b', 'aa', 'L')],
    'W_bRLR': [('b', 'aa', 'R'), ('a', 'bb', 'L'), ('b', 'aa', 'R')],
}


def run_word(start, word):
    t = start
    for (A, B, d) in word:
        f = subst if d == 'L' else substR
        t = f(A, B, t)
    return t


def word_table(word, dom):
    return tuple(run_word(s, word) for s in dom)


# --------------------------------------------------------------- E0

def e0():
    print('--- E0: W closed forms ---')
    t = Tally('E0')
    W = SURVIVORS['W_LRL']
    alt = [s for s in domain(9)
           if all(s[i] != s[i+1] for i in range(len(s) - 1))]
    for s in alt:
        t.check(run_word(s, W) == s, f'W does not fix {s!r}')
    print(f'    W fixes all {len(alt)} alternating strings of length <= 9')

    # W(b^n) closed form, hand-derived: with q = (n div 2) div 2, r = n mod 2,
    #   W(b^n) = a^{(n div 2) mod 2 + (q + r) div 2} . b^{(q + r) mod 2}
    def wbn(n):
        m = n // 2
        q = m // 2
        r = n % 2
        return ('a' * ((m % 2) + (q + r) // 2) + 'b' * ((q + r) % 2))
    for n in range(0, 66):
        got = run_word('b' * n, W)
        t.check(got == wbn(n), f'W(b^{n}) = {got!r}, formula {wbn(n)!r}')
    print('    W(b^n) matches the derived closed form for n <= 65')
    return t


# --------------------------------------------------------------- E1

def e1():
    print('--- E1: direction-independence and orientation lemmas ---')
    t = Tally('E1')
    repls = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    dom = domain(10)
    n = 0
    for B in P1:
        for A in repls:
            for s in dom:
                t.check(subst(A, B, s) == substR(A, B, s),
                        f'[{A}/{B}] L != R on {s!r}')
                n += 1
    print(f'    E1a: single-letter patterns: L = R on all {len(dom)} strings '
          f'x {len(P1)} patterns x {len(repls)} repls = {n} checks')

    for sigma, tau in [('a', 'b'), ('b', 'a')]:
        for p in (2, 3):
            for q in (1, 2):
                A, B = tau * q, sigma * p
                for l in range(0, 13):
                    prod = tau * q * (l // p)
                    res = sigma * (l % p)
                    lval = subst(A, B, sigma * l)
                    rval = substR(A, B, sigma * l)
                    t.check(lval == prod + res,
                            f'L({sigma}^{l}) = {lval!r} != prod+res')
                    t.check(rval == res + prod,
                            f'R({sigma}^{l}) = {rval!r} != res+prod')
                    t.check(rval == lval[::-1], 'R != rev(L) on run')
                    s = 'c' + sigma * l + 'c'
                    t.check(subst(A, B, s) == 'c' + prod + res + 'c',
                            f'sentineled L mismatch at l={l}')
                    t.check(substR(A, B, s) == 'c' + res + prod + 'c',
                            f'sentineled R mismatch at l={l}')
    print('    E1b: cross-letter power passes: L = produced-then-residue, '
          'R = residue-then-produced = rev(L), bare and sentineled, '
          'l <= 12, p in {2,3}, q in {1,2}')
    return t


# --------------------------------------------------------------- E2

def e2():
    print('--- E2: COMPLETE two-block impossibility (saturated closures) ---')
    t = Tally('E2')
    results = {}
    for uname, U in [('U_min', U_MIN), ('U2', U2), ('U36', U36)]:
        lg = [g for g in U if g[2] == 'L']
        rg = [g for g in U if g[2] == 'R']
        for n in (5, 6, 7):
            dom = domain(n)
            idx = {s: i for i, s in enumerate(dom)}
            idtab = bytes(range(len(dom)))
            lmaps = [gen_map(g, dom, idx) for g in lg]
            rmaps = [gen_map(g, dom, idx) for g in rg]
            s_l, c1 = closure(lmaps, [idtab], 400000, f'{uname}/N={n}/S_L')
            s_r, c2 = closure(rmaps, [idtab], 400000, f'{uname}/N={n}/S_R')
            if c1 is None or c2 is None:
                print(f'    [{uname}/N={n}] pure closures too big -- '
                      f'universe at its limit here')
                break
            lr, c3 = closure(lmaps, list(s_r), 600000, f'{uname}/N={n}/LR',
                            ' (L-closure of S_R: f pure-L o g pure-R)')
            rl, c4 = closure(rmaps, list(s_l), 600000, f'{uname}/N={n}/RL',
                             ' (R-closure of S_L: f pure-R o g pure-L)')
            del s_l, s_r
            plantLR = bytes(idx[v] for v in
                            word_table([('b', 'aa', 'R'), ('a', 'bb', 'L')],
                                       dom))
            plantRL = bytes(idx[v] for v in
                            word_table([('a', 'bb', 'L'), ('b', 'aa', 'R')],
                                       dom))
            verdict = {}
            for wname, word in SURVIVORS.items():
                tab = bytes(idx[v] for v in word_table(word, dom))
                in_lr = (tab in lr) if c3 is not None else None
                in_rl = (tab in rl) if c4 is not None else None
                verdict[wname] = (in_lr, in_rl)
            comp = ('COMPLETE' if (c3 is False and c4 is False)
                    else 'INCOMPLETE (cap hit)')
            ok_plants = (c3 is None or plantLR in lr) and \
                        (c4 is None or plantRL in rl)
            print(f'    [{uname}/N={n}] {comp}; survivors in LR/RL: '
                  f'{verdict}; 1-alt plants present: {ok_plants}')
            t.check(ok_plants, f'{uname}/N={n}: plant missing')
            if comp == 'COMPLETE':
                for wname, (a, b) in verdict.items():
                    t.check(a is False and b is False,
                            f'{uname}/N={n}: {wname} IS a two-block')
                if uname == 'U_min' and n == 7:
                    # complete depth-3 census: which mixed words over U_min
                    # are not two-blocks at ANY block length?
                    need2 = []
                    for w in itertools.product(U_MIN, repeat=3):
                        tab = bytes(idx[v] for v in word_table(list(w), dom))
                        if tab not in lr and tab not in rl:
                            need2.append(w)
                    print(f'    [{uname}/N={n}] depth-3 census: '
                          f'{len(need2)}/{4**3} mixed words are not '
                          f'two-blocks at any block length:')
                    for w in need2:
                        print(f'        {w}')
            results[(uname, n)] = (comp, verdict)
            del lr, rl
    return t, results


# --------------------------------------------------------------- E3
#
# Invariant hunt, three operationalizations tested in turn:
#   v1 (whole-output prefix/suffix events) -- FALSIFIED: even the identity
#      has SUFFIX events when a MIDDLE run is extended (the input difference
#      itself sits left of center); record kept in the run log of REPORT.
#   v2 (bounded prefix-erosion) -- FALSIFIED: eq(x,c) erodes the common
#      prefix unboundedly (output position 0 depends on the whole input);
#      but eq's outputs are never suffix-comparable.
#   v3 (CURRENT): "R2L event" = outputs SUFFIX-COMPARABLE with prefix
#      EROSION >= 3 (one output a proper suffix of the other while the
#      shared input prefix lost >= 3 characters of image).  The R-pass
#      signature (b^{2m} -> a^m, b^{2m+1} -> b a^m: erosion 2m) is an R2L
#      event; single L-passes are suffix-comparable only with erosion
#      <= |B| - 1 (the straddle argument); the question is whether ANY
#      L-expression produces one.  Scan: single constant passes, complete
#      closures, toolkit slices, random L-expressions (spanning-needle
#      class) -- vs R-passes / rho-slices / W.

CLS_NAMES = ('ABSORBED', 'PREFIX', 'SUFFIX', 'MIXED')


def cls(y, y2):
    if y == y2:
        return 0
    if y.startswith(y2) or y2.startswith(y):
        return 1
    if y.endswith(y2) or y2.endswith(y):
        return 2
    return 3


def cp_len(y, y2):
    n = 0
    for a, b in zip(y, y2):
        if a != b:
            break
        n += 1
    return n


def run_pairs(s):
    """(x2 = x with ONE run lengthened by 1); pairs share the input prefix
    up to the start of the lengthened run."""
    out = []
    j = 0
    while j < len(s):
        k = j
        while k < len(s) and s[k] == s[j]:
            k += 1
        out.append((s[:j] + s[j] + s[j:k] + s[k:], j))
        j = k
    if not s:
        out += [('a', 0), ('b', 0)]
    return out


def scan_r2l(fn, pairs, thresh=3):
    """pairs: (x, x2, cp_in).  v4: R2L event = suffix-comparable, NOT
    prefix-comparable, erosion >= thresh.  Returns (n, max_erosion, ex)."""
    cache = {}

    def val(s):
        if s not in cache:
            cache[s] = fn(s)
        return cache[s]
    n_ev = 0
    max_er = 0
    ex = None
    for (x, x2, cp_in) in pairs:
        y, y2 = val(x), val(x2)
        if y is None or y2 is None or y == y2:
            continue
        if y.startswith(y2) or y2.startswith(y):
            continue                     # right-flank event, not routing
        if not (y.endswith(y2) or y2.endswith(y)):
            continue
        er = cp_in - cp_len(y, y2)
        if er >= thresh:
            n_ev += 1
            max_er = max(max_er, er)
            if ex is None:
                ex = (x, x2, y, y2, er)
    return n_ev, max_er, ex


def e3():
    print('--- E3: v3 R2L-event scan (suffix-comparable + erosion >= 3) ---')
    n = 6
    dom = domain(n)
    idx = {s: i for i, s in enumerate(dom)}
    pairs = []
    for s in domain(n - 1):
        for (s2, j) in run_pairs(s):
            pairs.append((s, s2, j))
    print(f'    {len(pairs)} probe pairs (single-run +1 extensions, all '
          f'runs), |x| <= {n-1}')

    def report(fn, label):
        n_ev, max_er, ex = scan_r2l(fn, pairs)
        print(f'    [{label}] R2L events: {n_ev}, max erosion {max_er}'
              + (f'; e.g. {ex[0]!r}->{ex[2]!r} vs {ex[1]!r}->{ex[3]!r} '
                 f'(erosion {ex[4]})' if ex else ''))
        return n_ev, max_er

    # single constant passes (both directions, all 84)
    worst_L = (0, 0, None)
    for B in ['a', 'b', 'aa', 'ab', 'ba', 'bb']:
        for A in ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']:
            if not B:
                continue
            nev, mer = report(lambda s, A=A, B=B: subst(A, B, s),
                              f'single L-pass [{A}/{B}]')
            if mer > worst_L[1]:
                worst_L = (nev, mer, (A, B))
    print(f'    worst single L-pass erosion: {worst_L[1]} '
          f'(pass {worst_L[2]})')
    for (A, B) in [('b', 'aa'), ('a', 'bb')]:
        report(lambda s, A=A, B=B: substR(A, B, s), f'R-pass [{A}/{B}]^R')

    # complete closures
    for uname, U in [('U2', U2), ('U_min', U_MIN)]:
        lg = [g for g in U if g[2] == 'L']
        rg = [g for g in U if g[2] == 'R']
        idtab = bytes(range(len(dom)))
        lmaps = [gen_map(g, dom, idx) for g in lg]
        rmaps = [gen_map(g, dom, idx) for g in rg]
        s_l, c1 = closure(lmaps, [idtab], 300000, f'E3/{uname}/S_L')
        s_r, c2 = closure(rmaps, [idtab], 300000, f'E3/{uname}/S_R')
        if c1 is None or c2 is None:
            print(f'    [E3] {uname} closures too big at N={n}; skipping')
            del s_l, s_r
            continue
        pidx = [(idx[x], idx[x2], cp_in) for (x, x2, cp_in) in pairs]
        SUF = bytearray(65536)
        ERO = bytearray(65536)
        for i, s in enumerate(dom):
            for j, s2 in enumerate(dom):
                c = cls(s, s2)
                if c == 2:
                    SUF[i * 256 + j] = 1

        def scan_tabs(tabs, label):
            n_ev = 0
            max_er = 0
            ex = None
            for tab in tabs:
                for (i, j, cp_in) in pidx:
                    a, b = dom[tab[i]], dom[tab[j]]
                    if a == b or a.startswith(b) or b.startswith(a):
                        continue
                    if not (a.endswith(b) or b.endswith(a)):
                        continue
                    er = cp_in - cp_len(a, b)
                    if er >= 3:
                        n_ev += 1
                        if er > max_er:
                            max_er = er
                            ex = (a, b, er)
                        break       # one event suffices per table
            print(f'    [{label}] {len(tabs)} tables: {n_ev} with an R2L '
                  f'event, max erosion {max_er}'
                  + (f'; e.g. {ex[0]!r} vs {ex[1]!r} (erosion {ex[2]})'
                     if ex else ''))
            return n_ev, max_er

        scan_tabs(s_l, f'E3/{uname}/pure-L closure')
        scan_tabs(s_r, f'E3/{uname}/pure-R closure')
        lr, c3 = closure(lmaps, list(s_r), 400000, f'E3/{uname}/LR')
        if c3 is not None:
            scan_tabs(lr, f'E3/{uname}/two-block LR')
            del lr
        rl, c4 = closure(rmaps, list(s_l), 400000, f'E3/{uname}/RL')
        if c4 is not None:
            scan_tabs(rl, f'E3/{uname}/two-block RL')
            del rl
        del s_l, s_r
        break                         # first feasible universe

    # W itself
    report(lambda s: run_word(s, SURVIVORS['W_LRL']), 'W_LRL')

    # ---- toolkit slices (computed needles)
    A2 = sg.b + sg.b
    T = lambda E: C(tk.enc2(sg, E), K(A2))
    PA, PB = sg.x + 'a' + A2, sg.x + 'b' + A2
    last_e = tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                    tk.if_(sg, tk.contains(sg, T(V(0)), K(PA)), K('a'),
                           K('b')))
    init_e = tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                    tk.if_(sg, tk.contains(sg, T(V(0)), K(PA)),
                           tk.dec2(sg, tk.comp([('', PA)], T(V(0)))),
                           tk.dec2(sg, tk.comp([('', PB)], T(V(0))))))
    rot_e = tk.cat(sg, last_e, init_e)
    consts = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    slices = [
        ('enc', lambda s: run(tk.enc(sg, V(0)), (s,))),
        ('dec', lambda s: run(tk.dec(sg, V(0)), (s,))),
        ('enc2', lambda s: run(tk.enc2(sg, V(0)), (s,))),
        ('dec2', lambda s: run(tk.dec2(sg, V(0)), (s,))),
        ('head', lambda s: run(tk.head(sg, V(0)), (s,))),
        ('tail', lambda s: run(tk.tail(sg, V(0)), (s,))),
        ('last', lambda s: run(last_e, (s,))),
        ('init', lambda s: run(init_e, (s,))),
        ('rot', lambda s: run(rot_e, (s,))),
    ]
    for c in consts:
        slices.append((f'cat(.,{c!r})',
                       lambda s, c=c: run(tk.cat(sg, V(0), K(c)), (s,))))
        slices.append((f'cat({c!r},.)',
                       lambda s, c=c: run(tk.cat(sg, K(c), V(0)), (s,))))
        slices.append((f'eq(.,{c!r})',
                       lambda s, c=c: run(tk.eq(sg, V(0), K(c)), (s,))))
        for d in ('a', 'b'):
            slices.append((f'if(top,.,{d!r})',
                           lambda s, d=d: run(tk.if_(sg, K(sg.top), V(0),
                                                     K(d)), (s,))))
    print(f'    [E3b] {len(slices)} toolkit slices:')
    bad = []
    for name, fn in slices:
        nev, mer, _ = scan_r2l(fn, pairs)
        if nev:
            bad.append((name, mer))
    print(f'    [E3b] toolkit slices with R2L events: {len(bad)}/{len(slices)}'
          + (f' -- {bad}' if bad else ''))

    # ---- random 1-ary expressions (spanning-needle class)
    def rand_expr(rng, budget, allow_R):
        if budget <= 1 or rng.random() < 0.3:
            if rng.random() < 0.6:
                k = rng.randint(0, 3)
                return K(''.join(rng.choice(AB) for _ in range(k)))
            return V(0)
        r = rng.random()
        if r < 0.25:
            return C(rand_expr(rng, budget // 2, allow_R),
                     rand_expr(rng, budget // 2, allow_R))
        node = SR if (allow_R and rng.random() < 0.5) else S
        return node(rand_expr(rng, max(1, budget // 3), allow_R),
                    rand_expr(rng, max(1, budget // 3), allow_R),
                    rand_expr(rng, max(1, budget // 3), allow_R))

    rng = random.Random(9)
    for allow_R, n_expr, tag in ((False, 4000, 'random L-exprs'),
                                 (True, 1500, 'random mixed exprs')):
        with_ev = 0
        ex = None
        for _ in range(n_expr):
            e = rand_expr(rng, 14, allow_R)
            try:
                cache = {}
                for s in {x for p in pairs for x in p[:2]}:
                    v = run(e, (s,))
                    if v is not None and any(ch not in AB for ch in v):
                        v = None
                    cache[s] = v
            except Exception:
                continue
            for (x, x2, cp_in) in pairs:
                a, b = cache.get(x), cache.get(x2)
                if a is None or b is None or a == b:
                    continue
                if a.endswith(b) or b.endswith(a):
                    er = cp_in - cp_len(a, b)
                    if er >= 3:
                        with_ev += 1
                        if ex is None:
                            ex = (x, x2, a, b, er)
                        break
        print(f'    [E3c] {tag}: {with_ev}/{n_expr} expressions with an '
              f'R2L event'
              + (f'; first: {ex[0]!r} vs {ex[1]!r} -> {ex[2]!r} vs '
                 f'{ex[3]!r} (erosion {ex[4]})' if ex else ''))

    # ---- rho-slices
    print('    [E3d] rho-slices (constant A, B):')
    for (A3, B3) in [('b', 'aa'), ('a', 'bb'), ('ba', 'aa'), ('ab', 'bb')]:
        report(lambda s, A=A3, B=B3: substR(A, B, s), f'[{A3}/{B3}]^R')

    # ---- v5 offset scan: WHERE does the parity signal surface?
    # Probes (u.b^{2m}, u.b^{2m+1}), u not ending in b: the input difference
    # is at the run's END; an L-pass surfaces it at the run-image's RIGHT
    # edge, an R-pass at the LEFT edge.  Statistic: first-difference offset
    # d relative to output length (0 = far left = routed, 1 = right edge).
    print('    [v5] first-difference offset (rel = d / max(|y|,|y\'|); '
          'LOW = right-to-left routing):')
    P5 = []
    for u in ('a', 'aa', 'ab', 'ba', 'aba', 'abab'):
        for m in range(1, 6):
            P5.append((u + 'b' * (2 * m), u + 'b' * (2 * m + 1)))
            P5.append((u + 'a' * (2 * m), u + 'a' * (2 * m + 1)))

    def v5(fn):
        rels = []
        for (x, x2) in P5:
            y, y2 = fn(x), fn(x2)
            if y is None or y2 is None or y == y2:
                continue
            d = cp_len(y, y2)
            rels.append(d / max(len(y), len(y2)))
        if not rels:
            return None
        return min(rels), sum(rels) / len(rels), len(rels)

    def v5_report(fn, label):
        got = v5(fn)
        if got is None:
            print(f'    [v5] {label}: all probes absorbed')
        else:
            print(f'    [v5] {label}: min rel {got[0]:.2f}, mean '
                  f'{got[1]:.2f} ({got[2]} probes)')

    v5_report(lambda s: s, 'identity')
    v5_report(lambda s: subst('a', 'bb', s), '[a/bb] L')
    v5_report(lambda s: substR('a', 'bb', s), '[a/bb]^R')
    v5_report(lambda s: subst('b', 'aa', s), '[b/aa] L')
    v5_report(lambda s: substR('b', 'aa', s), '[b/aa]^R')
    v5_report(lambda s: subst('', 'a', s), '[eps/a] L')
    v5_report(lambda s: run(tk.enc(sg, V(0)), (s,)), 'enc')
    v5_report(lambda s: run(tk.dec(sg, V(0)), (s,)), 'dec')
    v5_report(lambda s: run(tk.tail(sg, V(0)), (s,)), 'tail')
    v5_report(lambda s: run(init_e, (s,)), 'init')
    v5_report(lambda s: run(rot_e, (s,)), 'rot')
    v5_report(lambda s: run(last_e, (s,)), 'last')
    v5_report(lambda s: run_word(s, SURVIVORS['W_LRL']), 'W_LRL')
    rng2 = random.Random(31)
    mins_L, mins_M = [], []
    low_L = []
    for allow_R, acc in ((False, mins_L), (True, mins_M)):
        for _ in range(30):
            e = rand_expr(rng2, 14, allow_R)
            def fn(s, e=e):
                try:
                    v = run(e, (s,))
                except Exception:
                    return None
                return v if v is not None and all(c in AB for c in v) \
                    else None
            got = v5(fn)
            if got is not None:
                acc.append(got[0])
                if got[0] <= 0.2 and not allow_R:
                    low_L.append((e, got[0]))
    if mins_L:
        print(f'    [v5] random L-exprs (n={len(mins_L)}): min-rel range '
              f'[{min(mins_L):.2f}, {max(mins_L):.2f}]')
    if mins_M:
        print(f'    [v5] random mixed exprs (n={len(mins_M)}): min-rel '
              f'range [{min(mins_M):.2f}, {max(mins_M):.2f}]')
    for (e, r) in low_L[:3]:
        print(f'    [v5] low-rel L-expression (rel {r:.2f}): {e!r}')
    return Tally('E3')  # data; interpretation in REPORT


# --------------------------------------------------------------- E4

def e4():
    print('--- E4: growth bound transfer to mixed pipelines ---')
    t = Tally('E4')
    rng = random.Random(5)
    pats = [a + b for a in AB for b in AB] + list(AB)
    repls4 = [a + b for a in AB for b in AB] + list(AB) + ['']
    dom = domain(12)
    checks = 0
    for _ in range(20000):
        depth = rng.randint(1, 5)
        word = []
        bound = Fraction(1)
        for _ in range(depth):
            A = rng.choice(repls4)
            B = rng.choice(pats)
            d = rng.choice('LR')
            word.append((A, B, d))
            if len(A) > len(B):
                bound *= Fraction(len(A), len(B))
        x = rng.choice(dom)
        f = run_word(x, word)
        t.check(Fraction(len(f)) <= Fraction(len(x)) * bound,
                f'growth bound violated: {x!r} --{word}--> {f!r}')
        checks += 1
    print(f'    {checks} random mixed pipelines (depth <= 5) on strings '
          f'<= 12: |f(x)| <= |x| * prod(max(1, |A_i|/|B_i|)) holds')
    return t


# --------------------------------------------------------------- main

if __name__ == '__main__':
    t0 = time.time()
    ok = True
    ok &= e0().done()
    ok &= e1().done()
    t2, _ = e2()
    ok &= t2.done()
    e3()
    ok &= e4().done()
    print(f'total {time.time()-t0:.0f}s; '
          f'{"ALL GREEN" if ok else "FAILURES PRESENT"}')
    sys.exit(0 if ok else 1)

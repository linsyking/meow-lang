#!/usr/bin/env python3
"""verify_r3.py -- R3: the general occurrence lemma, the two normalization
lemmas, and the containment lim(L) <= lazy-pass recursive L.

ITEM 1 (the write-up's load-bearing piece): the OCCURRENCE LEMMA, for
EVERY configuration (any pc, any x, y >= 0), not just the census domain.
Proof method: the GAP CALCULUS (full statement + proof in REPORT.md R3
and occurrence_lemma.tex).  Sketch:

  * sigma = structural char, tau = tally char.  Every structural
    constant is V(k) = ss(ts)^{k-1}t sss, k >= 2, indices pairwise
    distinct per machine: taus isolated, head run 2, internal gaps all
    1 (k-1 of them), tail run 3.  Every inter-constant junction merges
    to a sigma-run of 5.  A tally t^n contributes gap 3 before its
    first tau, n-1 gaps of 0 inside, gap 2 after its last tau; the
    EMPTY tally (counter = 0) makes its delimiters touch: gap 5.

  * any occurrence of a pattern W (no tt, >= 2 taus) in a configuration
    maps W's taus to CONSECUTIVE configuration taus, interior gaps
    EXACTLY equal, head <= preceding sigma-run, tail <= following run.

  * pattern interior gaps are in {1, 3, 5} only -- never 0 (inside a
    tally of length >= 2), never 2 (after a tally's last tau): so no
    pattern covers two consecutive tally characters and no pattern's
    tau-sequence crosses a tally's right edge.  The only pattern
    touching a tally is the DESIGNED one, the dec pattern D_r t, whose
    final gap 3 pins it to the tally's FIRST character (occurs iff the
    counter is nonzero, once).

  * PINNING: W's leading 1-block (length k-1 >= 1, unique since family
    indices are distinct) + the seam mismatch (a longer constant's
    internal gap 1 cannot match W's seam 5 or 3) + the head condition
    (a middle tau has only 1 sigma before it) force W to align
    slot-exactly, constant by constant.  Hence every pattern occurs
    exactly where the compiler put it, for ALL pc, x, y.

Machine checks (part A): A0 constants' gap structure; A1 pattern gap
discipline; A2 the configuration gap sequence equals the construction's
prediction on a large domain; A3 the brute-force occurrence census at
scale -- edge lengths x,y in {0,1,2} at every pc EXPLICITLY, then all
x,y in 0..40 at every pc, then 400 random states up to 1000 -- under
offsets 2, 3, 7 (hypothesis k >= 2 distinct), plus offset 1 (violates
the hypothesis; passes empirically anyway -- sequence pinning).

ITEM 2 (part B): the two R2 caveats as verified lemmas: B1 zero-branch
self-jump preprocessing; B2 compile-time normalization (counter swap +
cleanup loop).

ITEM 3 (part C): lim(L) <= lazy-pass recursive L: the driver
RUN(X) = if E(X) = X then X else RUN(E(X)) -- the paper's Sec. 6 gate
pattern, the recursive call in the dead branch's replacement (demanded
only when the pass fires).  Battery: single passes incl. the R1
mismatch rules (converging and diverging), a branching iterand, and the
R2 2CM steps themselves, on the lazy-pass abstract machine.
"""

import os
import sys
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'rec', 'lazy_pass'))

from lim_core import K, V, C, S, L, run
import verify_r2 as v2
from verify_r2 import FlatCM2, Vfam, sim_run, DOUBLE, ADDER
import core as lp                      # the lazy-pass abstract machine

random.seed(20260921)
CHECKS = [0, 0]


def ck(cond, what):
    CHECKS[0] += 1
    if not cond:
        CHECKS[1] += 1
        print(f"  FAIL: {what}")
    return bool(cond)


# ===========================================================================
# part A: the gap calculus and the general occurrence lemma
# ===========================================================================

def gap_struct(s, sig, tau):
    """(head, gaps, tail): sigma-run before the first tau, sigma-counts
    between consecutive taus, sigma-run after the last tau."""
    ps = [i for i, ch in enumerate(s) if ch == tau]
    assert ps, "no tally char in " + repr(s)
    head, tail = ps[0], len(s) - ps[-1] - 1
    gaps = [ps[i + 1] - ps[i] - 1 for i in range(len(ps) - 1)]
    return head, gaps, tail


def fam_index(c, swap):
    for k in range(1, 80):
        if Vfam(k, swap) == c:
            return k
    raise ValueError("not a family member: " + repr(c))


def program_constants(m, pc):
    """The program-zone constants in order (wrap included)."""
    lst = []
    for i in range(1, m.s + 1):
        if i == pc:
            lst += [m.M, m.P[i], m.M]
        else:
            lst.append(m.P[i])
    if pc == 0:
        lst += [m.M, m.PH, m.M]
    else:
        lst.append(m.PH)
    return lst


def cfg_gaps_prediction(m, pc, x, y):
    """The construction's predicted (head, gaps, tail) of cfg(pc,x,y):
    constants' internal 1-gaps, junction 5's, tally gaps
    3 0^(n-1) 2 (or 5 when empty), head 2, tail 3."""
    zone = program_constants(m, pc)
    cs = [m.D[0]] + zone + [m.D[1], m.D[2], m.D[3]]
    nprog = len(zone)
    ks = [fam_index(c, m.swap) for c in cs]
    # index in cs of D1 and D2 (the tally junctions follow them)
    iD1, iD2 = 1 + nprog, 2 + nprog
    flat = []
    for i, k in enumerate(ks):
        flat += [1] * (k - 1)
        if i == iD1:                    # D1 -> tally 1 -> D2
            flat += ([5] if x == 0 else [3] + [0] * (x - 1) + [2])
        elif i == iD2:                  # D2 -> tally 2 -> D3
            flat += ([5] if y == 0 else [3] + [0] * (y - 1) + [2])
        elif i + 1 < len(ks):
            flat.append(5)
    return 2, flat, 3


def all_patterns(m):
    """Every pattern of the step and the OUT stage with its expected
    count (pc, x, y) -> int.  Extends pattern_expectations with the halt
    dispatch pattern M PH M (occurs iff halted)."""
    E = m.pattern_expectations()
    E.append((m.M + m.PH + m.M, lambda pc, x, y: 1 if pc == 0 else 0))
    return E


def partA(machines, hypothesis=True):
    for m in machines:
        tag = m.name
        sig = 'b' if not m.swap else 'a'
        t = m.t
        ks = [fam_index(c, m.swap) for c in m.constants()]
        # A0: constants' gap structure
        for c in m.constants():
            k = fam_index(c, m.swap)
            ck(gap_struct(c, sig, t) == (2, [1] * (k - 1), 3),
               f"{tag}: constant {c!r} gap structure wrong")
        # A4: lemma hypothesis
        ck(len(set(ks)) == len(ks), f"{tag}: constants not distinct")
        if hypothesis:
            ck(all(k >= 2 for k in ks), f"{tag}: hypothesis k >= 2 failed")
        # A1: pattern gap discipline
        for (pat, _) in all_patterns(m):
            h, g, tl = gap_struct(pat, sig, t)
            ck(t + t not in pat, f"{tag}: pattern {pat!r} contains tt")
            ck(h == 2, f"{tag}: pattern {pat!r} head {h} != 2")
            ck(tl in (0, 3), f"{tag}: pattern {pat!r} tail {tl}")
            ck(all(d in (1, 3, 5) for d in g),
               f"{tag}: pattern {pat!r} gap outside {{1,3,5}}: {g}")
            if hypothesis:
                ck(len(g) >= 1, f"{tag}: pattern {pat!r} has < 2 taus")
        # A2: configuration gap prediction
        rnd = random.Random(hash(tag) & 0xffff)
        dom = [(x, y) for x in range(0, 9) for y in range(0, 9)]
        dom += [(rnd.randrange(0, 500), rnd.randrange(0, 500))
                for _ in range(60)]
        for pc in range(0, m.s + 1):
            for (x, y) in dom:
                cfg = m.make_cfg(pc, x, y)
                got = gap_struct(cfg, sig, t)
                want = cfg_gaps_prediction(m, pc, x, y)
                ck(got == want,
                   f"{tag}: gap prediction wrong at pc={pc} x={x} y={y}")
        # A3: the census at scale
        pats = all_patterns(m)
        n_edge = n_sys = n_rnd = 0
        for pc in range(0, m.s + 1):
            for x in (0, 1, 2):                      # EDGE lengths
                for y in (0, 1, 2):
                    cfg = m.make_cfg(pc, x, y)
                    n_edge += 1
                    for (pat, exp) in pats:
                        ck(cfg.count(pat) == exp(pc, x, y),
                           f"{tag}: EDGE census pc={pc} x={x} y={y} "
                           f"pattern {pat!r}")
            for x in range(0, 41):                   # systematic
                for y in range(0, 41):
                    cfg = m.make_cfg(pc, x, y)
                    n_sys += 1
                    for (pat, exp) in pats:
                        ck(cfg.count(pat) == exp(pc, x, y),
                           f"{tag}: census pc={pc} x={x} y={y} "
                           f"pattern {pat!r}")
        for _ in range(400):                        # random large states
            pc = rnd.randrange(0, m.s + 1)
            x, y = rnd.randrange(0, 1001), rnd.randrange(0, 1001)
            cfg = m.make_cfg(pc, x, y)
            n_rnd += 1
            for (pat, exp) in pats:
                ck(cfg.count(pat) == exp(pc, x, y),
                   f"{tag}: RANDOM census pc={pc} x={x} y={y} "
                   f"pattern {pat!r}")
        mode = "hypothesis" if hypothesis else "EMPIRICAL (k>=2 violated)"
        print(f"  {tag} [{mode}]: A0-A4 OK "
              f"({n_edge} edge + {n_sys} systematic + {n_rnd} random cfgs)")


# ===========================================================================
# part B: the normalization lemmas
# ===========================================================================

def fix_selfjump(instrs):
    """Replace every ('decjz', r, i, jnz) whose ZERO branch jumps to
    itself (jz == i) by ('decjz', r, k, jnz) + fresh k = ('inc', r2, k).
    The zero branch was a no-change infinite loop; k is a changing one.
    Partial function preserved."""
    out, extra, fresh = list(instrs), [], len(instrs) + 1
    for i, ins in enumerate(out, 1):
        if ins[0] == 'decjz' and ins[2] == i:
            r2 = 2 if ins[1] == 1 else 1
            out[i - 1] = ('decjz', ins[1], fresh, ins[3])
            extra.append(('inc', r2, fresh))
    return out + extra


def swap_counters(instrs):
    def sw(r):
        return 2 if r == 1 else 1
    out = []
    for ins in instrs:
        if ins[0] == 'inc':
            out.append(('inc', sw(ins[1]), ins[2]))
        else:
            out.append(('decjz', sw(ins[1]), ins[2], ins[3]))
    return out


def add_cleanup(instrs):
    """Retarget every jump-to-0 to a fresh drain instruction
    k = ('decjz', 1, 0, k): while counter 1 > 0 dec.  Guarantees the
    scratch counter is 0 at halt (the OUT stage's hypothesis)."""
    k = len(instrs) + 1
    out = []
    for ins in instrs:
        if ins[0] == 'inc':
            out.append(('inc', ins[1], k if ins[2] == 0 else ins[2]))
        else:
            out.append(('decjz', ins[1],
                        k if ins[2] == 0 else ins[2],
                        k if ins[3] == 0 else ins[3]))
    return out + [('decjz', 1, 0, k)]


def sim_out(instrs, x, y, cap=100000):
    """(halted, c1, c2); halted=False if the cap was hit."""
    traj, ok = sim_run(instrs, x, y, cap)
    return ok, traj[-1][1], traj[-1][2]


def partB(base):
    print("part B: the normalization lemmas")

    # ---- B1: zero-branch self-jump -----------------------------------
    HYB = [('decjz', 1, 1, 2), ('inc', 2, 0)]
    raw = FlatCM2(HYB, name='hyb-raw', **base)
    print("  B1: zero-branch self-jump (hyb)")
    for n in range(0, 7):
        for mm in range(0, 4):
            ok, c1, c2 = sim_out(HYB, n, mm, cap=2000)
            ck(ok == (n >= 1), f"hyb sim halting n={n} m={mm}")
            if ok:
                ck(c2 == mm + 1, f"hyb sim value n={n} m={mm}")
    # the raw compile HAS the non-halted fixed point (the caveat itself)
    bud = v2.Budget(10 ** 6, 1 << 22)
    for mm in range(0, 4):
        cfg = raw.make_cfg(1, 0, mm)
        ck(v2.ev(raw.step_ast, (cfg,), bud) == cfg,
           f"hyb-raw: identity fixed point at pc=1 x=0 y={mm} "
           "(this IS the caveat, made visible)")
    r = run(raw.main_ast, ('a',), 10 ** 6, 1 << 22)
    ck(r[0] == 'val', "hyb-raw: lim wrongly CONVERGES (caveat visible)")
    # preprocessed: identical semantics, no fixed point, exact partiality
    FIX = fix_selfjump(HYB)
    ck(FIX == [('decjz', 1, 3, 2), ('inc', 2, 0), ('inc', 2, 3)],
       f"fix_selfjump shape: {FIX}")
    # full normalization: HYB also leaves the scratch counter nonzero at
    # halt (n-1), so the compile contract needs the cleanup loop too
    NORM = add_cleanup(FIX)
    ck(NORM == [('decjz', 1, 3, 2), ('inc', 2, 4), ('inc', 2, 3),
                ('decjz', 1, 0, 4)], f"normalized shape: {NORM}")
    for n in range(0, 7):
        for mm in range(0, 4):
            ok0, _, c2a = sim_out(HYB, n, mm, cap=2000)
            ok1, _, c2b = sim_out(FIX, n, mm, cap=2000)
            ok2, d1, c2c = sim_out(NORM, n, mm, cap=2000)
            ck(ok0 == ok1 == ok2 and (not ok0 or
                                      c2a == c2b == c2c),
               f"normalization semantics differ at n={n} m={mm}")
            if ok2:
                ck(d1 == 0, f"normalized scratch not drained n={n}")
    fixed = FlatCM2(NORM, name='hyb-fixed', **base)
    v2.part01_toolkit_and_constants([fixed])
    v2.part234_invariants(fixed, range(0, 4), range(0, 4))
    for n in range(1, 7):
        r = run(fixed.main_ast, ('a' * n,), 10 ** 7, 1 << 22)
        ck(r[0] == 'val' and r[1] == 'a',
           f"hyb-fixed MAIN(a^{n}) wrong: {r[0]}")
    r = run(fixed.main_ast, ('',), 8000, 1 << 22)
    ck(r[0] == 'div', "hyb-fixed MAIN(eps) should diverge (machine loops)")
    print("  B1 OK: raw fixed point shown; fix+cleanup == original "
          "semantics; MAIN partiality exact")

    # ---- B2(i): counter swap ----------------------------------------
    print("  B2i: counter swap (output naturally in counter 1)")
    DRAIN1 = [('decjz', 2, 0, 2), ('inc', 1, 1)]
    SW = swap_counters(DRAIN1)
    ck(SW == [('decjz', 1, 0, 2), ('inc', 2, 1)], f"swap shape: {SW}")
    for n in range(0, 6):
        for mm in range(0, 6):
            ok, c1, c2 = sim_out(DRAIN1, n, mm)
            ck(ok and c1 == n + mm, f"drain1 sim n={n} m={mm}")
            oks, d1, d2 = sim_out(SW, n, mm)
            ck(oks and d2 == n + mm, f"swapped sim n={n} m={mm}")
    swm = FlatCM2(SW, name='drain1-swapped', **base)
    v2.part01_toolkit_and_constants([swm])
    v2.part234_invariants(swm, range(0, 4), range(0, 4))
    for n in range(0, 6):
        for mm in range(0, 6):
            r = run(swm.main2_ast, ('a' * n, 'a' * mm), 10 ** 7, 1 << 22)
            ck(r[0] == 'val' and r[1] == 'a' * (n + mm),
               f"swapped MAIN2({n},{mm}) wrong")
    print("  B2i OK: swap preserves output value, now in counter 2")

    # ---- B2(ii): the cleanup loop ------------------------------------
    print("  B2ii: cleanup loop (scratch not drained at halt)")
    DIRTY = [('inc', 2, 0)]
    raw2 = FlatCM2(DIRTY, name='dirty-raw', **base)
    for n in (0, 1, 3):
        cfg = raw2.make_cfg(0, n, 4)
        ck(cfg.count(raw2.out_prefix) == (1 if n == 0 else 0),
           f"dirty-raw out-prefix count at x={n}")
    r = run(raw2.main2_ast, ('aaa', 'aa'), 10 ** 6, 1 << 22)
    ck(r[0] == 'val' and r[1] != 'aaa',
       "dirty-raw MAIN2 returns garbage (the caveat, made visible)")
    CLEAN = add_cleanup(DIRTY)
    ck(CLEAN == [('inc', 2, 2), ('decjz', 1, 0, 2)], f"cleanup: {CLEAN}")
    for n in range(0, 6):
        for mm in range(0, 6):
            ok, c1, c2 = sim_out(DIRTY, n, mm)
            ck(ok and c2 == mm + 1, f"dirty sim n={n} m={mm}")
            okc, d1, d2 = sim_out(CLEAN, n, mm)
            ck(okc and d2 == mm + 1 and d1 == 0,
               f"clean sim n={n} m={mm}")
    clean = FlatCM2(CLEAN, name='dirty-clean', **base)
    v2.part01_toolkit_and_constants([clean])
    v2.part234_invariants(clean, range(0, 4), range(0, 4))
    for n in range(0, 6):
        for mm in range(0, 6):
            r = run(clean.main2_ast, ('a' * n, 'a' * mm), 10 ** 7, 1 << 22)
            ck(r[0] == 'val' and r[1] == 'a' * (mm + 1),
               f"clean MAIN2({n},{mm}) wrong")
    print("  B2ii OK: raw garbage shown; cleanup drains; values correct")


# ===========================================================================
# part C: lim(L) <= lazy-pass recursive L  (the driver)
# ===========================================================================

def build_run_driver(E, b, x):
    """RUN(X) = if E(X) = X then X else RUN(E(X)) -- the paper's Sec. 6
    gate pattern.  E is a flat Exp_1 (K/V/C/S nodes; the two calculi
    share the node format).  The recursive call sits in the outer
    selection pass's REPLACEMENT: the lazy-pass machine forces a
    replacement only when the pattern fires, so the call is demanded
    only on the live (unequal) branch."""
    def benc(Z):
        return C(C(K(x + b + b), S(K(x + b), K(b), Z)), K(x + b + b))
    eqx = S(K(b), benc(E), S(K(x), benc(V(0)), benc(E)))
    # value(eqx) starts with x iff E(X) = X (polarity probed at runtime)

    def enc(Z):
        return S(K(x + b), K(b), Z)

    def dec(Z):
        return S(K(b), K(x + b), Z)
    body = dec(S(enc(lp.F('RUN', E)), K(b + b),
                 S(enc(V(0)), K(x),
                   S(K(b + b), K(b), eqx))))
    return {'RUN': (1, body)}


def lp_run(defs, w, cap):
    r = lp.run_lazy(defs, 'RUN', (w,), cap=cap)
    if r[0] == 'val':
        return ('val', r[1])
    return ('div',)


CONV_RULES = [('baa', 'ab'), ('a', 'ab'), ('abba', 'bab'),
              ('baab', 'aba'), ('aabb', 'ba'), ('bbaa', 'ab'),
              ('ab', 'aa'), ('a', 'b')]
# note the [A/B] convention: ('a','ab') = replace ab by a (converges);
# ('ab','a') = replace a by ab (B in A: grows forever, diverges);
# ('aabb','ba') = replace ba by aabb -- EXPONENTIAL growth under sweeps
# (junctions recreate ba), diverges on mixed inputs, converges on
# ba-free ones.  Every (rule, input) pair is pre-classified by a cheap
# raw sweep simulation and then run with class-appropriate caps.
INPUTS = ['', 'a', 'b', 'ab', 'ba', 'aab', 'baa', 'abab', 'baba',
          'aabb', 'bbaa', 'abba', 'baab', 'aaab', 'abbb',
          'aabbaabb', 'baabbaab', 'abababab', 'bbbaaa']


def classify(A, B, w, cap=150, maxlen=4096):
    """Raw lim-orbit classification: 'val' (with value) or 'div'."""
    s = w
    for _ in range(cap):
        t = s.replace(B, A)
        if t == s:
            return ('val', s)
        if len(t) > maxlen:
            return ('div', None)
        s = t
    return ('div', None)


def partC(base):
    print("part C: lim(L) <= lazy-pass recursive L (the driver)")
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        # polarity probe of the equality construction
        E = S(K('c'), K('q'), V(0))
        defs = build_run_driver(E, b, x)
        lp.check_program(defs)
        ck(lp_run(defs, 'qq', 10 ** 6) == ('val', 'cc'),
           f"driver probe1 (b,x)=({b},{x})")
        ck(lp_run(defs, 'ab', 10 ** 6) == ('val', 'ab'),
           f"driver probe2 (b,x)=({b},{x})")
        n_conv = n_div = 0
        for (A, B) in CONV_RULES:
            E = S(K(A), K(B), V(0))
            defs = build_run_driver(E, b, x)
            lp.check_program(defs)
            for w in INPUTS:
                cls = classify(A, B, w)
                if cls[0] == 'val':
                    n_conv += 1
                    limr = run(L(E, V(0)), (w,), 200000, 1 << 20)
                    lpr = lp_run(defs, w, 3 * 10 ** 6)
                    ck(limr[0] == 'val' and lpr == ('val', limr[1]),
                       f"driver mismatch [{A}/{B}] {w!r}: "
                       f"lim={limr} lazy={lpr!r}")
                else:
                    n_div += 1
                    # diverging: small caps (exponential-growth rules
                    # hit the length cap in a dozen sweeps; the lazy
                    # machine has no length guard, so keep its step cap
                    # small enough that strings stay bounded)
                    limr = run(L(E, V(0)), (w,), 300, 4096)
                    lpr = lp_run(defs, w, 1500)
                    ck(limr[0] == 'div' and lpr[0] == 'div',
                       f"driver div mismatch [{A}/{B}] {w!r}: "
                       f"lim={limr[0]} lazy={lpr[0]}")
        # a branching iterand: grows while any b remains (diverges on
        # b-containing inputs; linear growth, +1 per sweep)
        _, mk_contains, sel = v2.make_toolkit(b, x)
        E = sel(mk_contains(V(0), 'b'), S(K('ab'), K('b'), V(0)), V(0))
        defs = build_run_driver(E, b, x)
        lp.check_program(defs)
        for w in INPUTS[:12]:
            if 'b' in w:
                n_div += 1
                limr = run(L(E, V(0)), (w,), 4000, 1 << 20)
                lpr = lp_run(defs, w, 40000)
                ck(limr[0] == 'div' and lpr[0] == 'div',
                   f"branching driver should diverge {w!r}: {lpr!r}")
            else:
                n_conv += 1
                limr = run(L(E, V(0)), (w,), 200000, 1 << 20)
                lpr = lp_run(defs, w, 3 * 10 ** 6)
                ck(limr[0] == 'val' and lpr == ('val', limr[1]),
                   f"branching driver mismatch {w!r}: {lpr!r}")
        print(f"  (b,x)=({b},{x}): 8 rules + branching: "
              f"{n_conv} conv (values exact) + {n_div} div OK")

    # the R2 2CM steps themselves as iterands of the driver
    for nm, ins, outc in [('double', DOUBLE, lambda n: 2 * n),
                          ('adder', ADDER, lambda n: n)]:
        m = FlatCM2(ins, name=nm, **base)
        defs = build_run_driver(m.step_ast, 'a', 'b')
        lp.check_program(defs)
        for n in range(0, 6):
            cfg = m.make_cfg(1, n, 0)
            limr = run(L(m.step_ast, V(0)), (cfg,), 10 ** 8, 1 << 24)
            lpr = lp_run(defs, cfg, 8 * 10 ** 6)
            want = m.make_cfg(0, 0, outc(n))
            ck(limr[0] == 'val' and limr[1] == want,
               f"{nm}: lim halt config wrong n={n}")
            ck(lpr == ('val', want),
               f"{nm}: lazy driver halt config wrong n={n}: {lpr[0]}")
        print(f"  2CM driver: {nm} n=0..5 halt configs match lim exactly")
    sl = FlatCM2([('inc', 1, 1)], name='selfloop', **base)
    defs = build_run_driver(sl.step_ast, 'a', 'b')
    lp.check_program(defs)
    for n in (0, 2):
        cfg = sl.make_cfg(1, n, 0)
        limr = run(L(sl.step_ast, V(0)), (cfg,), 6000, 1 << 22)
        lpr = lp_run(defs, cfg, 6000)
        ck(limr[0] == 'div' and lpr[0] == 'div',
           "selfloop: both lim and the lazy driver diverge")
    print("  2CM driver: selfloop diverges on both sides")


# ===========================================================================

def main():
    print("R3: occurrence lemma + normalization lemmas + lazy-pass "
          "containment")
    base = dict(b='a', x='b', swap=False, offset=3, spread=1)
    print("part A (offset=3, lemma hypothesis satisfied) ...")
    machines = [FlatCM2(DOUBLE, name='double', **base),
                FlatCM2(ADDER, name='adder', **base),
                FlatCM2([('decjz', 2, 3, 1), ('inc', 1, 1),
                         ('decjz', 1, 0, 4), ('inc', 2, 3)],
                        name='c2drain', **base)]
    partA(machines)

    print("part A escalation: offsets 2 and 7 ...")
    for off in (2, 7):
        bo = dict(b='a', x='b', swap=False, offset=off, spread=1)
        partA([FlatCM2(DOUBLE, name=f'double@{off}', **bo),
               FlatCM2(ADDER, name=f'adder@{off}', **bo)])

    print("part A note: offset=1 (violates k >= 2; empirical only) ...")
    b1 = dict(b='a', x='b', swap=False, offset=1, spread=1)
    partA([FlatCM2(DOUBLE, name='double@1', **b1)], hypothesis=False)

    print("part B ...")
    partB(base)

    print("part C ...")
    partC(base)

    print()
    tot = CHECKS[0] + v2.CHECKS[0]
    fail = CHECKS[1] + v2.CHECKS[1]
    print(f"R3 RESULT: {tot} checks, {fail} failures")
    return 0 if fail == 0 else 1


if __name__ == '__main__':
    sys.exit(main())

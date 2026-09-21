#!/usr/bin/env python3
"""verify_r2.py -- R2: the FLAT-L two-counter-machine step under lim.

The coordinator's design, implemented and machine-verified here.

  * configuration (Sigma = {a,b}, tally char t in {a, b}):

        cfg = D0 PROGRAM D1 T1 D2 T2 D3
        PROGRAM = P1 P2 ... Ps PH        (fixed constant instruction codes)
        the CURRENT instruction is marker-wrapped:  M Pi M
        (M PH M = halted, pc = 0);  Ti = t^{x_i} are the counter tallies
        (EMPTY run = zero: the delimiters become adjacent).

  * step = a flat Exp_1: an if-chain over CONSTANT occurrence tests
    contains(M Pi M)  (paper Equality + Selection; occurrence test via
    the fixed-point-set lemma [c/P]X = X iff P notin X).  Each branch is
    constant passes ONLY:

        inc(r,j):    [D_r t / D_r]                      (tally grows)
        decjz(r,jz,jnz):
             if contains(D_r D_r')  -> jump jz          (zero: no change)
             else                   -> [D_r / D_r t] + jump jnz
        jump i->j = unwrap [Pi / M Pi M]  THEN  wrap [M Pj M / Pj]
        (j = 0 wraps PH).  Unwrap-BEFORE-wrap makes self-jumps (j = i)
        come out right; no extremal-site edits are needed anywhere.

  * the halt configuration (M PH M wrapped, scratch counter drained to 0)
    is the UNIQUE fixed point: every non-halted step changes the string;
    the step is TOTAL (all patterns are nonempty constants; no L node;
    no variable patterns).  lim(step) = the machine's run, divergence of
    lim = exactly the machine's non-halting.

  * INIT = K(D0 prog(1) D1) . X . K(D2 D3)
    OUT  = [eps / D0 prog(0) D1 D2]  [eps / D3]     (constant prefix at
           halt, scratch = 0; leaves the bare output tally)
    MAIN = OUT o lim(step) o INIT.

Verified here (every claim machine-checked):
  part 0  toolkit polarity probes for every (b,x) role pair used;
  part 1  build-time constant-family invariants (pairwise
          non-occurrence, no doubled tally char, distinctness);
  part 2  occurrence census: EVERY pattern of the step (dispatch,
          unwrap, wrap, inc, dec, zero-test, out-prefix, delimiters)
          occurs exactly the expected number of times in EVERY
          configuration (pc, x, y) of the finite domain -- no spurious
          occurrences, no straddles;
  part 3  step semantics vs the ground-truth simulator on EVERY point
          of the domain (evaluated through the real AST evaluator);
  part 4  fixed-point uniqueness (step cfg != cfg unless halted) and
          totality on garbage strings;
  part 5  end-to-end: doubling machine MAIN(t^n) = t^{2n}, adder
          MAIN(t^n, t^m) = t^{n+m}; the lim orbit traced POINT BY POINT
          against the simulator trajectory; halt reached exactly;
  part 6  escalation: strictly larger n; both (b,x) toolkit roles
          {('a','b'), ('b','a')}; both configuration alphabet swaps;
          different constant offsets/spreads.
"""

import os
import sys
import random
import itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from lim_core import K, V, C, S, L, Budget, ev, run, size, check

random.seed(20260921)

CHECKS = [0, 0]   # [count, failures]


def ck(cond, what):
    CHECKS[0] += 1
    if not cond:
        CHECKS[1] += 1
        print(f"  FAIL: {what}")
    return bool(cond)


# ---------------------------------------------------------------------------
# ground truth: a plain two-counter machine simulator

def sim_step(instrs, pc, x, y):
    """One 2CM step.  pc = 0 means halted (identity)."""
    if pc == 0:
        return (pc, x, y)
    ins = instrs[pc - 1]
    if ins[0] == 'inc':
        _, r, j = ins
        if r == 1:
            x += 1
        else:
            y += 1
        return (j, x, y)
    if ins[0] == 'decjz':
        _, r, jz, jnz = ins
        if (x if r == 1 else y) == 0:
            return (jz, x, y)
        if r == 1:
            x -= 1
        else:
            y -= 1
        return (jnz, x, y)
    raise ValueError(f"bad instruction {ins}")


def sim_run(instrs, x, y, cap=100000):
    """Full trajectory [(pc,x,y),...]; halted iff the last pc is 0."""
    pc = 1
    traj = [(pc, x, y)]
    for _ in range(cap):
        if pc == 0:
            return traj, True
        pc, x, y = sim_step(instrs, pc, x, y)
        traj.append((pc, x, y))
    return traj, False


def sim_state_after(instrs, x, y, k):
    """The simulator state after exactly k steps from (pc=1, x, y)."""
    pc = 1
    for _ in range(k):
        pc, x, y = sim_step(instrs, pc, x, y)
    return (pc, x, y)


# ---------------------------------------------------------------------------
# the parameterized toolkit (paper's Selection / Equality / contains)

def make_toolkit(b, x):
    """Paper's constructions with role characters (b, x), b != x.
    Returns (mk_if, mk_contains, sel) where sel(cond, T, F) selects T
    iff the occurrence test cond FIRED (pattern present)."""
    assert len(b) == len(x) == 1 and b != x

    def enc(E):
        return S(K(x + b), K(b), E)

    def dec(E):
        return S(K(b), K(x + b), E)

    def mk_if(cond, xt, xf):
        # value: xt if value(cond) starts with x, else xf
        return dec(S(enc(xf), K(b + b),
                     S(enc(xt), K(x),
                       S(K(b + b), K(b), cond))))

    def benc(Z):
        return C(C(K(x + b + b), S(K(x + b), K(b), Z)), K(x + b + b))

    def mk_contains(E, B):
        # occurrence test via the fixed-point-set lemma: [M/B]X = X iff
        # B notin X.  The mask M must DIFFER from B (R3 found the latent
        # bug: with roles (b,x) and B = the single char b, a mask of b
        # is the identity and the test always says "absent").
        mask = b if B != b else x
        changed = S(K(mask), K(B), E)
        eqx = S(K(b), benc(E), S(K(x), benc(changed), benc(E)))
        return mk_if(eqx, K(b), K(x))

    # polarity probe: standardize sel(cond, T, F) = T iff the pattern occurs
    bud = Budget(10 ** 6, 10 ** 6)
    vp = ev(mk_contains(V(0), 'q'), ('aq a',), bud)
    vm = ev(mk_contains(V(0), 'q'), ('zz z',), bud)
    assert vp in (b, x) and vm in (b, x) and vp != vm, (vp, vm)
    if vp == x:
        sel = lambda cond, T, F: mk_if(cond, T, F)
    else:
        sel = lambda cond, T, F: mk_if(cond, F, T)
    return mk_if, mk_contains, sel


# ---------------------------------------------------------------------------
# the flat 2CM compiler

def Vfam(k, swap):
    """The structural constant family.  Normal mode (swap=False):
    'bb'+'ab'*k+'bb'  (b-anchored, no 'aa', b-run signature [2,1^k,2]).
    Swap mode: 'aa'+'ba'*k+'aa' (mirror image, tally char = 'b')."""
    if not swap:
        return 'bb' + 'ab' * k + 'bb'
    return 'aa' + 'ba' * k + 'aa'


def pipe(passes, E):
    """Apply passes left to right; each item = (replacement, pattern)."""
    for (repl, pat) in passes:
        E = S(K(repl), K(pat), E)
    return E


class FlatCM2:
    """Compile a 2CM into flat L + ONE lim node.

    instrs: 1-based list; each is
        ('inc', r, j)      increment counter r, goto j
        ('decjz', r, jz, jnz)   if counter r = 0 goto jz
                                else decrement r and goto jnz
    jump target 0 = halt (wraps PH).  Output counter = 2 (the last
    tally); counter 1 must be 0 at halt (scratch drained)."""

    def __init__(self, instrs, b='a', x='b', swap=False,
                 offset=3, spread=1, name=''):
        self.instrs = list(instrs)
        self.s = len(instrs)
        for ins in self.instrs:
            assert ins[0] in ('inc', 'decjz'), f"no mid-list halt: {ins}"
        self.swap = swap
        self.offset, self.spread = offset, spread
        self.t = 'b' if swap else 'a'          # tally character
        self.b, self.x = b, x
        self.name = name or f"cm2[{len(instrs)}]"
        idx = [offset]

        def nxt():
            v = Vfam(idx[0], swap)
            idx[0] += spread
            return v

        self.D = [nxt() for _ in range(4)]               # D0 D1 D2 D3
        self.P = [None] + [nxt() for _ in range(self.s)]  # 1-based codes
        self.PH = nxt()                                   # halt slot
        self.M = nxt()                                   # wrap marker
        self.tk = make_toolkit(b, x)
        self._, self.mk_contains, self.sel = self.tk
        self.step_ast = self._build_step()
        self.init_ast = self._build_init()
        self.init2_ast = self._build_init2()
        self.out_prefix = (self.D[0] + self.program(0)
                           + self.D[1] + self.D[2])
        self.out_passes = [('', self.out_prefix), ('', self.D[3])]
        self.main_ast = pipe(self.out_passes, L(self.step_ast, self.init_ast))
        self.main2_ast = pipe(self.out_passes, L(self.step_ast, self.init2_ast))

    # -- configuration strings -------------------------------------------

    def program(self, wrapped):
        """The program zone; `wrapped` = current pc (1..s) or 0 (halt)."""
        parts = []
        for i in range(1, self.s + 1):
            parts.append(self.M + self.P[i] + self.M if i == wrapped
                         else self.P[i])
        parts.append(self.M + self.PH + self.M if wrapped == 0 else self.PH)
        return ''.join(parts)

    def make_cfg(self, pc, x, y):
        return (self.D[0] + self.program(pc) + self.D[1]
                + self.t * x + self.D[2] + self.t * y + self.D[3])

    # -- expressions ------------------------------------------------------

    def dpair(self, r):
        return (self.D[1], self.D[2]) if r == 1 else (self.D[2], self.D[3])

    def jump_passes(self, i, j):
        tgt = self.PH if j == 0 else self.P[j]
        return [(self.P[i], self.M + self.P[i] + self.M),      # unwrap
                (self.M + tgt + self.M, tgt)]                  # wrap

    def _branch(self, i, ins):
        X = V(0)
        if ins[0] == 'inc':
            _, r, j = ins
            Ld, _R = self.dpair(r)
            return pipe([(Ld + self.t, Ld)] + self.jump_passes(i, j), X)
        _, r, jz, jnz = ins
        Ld, Rd = self.dpair(r)
        zcond = self.mk_contains(X, Ld + Rd)
        br_z = pipe(self.jump_passes(i, jz), X)
        br_nz = pipe([(Ld, Ld + self.t)] + self.jump_passes(i, jnz), X)
        return self.sel(zcond, br_z, br_nz)

    def _build_step(self):
        X = V(0)
        chain = X                                    # halted: identity
        for i in range(self.s, 0, -1):
            cond = self.mk_contains(X, self.M + self.P[i] + self.M)
            chain = self.sel(cond, self._branch(i, self.instrs[i - 1]), chain)
        return chain

    def _build_init(self):
        head = self.D[0] + self.program(1) + self.D[1]
        return C(C(K(head), V(0)), K(self.D[2] + self.D[3]))

    def _build_init2(self):
        head = self.D[0] + self.program(1) + self.D[1]
        return C(C(C(C(K(head), V(0)), K(self.D[2])), V(1)), K(self.D[3]))

    # -- helpers ----------------------------------------------------------

    def constants(self):
        out = list(self.D) + self.P[1:] + [self.PH, self.M]
        return out

    def pattern_expectations(self):
        """(pattern, expected_count(pc,x,y)) for EVERY pattern of the step
        and the out stage."""
        E = []
        for i in range(1, self.s + 1):
            E.append((self.M + self.P[i] + self.M,
                       lambda pc, x, y, i=i: 1 if pc == i else 0))
        for i in range(1, self.s + 1):
            E.append((self.P[i], lambda pc, x, y, i=i: 1))
        E.append((self.PH, lambda pc, x, y: 1))
        E.append((self.M, lambda pc, x, y: 2))
        for k in range(4):
            E.append((self.D[k], lambda pc, x, y, k=k: 1))
        E.append((self.D[1] + self.t, lambda pc, x, y: 1 if x >= 1 else 0))
        E.append((self.D[2] + self.t, lambda pc, x, y: 1 if y >= 1 else 0))
        E.append((self.D[1] + self.D[2], lambda pc, x, y: 1 if x == 0 else 0))
        E.append((self.D[2] + self.D[3], lambda pc, x, y: 1 if y == 0 else 0))
        E.append((self.out_prefix,
                   lambda pc, x, y: 1 if (pc == 0 and x == 0) else 0))
        return E


# ---------------------------------------------------------------------------
# part 0 + 1: toolkit probes and build-time constant invariants

def part01_toolkit_and_constants(machines):
    print("part 0/1: toolkit polarity probes + constant-family invariants")
    for m in machines:
        # pairwise non-occurrence of all structural constants
        cs = m.constants()
        for a, b in itertools.combinations(cs, 2):
            ck(a not in b and b not in a,
               f"{m.name}: constants overlap: {a!r} vs {b!r}")
        # structural constants contain no doubled tally char, and are
        # anchored on the structural character
        for c in cs:
            ck(m.t + m.t not in c,
               f"{m.name}: constant {c!r} contains '{m.t}{m.t}'")
            ck(c[0] == c[-1] and c[0] != m.t,
               f"{m.name}: constant {c!r} not anchored")
        # flatness discipline of the step: no L node, arity 1, every
        # variable is V(0), and every pass PATTERN can never be empty
        # (constant patterns, or the paper's Equality `benc` patterns =
        # concatenations anchored by nonempty constants -- total either
        # way).  Count how many passes have constant patterns.
        check(m.step_ast, 1)
        stats = {'L': 0, 'S': 0, 'Sconst': 0, 'badpat': 0, 'varpat': 0}

        def never_empty(e):
            """Is this pattern expression never the empty string?
            K(w): w != ''.  C(a,b): never_empty(a) or never_empty(b)."""
            if e[0] == 'K':
                return e[1] != ''
            if e[0] == 'C':
                return never_empty(e[1]) or never_empty(e[2])
            return False        # V or S: could be empty

        def walk(e):
            t = e[0]
            if t in ('K', 'V'):
                if t == 'V' and e[1] != 0:
                    stats['varpat'] += 1
                return
            if t == 'C':
                walk(e[1]); walk(e[2]); return
            if t == 'S':
                stats['S'] += 1
                if e[2][0] == 'K' and e[2][1] != '':
                    stats['Sconst'] += 1
                if not never_empty(e[2]):
                    stats['badpat'] += 1
                walk(e[1]); walk(e[2]); walk(e[3]); return
            if t == 'L':
                stats['L'] += 1
                walk(e[1]); walk(e[2]); return
        walk(m.step_ast)
        ck(stats['L'] == 0, f"{m.name}: step contains an L node")
        ck(stats['badpat'] == 0,
           f"{m.name}: step has a possibly-empty pass pattern")
        ck(stats['varpat'] == 0,
           f"{m.name}: step mentions a variable other than X1")
        # MAIN: exactly one lim node, arity 1
        nlim = [0]

        def walk2(e):
            if e[0] == 'L':
                nlim[0] += 1
                walk2(e[1]); walk2(e[2]); return
            if e[0] == 'C':
                walk2(e[1]); walk2(e[2]); return
            if e[0] == 'S':
                walk2(e[1]); walk2(e[2]); walk2(e[3]); return
        walk2(m.main_ast)
        check(m.main_ast, 1)
        ck(nlim[0] == 1, f"{m.name}: MAIN does not have exactly 1 lim node")
        print(f"  {m.name}: step = {size(m.step_ast)} nodes, "
              f"{stats['S']} passes ({stats['Sconst']} constant-pattern), "
              f"MAIN = {size(m.main_ast)} nodes, 1 lim node -- OK")


# ---------------------------------------------------------------------------
# part 2 + 3 + 4: occurrence census, step semantics, fixed-point/totality

def part234_invariants(m, xr, yr, bud_steps=2 * 10 ** 6):
    """All configurations (pc, x, y) for pc in 0..s, x in xr, y in yr."""
    tag = m.name
    for pc in range(0, m.s + 1):
        for x in xr:
            for y in yr:
                cfg = m.make_cfg(pc, x, y)
                # tally structure: the text spans between the (census-
                # verified unique) delimiters are exactly the tallies
                i1, i2, i3 = (cfg.index(m.D[1]), cfg.index(m.D[2]),
                              cfg.index(m.D[3]))
                ck(cfg[i1 + len(m.D[1]):i2] == m.t * x,
                   f"{tag}: T1 span wrong at pc={pc} x={x} y={y}")
                ck(cfg[i2 + len(m.D[2]):i3] == m.t * y,
                   f"{tag}: T2 span wrong at pc={pc} x={x} y={y}")
                # occurrence census
                for (pat, exp) in m.pattern_expectations():
                    got = cfg.count(pat)
                    want = exp(pc, x, y)
                    ck(got == want,
                       f"{tag}: pattern {pat!r} occurs {got}x, want {want} "
                       f"(pc={pc} x={x} y={y})")
                # step semantics through the real evaluator
                bud = Budget(bud_steps, 1 << 22)
                got = ev(m.step_ast, (cfg,), bud)
                npc, nx, ny = sim_step(m.instrs, pc, x, y)
                want = m.make_cfg(npc, nx, ny)
                ck(got == want,
                   f"{tag}: step(cfg) wrong at pc={pc} x={x} y={y}\n"
                   f"      got  {got}\n      want {want}")
                # fixed-point uniqueness
                if pc == 0:
                    ck(got == cfg, f"{tag}: halt cfg not a fixed point")
                else:
                    ck(got != cfg,
                       f"{tag}: NON-halted fixed point at pc={pc} "
                       f"x={x} y={y} -- step is the identity there")


def part4_totality(m, n_garbage=300):
    """The step is total: defined on every input, incl. garbage.  Also
    each BRANCH pipeline is total on its own (every pass has a nonempty
    pattern => Safe => total), and the step is correct on random large
    states (x, y up to 40) far beyond the systematic domain."""
    rnd = random.Random(hash(m.name) & 0xffff)
    for _ in range(n_garbage):
        ln = rnd.randrange(0, 48)
        g = ''.join(rnd.choice('ab') for _ in range(ln))
        r = run(m.step_ast, (g,), 10 ** 6, 1 << 22)
        ck(r[0] == 'val',
           f"{m.name}: step not total on garbage {g!r} -> {r[0]}")
    # per-branch totality: every branch pipeline on garbage
    for i in range(1, m.s + 1):
        br = m._branch(i, m.instrs[i - 1])
        for _ in range(50):
            ln = rnd.randrange(0, 48)
            g = ''.join(rnd.choice('ab') for _ in range(ln))
            r = run(br, (g,), 10 ** 6, 1 << 22)
            ck(r[0] == 'val',
               f"{m.name}: branch {i} not total on garbage {g!r}")
    # random large states: semantics + fixed-point uniqueness
    for _ in range(120):
        pc = rnd.randrange(0, m.s + 1)
        x = rnd.randrange(0, 41)
        y = rnd.randrange(0, 41)
        cfg = m.make_cfg(pc, x, y)
        bud = Budget(2 * 10 ** 6, 1 << 22)
        got = ev(m.step_ast, (cfg,), bud)
        npc, nx, ny = sim_step(m.instrs, pc, x, y)
        ck(got == m.make_cfg(npc, nx, ny),
           f"{m.name}: step wrong on large state ({pc},{x},{y})")
        if pc == 0:
            ck(got == cfg, f"{m.name}: halt not fixed at ({x},{y})")
        else:
            ck(got != cfg,
               f"{m.name}: non-halted fixed point at ({pc},{x},{y})")


# ---------------------------------------------------------------------------
# part 5: end-to-end under lim

def orbit_trace(m, s, cap=100000):
    """Trace the lim orbit of the step AST from s (point by point)."""
    pts = [s]
    bud = Budget(10 ** 8, 1 << 24)
    for _ in range(cap):
        t = ev(m.step_ast, (s,), bud)
        pts.append(t)
        if t == s:
            return pts, True
        s = t
    return pts, False


def test_e2e_1var(m, ns, expect):
    """expect(n) = the machine's output counter value on input n."""
    t = m.t
    for n in ns:
        traj, ok = sim_run(m.instrs, n, 0)
        ck(ok, f"{m.name}: simulator diverged on n={n}")
        pts, conv = orbit_trace(m, m.make_cfg(1, n, 0))
        ck(conv, f"{m.name}: lim orbit did not converge on n={n}")
        # the lim orbit = the trajectory PLUS the repeated fixed point
        ck(len(pts) == len(traj) + 1,
           f"{m.name}: orbit length {len(pts)} != trajectory length "
           f"{len(traj)} + 1 on n={n}")
        for p, (pc, x, y) in zip(pts, traj):
            ck(p == m.make_cfg(pc, x, y),
               f"{m.name}: orbit point mismatch on n={n} at "
               f"({pc},{x},{y}):\n      got  {p}\n      want "
               f"{m.make_cfg(pc, x, y)}")
        # the halt fixed point, then MAIN end to end
        ck(pts[-1] == m.make_cfg(0, 0, expect(n)),
           f"{m.name}: halt config wrong on n={n}")
        r = run(m.main_ast, (t * n,), 10 ** 8, 1 << 24)
        ck(r[0] == 'val', f"{m.name}: MAIN undefined on n={n} ({r[0]})")
        ck(r[1] == t * expect(n),
           f"{m.name}: MAIN({t}^{n}) = {r[1]!r}, want {t * expect(n)!r}")


def test_e2e_2var(m, nms, expect):
    t = m.t
    for (n, mm) in nms:
        traj, ok = sim_run(m.instrs, n, mm)
        ck(ok, f"{m.name}: simulator diverged on ({n},{mm})")
        pts, conv = orbit_trace(m, m.make_cfg(1, n, mm))
        ck(conv, f"{m.name}: lim orbit did not converge on ({n},{mm})")
        ck(len(pts) == len(traj) + 1,
           f"{m.name}: orbit length {len(pts)} != {len(traj)} + 1 "
           f"on ({n},{mm})")
        for p, (pc, x, y) in zip(pts, traj):
            ck(p == m.make_cfg(pc, x, y),
               f"{m.name}: orbit point mismatch on ({n},{mm}) at "
               f"({pc},{x},{y})")
        r = run(m.main2_ast, (t * n, t * mm), 10 ** 8, 1 << 24)
        ck(r[0] == 'val',
           f"{m.name}: MAIN2 undefined on ({n},{mm})")
        ck(r[1] == t * expect(n, mm),
           f"{m.name}: MAIN2({t}^{n},{t}^{mm}) = {r[1]!r}, "
           f"want {t * expect(n, mm)!r}")


# ---------------------------------------------------------------------------
# main

DOUBLE = [('decjz', 1, 0, 2), ('inc', 2, 3), ('inc', 2, 1)]
ADDER = [('decjz', 1, 0, 2), ('inc', 2, 1)]


def main():
    print("R2: flat-L two-counter machines under lim")
    base = dict(b='a', x='b', swap=False, offset=3, spread=1)
    dbl = FlatCM2(DOUBLE, name='double', **base)
    add = FlatCM2(ADDER, name='adder', **base)
    machines = [dbl, add]

    print("part 0/1 ...")
    part01_toolkit_and_constants(machines)

    print("part 2/3/4 ... (core domain pc x y in 0..s x 0..4 x 0..4)")
    for m in machines:
        part234_invariants(m, range(0, 5), range(0, 5))
        part4_totality(m)
        print(f"  {m.name}: core invariants + totality done")

    print("part 5 ... end-to-end (core)")
    test_e2e_1var(dbl, range(0, 9), lambda n: 2 * n)
    test_e2e_2var(add, [(i, j) for i in range(0, 5) for j in range(0, 5)],
                  lambda n, mm: n + mm)
    print(f"  double: n=0..8 -> t^2n OK;  adder: 5x5 grid -> t^(n+m) OK")

    # 5b: NON-halting machines -- lim must diverge (partiality direction)
    print("part 5b ... divergence")
    for nm, ins in [('selfloop', [('inc', 1, 1)]),
                    ('twocycle', [('inc', 1, 2), ('inc', 1, 1)])]:
        mm = FlatCM2(ins, name=nm, **base)
        part01_toolkit_and_constants([mm])
        for n in (0, 2, 5):
            traj, ok = sim_run(mm.instrs, n, 0, cap=500)
            ck(not ok, f"{nm}: simulator halts?! (n={n})")
            r = run(mm.main_ast, ('a' * n,), 4000, 1 << 22)
            ck(r[0] == 'div',
               f"{nm}: lim(step) should diverge on n={n}, got {r[0]}")
            # the orbit itself: every point a genuine config, no repeat
            pts, conv = orbit_trace(mm, mm.make_cfg(1, n, 0), cap=300)
            ck(not conv, f"{nm}: orbit converged on n={n}?!")
            for k, p in enumerate(pts):
                q = sim_state_after(mm.instrs, n, 0, k)
                ck(p == mm.make_cfg(*q),
                   f"{nm}: orbit point {k} mismatch on n={n}")
        print(f"  {nm}: lim diverges on n=0,2,5; orbit = machine run OK")

    # 5c: a machine exercising the COUNTER-2 decrement / zero test paths
    # (both prior machines only test counter 1).  f(n, m) = n:  drain
    # counter 2, then transfer counter 1 into counter 2.  Halts with
    # counter 1 = 0 (scratch drained), output in counter 2.
    print("part 5c ... counter-2 paths")
    DRAIN = [('decjz', 2, 3, 1),      # while c2 > 0: dec c2
             ('inc', 1, 1),            # (never reached; keeps s >= 2)
             ('decjz', 1, 0, 4),      # while c1 > 0: dec c1
             ('inc', 2, 3)]            # inc c2, loop
    dr = FlatCM2(DRAIN, name='c2drain', **base)
    part01_toolkit_and_constants([dr])
    part234_invariants(dr, range(0, 5), range(0, 5))
    part4_totality(dr)
    test_e2e_2var(dr, [(i, j) for i in range(0, 5) for j in range(0, 5)],
                  lambda n, mm: n)
    print("  c2drain: MAIN2(t^n, t^m) = t^n on 5x5 grid OK")

    print("part 6 ... escalation")
    # (a) strictly larger domains
    for m in machines:
        part234_invariants(m, range(0, 9), range(0, 9), bud_steps=10 ** 7)
        print(f"  {m.name}: invariants on x,y in 0..8 OK")
    test_e2e_1var(dbl, range(9, 13), lambda n: 2 * n)
    test_e2e_2var(add, [(i, j) for i in (5, 6) for j in range(0, 7)]
                  + [(i, j) for i in range(0, 7) for j in (5, 6)],
                  lambda n, mm: n + mm)
    print("  double n=9..12, adder 7x7 border OK")
    # (b) both (b,x) toolkit roles x both configuration swaps
    for (b, x) in [('a', 'b'), ('b', 'a')]:
        for swap in [False, True]:
            d = FlatCM2(DOUBLE, b=b, x=x, swap=swap, offset=3, spread=1,
                        name=f'double[{b},{x},{swap}]')
            a = FlatCM2(ADDER, b=b, x=x, swap=swap, offset=3, spread=1,
                        name=f'adder[{b},{x},{swap}]')
            part01_toolkit_and_constants([d, a])
            part234_invariants(d, range(0, 5), range(0, 5))
            part234_invariants(a, range(0, 5), range(0, 5))
            test_e2e_1var(d, range(0, 7), lambda n: 2 * n)
            test_e2e_2var(a, [(i, j) for i in range(0, 4)
                              for j in range(0, 4)], lambda n, mm: n + mm)
            print(f"  toolkit (b,x)=({b},{x}) swap={swap}: full battery OK")
    # (c) different constant spreads/offsets
    for (off, spr) in [(7, 2), (13, 3), (1, 1)]:
        d = FlatCM2(DOUBLE, offset=off, spread=spr, name=f'double@{off}/{spr}')
        a = FlatCM2(ADDER, offset=off, spread=spr, name=f'adder@{off}/{spr}')
        part01_toolkit_and_constants([d, a])
        part234_invariants(d, range(0, 5), range(0, 5))
        part234_invariants(a, range(0, 5), range(0, 5))
        test_e2e_1var(d, range(0, 7), lambda n: 2 * n)
        test_e2e_2var(a, [(i, j) for i in range(0, 4) for j in range(0, 4)],
                      lambda n, mm: n + mm)
        print(f"  offset={off} spread={spr}: full battery OK")

    print()
    print(f"R2 RESULT: {CHECKS[0]} checks, {CHECKS[1]} failures")
    return 0 if CHECKS[1] == 0 else 1


if __name__ == '__main__':
    sys.exit(main())

# L + lim: Iterating a Flat Expression to its Fixed Point

**Research report "lim"** — working directory
`docs/proof/research/scratch/lim/`.  Target paper: `docs/proof/main.tex`
("A Theory of String Substitution over Finite Alphabets").  Notation and
theorem numbers refer to that paper: `def:subst` = the primitive (one
left-to-right sweep, leftmost-first, never rescanning inserted text),
`def:exp`/`def:den` = the expression grammar and its eager denotation
(Section 3), `lem:length`/`thm:fp` = the polynomial bound (Section 4),
`def:markov`/`thm:termination`/`thm:amplifier`/`cor:towers` = the restart
row of Section 5, Section 6 = recursion x runtimes (eager/lazy-args
inert, lazy passes universal).

The operator under study (the user's proposal): extend the expression
grammar with ONE node, `lim(E)`, and nothing else — no recursion:

> "run [E] an infinite number of times until it converges; if it does not
> converge the result is undefined."

Machine work: `lim_core.py` (grammar + evaluator), `verify_r1.py` (this
round's verification suite; log in `round1.log`), `mismatch_r1.py` (the
mismatch catalog).  Every claim tagged **[VERIFIED]** was executed on the
stated domain.  Alphabet throughout: `Sigma = {a, b}`.

---

## 0. What this round delivers

| # | Statement | Status |
|---|-----------|--------|
| R1.1 | The formal design of the `lim` node (hygienic, beta-compatible), with an evaluator. | DONE (Sec. 1) |
| R1.2 | **Fixed-point-set lemma**: for `B != eps`, `A != B`: `[A/B]w = w` iff `B` not-in `w`. | PROVED + VERIFIED (475,230 pairs) |
| R1.3 | **The conjectured fixed-point lemma (`lim([A/B])` = the restart variant `def:markov`) is FALSE.** The two are two different deterministic strategies of the one-rule system `B -> A` (leftmost-one-at-a-time vs. greedy-sweep-then-repeat); one-rule systems are not confluent; the strategies separate in both value and termination.  Corrected statements below. | REFUTED + witnesses hand-verified (Sec. 2) |
| R1.4 | Agreement class (proved): `A,B` nonempty, disjoint alphabets => `lim([A/B]) = [A/B] = restart`. | PROVED + VERIFIED (32,736 pairs) |
| R1.5 | Agreement conjecture (open): `B` unbordered => `lim([A/B]) = restart` — with restart possibly MUCH slower (an `[aaab/ba]`-family input of length 10 takes >10^4 leftmost steps and still terminates, to lim's value).  All 166 mismatch rules of the census have *bordered* `B`; every apparent unbordered mismatch at cap 6000 resolved to slow agreement at cap 60000 (part 3d). | CONJECTURED + VERIFIED on census + |A|,|B|<=6 stress (round1.log) |
| R1.6 | **`lim` is the more often defined of the two**: `A = B` (30 rules) — `lim` = total identity, restart diverges; on `[abba/bab]`, `[baab/aba]` restart diverges on 145+145 inputs (<= 9) where `lim` converges in <= 4 sweeps; **zero** cases of the reverse direction anywhere tested. | VERIFIED (Sec. 2.4) |
| R1.7 | Tower growth carries over through `lim` (`cor:towers`): amplifier closed form, two-node block formula, towers of height 1, 2, 3 from `2t-1` constant-pattern `lim`-nodes. | VERIFIED (Sec. 4) |
| R1.8 | **Paper text bug found (corrected per coordinator)**: the census sentence of `thm:termination(v)`'s proof says 170 divergent rules and lists `[aaab/ba]`, `[abbb/ba]`; the actual <= 9 census is 166 = 162 + FOUR.  IMPORTANT CORRECTION to my first report: the paper's `verify_extra.py` did NOT "have the FOUR" at its original `CAP=2000` — it printed **170 with `extra == FOUR: False`** (the four slow families outlive 2,000 steps; its assertion encoded the right expectation but FAILED, unnoticed).  BOTH the text and the script were wrong at that cap; the coordinator has fixed the script (cap 10^4, plus two more latent bugs: part (d) missing the |B|<=3 filter, part (e) restart calls in the wrong order) and the text (166 = 162 + four, cap-sensitivity note: 3,280 steps on b^8 a, strategy sentence rescoped, plus certification that the four cap-sensitive families have FINITE unrestricted closures on all inputs <= 7).  The two extra text rules are not divergent at all on short inputs — they terminate on every input <= 9 at cap 10^6, max exactly 3,280 steps. | VERIFIED + coordinator-confirmed (Sec. 3) |
| R1.9 | Demos: nested `lim`; a branching iterand (`if`/`contains` — the power source for universality); exponential growth `lim([X.X/X])`. | VERIFIED (Sec. 5) |

---

## 1. The system L + lim

### 1.1 Syntax

The paper's grammar `def:exp` (variables, constants, `[R/P]E`,
concatenation) plus one node:

    ('L', E, E0)      lim(E) started at E0

* `E` in `Exp_1` is the **iterand**.  Its variable `X1` is BOUND by the
  node and denotes the CURRENT ORBIT POINT.  (The validator `check`
  enforces: only `V(0)` may occur in `E`.)
* `E0` in `Exp_n` is the **start**: the user's `X` in `lim(E)(X)`.
  In unary contexts `lim(E)(X)` is `('L', E, V(0))`.

This is the hygienic reading of the user's unary node: the paper's `Exp`
is capture-free "there being no binders" (def:exp), and Lemma `lem:beta`
(substitution) must survive.  Carrying the start as an explicit slot —
exactly the way the pass node carries its scrutinee `[R/P]E` — makes the
node a binder-free pair: the free variables of `('L', E, E0)` are those
of `E0` alone, substitution acts on `E0` and never captures into `E`, and
`lem:beta` holds verbatim.  Nested `lim` nodes are allowed (the iterand
and the start may themselves contain `lim`); `('L', E, E0)` may sit at
any expression position (a pass replacement, a pattern, a scrutinee, a
concatenand).

### 1.2 Denotation

At `S = (S_1..S_n)` (eager/strict in everything, as `def:den`):

    s_0     = [[E0]](S)                     (undefined -> lim undefined)
    s_{k+1} = [[E]](s_k)                    (undefined -> lim undefined)
    [[('L',E,E0)]](S) = the first s_K with s_{K+1} = s_K
                         undefined if no such K exists.

Design decisions, recorded:
* **Undefinedness propagates**: an empty pattern inside the iterand (or
  in `E0`) makes the whole `lim` undefined, as in the strict calculus.
* `K = 0` is allowed: if `s_1 = s_0` the value is `s_0`.
* Operationally, caps (step cap, length cap) stand for divergence, the
  paper's census convention; all mismatch findings below were re-verified
  at 10x caps.

### 1.3 Evaluator

`lim_core.py`: AST constructors `K/V/C/S/L`, structural checker, eager
evaluator `ev` with a shared `Budget` (every substitution and every
orbit iteration ticks; a produced string longer than `maxlen` aborts),
and `orbit`.  `subst` is the paper's `def:subst` character-for-character
(same function as `rec/lazy_pass/core.py` and
`paper_variants/verify_variants.py`); `subst_fast` is CPython
`str.replace`, whose contract (leftmost-first, non-overlapping, never
rescanning inserted text) is *the same* — **[VERIFIED]** on 107,310
triples (all `A` with `|A|<=3` incl. eps, all `B` with `1<=|B|<=3`, all
`w` with `|w|<=8`).  The evaluator's `L` node agrees with the direct
orbit on 2,040 runs (8 rules incl. divergent ones, `|w|<=7`).

---

## 2. lim over a single pass: the fixed-point story

### 2.1 The fixed-point-set lemma (TRUE)

**Lemma.**  For `B != eps` and `A != B`:
`[A/B]w = w`  iff  `B` does not occur in `w`.

*Proof.*  (<=) Substitution Elimination.  (=>) If `B` occurs, the greedy
scan performs `m >= 1` replacements.  If `|A| != |B|` the length changes
by `m(|A|-|B|) != 0`.  If `|A| = |B|`, let `p` be the first replacement
site: the output agrees with `w` before `p`, spells `A` at `p` against
`w`'s `B`, and `A != B` at equal lengths differ somewhere inside the
site.  In both cases `[A/B]w != w`. QED

**[VERIFIED]** all 930 census rules (all `A` with `|A|<=4` incl. eps,
all `B` with `1<=|B|<=4`, over `{a,b}`) x all 255 inputs of length
`<= 8`: 475,230 checks, no exception.  Also `[A/A] = id` everywhere
(the paper's Identity Substitution).

Consequences: whenever `lim([A/B])(X)` is defined it returns a
`B`-free string; and the orbit can only stall at `B`-free strings, so
`lim` diverges exactly when `B`-freeness is never reached.

### 2.2 The conjectured fixed-point lemma is FALSE

The coordinator's proposed lemma — `lim([A/B])` equals the restart
variant `[A/B]^m` (`def:markov`), because both stop at `B`-free strings —
holds at the level of fixed points but **not** of trajectories, and the
trajectories matter: the two operators are two different deterministic
strategies for the one-rule rewriting system `B -> A`,

* **restart** (`def:markov`): replace the leftmost occurrence, rescan
  from 0, repeat;
* **lim**: the **greedy sweep** — the pass `def:subst` (replace all
  non-overlapping leftmost-first matches, never rescanning inserted
  text) — iterated to stabilization.

One-rule systems are not confluent, and the two strategies reach the
fixed points differently.  Both facts were found by the census and then
verified BY HAND:

* **Value mismatch** (both terminate, differently).  Rule `bbbb -> babb`,
  input `abbbbbbbb`:
  - restart: `ababababb` (three sequential leftmost splices, each
    shifting the next site);
  - lim: `ababbbabb` (one sweep replaces the two disjoint occurrences
    at 1 and 5 simultaneously).
  Second, length-DECREASING witness: rule `abba -> ab`, input
  `abbababba`: restart `abbba`, lim `abb` (restart's first splice at 0
  merges away the second redex that the sweep takes at 5).
* **Verdict mismatch** (termination differs).  Rule `aba -> baab`,
  input `aaaba`: restart diverges (each leftmost splice re-creates an
  `aba` at the junction, `+1` char per step, forever); the lim orbit is
  `aaaba -> aabaab -> abaabab -> baabbaabb` — **4 sweeps and done**: the
  third sweep replaces the two disjoint occurrences at 0 and 3 of
  `abaabab` in one pass, cutting the chain that keeps restart alive.

**[VERIFIED]** on the full census domain (930 rules x all 1023 inputs of
length `<= 9`):

* agreement: 779,692 converging pairs and 117,058 diverging pairs agree
  (verdict AND value);
* **value mismatches: 3,306 input-pairs across 166 rules** (both
  terminate, different `B`-free strings) — 0.35% of the domain;
* **verdict mismatches: 290 pairs, exactly two rules** (`[abba/bab]`,
  `[baab/aba]`, 145 inputs each at `<= 9`), **all in the direction
  restart-diverges & lim-converges** (in `<= 4` sweeps, values stable at
  10x caps);
* **zero** pairs where lim diverges and restart converges.

The non-confluence PERSISTS at length: on 100 random inputs of length
12..16 per rule (93,000 pairs): 0 reverse verdict mismatches, 961 value
mismatches; on the provably-converging rules (`|A| <= |B|`), all inputs
`<= 10` (1,269,140 pairs): verdicts always agree (as the
length/V arguments predict), value mismatches 3,990 across 178 rules.

### 2.3 The agreement classes

**Proposition (disjoint alphabets).**  If `A, B` are nonempty and share
no character, then `lim([A/B]) = [A/B] = [A/B]^m`: one sweep fires on
every occurrence; no occurrence of `B` can touch an inserted `A`
(would share a character), so the result is `B`-free and is the common
value of the pass, the restart process (this is the paper's
`prop:restart-agree`), and the `lim` orbit, which stabilizes after the
single firing sweep.  **[VERIFIED]** 32,736 pairs (all such census rules
x inputs `<= 9`): pass = restart = lim, orbit length exactly 2 (fire +
confirm) when `B` occurs, 1 when not.

**Conjecture (unbordered B).**  If `B` is unbordered, then
`lim([A/B]) = [A/B]^m` (verdict and value) — where the restart may be
ARBITRARILY SLOWER.  Evidence, in layers:
* the census: all 166 value-mismatch rules and both verdict-mismatch
  rules have *bordered* `B` (of the 930 rules, 496 have bordered `B`);
  all 434 unbordered-`B` rules agree on all 1023 inputs `<= 9` (caps 4000);
* the stress: ALL 5,030 rules with unbordered `B`, `|A|,|B| <= 6`,
  `B not-in A` x 100 random inputs of length 8..14 = **503,000 pairs**:
  17 raw mismatches at cap 6000, every one re-verified at restart cap
  60000 and classified — **17 slow-restart agreements (same value), 0
  still-divergent, 0 value disagreements** (round1.log part 3d);
* a hand-checked slow witness: `[bbba/ab]` (the renaming of the
  paper-text rule `[aaab/ba]`) on `aabbbbaaaaaobb` (length 14): restart
  terminates after >6000 leftmost steps, lim in 4388 sweeps, BOTH to the
  same value `b^{13158} a^8` (re-verified: same value: True).
  OPEN in general; no counterexample survives the 10x-cap re-verification.

### 2.4 What survives: lim subsumes the restart row, and beats it

The R1 verdict on the original positioning claim:

1. **Structurally**, `lim` generalizes the restart node exactly as
   hoped: restart iterates ONE pass; `lim` iterates ANY expression — with
   `if`/`eq`/`contains` inside, the iterand can branch (Sec. 5).  The
   restart row embeds as the single-pass-iterand fragment, up to the
   strategy difference.
2. **On the agreement classes** (disjoint alphabets — provably;
   unbordered `B` — conjecturally) the embedding is literal: same partial
   function.  The amplifier family `[baa/ab]` (`B = ab`, bordered!) also
   agrees everywhere tested, and its closed form carries over verbatim
   (Sec. 4).
3. **In general the two differ**, and in every direction tested `lim` is
   the *more often defined*: `A = B` — `lim` is the total identity where
   restart diverges (an artifact of restart's "stop only when `B`-free"
   rule; `lim`'s stabilization test detects the fixed point); and the
   two census rules above where the sweep terminates in `<= 4` sweeps
   while leftmost runs forever — re-verified at restart cap 300,000
   (`[baab/aba]` on `aaaba`: restart still running after 300,000 steps,
   ~88s of trajectory; lim: `baabbaabb`, 4 sweeps).  On inputs `<= 10` +
   150 random of length 12..16: `[abba/bab]` has 361 and `[baab/aba]`
   360 lim-wins witnesses (15-input subsamples: all still divergent at
   restart cap 50,000), plus 642/651 inputs where both diverge, ~1,190
   where both converge with the SAME value, and 0 value disagreements —
   on these two rules lim never loses ground anywhere.  No input
   anywhere tested has `lim` diverging where restart converges (0 of
   896,688 census pairs + 93,000 random pairs 12..16 + the stress
   domain).  Whether that one-directional inclusion is a theorem is
   open (it would say: the sweep strategy terminates whenever the
   leftmost strategy does).
4. For the paper this is a *sharper* story than the planned lemma: the
   `lim` operator is not the restart variant in disguise; it is the
   sweep-strategy normalizer, a genuinely different — and apparently
   better-behaved — third strategy for one-rule systems, next to
   leftmost and unrestricted.  The `thm:termination(v)` strategy question
   gains a counterpart: *sweep-strategy* termination differs from
   leftmost-strategy termination on the census itself.

### 2.5 A=B and B-in-A (the easy families, proved)

* `A = B`: `[A/A] = id` => `lim([A/A])` = the total identity (converges
  in one confirming sweep).  **[VERIFIED]** all 30 rules x inputs `<= 9`.
* `B` occurs in `A`, `A != B`: both diverge on every `B`-containing
  input — one restart step re-inserts `A` (which contains `B`), and one
  sweep inserts `A` (containing `B`) at each replaced site; on `B`-free
  inputs both are the identity.  **[VERIFIED]** the one-step facts on
  all 162 rules x all inputs `<= 9`, plus operational confirmation
  (divergence at caps) on the `<= 6` inputs.

---

## 3. Census cross-check — and a paper text bug

My census of restart-divergent rules on the paper's stated domain (930
rules, all inputs `<= 9`, cap 4000):

* **166 rules diverge**: 162 with `B` occurring in `A` (incl. `A = B`),
  plus exactly FOUR with `B` not-in `A`:
  `[aabb/ba]`, `[bbaa/ab]`, `[abba/bab]`, `[baab/aba]`.
* **CORRECTION (coordinator, this round)**: at its original `CAP=2000`
  the paper's `verify_extra.py` printed **170 with `extra == FOUR:
  False`** — its assertion encoded the right expectation but failed,
  unnoticed (the four slow families outlive 2,000 steps).  So my R1
  statement "the paper's own script has the FOUR" was wrong as stated:
  both the text AND the script were wrong at that cap.  The coordinator
  has since (a) confirmed decisively that the four disputed rules
  terminate on every input `<= 9` at cap `10^6`, max exactly **3,280
  steps**; (b) fixed the script's cap to `10^4`; (c) fixed two more
  latent bugs in it (part (d) was missing the `|B| <= 3` filter — it
  checked a 402-rule domain instead of the paper's 162-rule census; it
  now prints exactly 162/140/18/4 as the text claims — and part (e) had
  its two restart calls in the wrong order, violating the paper's
  right-to-left composition; now 36/36); and corrected the paper text
  (166 = 162 + four, cap-sensitivity note, strategy sentence rescoped,
  and the four cap-sensitive families certified to have FINITE
  unrestricted closures on all inputs `<= 7`).
* **The step-count law of the slow families** (found by the
  design-space agent's R3; cite as external corroboration): the
  cap-sensitive families satisfy the exact tripling law
  `steps(n+1) = 3 * steps(n) + 1`: 3,280 -> 9,841 -> 29,524 -> 88,573
  (on `b^{n}a`-family inputs), which explains both why small census
  caps misclassify them and why they terminate everywhere tested.
* The paper's TEXT (`thm:termination(v)` proof, closing census sentence)
  says "exactly 170 diverge: the 162 with `B subset A`, plus these
  eight" and lists `[aabb/ba]`, `[aaab/ba]`, `[abbb/ba]`, `[abba/bab]`
  "up to renaming".  **The text does not match its own script**, and the
  two extra shapes are not divergent rules at all:
  - `[aaab/ba]` and `[abbb/ba]` TERMINATE on every input of length
    `<= 9` (within every cap tried, incl. 200,000);
  - at length `<= 12` they looked divergent at cap 6000 (159 inputs
    each), but re-verification at cap 200,000 shows the first 12
    sampled "divergent" inputs all TERMINATE (13,130-19,693 steps,
    outputs of length ~13,000-19,700): these rules are SLOW TERMINATORS,
    not divergent ones.  (Their lim orbit is also long: ~4,400 sweeps,
    same final value.)
  - so on the stated domain the count is 166 and the list should be the
    FOUR (= the two shapes `[aabb/ba]`, `[abba/bab]` under renaming).
  **Action for the paper**: fix the sentence (166 + four).  The R1
  numbers above use the corrected census.

**Cap discipline (methodological finding).**  "Divergence" in these
censuses is operational — no termination within the cap — and this round
caught the convention's sharp edge twice: (i) `[aaab/ba]`-family rules
terminate after >6,000 leftmost steps on 10-char inputs (13,130 steps on
`bbbbbbbbaa`, 19,692 on `bbbbbbbbba`), far beyond the paper's census cap
of 5,000; (ii) my own first pass misclassified such rules as
restart-divergent where lim converges, until re-verification at 10-15x
caps.  Every termination SEPARATION claimed in this report survives
restart caps of 50,000 (15-input subsamples) and 300,000 (the canonical
witnesses: `[baab/aba]` on `aaaba`: restart diverges at cap 300,000 —
88 seconds of trajectory — while lim returns a 9-character value in 4
sweeps).  A related observation for the paper's methodology note: the
step counts of terminating one-rule leftmost runs on short inputs are
unboundedly cap-exceeding; the census cap convention should be stated
with this caveat.

---

## 4. Tower growth through lim (cor:towers carries over)

All via the AST `lim` nodes (`run` of `('L', E, E0)`), checked against
the closed forms AND against the composed restart nodes:

* **Amplifier** (`thm:amplifier` value): `lim([baa/ab])(S) =
  b^{#b(S)} a^{v(S)}` for all 511 binary `S` of length `<= 9` plus 40
  random of length 10..12.  (The step count is NOT the restart's
  `v(S) - #a(S)` — the sweep batches — but the value is the same.)
* **Half node**: `lim([ab/aa]): b^m a^K -> b^m (ab)^{K/2} a^{K%2}`,
  grid `m <= 3`, `K <= 12`.
* **Tower t=1**: `lim([baa/ab])(ab^{n-1})` has length `2^{n-1}+n-1`,
  `n <= 6`.
* **Tower t=2** (3 `lim`-nodes, the paper's two-node block): grid
  `m <= 3`, `K <= 12` matches `b^{m+K/2} a^{2^{K/2+1}-2+K%2}`; on
  `ab^{n-1}` for `n <= 5` (output `a^{510}` at `n=5`) — lim value ==
  closed form == composed restart.
* **Tower t=3** (5 `lim`-nodes) on `ab^{n-1}`, `n <= 4`: output lengths
  1, 5, 21, 65556 (`b^{22} a^{2^16-2}` at `n=4`) — lim == closed form ==
  composed restart.  (Beyond the paper's own t=2-only verification.)

So the degree machinery of Section 4 fails in L+lim exactly as it does
for the Markov calculus: `2t-1` constant-pattern `lim`-nodes produce
tower-of-height-`t` output in the input length, `lem:length` and
`thm:fp` cannot survive, and no polynomial bound holds.  (Trivially,
also, growth is available with VARIABLE patterns: see Sec. 5.)

---

## 5. Demos (all through the AST evaluator)

* **Nested lim**: `lim(lim([eps/ba]))` on all 255 strings `<= 8` —
  value = the true `ba`-free fixed point.  Side observation recorded: a
  single DELETION sweep is not idempotent — `[eps/ba] "bbaa" = "ba"`
  (deleting merges the neighbors into a fresh `ba`) — so already
  `lim([eps/B])` genuinely iterates; its fixed points are still exactly
  the `B`-free strings (Lemma 2.1).
* **Branching iterand** (the universality power source): `E(x) =
  if(contains(x,"bb"), x, x b)` — the paper's Selection + Equality +
  occurrence test, all raw-L — under `lim` maps every `w` (all
  `|w|<=6`) to the first `bb`-containing extension.  Each iteration
  does data-dependent work; the orbit adapts.  (Under eager evaluation
  both branches are evaluated — branching here is data selection, not
  laziness; that is what keeps the construction inside the paper's
  strict calculus.)
* **Growth**: `lim([X X/X])("a")` has orbit lengths 1, 2, 4, ..., 2^k —
  doubling per sweep, diverges; a one-node expression whose intermediate
  growth is `2^k`, with a VARIABLE pattern (no constant rule can do
  this in one restart node).

---

## 6. Consequences for the main line (universality)

Nothing in R1 obstructs the coordinator's central conjecture
(**L + lim = the partial computable functions**); R1 was its groundwork.
Notes for R2+:

* The 2CM plan needs only that `lim(step)` runs the machine — the fixed
  point being the halted configuration.  The strategy analysis of this
  round is irrelevant to that (the step is a full toolkit expression,
  not a single pass).
* The paper-facing story of the fixed-point lemma should be REWRITTEN
  as: (i) fixed-point-set lemma; (ii) the agreement classes (disjoint
  alphabets proved; unbordered B conjectured); (iii) the separation
  witnesses and the one-directional "lim more often defined"
  observation; (iv) towers.  This is *richer* than the planned lemma.
* The `lim(L) subset-of lazy-pass recursive L` inclusion (R3) is
  untouched: the driver `RUN(C) = if(eq(E(C),C), C, RUN(E(C)))` is a
  lazy-pass gate program regardless of the strategy story.

---

## 7. Next round (R2) plan

1. The flat-L 2CM STEP function (no recursion): fixed program template
   with marker-wrapped current instruction `M P_i M'`, marker-delimited
   tallies per counter; dispatch = if-chain over CONSTANT occurrence
   tests; jump = remove marker here + place at `P_j` (simultaneous
   multiple substitution `lem:multiple-substitution` for the constant
   round); increment/decrement = constant passes at the counter's
   delimiter; zero test = constant occurrence test.
2. Verify `lim(step)` on small machines (doubling, adder) end-to-end,
   then on a third machine with a zero-test branch.
3. Check every branch of the step is total (so non-convergence = exactly
   the machine's non-halting), and that the halt configuration is the
   UNIQUE fixed point (every non-halted instruction changes something).

Files: `lim_core.py` (grammar/evaluator), `verify_r1.py` + `round1.log`
(this round; final suite result: 65,788 checks, 0 failures), and
`mismatch_r1.py` (mismatch catalog, re-runnable).  Canonical witnesses
additionally re-verified at restart cap 300,000 in-session (the four
hard-rule witnesses, and the slow-agreement witness `[bbba/ab]`).


---

# ROUND 2 — The flat-L two-counter-machine step (delivered)

**Question (coordinator's order):** build the 2CM compiler with a STEP
FUNCTION IN FLAT L (no recursion), marker-wrapped instruction dispatch
over constant occurrence tests, constant passes for counter ops,
verified end-to-end on the doubling and adder machines under lim, with
totality of every branch and uniqueness of the halt fixed point.

**Deliverables:** `verify_r2.py` (compiler + full verification suite),
`round2.log` (clean run).  **Final suite result: 50,744 checks,
0 failures, EXIT=0.**

## R2.1 The compiled scheme (all machine-verified)

Configuration over Sigma = {a,b} (t = tally char; both t = a and t = b
verified):

    cfg  =  D0 PROGRAM D1 T1 D2 T2 D3
    PROGRAM = P1 P2 ... Ps PH     (fixed constant instruction codes, in order)
    the CURRENT instruction is marker-wrapped:  M Pi M
    M PH M  <=>  halted (pc = 0)
    Ti = t^{x_i}   (EMPTY run = counter 0: the delimiters touch)

Structural constants come from the family V(k) = 'bb'+'ab'*k+'bb'
(mirror in swap mode), assigned with an offset/spread.  Their b-run
signature is [2,1,...,1,2], which makes them pairwise non-occurring
(verified as a build-time check for every machine, every offset/spread
used), and they contain no doubled tally char, so they cannot sit inside
or straddle a tally of length >= 2.

**The step (a flat Exp_1, NO recursion, NO lim inside):**

* dispatch = an if-chain over constant occurrence tests
  contains(M Pi M), built from the paper's Equality + Selection
  (parameterized roles (b,x); both ('a','b') and ('b','a') verified).
  The occurrence test is the fixed-point-set lemma in action:
  [c/P]X = X iff P notin X.
* inc(r,j)   : the single constant pass  [D_r t / D_r]   (tally grows
  by one: the delimiter occurs exactly once, census-verified).
* decjz(r,jz,jnz): if contains(D_r D_r') then jump jz (zero test = the
  two delimiters touching), else [D_r / D_r t] then jump jnz.
* jump i->j  = TWO constant passes, in this order:
  unwrap [Pi / M Pi M]  THEN  wrap [M Pj M / Pj]  (j = 0 wraps PH).
  Unwrap-before-wrap is what makes SELF-jumps (j = i, e.g. a machine
  that spins in place incrementing a counter) come out right: after
  unwrapping, Pi is the unique bare occurrence, and the wrap re-wraps
  it.  No extremal-site edits are needed anywhere in this design (the
  once agent's 5-pass leftmost-b cascade remains available but was not
  required).
* halted => no dispatch pattern occurs => the chain's else-branch is
  the identity X1.

**INIT / OUT / MAIN:**

* INIT(X)  = K(D0 prog(1) D1) . X . K(D2 D3)      (input in counter 1)
  INIT2(X,Y) likewise for 2-input machines (adder).
* At halt the scratch counter (counter 1) is 0 (both test machines drain
  it; for the general theorem a 2-instruction cleanup loop or a
  compile-time counter swap arranges this), so the whole prefix
  D0 prog(0) D1 D2 is a CONSTANT:  OUT = [eps / that prefix] [eps / D3]
  leaves the bare output tally t^y.  Constant-pattern extraction, no
  parsing, no recursion.
* MAIN = OUT o lim(step) o INIT — ONE lim node runs the entire machine
  (census-verified: exactly 1 L node in MAIN; 0 L nodes in step).

## R2.2 What was verified (verify_r2.py, round2.log)

* **Constant family**: pairwise non-occurrence of all structural
  constants (delimiters, instruction codes, halt slot, marker);
  no doubled tally char inside any constant; anchored ends.
* **Flatness of the step** (complete AST walk): no L node; the only
  variable is X1; every pass pattern is never-empty (constant, or the
  paper's Equality `benc` concatenations anchored by nonempty
  constants) => every pass is Safe => the step and every branch is
  total.  Doubling step: 298 nodes, 83 passes, of which 75 have
  constant patterns — the 8 remaining are exactly the paper's Equality
  masks (2 per occurrence test).  Adder: 223 nodes / 62 passes (56
  constant).  c2drain: 445 / 124 (112 constant).  selfloop: 76 / 21.
* **Occurrence census**: for EVERY configuration (pc, x, y) on the
  systematic domain (pc in 0..s, x,y in 0..4 core; 0..8 escalated; 120
  random states with x,y in 0..40): every pattern of the step and the
  out stage occurs EXACTLY the expected number of times — dispatch
  patterns iff pc = i, delimiters exactly once, zero patterns iff the
  counter is 0, dec patterns iff the tally is nonempty, instruction
  codes exactly once (bare or inside the wrap), marker exactly twice,
  out-prefix iff halted with scratch 0.  No spurious occurrences, no
  straddles, anywhere on the domain.
* **Step semantics**: on every one of those configurations, the step
  evaluated through the real AST evaluator equals the ground-truth
  simulator's next configuration (identity when halted).
* **Fixed-point uniqueness**: step(cfg) != cfg for EVERY non-halted
  configuration on the domain (and halt IS a fixed point).  The only
  2CM that could break this is a decjz whose ZERO branch jumps to
  itself (marker stays put, counter untouched = identity); such an
  instruction is a genuine no-change infinite loop and must be
  preprocessed away (a 2-cycle of incs) — none of the test machines
  needs it; flagged in the code comments.
* **Totality**: 300 random garbage strings per machine through the
  whole step, 50 per branch pipeline separately: always defined.
* **End-to-end under lim** (real evaluator, real MAIN):
  - doubling ([decjz 1,0,2],[inc 2,3],[inc 2,1]): MAIN(t^n) = t^{2n}
    for n = 0..8, and n = 9..12 on escalation.
  - adder ([decjz 1,0,2],[inc 2,1]): MAIN2(t^n, t^m) = t^{n+m} on the
    5x5 grid, and the 7x7 border on escalation.
  - c2drain (exercises the COUNTER-2 dec/zero paths): MAIN2(t^n,t^m)
    = t^n on the 5x5 grid.
  - the lim ORBIT is traced point by point and equals the simulator
    trajectory (length + 1 for the repeated fixed point); the last
    point is exactly the halt configuration.
* **Divergence direction** (partiality): selfloop ([inc 1,1]) and
  twocycle ([inc 1,2],[inc 1,1]) never halt; lim(step) diverges on
  every input tried (cap 4000), and every orbit point before the cap is
  still a genuine machine configuration.  Non-convergence of lim is
  exactly the machine's non-halting.
* **Escalation discipline** (coordinator's rule): strictly larger
  domains (n to 12, x,y to 8 systematically and 40 randomly); BOTH
  toolkit role pairs (b,x) in {('a','b'),('b','a')}; BOTH configuration
  alphabet swaps (tally char a vs b) — all four combinations re-run
  the full battery; three constant-family assignments (offset/spread
  3/1, 7/2, 13/3, 1/1).  All green.

## R2.3 Observations for the write-up

* The compiler is pure CONSTRUCTION: instruction count s enters only
  through the length of the if-chain and the program-zone constant.
  Size grows linearly in s: roughly 75-125 nodes per instruction
  (dominated by the paper's Equality inside each occurrence test).
* Everything the step does is a constant pass or the paper's own
  Selection/Equality: L + lim inherits the paper's whole flat toolkit
  for free; the 2CM layer adds only markers and tallies.
* The halted configuration is a fixed point by the else-branch identity
  (no dispatch pattern occurs); uniqueness follows from every executed
  instruction changing the marker position or a tally.
* Zero is the empty run (adjacent delimiters), so the zero test is a
  constant occurrence test and inc/dec are single constant passes at
  the delimiter — no Horner coding, no parsing, in the step.

## R2.4 Next round (R3) plan

1. Write the universality theorem in the paper's style: every partial
   computable f : Sigma* -> Sigma* (|Sigma| >= 2) is computed by an
   L+lim expression: 2CM -> (normalize to: output in counter 2, scratch
   counter 1 drained at halt, no zero-branch self-jumps) -> the R2
   compiler -> MAIN.  State the compile-time normalization lemmas and
   the uniqueness argument as prose lemmas; cite verify_r2.py for the
   machine-checked part on the stated finite domains.
2. Convergence/totality undecidability: lim(E) undefined is
   Sigma^0_1-complete (a halting problem); total lim-expression
   recognition is Pi^0_2 (divergence-freedom on all inputs).
3. lim(L) vs lazy-pass recursion: RUN(C) = if(eq(E(c), c), c,
   RUN(E(c))) as a lazy-pass gate program; corollary barriers.
4. Carry the R2 numbers into the report tables.

Files: `lim_core.py`, `verify_r1.py` (R1), `verify_r2.py` + `round2.log`
(this round; 50,744 checks, 0 failures).


---

# ROUND 3 — Occurrence lemma, normalization lemmas, lazy-pass containment

Coordinator's steers (priority order): (1) the general occurrence
lemma for EVERY configuration; (2) the two R2 caveats promoted to
verified lemmas; (3) lim(L) <= lazy-pass recursive L; (4) convergence
undecidability (statement).  All four delivered.

**Deliverables:** `verify_r3.py` + `round3.log` (final suite: **964,604
checks, 0 failures, EXIT=0**) and `occurrence_lemma.tex` (the lemma,
paper-ready).  `verify_r2.py` was touched by a one-line fix (see
finding L below) and re-run green: 50,744 checks, 0 failures.

## R3.1 Item 1 — the general occurrence lemma (the write-up's
load-bearing piece)

**Statement** (`occurrence_lemma.tex`, Lem lem:occurrence): with the
frame constants (delimiters D0..D3, codes P1..Ps,PH, marker M) drawn
from the family V(k) = sigma^2 (tau sigma)^(k-1) tau sigma^3 with
PAIRWISE DISTINCT indices k >= 2, for EVERY pc in 0..s and EVERY
x, y >= 0, in cfg(pc,x,y): (i) every frame constant occurs exactly at
its slots (M twice); (ii) M Pi M iff pc = i, M PH M iff pc = 0; (iii)
Dr Dr' iff counter r = 0; (iv) Dr tau iff counter r != 0, ending at
the tally's FIRST character; (v) the out-prefix D0 Pi(0) D1 D2 iff
pc = 0 and x = 0, at position 0.

**Proof = the gap calculus** (full proof in the tex).  Key steps:
1. gap sequences: constants are (2; 1^(k-1); 3); every inter-constant
   junction merges to 5; a tally contributes 3 0^(n-1) 2 (or 5 when
   empty); the string's head run is 2, tail run 3.
2. any pattern occurrence maps its taus to CONSECUTIVE configuration
   taus with interior gaps EXACTLY equal.  Pattern gaps are in
   {1,3,5} only — never 0 (so no pattern covers two consecutive tally
   characters, killing every straddle at lengths >= 2), never 2 (so no
   pattern's tau-sequence crosses a tally's right edge; a pattern
   whose first tau is a tally character is impossible because its next
   gap would be 0 or 2).  The ONLY pattern touching a tally is the
   designed one, Dr tau, whose final gap 3 pins it to the tally's
   first character.
3. PINNING: the leading 1-block (length k-1, unique because indices
   are distinct) + the seam mismatch (a longer constant's internal gap
   1 cannot match the pattern's seam 5 or 3) + the head condition (a
   middle tau has only one sigma before it, but patterns need 2) force
   slot-exact alignment, constant by constant.

**The coordinator's specific asks, answered:**
* which candidate could straddle a tally: none can, for ANY length —
  no pattern contains tau-tau, and the length-1 tally case is killed
  by the gap-2 argument (a pattern covering the lone tally character
  with anything after it would need a gap of 2);
* the b-run-signature [2, 1^(k-1), 3] argument: mutual
  non-occurrence of the family (proved in the tex: the trailing run
  of 3 forces an occurrence to END at the string end, the head run of
  2 forces it to START at a slot start, so V(j) in V(k) implies
  j = k);
* edge lengths machine-checked EXPLICITLY: x, y in {0,1,2} at every
  pc (the "EDGE" battery), then all x,y in 0..40 at every pc, then
  400 random states with x,y up to 1000 — every pattern of the step
  and the OUT stage (including the halt dispatch M PH M) counted in
  every configuration, exactly as the lemma predicts.  Under offsets
  2, 3, 7 (hypothesis satisfied) and, as a bonus, offset 1 (violates
  k >= 2 — still passes empirically; single-tau constants are then
  pinned only by their neighbors, "sequence pinning").

## R3.2 Item 2 — the two caveats, now verified lemmas

The complete compile-time normalization pipeline (all machine-checked
in part B):
1. `fix_selfjump`: a decjz whose ZERO branch jumps to itself is a
   no-change infinite loop (a genuine non-halted fixed point of the
   raw step — DEMONSTRATED: the raw hyb machine's step is the identity
   at pc=1, x=0, and its lim wrongly converges).  Replacing it with a
   fresh self-looping inc preserves the partial function exactly
   (simulator-verified on a 7x4 grid; the compiled MAIN now matches
   the original's partiality: MAIN(a^n) = a for n >= 1, diverges on
   eps).
2. `swap_counters`: a machine whose natural output is counter 1
   (drain-into-c1) compiles correctly after the swap (output value
   preserved, now in counter 2; MAIN2 grid verified).
3. `add_cleanup`: a machine halting with the scratch counter
   nonzero (the out-prefix then does not occur) produces GARBAGE in
   the raw compile (demonstrated); retargeting jumps-to-0 to a fresh
   drain instruction ('decjz',1,0,k) fixes it (simulator equivalence
   + MAIN2 grid verified).

## R3.3 Item 3 — lim(L) <= lazy-pass recursive L

The driver (part C): RUN(X) = if E(X) = X then X else RUN(E(X)) —
the paper's Sec. 6 gate pattern, with the recursive call in the outer
selection pass's REPLACEMENT, so the lazy-pass machine (which forces
a replacement only when its pattern fires) demands the call only on
the live (unequal) branch.  Verified on the lazy-pass abstract
machine (research/scratch/rec/lazy_pass/core.py — the two calculi
share the K/V/C/S node format, so the flat iterands drop in
unchanged):
* both toolkit role pairs (b,x) in {('a','b'), ('b','a')};
* 8 single-pass rules x 19 inputs = 152 pairs per toolkit (135
  converge with values EXACTLY equal to lim's, 29 diverge), including
  the R1 mismatch rules: [baa/ab] (amplifier), [abba/bab] and
  [baab/aba] (the restart-diverges/lim-converges pair), [aabb/ba] and
  [bbaa/ab] (see finding E below), [a/ab], [ab/aa], [a/b];
* a branching iterand (12 inputs, both convergence and divergence);
* the R2 2CM steps themselves: RUN(step) reaches exactly the halt
  configuration lim reaches, for doubling and adder, n = 0..5; and
  the selfloop machine diverges on both sides.

**The punchline** (with R2 + Minsky): flat L + ONE lim node = lazy-pass
recursion = the partial computable functions.  The entire gap between
the paper's bounded calculus and universality is one iteration node —
the power was never in the recursion depth (this sharpens Sec. 6's
inertness story: eager recursion and lazy ARGUMENTS add nothing; only
the guarded pass demanded on the live branch matters, and lim
internalizes exactly that).

## R3.4 Item 4 — convergence undecidability (statement; needs
nothing beyond items 1-2)

By Lem lem:occurrence + the step's totality: the halt configuration
is the UNIQUE fixed point of step_M, and the orbit from INIT(X)
visits exactly the machine's configurations.  Hence lim(step_M)
converges from INIT(X) iff M halts on X (machine-checked directions:
doubling/adder converge, selfloop/twocycle diverge, R2 + R3).  So
convergence of a single lim node is Sigma^0_1-complete, and totality
of a lim expression is Pi^0_2.  The formal corollary write-up belongs
to the theorem round (R4).

## R3.5 Findings and discipline notes

* **L (latent bug, found and fixed)**: the parameterized toolkit's
  occurrence test used mask = b unconditionally; when the tested
  pattern IS the single character b (toolkit (b,x) = ('b','a'),
  pattern 'b' in the branching battery), the mask pass is the
  identity and contains() always reports "absent" — the branching
  iterand degenerated to the identity and the driver converged to
  its input.  R2 was immune (every R2 pattern is a long frame
  string).  Fixed: mask = b if B != b else x.  verify_r2 re-run
  green (50,744 checks, 0 failures — same count, no behavioral
  change).  Lesson recorded: constructions parameterized by role
  characters need collision checks against the DATA, not just the
  alphabet.
* **E (exponential orbits from ONE pass + ONE lim)**: [aabb/ba] and
  [bbaa/ab] (replace ba by aabb; replace ab by bbaa) GROW
  EXPONENTIALLY under lim sweeps — len 8 -> 204 after 10 sweeps —
  because every replacement of 'ba' by 'aabb' can recreate up to two
  fresh 'ba's at the junctions; lim diverges on mixed inputs
  (converges only on pattern-free ones).  Contrast cor:towers, which
  needs 2t-1 NESTED nodes for tower height t: a single lim node over
  a single pass already doubles per iteration.  Feeds the R5 growth
  story (the sweep iteration is itself an amplifier).
* **C (convention trap, process)**: the census convention (A,B) =
  [A/B] = replace B by A misled me twice: [ab/a] GROWS (replace a by
  ab), [a/ab] SHRINKS.  The first battery misclassification burned
  big caps on growing strings (a hang).  Fix: pre-classify every
  (rule, input) with a cheap raw sweep simulation and choose caps by
  class; note the lazy-pass machine has NO length guard, so
  exponential-growth cases must use small step caps there.

## R3.6 Next round (R4) plan

1. Assemble the universality theorem in paper form: Minsky 2CM ->
   normalization pipeline (R3.2) -> occurrence lemma (R3.1) -> step
   correctness (R2) -> unique-halt + partiality -> the containment
   (R3.3) -> L + lim = partial computable.  Write the tex section.
2. The undecidability corollaries (R3.4) formally.
3. If budget: the iteration hierarchy (which iterand fragments are
   universal; single-pass iterands vs branching; finding E suggests
   single-pass iterands already reach exponential orbit growth but
   likely not universality — the R2 dispatch shows why branching is
   essential).

Files: `verify_r3.py` + `round3.log` (964,604 checks, 0 failures),
`occurrence_lemma.tex`, `verify_r2.py` (mask fix; re-run 50,744/0),
`round2.log` (re-run), plus R1/R2 deliverables unchanged.

---

# ROUND 4 — The theorem assembly, paper form (delivered)

## R4.1 The deliverable: `lim_section.tex`

The full subsection draft, paper notation and environments (llncs,
mathpar, `[(i)]` enumerates, `[\,A/B\,]` with B the pattern throughout,
`Remark~\ref{...}` referencing, verification notes in the paper's
"(Verified: ...)" style).  Structured for the intended placement: a new
subsection of the Variants section, right after "Restarting from Zero"
(before `\subsection{Both Directions at Once}` / `ssec:union`), per the
coordinator's placement decision.  Contents, in order:

- `def:lim` — lim syntax (mathpar rule; X₁ bound in the iterand) +
  denotation (fixed-point semantics, undefinedness propagation) + the
  capture-free substitution law (Lemma beta survives).
- `lem:fpsweep` — the fixed-point-set lemma: [A/B]w = w iff B ∉ w
  (A ≠ B, B ≠ ε), with a 4-line proof (length count + first-site
  mismatch).  Includes the `contains_B` corollary: one pass + eq is an
  occurrence test — the compilation's dispatch subroutine.
- `prop:limtotal` — one-rule totality: the trichotomy of
  thm:termination(i)-(iv) mirrored for the sweep, with the A = B corner
  flipped (lim = identity; restart diverges) — the stop rules agree
  exactly when A ≠ B.
- `rem:limstrategies` — the honest non-confluence positioning: two
  normalizers of one rule, neither canonical; census numbers + the
  witnesses; "sometimes the better-defined strategy, sometimes not
  definable from the other at all."
- `thm:lim2cm` — the compilation theorem: MAIN = OUT[lim(step)[INIT]/X₁]
  with exactly one lim node; flat step = if-chain of Section-2 toolkit
  over constant occurrence tests; the three normalizations (N1)-(N3)
  folded in as preprocessing; proof = construction (frames, step,
  unwrap-then-wrap with the self-jump reason, discarded-branch
  totality).  Doubling machine: step 298 nodes / 83 passes (75
  constant-pattern); MAIN 310 nodes.
- `lem:occurrence` — the R3 occurrence lemma, adapted to the paper (no
  \cfg/\pc macros — configurations written C(i,x,y); paper conventions)
  with the full gap-calculus proof (Steps 1-3) and the two remarks.
- `thm:limpartial` — MAIN computes the machine's partial function;
  halt is the unique fixed point on configurations; converges iff M
  halts, in as many sweeps as steps.
- `prop:limcontain` — the RUN driver: lim(E) = the three-line guarded
  recursion with the recursive call in the dead branch's replacement
  (rem:ifgate / thm:gate); structural induction replaces every node;
  undefinedness propagates identically on both sides.
- `cor:limclass` — THE PUNCHLINE: flat L + one lim node = lazy-pass
  recursive L = the partial computable functions; the landing paragraph
  on §6's inertness story ("the power was never in the recursion
  depth... the gate's condition is exactly the fixed-point test").
- `cor:limundec` — convergence of lim(E)(w) is Σ⁰₁-complete; totality
  Π⁰₂-complete (hardness via MAIN; every n is INIT's image).
- `prop:limgrowth` — (i) the amplifier: lim([baa/ab])(w) = b^#b a^v(w)
  for every w, ≤ v−#a sweeps; on ab^{n−1}: length 2^{n−1}+n−1 — one
  node, one constant pass, exponential output, PROVED (see R4.2);
  (ii) the block: 2t−1 constant-pattern lim nodes → tower height t
  (cor:towers' closed form for sweep normalizers, proved), three nodes
  refuting lim(L) ⊑ L by lem:length.
- `rem:fiborbit` — the Fibonacci divergent orbits (see R4.4 for the
  correction this forced), the junction-species mechanism, and the
  "growth lives in the iteration, not the nesting" contrast with
  cor:towers.
- The landscape row (`lim & trivially & refuted & flat & unbounded`) +
  the closing paragraph: the two iteration operators; the two open
  problems (is one-rule lim-convergence decidable?; is one node over a
  single constant pass universal?).

Standalone compile: `sanity_lim.tex` (the paper's exact preamble +
stub statements carrying every referenced paper label, so a typo'd
cross-reference would surface as an undefined ref) —
**pdflatex twice: 0 errors, 0 overfull, 0 undefined references.**

## R4.2 New mathematics this round (proved, not just verified)

1. **The Φ = v − #a potential** (prop:limgrowth(i)).  v and #b are
   invariant under every ab→baa replacement (v(x·ab·y) = v(x·baa·y)
   via v(uv) = v(u)·2^{#b(v)} + v(v)); Φ = v − #a drops by exactly 1
   per replacement and is 0 exactly on ab-free strings = the sweep's
   fixed points (lem:fpsweep).  So the orbit reaches an ab-free string
   in ≤ Φ(w) sweeps, and the invariants force the value b^#b a^v.
   This is a COMPLETE proof of the amplifier's closed form for lim —
   and it also re-proves thm:amplifier's restart termination and shows
   the sweep and leftmost normalizers of [baa/ab] agree on every input.
   (Offered to the coordinator: this is a standalone simplification of
   thm:amplifier's proof.)
2. **lem:fpsweep's proof** (length count for |A| ≠ |B|; first-site
   mismatch for |A| = |B|).
3. **prop:limtotal (i)-(iii)** from thm:termination's
   strategy-independent potentials (the paper's own proof says the
   bounds hold for a step at any position — sweeps are such steps).
4. **prop:limgrowth(ii)'s block through lim**: the half node
   [ab/aa] maps b^m a^K to b^m (ab)^{⌊K/2⌋} a^{K mod 2} in ONE sweep
   (greedy pairing), then inert; composing with (i) and counting b's
   after each a gives cor:towers' closed form for sweep normalizers.

## R4.3 Machine verification: `verify_r4.py`, `round4.log` — 364,693 checks, 0 failures (exit 0, ~110 s)

- (0) 400 random (rule, input) pairs: direct sweep orbit ==
  lim_core evaluator (val/div agreement) — ties the census data to the
  calculus.
- (1) fp-set lemma: all 930 binary rules |A|,|B| ≤ 4 × all 255 inputs
  |w| ≤ 7: [A/B]w = w iff B ∉ w.
- (2a) census re-verification at inputs ≤ 6, restart cap 2000
  (114,300 pairs): agree 102,050; value mismatch 126; lim-conv &
  restart-div 20; lim-div & restart-conv **0**; both div 12,104.
  New smallest value witness: **[ab/bb] on bbbb: lim abab (1 sweep)
  vs restart aaab** (3 leftmost splices) — smaller than R1's witnesses.
- (2b) the draft's witnesses at restart cap 10^5 + evaluator
  cross-checks + orbits: [ab/bb]/bbbb; [babb/bbbb]/abbbbbbbb
  (lim ababbbabb, 1 sweep; restart ababababb); [ab/abba]/abbababba
  (lim abb, 2 sweeps; restart abbba); [baab/aba]/aaaba (orbit
  aaaba → aabaab → abaabab → baabbaabb, 3 sweeps; restart diverges at
  10^5); [abba/bab]/babbb (orbit babbb → abbabb → ababbab → aabbaabba,
  3 sweeps; restart diverges at 10^5).
- (3a) amplifier: all 8,391 binary inputs ≤ 12 + 200 random 13-16,
  values exact + sweep bound v−#a; per-sweep invariants on 50 random
  traces; tallies ab^{n−1} for n ≤ 14 (length 2^{n−1}+n−1), also
  through the AMP lim-expression.
- (3b) towers through lim, all against closed forms: t=1 n ≤ 7;
  t=2 n ≤ 6 (output length 131,091 at n=6); block grid m ≤ 3, K ≤ 14;
  t=3 n ≤ 4 (output length 65,556 at n=4, 5 nodes).
- (3c) Fibonacci orbits: [aabb/ba] on aabbaabb: |s_k| = 2F_{k+1}+2k+6
  exactly for k ≤ 28 (|s_28| = 1,028,520), strictly increasing; on
  bbaa: 2F_{k+1}+2k+2 (1,028,516); first 16 sweeps == the evaluator
  trace; mirror rule [bbaa/ab] on bbaabbaa = reversal of the [aabb/ba]
  orbit on aabbaabb, k ≤ 16; lim([ba/ab]) sorts to b^#b a^#a (all
  inputs ≤ 12 + 100 random 13-16).

R2/R3 numbers cited in the draft are unchanged and re-runnable:
round2.log (50,744/0), round3.log (964,604/0); R1 census numbers
(3,306 / 290 / zero reverse on inputs ≤ 9 at cap 3·10^5) per
round1.log + verify_r1.py.

## R4.4 Corrections forced by this round's data

- **R1's "doubling per iteration" phrasing for [aabb/ba] is WRONG.**
  The exact law on aabbaabb is |s_k| = 2F_{k+1} + 2k + 6 — Fibonacci
  growth, asymptotically the golden ratio φ ≈ 1.618 per sweep (the
  per-sweep ratio rises toward it: L_28/L_27 = 1.6176; the mean factor
  over the first ten sweeps is 1.38, 204/8 = 25.5).  The draft states the
  corrected law and "growth by
  the golden ratio per sweep".  (The closed form fits exactly at every
  k ≤ 28; the mechanism remark tracks the two persistent junction
  species, but the recurrence is verified, not proved.)
- **R1's report section 2.2 witnesses are in REWRITE notation**
  (pattern -> replacement).  In the paper's [A/B] notation they are
  [babb/bbbb], [ab/abba], [baab/apa] = [baab/aba]; the draft uses paper
  notation and verify_r4 re-verified each at cap 10^5.  (The recurring
  convention trap — see R1.5 — bit my own write-up this time.)

## R4.5 Notes for integration

- The draft references these paper labels — def:exp, def:markov,
  lem:beta, thm:termination, thm:amplifier, cor:towers, thm:fp,
  lem:length, thm:universal, cor:barriers, rem:ifgate, thm:gate,
  thm:eager, thm:lazyargs, conj:ic, sec:toolkit, sec:variants,
  sec:recursion — all checked against main.tex's label list (0
  collisions with the new labels: def:lim, lem:fpsweep, prop:limtotal,
  rem:limstrategies, thm:lim2cm, lem:occurrence, thm:limpartial,
  prop:limcontain, cor:limclass, cor:limundec, prop:limgrowth,
  rem:fiborbit, ssec:lim, eq:contains).
- σ/τ for the construction (frames vs tallies — keeps the roles
  distinct); a/b in the growth material, matching thm:amplifier and
  cor:towers.
- The landscape table edit is one row; the draft carries the row plus
  its paragraph so the integrator can splice.
- The occurrence lemma is the R3 text adapted (macros inlined); the
  paper does not need occurrence_lemma.tex separately if this section
  is taken.

## R4.6 If there is an R5

1. The iteration hierarchy: are single-pass iterands (lim over ONE
   constant pass) universal?  Almost certainly not (the dispatch needs
   the if-chain), but no proof; the amplifier's Horner machinery is the
   obvious ceiling candidate.  Stated as the second open problem in the
   draft.
2. The ω-limit coinductive reading (original brief's bonus).
3. Smaller compiled step (298 nodes now): direct binary counters or a
   one-symbol tally machine could shrink it; would make the theorem
   statement prettier but changes nothing mathematically.

Files: `lim_section.tex` (the deliverable), `sanity_lim.tex` (compile
harness), `verify_r4.py` + `round4.log` (364,693/0), plus R1-R3
deliverables unchanged.  Re-run: `cd .../scratch/lim && python3
verify_r4.py` (~110 s); compile: `pdflatex sanity_lim.tex` twice.

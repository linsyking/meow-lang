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
| R1.8 | **Paper text bug found**: the census sentence of `thm:termination(v)`'s proof says 170 divergent rules and lists `[aaab/ba]`, `[abbb/ba]`; the actual <= 9 census is 166 = 162 + FOUR (the paper's own `verify_extra.py` has the FOUR).  The two extra text rules are not divergent at all on short inputs — they TERMINATE, but only after >6,000 (resp. within 200,000) leftmost steps on 10-12 char inputs, i.e. beyond the census cap; at length <= 9 they terminate within every cap tried. | VERIFIED (Sec. 3) |
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
  `[aabb/ba]`, `[bbaa/ab]`, `[abba/bab]`, `[baab/aba]` — the same FOUR
  as the paper's own `verify_extra.py` (`FOUR = {(aabb,ba), (bbaa,ab),
  (abba,bab), (baab,aba)}`).
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

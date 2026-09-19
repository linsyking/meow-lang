# Streams: a coinductive semantics for recursive substitution definitions

Research agent `rec-streams` for *A Theory of String Substitution over Finite
Alphabets* (`docs/proof/main.tex`, read-only).

**Question.** What happens to the lazy/pass side of the calculus when values
are finite-or-infinite strings and recursive definitions are read
coinductively -- "termination" becoming *productivity* (unbounded output
emission)?

**Answer in one paragraph.** There is a clean, machine-implementable,
adequate least-fixpoint semantics for a minimal fragment F1 (one unary
function, constant/cat/pass nodes, one recursive definition): values live in a
domain of partial / finite-total / infinite strings, the pass `[R/P]E` is run
as the classical causal pattern-matching process (state = longest suffix of
the consumed scrutinee that is a proper prefix of `P`, replacement forced
exactly when a match completes, mismatch detected with only as much of the
pattern as was compared), and the recursive definition gets the least fixpoint
of the induced functional.  Adequacy holds (machine = Kleene denotation on all
21 zoo cases, both finite and infinite inputs).  Guardedness, however, has no
simple syntactic characterisation: the naive "each unfolding emits something"
condition is refuted several ways; the correct conditions are semantic
(pre-pull emission `e(W)`, pattern alphabet, length ratios).  On finite inputs
the semantics is *conservative* over the sibling flat lazy-pass design
(verified on 146 programs, proved), but pattern laziness over stream-valued
patterns breaks conservativity in the other direction (machine terminates
where the flat semantics diverges).  One recursive definition computes strictly
more than any constant-pattern pipeline: the doubling program emits a stream
that is not ultimately periodic, hence not omega-rational, hence not
subsequential.

Files (all in `research/scratch/rec/streams/`):
- `streams.py` -- the stream machine (explicit process tree, no host recursion)
- `semantics.py` -- reference evaluators: paper `sub` (Def. 1), flat lazy-pass
  `feval`/`flat_fix`, Kleene evaluator `keval`/`mu_eval` on the domain below
- `verify1.py` -- B1 (non-recursive vs `sub`), zoo verdicts
- `verify2.py` -- B2 (adequacy), B3 (guardedness grids), B5 (variable patterns)
- `verify3.py` -- B4 (finite conservativity)


## 1. The fragment F1

Expressions: `E ::= X | w | E.E | [R/P]E | f(E)` with `w` in Sigma* constants
(Sigma finite; in experiments `{a,b}` or `{a,b,c}`), and one recursive
definition `f(X) = body`.  A program is `(main, body)`; `main` is closed but
for `X`, bound to the input stream.  Patterns `P` are officially constants in
F1; section 7 experiments lift this to arbitrary stream-valued patterns.

Values: input streams are finite strings or infinite; the scrutinee of a pass
is consumed left to right, causally.

## 2. The pass as a causal process

The operational semantics of `[R/P]E` (paper Def. 1 run online; cf. the
paper's subsequentiality theorem, whose machine state is exactly ours):

- state: `buf` = the longest suffix of the scrutinee read so far that is a
  proper prefix of the pattern's forced value; invariant `|buf| <= |P|-1`.
- on a scrutinee character `c`: compare with the pattern's char at index
  `|buf|` (forcing that char of the pattern's own stream if needed).
  *Match completed* -> emit the replacement's characters (the replacement is
  itself a stream, forced exactly now, fresh per match), reset `buf := eps`,
  resume scanning after the match -- never rescanning inserted text.
  *Mismatch* -> keep the longest suffix of `buf.c` that is a proper prefix of
  the pattern, flush the remaining characters onward.
- scrutinee EOS -> flush `buf`, signal EOS.  Pattern exhausts at length 0 ->
  `[R/eps]` undefined (raised at the initial probe).

So a mismatch is detected having compared only as much of the pattern as the
buffered prefix, and a replacement is demanded only at a completed match: the
process is causal and online, with delay bounded by `|P|-1`.

**Machine.** `streams.py` implements this as an explicit demand-driven tree of
processes stepped by a flat work stack (no host-language recursion, so
arbitrarily deep unfolding is fine; deadlock by infinite regress and
absorbing loops are detected by stack/step caps).  A run answers each demand
with a character, EOS, or *no answer ever*:

- **LIVE** -- at least `n` characters emitted (productive);
- **TERM** -- EOS, finite output;
- **STALL** -- no further answer (the operational face of the least fixpoint's
  partiality);
- **UNDEF** -- `[R/eps]`.

## 3. Denotational semantics: the domain D and the least fixpoint

`D = {w| : w in Sigma*} (partial)  U  {w! : w in Sigma*} (finite-total, EOS'd)
U Sigma^omega (infinite)`.  Order: prefix order on partials; totals and
infinites are maximal; **a finite total is incomparable with its infinite
extensions** (the point: a causal process cannot decide "there will be no more
output" while its input is still open -- e.g. the deletion `[eps/a](a^omega)`
has value bottom, not `eps!`).  Operators (as implemented in
`keval`/`kpass`):

- `cat`: left total -> continue with the right; left partial -> the left;
  left infinite -> the left.
- pass: the causal scan of section 2 on D-valued scrutinee/pattern; EOS flush
  only at scrutinee EOS; a partial replacement truncates the value at the
  replacement's frontier (everything after a bottom is unreachable).

`Phi_f(g)(s) = [[body]](f := g, X := s)` is monotone and continuous (routine
case analysis: each operator's output is determined by finite prefixes of its
inputs and commutes with sups of chains).  `mu Phi = sup_j D_j`,
`D_0 = bottom`, `D_{j+1} = Phi(D_j)` -- a Call at unfolding depth `j` reads
the body with `f := D_{j-1}`.

**T1 (adequacy).** *For F1 programs on finite or infinite input streams:
machine LIVE iff `mu Phi(s)` is infinite; machine TERM with output `w` iff
`mu Phi(s) = w!`; machine STALL after emitting `w` iff `mu Phi(s) = w|`
(partial).*
Proof sketch.  (Soundness) every character the machine emits carries a finite
emission certificate -- an induction on the certificate depth `d` shows the
character sits in `D_d(s)`; hence machine output <= mu Phi always.
(Completeness) if `mu Phi(s)` has an `n`-character prefix, some `D_j` does;
the machine is call-by-name and each pass pulls its scrutinee one character at
a time, so the finite dataflow of `D_j` is realised in finite time; the only
obstruction is an infinite demand descent with no emission, which is exactly
the partial case.  (Verified: B2, 21/21 zoo cases agree
character-for-character, the plateau-robust Kleene evaluator of section 10
agreeing on all three verdicts.)  Label: theorem with proof sketch; full
operational proof not written out.

## 4. Anchor-tail recursion: closed form (product theorem)

**T2 (product theorem).** *Let `f(X) = E0(X) . f(G(X))` with `E0, G`
f-free (passes allowed; both total on finite inputs -- the "anchor-tail"
form).  Then for every input stream `s`:*

  `D_k(s) = (prod_{n<k} E0(G^n(s))) |`   *and*   `mu Phi(s) =
  prod_{n=0}^{inf} E0(G^n(s))`,

*where the infinite product stops at its first infinite factor; it is an
infinite value iff infinitely many factors are nonempty, and the partial
`w|` (with `w` the finite concatenation of the nonempty factors) otherwise.*

Proof.  Induction: `D_{k+1}(s) = E0(s) . D_k(G(s))` by the `cat` clause
(`E0(s)` total; a partial left blocks nothing but keeps its prefix, an
infinite left swallows the right); unrolling gives the product with the
end-marker of the deepest, always-partial, iterate.  For the sup: the chain
`D_k(s)` is the increasing sequence of the finite products.  QED

**C1 (never TERM).** *An anchor-tail program never terminates: `mu Phi(s)`
is infinite or partial, never finite-total.* (The unfolding always contains a
fresh cat-right; EOS never propagates.)  Verified: P2/P4 stall with the
finite product as output; Z1a/Z1c/P1'/P3/P5/P6/Z4/Z5 are live with exactly
the product streams.

**C2 (beyond omega-rational).** *The doubling program `f(X) = X.b.f(X.X)` on
`X = a` has `mu Phi = a b aa b aaaa b aaaaaaaa b ...`, which is not
ultimately periodic.*  By T2 with `E0(Y) = Y.b`, `G(Y) = Y.Y`: the `a`-block
lengths double.  A singleton omega-language is omega-regular iff the word is
ultimately periodic (Buchi), hence not the output of any finite-state
(subsequential) transducer -- so **one recursive definition computes stream
functions strictly beyond the constant-pattern pipeline closure** (menu
item 5: pipelines = causal finite-state = left-subsequential transductions,
closed under composition by the paper's subsequentiality theorem; the
counter `f(X) = X.b.f(X.a)` gives the same conclusion with linearly growing
blocks).  Verified LIVE with output prefixes matching the products to 40+
characters, cross-checked against the Kleene evaluator.

Corner cases verified for T2 (machine verdict = expected product):
`f=[eps/b]X.f(X.a)`, `X=b` (first factor eps, then `a, aa, aaa, ...`): LIVE
`a^{1+2+3+...}`; `f=[eps/b]X.f(X.b)`, `X=b` (all factors eps): STALL ``;
`f=[eps/bb]X.f(X.b)` (alternating eps/`b` factors): LIVE `b^omega`;
`f=[eps/ab]X.f([eps/ab]X)`, `X=abab` (contracting `G`: factors die out):
STALL ``; `f=a.f(X)`: LIVE `a^omega`; `f=X.f(X)`, `X=(ab)^inf`: LIVE
`(ab)^omega`.

## 5. Junction-guarded recursion: guardedness

Now the guardedness core: `f(X) = [R/P](W . f(X))` with `W, P, R` constants,
`P` nonempty.  The pass **straddles the junction** between the emitted
`W`-part and the recursive stream; this is where "guarded" definitions stop
being productive.  Define:

- `e(W)` = the **pre-pull emission**: the pass's emission from consuming `W`
  alone, before pulling the child, with no end-of-input flush (flushed chars
  plus `R`-copies of matches completed inside `W`; the post-`W` buffer is
  *not* flushed).

**T3 (deadlock theorem).** *If `e(W) = eps` then the machine stalls with
empty output and `mu Phi = bottom`.*
Proof.  A level emits before pulling its child only from the `W`-scan, which
by hypothesis yields nothing.  After that, every emission of level `n` is
caused by a character emitted by level `n+1` (flush or match on the relayed
stream).  By induction on levels, no level ever emits.  QED
Verified: base grid 192/192 configs with `e = eps` stall with output ``
(including all deletion cases `R = eps` where matches inside `W` eat text and
emit nothing); ext grid 108/108.

**T4 (sufficient liveness conditions).**  All with `e(W) != eps`:

**(a) length condition.**  `|R| >= |P|` and `|W| >= |P|`  =>  LIVE.
Proof.  For any consumed text `y`: emitted(`y`) `= |y| - |buf| + sum_over
matches (|R|-|P|) >= |y| - (|P|-1)` (buffer invariant).  The iterate
`D_{k+1} = [R/P](W . D_k)` consumes `|W| + |D_k|` characters, so
`|D_{k+1}| >= |D_k| + (|W| - |P| + 1)` -- strictly growing when `|W| >= |P|`;
the chain is unbounded, mu is infinite.  QED  (Note `|W| >= |P|` forces
`e(W) != eps` already: `e(W) >= |W| - (|P|-1) >= 1`.)

**(b) fresh emission.**  `e(W)` contains a character **outside
`alphabet(P)`**  =>  LIVE.  Each unfolding injects a character no upper buffer
can ever hold -- a buffer extension by it always mismatches, so it is
flushed upward at the next event; per level the fresh character reaches the
top with bounded delay, and the machine spawns a new level per demand.
Label: proof sketch (the finite-delay flow argument); verified 560/560 in
the three-letter-word grid.

**(c) relay condition.**  `|P| = 1`  =>  LIVE.  With a single-character
pattern the buffer is always empty: every consumed character is either
flushed immediately (if not P) or matched (emitting `|R| >= 1` when
`R != eps`).  If `R = eps`, `e(W) != eps` implies a flushed character `!= P`
exists, which relays 1:1 at every level.  QED

**R1 (refutation: emission is not enough).**  `e(W) != eps` and `R != eps`
do **not** imply LIVE.  Two mechanisms, both machine-verified and
Kleene-cross-checked:

- *Deletion eats the junction buffer.*  `f = [eps/ab](X.f(X))` (so `W = X`):
  on `X = aab` the own-scan emits `a` (`e != eps`), but the buffered `a`
  plus the child's first character completes `ab`, and the eps-replacement
  swallows both -- each output character would need one more level of
  descent: STALL after `a`.  Same on `X = ba` (STALL after `b`).  (Z2i/Z2j.)
- *Geometric decay.*  `f = [b/bab](bab.f(X))`: each level's own match emits
  one `b` and then holds buffer `b` awaiting a second child character that
  never comes (every level is in the same state): STALL after `b`.  In the
  region `e != eps, R != eps, |R| < |P|` with `R` over `alphabet(P)`, the
  cascade is a geometric contraction: to emit `|R|` a level must consume
  `|P|`, so the `k`-th level contributes a fraction `(|R|/|P|)^k` and the
  total converges.  Grid: 58 residual stalls (base) / 18 (ext), e.g.
  `W='aa', P='aa', R='a'`; `W='ab', P='bab', R='ab'`.

**Least vs. productive fixpoints (the key coinductive phenomenon).**  In the
geometric-decay cases the equation `v = [R/P](W.v)` has **productive**
solutions -- for `W='bab', P='bab', R='b'` the value `b^omega` is a fixpoint
(and `ab^omega`, `bab^omega`, ...) -- but the **least** fixpoint is the
partial `b|`: the stream semantics selects the least, and the machine
stalls.  Productivity of *some* fixpoint is not what the semantics gives;
guardedness must guarantee productivity of the *least* fixpoint, which is
strictly harder.

**R2 (refutation: fresh replacement is not enough).**  "`R` contains a
character outside `alphabet(P)`" does **not** imply LIVE either: 4
counterexamples, e.g. `W='ab', P='baa', R='c'` (`e = 'a'`, STALL after `a`).
The fresh character never fires because no match completes during the
cascade (the `a`'s keep extending upper buffers); what matters is freshness
**of the emission `e(W)`** -- the corrected condition T4(b), which these 4
cases violate (their `e(W)` lies inside `alphabet(P)`).

**Grid summary (B3).**  Base: 15 words (`|W| <= 3` over `{a,b}`, incl. eps)
x 14 patterns (`|P| <= 3`) x 5 replacements = 1050 configs; ext: 12 words
over `{a,b,c}` (`|W| <= 2`) x 14 patterns over `{a,b}` x 5 replacements =
840 configs (the 3-letter word alphabet makes fresh `e(W)` possible).
Violations of T3, T4(a) restricted to the grid (`|R| >= |P|` and
`e != eps`), T4(b), T4(c): **0** in both grids.

**O1 (boundary, open).**  The region `e != eps` and `R != eps` and
`|R| < |P|` and `alphabet(R) subset alphabet(P)` is undecidable by the four
conditions above: it contains both LIVE and STALL behaviour, and I did not
find a complete invariant.  The per-iteration length bound of T4(a)
degrades to `|D_{k+1}| >= |D_k| - (|P|-|W|)` there -- non-growing, matching
neither verdict.  Conjecture (section 11): some progress-measure refinement
(charge the buffer deficit against the next iterate's refund) settles it.

## 6. Replacement-slot recursion: a trichotomy

**T5.**  `f(X) = [f(X)/a]X` (pattern `a`, replacement the recursive call,
scrutinee `X`).  Let `s` be the input, and let `n` be the position of the
first `a` in `s` (infinity if none).

1. `a` does not occur in `s` (no gate opens): **TERM**, value `s`.  The
   replacement is never forced -- exactly the flat lazy-pass gate, and the
   machine's causal gate agrees.
2. `n = 0`: **STALL**, `mu Phi = bottom`.  The first character matches; the
   forced replacement is the value itself: `D_k = eps|` for all `k >= 1` (a
   partial replacement truncates everything after the bottom, including the
   rest of the scrutinee).
3. `n >= 1` with `s[:n]` a-free: **LIVE**, `mu Phi = s[:n]^omega` -- the
   machine emits the block forever.

Proof.  (1) no match, `R` never demanded.  (2,3) unroll the Kleene chain: the
prefix `s[:n]` flushes verbatim (single-char pattern, no matches inside),
then the match forces `D_{k-1}`, and a partial replacement ends the value
there: `D_k = (s[:n])^k |`; the sup is the periodic stream, or bottom when
the block is empty (`n = 0`).  QED  Verified: Z3a-Z3f (TERM `b`; STALL
`ab`, `aba`; LIVE `ba -> b^omega`, `bba -> (bb)^omega`, `bab -> b^omega`),
plus B2/B4 agreement.  The general-`P` version of T5 has buffer carry
across the match and I did not attempt it.

## 7. Variable patterns (menu item 3)

Now patterns are arbitrary expressions -- a pattern is itself a stream,
pulled lazily along the comparison frontier.

**T6 (forcing frontier).**  *In `[R/P]E`, the pass forces at most `l+1`
characters of `P`'s value, where `l` is the length of the longest prefix of
`P`'s value that occurs as a factor of the scrutinee's consumed prefix (l as
measured on the full scrutinee value bounds every intermediate state).*
Proof.  The buffer is always simultaneously a factor of the consumed
scrutinee and a proper prefix of `P`'s value, so `|buf| <= l` at all times;
the pattern is only ever forced at index `|buf|` (extension probe), plus the
one initial empty-pattern probe.  QED  Verified: `[c/f(X)]X` with
`f(X) = X.f(X)` (pattern value `s^omega`) on 9 finite inputs: TERM with
output `s` and forced `= l+1` in every case (e.g. `s = abba` forces 5 of the
infinite pattern).

So an **infinite pattern can never complete a match** (a match needs the
pattern's EOS), the replacement is never forced, and the pass degenerates to
"stream through mismatches" -- with two regimes:

- **Identity.**  If no tail of the scrutinee keeps extending the pattern's
  prefixes, every character is eventually flushed: `[c/aX]X` on
  `X = (ab)^omega` (pattern `a.(ab)^omega`) runs LIVE with output
  `(ab)^omega`.  (Verified.)
- **Absorption.**  If the scrutinee is itself a tail-extension of the
  pattern's prefixes, the buffer grows without bound and nothing is ever
  emitted: `[c/X]X` on `(ab)^omega` (pattern = scrutinee) STALLs with `''`.

**R3 (conservativity break -- pattern laziness buys totality).**  `[c/f(X)]X`
with `f(X) = X.f(X)`, finite input: the machine forces only `<= |s|+1`
characters of the pattern (T6), sees the mismatch, flushes, and **TERMs**
with output `s` -- while the flat lazy-pass semantics, being strict in `P`,
must compute the full (infinite) pattern value and **diverges**.  Verified
on `s = b, ab, aabb` (B5d).  This is the one place the stream machine is
*more defined* than the strict-in-P flat design: causality of the pass
decides mismatches with only a prefix of the pattern.

## 8. Finite conservativity (menu item 4)

The sibling design: flat lazy-pass on finite strings -- strict in scrutinee
and pattern, replacement forced iff the pattern occurs in the scrutinee's
value; recursion by Kleene iteration of the induced functional on the flat
domain (strings with bottom and UNDEF), per argument, with dynamic argument
closure.

**T7 (conservativity).**  *For constant-pattern F1 programs and finite
input strings:*
- *machine TERM with output `w` iff flat-mu is the string `w`;*
- *machine UNDEF iff flat-mu is UNDEF (`[R/eps]`);*
- *machine STALL or LIVE implies flat-mu = bottom (divergence), and
  conversely flat-mu = bottom implies the machine is not TERM.*

*So the stream semantics is a conservative extension of the flat lazy-pass
semantics on finite strings; the flat world's bottom is exactly refined into
STALL (least fixpoint partial) vs LIVE (least fixpoint infinite).*

Proof.  (i) On total finite values the stream operators coincide with the
flat ones (`cat` = concatenation; the causal pass = `sub` of Def. 1, B1:
300 random non-recursive expressions agree; the forcing gate agrees: a match
completes iff `P` occurs in the finite scrutinee).  (ii) Levelwise, the flat
Kleene iterates embed under the stream iterates.  (iii) If the flat chain
stabilises at the total `w!`, then evaluating the body with `f := w!` is
total-finite and equals `w` on both sides, so `w!` is a stream fixpoint;
but a total is maximal in `D`, and the stream chain dominates the flat one,
so it reaches `w!` and stops: `mu Phi = w!`, machine TERM `w`.  (iv) If
`mu Phi = w!` total: the flat chain is increasing and bounded by `w`
(finite prefixes only), so it stabilises within `|w|+1` steps; its limit `u`
is a flat fixpoint, hence a stream fixpoint by (i), so `u >= mu Phi = w` by
leastness while `u <= w` -- `u = w`.  (v) UNDEF is raised by the same
condition (pattern exhausts at eps) on both sides.  QED

Verified (B4): 20 zoo cases + 6 junction cases + **120 random
constant-pattern programs** (random bodies over `{X, w, cat, pass, f-call}`,
arguments from `{X, Xa, Xb, aX, bX, a}`, inputs over `{a,b}` up to length 4)
-- 0 mismatches.  Note T7 is stated only for constant patterns: R3 shows
pattern laziness breaks the reverse direction for stream-valued patterns.

**A flat/stream asymmetry worth recording.**  The flat Kleene chain can grow
unboundedly while the stream chain stabilises at a partial: for
`f = [b/bab](bab.f(X))` the flat iterates are `b, bb, bbb, ...` (unbounded,
no flat value) while the stream iterates stabilise at `b|`.  Both are
"bottom" to the flat eye; only the stream semantics can *see* the difference
between geometric decay to a partial and genuine liveness.

## 9. What one recursive definition computes (menu item 5, partial)

- Without recursion, constant-pattern pipelines over streams are exactly
  compositions of causal finite-state passes, i.e. left-subsequential
  transductions run on infinite inputs (the paper's subsequentiality theorem
  + closure of subsequential functions under composition).  Their output on
  an ultimately periodic input is ultimately periodic.
- With **one** recursive definition: T2 gives closed-form infinite products,
  and C2 shows the doubling program emits a non-ultimately-periodic (hence
  non-omega-rational) stream.  So the hierarchy `pipelines strict-subset
  one-recursive-definition` is strict on stream functions.
- Universality ("can a stream program enumerate any computable sequence?"):
  not settled -- see section 11.

## 10. Verification

All batteries pass; run any of
`python3 verify1.py`, `python3 -u verify2.py {b2,b3,b5}`,
`python3 -u verify3.py b4`.

| battery | what | result |
|---|---|---|
| B1 | 300 random non-recursive F1 exprs vs paper `sub()` composition | 0 mismatches |
| Zoo | 22 machine verdicts (LIVE/TERM/STALL) incl. junction, deletion, doubling, counter, infinite inputs | all as predicted |
| B2 | adequacy: machine vs Kleene `mu_eval` (J=100), 21 cases, 3 verdicts + chars | 21/21 |
| B3 | guardedness grid, base 1050 + ext 840 configs, conditions T3/T4(a)/T4(b)/T4(c) | 0 violations; 560 fresh-emission LIVE confirmations; 4 R2 + 62+6 R1 counterexamples catalogued |
| B5 | variable patterns: frontier bound (9 inputs), identity, absorption, break | all OK |
| B4 | finite conservativity: 146 programs machine vs flat | 0 mismatches |
| P1-P6 | T2 corner cases (empty/all-empty/alternating factors, contracting G, `a^omega`, infinite input) | all OK |

Interpreter engineering notes that shaped the results (all found and fixed
during verification): the pattern cache must be compared as a string (a
list-vs-string comparison silently disabled fallback, i.e. dropped partial
matches); multi-character flushes must enter the output queue per character;
and -- a real bug in the *checker*, not the machine -- the Kleene chain
evaluated at a single input can **plateau and then grow again**
(`D_3 = D_4 < D_5`, first found in `f=[eps/bb]X.f(X.b)`), so stabilisation is
reported only after 3 consecutive equal iterates; the flat fixpoint iterates
the whole functional and is immune.  The adequacy battery was re-run after the
fix with no verdict changes.

## 11. Status

### PROVED (proofs above, machine-checked witnesses)
- **T1** adequacy (sketch) -- machine iff Kleene least fixpoint, all three
  verdicts.  Confidence: high (21/21 B2; sketch, not full operational proof).
- **T2** anchor-tail product theorem + **C1** never-TERM.  Confidence: high
  (clean induction; 8 corner cases verified).
- **T3** deadlock theorem (`e(W) = eps` => stall, no output).  Confidence:
  high (300/300 grid configs).
- **T4(a)** `|R| >= |P|` and `|W| >= |P|` => LIVE.  Confidence: high
  (per-iteration length growth proof).
- **T4(c)** `|P| = 1` and `e(W) != eps` => LIVE.  Confidence: high (relay
  argument, no counterexample in 1890 configs).
- **T5** replacement-slot trichotomy (single-char pattern).  Confidence:
  high.
- **T6** forcing frontier `<= l+1`.  Confidence: high.
- **T7** finite conservativity over the flat lazy-pass design (constant
  patterns).  Confidence: high (proof + 146/146).

### VERIFIED (machine-confirmed, analysis partial or labelled sketch)
- **T4(b)** fresh-emission condition.  560/560 in the 3-letter grid, 0
  violations anywhere; proof is a flow argument not fully formalised.
- **C2** doubling output is not omega-rational => strict hierarchy over
  subsequential pipelines.  (The non-periodicity is elementary given T2; the
  omega-regularity fact is Buchi's theorem, cited not reproved.)
- Junction pathology catalogue (Z2 family), deletion-eats-buffer,
  absorption, identity on infinite patterns (section 7).

### CONJECTURAL
- **T4(a')** `|R| >= |P|` and `e(W) != eps` => LIVE *without* the
  `|W| >= |P|` side condition.  No counterexample in 1890 grid configs; my
  length proof degrades to non-shrinking when `|W| < |P|`, and the refund
  accounting (buffer deficits repaid by the next iterate) did not close.
- A decision procedure / complete invariant for the boundary region **O1**
  (`e != eps`, `|R| < |P|`, `alphabet(R) subset alphabet(P)`): contains both
  LIVE and STALL; geometric decay explains many but not provably all
  stalls.
- Universality: whether the fragment (finite alphabet, one definition) can
  enumerate every computable omega-word.  The counter program suggests a
  positive answer is plausible via unary encodings; nothing proved.

### Abandoned, with reasons
- **A syntactic guardedness condition (a la Coquand's guarded
  lambda-calculus).**  The grids show the boundary is semantic: `e(W)` (a
  property of the pass's run on `W`), the pattern alphabet, and length ratios
  all matter, and each natural syntactic proxy I tried is refuted (R1, R2).
  Delivered instead: T3, T4(a-c) as verified sufficient conditions and the
  counterexample zoo.
- **Binary counter via constant-pattern pipelines** (would connect to the
  paper's open problem on recognising/computing with the toolkit): carrying
  requires a fresh marker alphabet or simultaneous two-pattern substitution;
  sequential single-pattern cascades reverse the substitution order.  Only
  the unary counter (Z5) was verified.
- **Thue-Morse via morphism recursion** -- same obstacle (needs a
  simultaneous two-symbol morphism; not directly expressible).  Not
  attempted beyond the design analysis.
- **Full characterisation of the stream-function class of one recursive
  definition** -- kept only the strict separation C2 (lower bound); no
  upper bound beyond the trivial "computable" (the machine is a computable
  process).

### Caveats
- The interpreter's STALL verdict is a cap-based detection (step budget /
  process-stack depth); a genuine absorbing loop and an infinite regress are
  distinguished operationally but both reported STALL.  The Kleene evaluator
  distinguishes them (stabilisation at a partial), and B2 agreement covers
  this on the zoo.
- All grid evidence is over `|W| <= 3`, `|P| <= 3`, `|R| <= 2`, alphabets of
  size <= 3; the theorems are proved for all sizes, the *conjectures* rest on
  the grid range.

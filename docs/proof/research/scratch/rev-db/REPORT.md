# Round DB — SEPARABLE RIGIDITY: the distinct-character regime closes at
# ALL S-depths; rev ∉ L over unbounded alphabets, every depth, by a
# fifteen-line induction

Task (coordinator): settle depth >= 3 of the descending-bijection program
— either prove the budget conjecture (all depths), or realize DB at depth
3+ on distinct-character inputs. The lane is the unbounded-alphabet prov
question, the direct route to "rev is not in L".

ANSWER IN ONE PARAGRAPH. Depth >= 3 is closed, and with it the entire
program target — but by a simpler route than the budget conjecture. On
SEPARABLE inputs (w with pairwise distinct letters, all avoiding Gamma(E)),
a self-maintaining invariant holds at EVERY S-depth, for every expression
shape (chains, deep patterns, deep replacements, C-compositions): every
value is constants interleaved with FULL FORWARD copies of w, and every
pass's match windows are COPY-ALIGNED (they cover whole copies and never
cut one), because a pattern value can never contain a proper piece of w —
pieces never exist to be matched, so they never get created. Consequently
prov(E,w) = (0,1,...,n-1)^M — a concatenation of ascending full runs —
which for n >= 2 is never DB, never even FDI of length >= 2; and the
output's non-constant text is forward copies of w, which for n >= 2 can
never equal rev(w). So no expression, at any depth, computes reversal on
ANY separable input of length >= 2; via the DB-forcing lemma (12.1) or
directly at the content level, rev is not computable in L over unbounded
alphabets — at all depths, all shapes, constants included. The budget
conjecture holds in the separable regime with C(E) = 1 for every E; the
conjecture for ARBITRARY w at depth >= 3 remains open but is no longer
needed for the rev application. Known witnesses do not contradict this:
every DB realization on record (round 10's chain3/C(3,1) at n = 3, round
11's four chain2 at n = 2) lives on a NON-separable w — repeated letters
or letters inside Gamma(E). Machine: 122.9M defined C pipelines (all
shapes S-depth <= 4) + 9.3k Python trials to depth 8 over Gamma in
{a,b} and {a,b,z} (independent evaluator) + 1,874 CROSS samples
re-verified against prov.py's lden: ZERO violations of the copy-alignment invariant, the block-form prov, the
content form, DB, FDI, or rev.

The round also records the honest scope: over a FIXED alphabet the
theorem gives only the constraint |Sigma \ Gamma(E)| <= 1 on any rev
witness (a witness's constants must cover all but one letter of Sigma) —
the fixed-alphabet content question (rounds 12-14 program, four adjacent
lanes) is untouched and remains the whole residual problem.

## 1. Setup and notation

Values are strings of ATOMS (character, label) with label in [0, n) (an
input position) or None (a constant character); matching is on characters
only (def:den; prov.py's lden is the reference implementation, and
rounds 1-13 have cross-verified it against the paper's semantics). For an
expression E let Gamma(E) be the finite set of letters occurring in E's
constants. Write W for the labeled input w = x_0 x_1 ... x_{n-1} (one atom
per letter, label = offset).

**Definition (separable).** w is SEPARABLE for E if its letters are
pairwise distinct and disjoint from Gamma(E).

**Definition (copy form).** A value is in COPY FORM (with M copies) if it
is v_0 W v_1 W v_2 ... W v_M where each W is a contiguous block of n
atoms spelling w with labels (0, 1, ..., n-1) in order, and each v_j is
an (unlabeled) string over Gamma(E)*. M >= 0; for M = 0 the value is a
constant word. The blocks W are the INSTANCES.

## 2. The theorem and its proof

**Lemma (Copy-Alignment).** Let w be separable, T = v_0 W v_1 ... W v_M a
copy-form value, X = u_0 W u_1 W ... W u_pi a copy-form pattern value
(pi >= 0, X != epsilon). Then every occurrence (match window) of X in T
is of one of two kinds:
  (i) pi = 0 (X = u_0 in Gamma+): the window lies inside a single
      constant run v_j; it touches no instance.
  (ii) pi >= 1: there is an instance index a in [1, M - pi + 1] such
      that the window consists of: the |u_0|-letter suffix of v_{a-1}
      (possibly empty), then instances a, a+1, ..., a+pi-1 ENTIRELY (X's
      i-th block coincides with instance a+i-1), with the interior
      constant runs equal as strings (v_{a+i-1} = u_i for
      1 <= i <= pi-1), then the |u_pi|-letter prefix of v_{a+pi-1}
      (possibly empty).
In particular NO match window starts or ends strictly inside an instance:
every instance is either wholly covered by one match or wholly uncovered.

*Proof.* First, where the letters live. In a copy-form value, the letters
of w occur exactly in the instances; a letter x_j occurs once per
instance, at offset j, and nowhere else: constant runs are Gamma-words,
and inside an instance (which spells w, whose letters are pairwise
distinct) x_j occurs only at offset j. In particular x_0 occurs exactly
at instance starts. Also, any n consecutive letters spelling w are
exactly one instance: such a stretch starts with x_0, hence at an
instance start, and has the instance's length.

Case pi = 0: X is a Gamma-word. If a window spelling X met an instance,
one of its letters would be a non-Gamma letter equal to a Gamma-letter —
impossible. So the window lies in a single constant run. (An empty window
is excluded: X != eps.)

Case pi >= 1: let the window start at position s. X's first non-Gamma
letter is x_0 (copy-form blocks start with x_0), at X-offset |u_0|, so
T[s + |u_0|] = x_0, and by the above s + |u_0| is the start p_a of an
instance a. X's first block is n contiguous letters spelling w, so the
window's letters at [p_a, p_a + n) spell w: that stretch is exactly
instance a, and it lies inside the window — X's first block coincides
with instance a. Now induct over X's gaps. Suppose X's i-th block
coincides with instance a+i-1. The next |u_i| letters of the window lie
in T after that instance, i.e. in the constant run v_{a+i-1} and (if the
gap is long enough) beyond it; they must spell u_i, a Gamma-word. If
|u_i| > |v_{a+i-1}|, the gap region includes the first letters of
instance a+i — non-Gamma letters — impossible (or the window runs past
T's end: no match). If |u_i| < |v_{a+i-1}|, then the letter of T at
p_{a+i-1} + n + |u_i| is the Gamma-letter v_{a+i-1}[|u_i|], but X's next
letter there is x_0, non-Gamma — impossible. So |u_i| = |v_{a+i-1}|, the
gap spells it exactly, and X's (i+1)-th block starts at the start
p_{a+i} of instance a+i — which must exist — and coincides with it by
the same argument as for i = 1. This runs for i = 1, ..., pi-1. The
trailing gap u_pi is Gamma-letters ending the window: the window's
letters after instance a+pi-1 are the first |u_pi| letters of
v_{a+pi-1} (if |u_pi| exceeded |v_{a+pi-1}| the window would again need
non-Gamma letters or run past the end); the leading gap u_0 is the |u_0|
letters of T before p_a, which lie in v_{a-1} and spell u_0. ∎

**Lemma (Preservation).** With T, X as above and y = z_0 W z_1 ... W z_nu
a copy-form replacement value, the value [y/X]T (greedy leftmost-first
scan, no rescanning of inserted text) is in copy form. Moreover its
instances are: the instances of T not covered by any match (whole, in
their order) plus, at each match site, nu fresh instances — the copies of
y's instances.

*Proof.* The greedy scan selects a set of pairwise disjoint match windows
in T, leftmost first, resuming after each; inserted text is never
rescanned. By Copy-Alignment each selected window is a union of whole
instances plus pieces of constant runs; so an instance of T is either
covered by exactly one match or by none. The output is therefore: the
uncovered instances of T, in order, with the surviving constant pieces
between them, and at each site the inserted block y (a copy-form value),
whose instances are fresh copies carrying labels 0..n-1. Concatenating
these pieces is a copy-form value: the v-parts are Gamma-words (pieces of
T's runs and y's constant runs), the W-parts are whole labeled blocks. ∎

**Theorem (Separable Rigidity).** Let E be any expression (any S-depth,
any shape) and w a separable input with |w| = n >= 1. Whenever [[E]]w is
defined it is in copy form:

    [[E]]w = v_0 W v_1 W ... W v_M      (v_j in Gamma(E)*, M >= 0),

and

    prov(E, w) = (0, 1, ..., n-1)^M.

*Proof.* Induction on the number of nodes of E.
- K(s): a constant word; copy form with M = 0; no labels.
- V(0): W itself; copy form with M = 1, v_0 = v_1 = epsilon; labels
  0..n-1 in order.
- C(E1, E2): both children are smaller, so [[E1]]w and [[E2]]w are in
  copy form by the induction hypothesis; their concatenation is in copy
  form (merge at the junction), and the labeled blocks keep their labels.
- S(R, P, F): the children are smaller, so T = [[F]]w, X = [[P]]w and
  y = [[R]]w are in copy form. If X = epsilon the pass is undefined —
  excluded. Otherwise [[S(R,P,F)]]w = [y/X]T is in copy form by
  Preservation.
In copy form the labeled atoms are exactly the instances' atoms, each
block contributing (0, 1, ..., n-1) left to right; hence the prov. ∎

**Corollary 1 (no DB, no FDI — all depths).** For n >= 2 and w separable,
prov(E, w) is either () or contains the adjacent ascending pair (0, 1).
In particular E never realizes DB(w), and never even an FDI prov of
length >= 2, at ANY S-depth. The budget conjecture holds in the
separable regime with C(E) = 1 for every E.

*Proof.* prov = (0..n-1)^M; if M >= 1 the first block contains the
adjacent pair (0, 1) (n >= 2), which no strictly decreasing sequence
contains; if M = 0 the prov is empty. DB requires all n labels
descending — excluded. ∎

**Corollary 2 (rev fails on every separable input — all depths).** For
n >= 2 and w separable, E(w) != rev(w).

*Proof.* If M = 0 the output is a Gamma-word; rev(w) contains non-Gamma
letters (all of w's), so they differ. If M >= 1 the output contains W —
w FORWARDS — as a contiguous block. rev(w) has length n and contains w as
a contiguous substring only if w = rev(w) (both length n), which for
pairwise distinct letters forces n <= 1. So for n >= 2 they differ. ∎

**Corollary 3 (the unbounded-alphabet theorem).** No expression computes
reversal on all strings; equivalently, for every E there are separable
inputs of every length >= 2 on which E fails. Hence no E computes rev on
Sigma* for every finite Sigma. Via the DB-forcing lemma (12.1): a
rev-computing E must realize DB on every separable input — impossible at
any depth (Corollary 1); or directly: Corollary 2. Combined with
Theorems 1-3 (depth <= 2, ALL w) this closes the program's target at
every depth: rev is not L-computable over unbounded alphabets.

**Corollary 4 (constraint on fixed-alphabet witnesses).** If E computes
rev on Sigma* then |Sigma \ Gamma(E)| <= 1: every pair of letters of
Sigma meets Gamma(E). (Else two letters of Sigma avoid Gamma(E) and give
a separable input of length 2 on which E fails, by Corollary 2.) This is
a constraint on witnesses, not an obstruction: by the laundering theorem
(12.2) a witness can always be rewritten to use more constant letters.
The fixed-alphabet question (does some E compute rev on Sigma* at all,
e.g. binary Sigma with Gamma(E) >= {a,b}) remains OPEN — it is the
adjacent lanes' program (rounds 12-14: split, two-b, interior exactness).

## 3. Consistency with rounds 10-14, and why nothing contradicts

- EVERY DB realization on record is on a NON-separable input: round 10's
  chain3 witnesses (w = bab, abb: repeated letters, and the patterns'
  constants 'b' etc. are letters OF w, so Gamma meets w) and the 29
  C(3,1) hits (w = aba); round 11's four chain2 witnesses (w = aa, ab,
  bb with Gamma(E) containing a and b — w not disjoint from Gamma).
  Separable rigidity says nothing about them, and they say nothing
  against it: on separable inputs those same expressions give prov =
  (0..n-1)^M (verified: part B re-runs the witness SHAPES on separable
  w, and the C sweep includes chain3/chain4 shapes — zero DB, zero
  FDI >= 2).
- The n = 1 degenerate case: separable w of length 1 gives prov =
  (0)^M, and M = 1 IS the DB (0,) — matching round 12 part 3's 8,391
  single-letter firings with prov = DB. Distinctness with n >= 2 is
  exactly the regime where the theorem bites.
- Round 12 part 3's crux check ("output atoms carrying letters outside
  Gamma(E) are never constants" — 1,397,644 atoms, 0 violations) is a
  pointwise shadow of the theorem's content form; this round upgrades it
  to the full block structure.
- Rounds 10-11's Theorems 1-3 bound {w : DB(w)} for ALL w at depth <= 2
  — stronger than needed in the w-dimension, weaker in depth. Separable
  Rigidity is all-depths but separable-only. They are complementary,
  and for the rev application (which, by DB-forcing, needs only
  separable inputs) the new theorem alone suffices at every depth. The
  machinery of rounds 10-11 (picks, sandwiches, frames, B-rigidity,
  residues) was built for the all-w budget and remains the record for
  depth <= 2 in that stronger statement; the budget conjecture for
  ARBITRARY w at depth >= 3 stays OPEN (round 13's one-b construction
  and round 14's fixed-middle theorem show how rich non-separable provs
  can be — all on inputs with repeated letters).
- Round 2's content-level relabeling bound (min-LDS <= n/LPS(w)) is
  vacuous for separable w (LPS(w) = 1), consistent with Corollary 1
  being the sharp statement there.
- The round-13 E_swap on separable inputs collapses: [eps/b]X = X (no b
  in w), bigsym = w b w, and [b/w](w b w) deletes both copies
  (pattern w, copy-aligned matches at instances 1 and 2), leaving the
  constant "b": prov = () — verified in part B, exactly (0..n-1)^0.

## 4. Why this was not found in rounds 10-13 (a note for the record)

The budget program asked for C(E) valid for ALL w; the residual corner
(w = tau^n, patterns containing w) consumed rounds 10-11, and the
fixed-alphabet content question consumed 12-14. The forcing lemma
(12.1) already isolated separable inputs as the ones that matter for rev,
and its machine check (12.4 part 3) verified a consequence of the copy
form — but the copy-alignment invariant itself ("pattern values never
contain a piece of w on separable inputs, so matches never cut
instances, so pieces never arise") was never written down. It is a
closed induction: the property maintains itself. The coordinator's
brief for this round — "the distinct-char regime is much more rigid
than the one-b regime — quantify that rigidity" — is answered in the
strongest possible form: the rigidity is total.

## 5. Machine record (all runs < 60 s each)

- **verify_separable.py** (log: verify_separable.log; prov.py's lden —
  the independent evaluator):
  - Part A: 4,000 random expressions, S-depth <= 4, all shapes (chains,
    deepR/deepP, C-compositions; constants over {a,b}), random separable
    inputs (n = 2..7, letters from {c..l}): 3,675 defined — prov =
    (0..n-1)^M and content = v_0 w v_1 ... w v_M in EVERY one; 0 DB, 0
    rev, 0 FDI of length >= 2.
  - Part A2: 1,500 random expressions of S-depth 5-8 (defined 1,241):
    same, all clean.
  - Part A3: 1,200 random expressions of S-depth 0-6 with constants over
    the BIGGER alphabet Gamma = {a,b,z}, inputs avoiding all three
    (defined 1,057): same, all clean -- the theorem treats Gamma
    uniformly and so does the check.
  - Part B: 21 adversarial expressions x n = 2..6 (piece-maker patterns
    w.w / a.w / w.a / a.w.b / w.a.w as patterns; glued-then-cut chains;
    deep patterns whose values are copy-doubling depth-1 values; the
    round-10 chain3 witness shapes; the round-11 n=2 witness shape; the
    round-13 E_swap; depth-6 chains; C-mixes; duplicators): 105 trials,
    all clean.
  - Part C: 2,500 trials with an instrumented evaluator tracking
    instance ids: 1,170 match windows fired, 0 cutting an instance
    (copy-alignment — the proof's engine, at the atom level), 0 split or
    malformed instances, 0 cross-mismatches against lden (the
    instrumented evaluator's content and prov match the independent
    evaluator on every case).
- **separable_hunt.c** (logs: hunt_mode1..5.log): exhaustive-in-shape
  falsification at S-depth <= 4 over a 24-form pass-free library
  (constants {a,b}; forms covering 0/1/2/3 copies with one- and
  two-sided constant decorations, incl. eps = deletion), on CANONICAL
  separable inputs w_n = "cdef..."[:n] — exhaustive over all separable
  inputs of each length, since any separable w of length n maps to the
  canonical one by a letter renaming fixing {a,b}, and the dynamics is
  invariant under such renamings. Every pipeline is simulated at the
  atom level with instance tracking; checked: copy-alignment (window
  borders never inside an instance), instance integrity (contiguous,
  spell w, labels 0..n-1), prov = (0..n-1)^M, content form, DB, FDI
  (length >= 2), rev. Totals: 122,935,396 defined pipelines
  (chain1/2/3: 45.8M; chain4: 29.2M; deepP3+deepR3: 12.5M; deepP4+
  deepR4: 13.5M; C(a+b<=3): 22.0M) + 75.4M undefined (empty pattern
  values) + 2.0M capped (value-length cap 200k atoms; explosive
  pipelines skipped and counted — a coverage loss, documented). ZERO
  violations of any kind in every mode.
- **verify_hunt_cross.py** (log: verify_hunt_cross.log): every 65,536th
  defined pipeline of the C sweep is emitted as a CROSS line carrying
  the simulator's prov (48-label prefix, length, weighted checksum);
  all 1,874 lines re-parsed, rebuilt as expressions, and re-evaluated
  with lden: the C simulator's prov agrees EXACTLY in every case, and
  the theorem claims hold on every rebuilt pipeline (semantics
  cross-check in the round-10 convention).
- Runtime: modes 22.3 + 15.9 + 3.5 + 4.5 + 10.9 s; the Python battery
  ~35 s; cross-verification ~20 s. C for everything CPU-bound.

## 6. Honest ledger

- PROVED (hand proofs above, machine-checked in their consequences):
  Lemma Copy-Alignment; Lemma Preservation; Theorem Separable Rigidity
  (content + prov form, every expression, every depth); Corollary 1
  (no DB and no FDI of length >= 2 on separable inputs at n >= 2, any
  depth — the budget conjecture in the separable regime with C(E) = 1);
  Corollary 2 (E(w) != rev(w) on every separable w with n >= 2);
  Corollary 3 (rev is not computable in L over unbounded alphabets —
  equivalently no E computes rev on all strings, or on Sigma* for every
  finite Sigma — at any S-depth; via DB-forcing 12.1 or directly);
  Corollary 4 (any fixed-Sigma rev witness satisfies
  |Sigma \ Gamma(E)| <= 1).
- VERIFIED ON STATED DOMAINS: the copy-alignment invariant and instance
  integrity at the atom level (2,500 instrumented trials + 122.9M C
  pipelines, 0 violations); prov = (0..n-1)^M and the content form
  (same domains + 9.3k random expressions to depth 8 over
  Gamma in {a,b} and {a,b,z} via the independent evaluator); no DB / FDI / rev on separable inputs at
  n >= 2 (same domains; the C sweep is exhaustive-in-shape over the
  24-form library at S-depth <= 4 and exhaustive over separable inputs
  of each swept length by renaming, but the pass-free library and the
  depth cap bound the coverage); the C simulator against lden (1,874
  CROSS samples, exact agreement).
- CONJECTURED: nothing new.
- OPEN (unchanged by this round): the budget conjecture for ARBITRARY w
  at S-depth >= 3 (not needed for rev; the separable regime is closed
  at all depths); the FIXED-alphabet question — does any E compute rev
  on Sigma* (e.g. binary Sigma with Gamma(E) >= {a,b}) — which by
  Corollary 4 + 12.2 is the only residual route, and is exactly the
  adjacent lanes' program (split, two-b, interior exactness, rounds
  12-14); the FDI-level analogue of Theorem 3 for arbitrary w (11.7);
  whether deeper shapes realize DB at n >= 4 on NON-separable inputs at
  depth >= 3 (round 10's question, untouched).
- LIMITS OF THE MACHINE RECORD: the C sweep's coverage is bounded by the
  pass-free library (24 forms) and the S-depth cap (4); deep R/P shapes
  are swept as chain-valued slots (deepP/deepR, reduced pools); 2.0M
  explosive pipelines were capped (skipped); the depth 5-8 evidence is
  random sampling (1,241 defined), not exhaustive. None of this weakens
  the proof — the theorem's evidence is the hand proof; the machine
  confirms the proof's engine locally and its conclusions on the stated
  domains.

## 7. Files

- `REPORT.md` — this report.
- `separable_rigidity.tex` — the paper-voice fragment: definitions,
  Copy-Alignment, Preservation, the theorem and Corollaries 1-4 with
  proofs, ready to fold into docs/proof/main.tex's open-problem-2
  discussion.
- `verify_separable.py` / `verify_separable.log` — the Python battery
  (parts A, A2, B, C) on the independent evaluator.
- `separable_hunt.c` / `./separable_hunt` / `hunt_mode1..5.log` — the
  exhaustive-in-shape C falsification sweep, five modes.
- `verify_hunt_cross.py` / `verify_hunt_cross.log` — the CROSS-sample
  re-verification against prov.py (1,874/1,874 exact).
- `prov.py`, `lcore.py` — copies of the round-1 evaluators (unmodified;
  lcore's relative import of ../rec/lazy_pass resolves identically from
  this directory).

# The Design Space of Substitution Systems

Research report "systems" — working directory
`docs/proof/research/scratch/systems/`.  Target paper:
`docs/proof/main.tex` ("A Theory of String Substitution over Finite
Alphabets").  §5 of the paper varied the primitive's design choices ONE at a
time; §6 varied the runtime of recursive definitions.  This study takes the
NEXT level: pairwise combinations of the §5 axes, and NEW axes nobody has
varied.  The deliverable per system: definition (paper style) → basic lemmas
→ placement in the web (vs L, R, ONCE, POS, RESTART, Markov, unsafe, the §6
runtimes) → toolkit survival → growth → machine-verified searches/censuses on
stated finite domains → verdict NEW PHENOMENON vs COLLAPSE (to which system).

**Out of scope** (owned by other agents, used here only as comparators): the
L+R union calculus; the is-reversal-in-L problem; recursion × runtime (§6 is
done).

Code: `systems.py` (all primitives of this study + the paper's, self-tested).
Reference machinery: `../rec/lazy_pass/core.py` + `toolkit.py` (evaluator and
the full §2 toolkit), `../paper_variants/verify_variants.py` (once / R /
rescan / restart / rep_ref reference implementations).

---

## Round log

* **R1 (this file, Secs. 1–5):** read the paper + the seven variant reports'
  OVERVIEW; built the design-space map; picked the deep-dive shortlist;
  wrote and self-tested `systems.py`.  Two cheap leads already settled by
  hand-derivation while reading (Sec. 4, to be machine-verified in later
  rounds): the single-site invariants transfer to ALL k-th-occurrence and
  anchored calculi, and three of the six pairwise combinations collapse
  trivially.
* R5 (done, Sec. 10 + map final + drafts): rows 1-3 closed (row 2
  corrected: pass-granularity restart ≠ Markov); the two paper drafts
  written (draft_flatlazy.tex, draft_Lk.tex); the design-space map
  finalized.
* R4 (done, Sec. 9): deep dive 4 — flat lazy-pass calculus.  Verdict:
  COLLAPSE into L as partial functions via the explicit translation TR
  (machine-verified); lpcons re-verified on a 65x bigger space; the
  denotation-space census (193 lazy-only at depth 2, all collapsed).
* R3 (done, Secs. 8.1–8.5): deep dives 2+3 — the k-th-occurrence family
  L_k (NEW: incomparability mosaic; two-sided measure lemma machine-confirmed
  for the whole single-site family, 135,136 checks) and rank-k Markov
  (COLLAPSE: rank-robust on the census domain; census cap-sensitivity
  independently confirmed + sharpened vs the lim agent's R1.8 erratum —
  the [aaab/ba] family is total on ≤ 9 with a 3·steps+1 tripling cascade).
* R2 (done, Sec. 7): deep dive 1 — ANCHORED.  Verdict: COLLAPSE into L,
  strictly and unconditionally (first variant with a proven placement);
  eq discovered with an alphabet-sensitive boundary; measure lemma found
  (unifies the four once-invariants for the whole single-site family).
* R3: deep dive 2+3 — the k-th-occurrence family and rank-k Markov.
* R4: deep dive 4 — flat lazy-pass calculus.
* R5: native multi-pattern one-sweep + survey of the rest + final map +
  recommendations.

---

## 1. The axes

The paper's §5 intro names THREE load-bearing choices in Definition def:subst.
Reading the whole paper (§2–§6) yields the full axis list below; positions
already studied are marked, positions this study owns are marked **NEW**.

* **A. Direction of the scan** (where the scan resumes / which match first):
  L leftmost-first (baseline) | R rightmost-first (§5.3) | **A† mixed L+R
  (other agent)**.
* **B. Multiplicity** (how many sites one pass edits):
  all occurrences (baseline) | once = leftmost one (§5.1) | k-th occurrence
  for constant k — **NEW** (once is k=1) | anchored = only at position 0
  (^) or the end ($) — **NEW** | positional = computed index (§5.2: setAt +
  repOcc; constant-k is its fragment).
* **C. Re-entry into inserted text**:
  never (baseline) | re-enter at insertion (rescan, §5.4) | restart from 0
  (Markov, §5.5).
* **D. Pattern language**:
  literal strings over Σ (baseline) | wildcards (don't-care characters) —
  **NEW** | several patterns per sweep — **NEW** (the freezing multi-pattern
  = `multi.md` ≡ L is known; the NATIVE one-sweep multi-pattern is not).
* **E. Iteration of the whole pipeline** (expression-level, not node-level):
  none (baseline) | to fixpoint = multi-rule Markov = classical semi-Thue,
  Turing-complete — known, out of interest.
* **F. Recursion × runtime** (§6, done, out of scope) and **G. inward
  fragments of L itself** (delete-only, single-char patterns,
  length-preserving) — **NEW**, census-able with the same methodology.

Each pairwise combination of {A, B, C} and each single new axis from {D, G}
plus the flat-lazy reading defines a candidate system; the map in Sec. 3
lists them all with status.

## 2. What §5/§6 already settled (reference points)

* **L** = baseline.  Toolkit complete (enc/dec, cat, head/tail, eq, if,
  rep_n, escape, last/init/rotate via the fresh-anchor prop:last).  Every
  reachable function polytime, degree ≤ deg(E); X↦X^|X| reachable,
  X↦X^{2^|X|} not.  Two hinges: once ∈ L? rev ∈ L?
* **ONCE** (§5.1): toolkit REBUILT (cat, tail, head, eq, if) on doubled
  markers; four invariants (fresh character, max run, balance, linear
  growth) ⇒ L ⊄ ONCE; unary simulation of delete-one-b via computed needles;
  L ⊆ ONCE open.  ONCE^R tied to ONCE via rev-conjugation.
* **POS** (§5.2): setAt/repOcc calculus; L ⊄ POS (single-site alphabet bound,
  linear growth); POS ⊆ L iff once ∈ L (thm:pos-hinge); unary dichotomy
  (piecewise-affine lengths vs halving); repOcc(k,B,A) = k once-passes with a
  fresh ALPHABET-DISJOINT marker M (thm:pos-hinge(ii)) — the disjointness is
  automatic for constant patterns over |Σ| ≥ 3 but NOT for variable patterns.
* **R** (§5.3): L = R iff rev ∈ L; toolkit verbatim (direction-robust passes);
  rep construction must be mirrored or needs |Σ| ≥ 3 + ending conditions;
  constant fragments incomparable ([b/aa]^R not left-subsequential).
* **UNSAFE** (§5.4): total iff B ⊄ A; agrees with L iff B ⊄ A and no
  nonempty suffix of A is a proper prefix of B; encoder diverges; toolkit
  collapses; run-collapse is a 1-node unsafe function; incomparability
  conjectures both ways.
* **MARKOV** (§5.5): towers of exponentials (amplifier [baa/ab]^m, Horner
  invariant); no total injective nodes; termination census: of 930 binary
  rules |A|,|B| ≤ 4 exactly 170 diverge under leftmost (162 with B ⊂ A + 8
  others, incl. [aabb/ba], [abba/bab]); IC conjecture; toolkit with
  black-box encoders; 4 exponential / 18 superlinear / 140 linear among 162
  total binary rules |A|,|B| ≤ 3.
* **§6 runtimes**: eager, lazy-args inert (= L); lazy-passes universal
  (partial computable); streams beyond finite-state.  Prop lpcons: on
  CALL-FREE programs the lazy-pass machine is conservative over eager L and
  strictly more defined only through discarded replacements — the seed of
  the flat-lazy system below.
* **multi (multi.md)**: the paper's FREEZING multi-pattern as a primitive ≡
  L, proven both directions (comma code).

## 3. The design-space map

Status legend: **KNOWN** = settled in the paper / a report; **NEW-?** =
candidate this study must classify; **COLLAPSES** = one-line reduction
(hand-derivation here, to be machine-checked); **∅** = degenerate.

| # | system | axes | status | evidence / pointer |
|---|--------|------|--------|--------------------|
| 1 | once + rescan ([A/B]₁^u) | B=once × C=rescan | **VERIFIED COLLAPSE to ONCE** (R5, verify_r5.py) | a once-pass performs ≤1 match, so at match time nothing has been inserted yet and the unsafe scan finds the same first occurrence: 2,646 checks (\|A\|,\|B\| ≤ 2, \|S\| ≤ 5), 0 mismatches. |
| 2 | rescan + restart ([A/B]^um) | C=rescan × C=restart | **TWO GRANULARITIES (R5, verify_r5b.py — R1 hand-derivation corrected)** | step-level (iterate "replace leftmost occurrence, rescan from 0"): = MARKOV, the rescan clause subsumed (restart already rescans everything each step).  pass-level (iterate the FULL unsafe pass to a fixpoint): **≠ MARKOV** — witness [aba/bab] on 'bbabb': pass-iter 'baaba' vs Markov 'abaab' (9,322 agreements, 2 differences; renaming [bab/aba] the other).  Small NEW fact: the restart axis itself has two granularities and they differ. |
| 3 | once + restart, node level ([A/B]₁ iterated to fixpoint) | B=once × C=restart | **VERIFIED COLLAPSE to MARKOV** (R5, verify_r5.py) | iterate "replace leftmost occurrence" = def:markov verbatim: 2,646 agreements (\|A\|,\|B\| ≤ 2, \|S\| ≤ 5), 0 mismatches. |
| 4 | once + restart, expression level (whole once-pipeline to fixpoint) | B=once × C=restart × E | **COLLAPSES to KNOWN: multi-rule Markov / semi-Thue** | iterating a k-pass pipeline to its joint fixpoint = leftmost-strategy normalization of a k-rule system; classically Turing-complete for enough rules (post47, markov54). No new phenomenon; record only. |
| 5 | once + positional (= constant-k repOcc, no setAt) — the family **L_k** | B=k-th | **NEW (R3, Secs. 8.1–8.3): incomparability mosaic** | L ⊄ L_k (two-sided measure lemma, 135,136 checks); ladder: each [A/B]_j in its own L_j at depth ≤ 3, spaces SHRINK with k (38,959 → 28,090 → 2,307); [a/b]_2-type ABSENT from the binary once-spaces of 969,321 (const, depth ≤ 4) + 3,773 (variable, depth ≤ 3) + 688,499 (const, reduced vocab) functions, and from R2's 1,298-function anchored space; marking chain over \|Σ\| ≥ 3: 18,522 agreements — the ONCE-vs-L_2 hinge = marker freshness. |
| 6 | positional + restart — **rank-k Markov** | B=k-th × C=restart | **COLLAPSE, rank-robust (R3, Sec. 8.4)** | k = 1, 2 reproduce rank 0's termination census (166 at adequate caps; robust at 5×) and growth buckets (same 4 exponential rules) exactly; apparent cures are cap- or domain-artifacts; created: none (0/1,600 sampled). Amplifier stays exponential at every rank (518/263/136 on (ab)^8). Byproducts: census cap-sensitivity map (3,280 steps / 6,569 length; tripling law of the [aaab/ba] family) confirming lim agent's R1.8; inertness semantics fix. |
| 7 | **anchored** calculus ([A/^B], [A/B$]) | B=anchored | **SETTLED (R2, Sec. 7): COLLAPSE into L — strictly, provably** | ANCHORED ⊆ L by explicit comma-code translation (guard lemma machine-verified); L ⊄ ANCHORED by the measure lemma; toolkit survives (cat, head, tail, init, last, doubling, rest, isne, eq: clean for \|Σ\|≥3, two-valued-false for binary); rev/`if` open. |
| 8 | anchored + once ([A/^B] + [A/B]₁ mixed) | B=anchored × B=once | NOT REACHED (survey row; R2 Sec. 7.5 recorded the seed: the anchored conditional [a/\hat{ab}] absent from once const depth ≤ 3) | untested; the conditional-splice seed suggests anchored+once may exceed both. |
| 9 | anchored + k-th | B=anchored × B=k-th | NOT REACHED | "replace the last occurrence" via anchors: the natural witness [a/B$]-flavored; untested. |
| 10 | **wildcard patterns** ([A/B′], B′ has don't-care characters) | D=pattern language | NOT REACHED | untested; trailing wildcards look Σ-foldable, [A/**] comma-code-ish. |
| 11 | **native multi-pattern one-sweep** (first-match-wins per position, priority list) | D=multipattern | NOT REACHED (only the R1 separation witness: native ≠ freezing on "aab": aY vs aaX — systems.py) | untested beyond that; constant fragment looks left-subsequential. |
| 12 | flat lazy-pass calculus (no calls, lazy replacement forcing) | §6 runtime axis, flattened | **COLLAPSE (R4, Sec. 9): = L as PARTIAL FUNCTIONS, via explicit translation TR** | lpcons re-verified (7.24M agreement points, 374K mechanism sample); 1.14M extra definedness points (~6%), all through discarded replacements; 193 lazy-only denotations at depth 2 ALL realized by TR(E) = [a/if(F,a,eps)] Phi(E) (0 mismatches; depth-3 sampled; |S|<=6 escalation; cross-checked vs run_eager). New lemmas: eps-coercion, computed-value occurrence test O, guard node. The §6 border is exactly at recursion: flat laziness adds definedness, not power. |
| 13 | inward fragments of L: delete-only ([ε/B]); single-char patterns; length-preserving (\|A\|=\|B\|); insert-only | G | NOT REACHED | untested; which retain cat/head/tail/eq is open. |
| 14 | L+R union | A† | other agent | — |

**Study summary (final).**  Of the systems explored: **NEW** — L_k (an
incomparability mosaic: pairwise incomparable fragments, separated from
ONCE by marker freshness; R3), and pass-granularity restart (iterate the
full unsafe pass ≠ Markov, witness; R5).  **COLLAPSED with new
proofs/translations** — anchored ⊆ L strictly (R2; the anchor-as-marker
theorem), flat-lazy = L as partial functions via TR (R4; three lemmas:
coercion, occurrence, guard), rank-k Markov rank-robust (R3).  **Erratum
cross-confirmed** — the §5.5 census number 170 is cap-sensitive (the
[aaab/ba] family is total on ≤ 9 with a 3·steps+1 tripling cascade; the lim
agent found this first as R1.8; my numbers agree and sharpen it).
**Integration queue** (paper-grade drafts): `draft_flatlazy.tex` (§6,
after prop:lpcons), `draft_Lk.tex` (§5 landscape); plus from R2 the
anchored ⊆ L translation and from R3 the census-cap-sensitivity remark
for thm:termination(v).
| 15 | rev ∈ L? | — | other agent | — |
| 16 | recursion × runtimes | F | §6 done | — |

## 4. Leads already derived while reading (to machine-verify)

### 4.1 The single-site lemma (covers ONCE, every L_k, ANCHORED, and their rev-mirrors)

Every pass of each of these calculi performs AT MOST ONE splice
(replace one occurrence of P by R at one site).  Hence each of the four
once-invariants of thm:once-invariants holds verbatim for ALL of them, with
the same one-line node computations (#c(URV) ≤ #c(T) + #c(R), etc.):

(i) fresh character, (ii) max run, (iii) balance, (iv) linear growth.

**Corollary (transfer of cor:once-sep):** over |Σ| ≥ 2, none of
replace-all [a/b], enc, dec, [xx/x], S↦σ^{|S|}, X↦X^{|X|}, escape_f is
reachable in ONCE, any L_k, or ANCHORED; the unary case transfers too.  So
ALL single-site calculi sit strictly below L on the same seven witnesses.

**New invariant, sharper than the four (candidate):** SPLICE COUNT — a
depth-d single-site expression performs ≤ d splices total, so the output is a
concatenation of ≤ 2d+1 alternating pieces, each either a contiguous chunk
of an input or the value of a strict sub-expression (order-preserving).  If
this induction survives scrutiny it gives ONE uniform separation where the
paper needed four, and it also separates anchored from rev (a one-chunk
normal form: output = F(X)·X[i:j]·G(X) with the chunk contiguous — rev is
not of this form on generic inputs).  To verify on bounded depth + attempt
the induction.

### 4.2 ANCHORED constructions derived (deep dive 1 targets)

Let [A/^B] = replace the prefix B by A if B ⊑ S (else S); [A/B$] the suffix
mirror.  Design decision: the empty pattern is DEFINED when anchored
(the anchored occurrence of ε is unique: position 0 / the end), so
[A/^ε]S = A·S and [A/ε$]S = S·A.  (In the baseline [A/ε] is undefined
because "all occurrences of ε" is ill-posed; the anchored site is not.)

* tail(X) = Π_{σ∈Σ} [ε/^σ] X  (each factor fires only if the head is σ).
* init(X) = Π_{σ∈Σ} [ε/σ$] X.
* cat(X,Y) = [X/^a][Y/b$](ab)  — the scaffold has a at the front, b at the
  end; both anchors fire exactly once.  (Same shape as the once-toolkit's
  cat, thm:once-toolkit(i).)
* head(X) = [ε/tail(X)$] X — since X always ends with tail(X) (|X|=|tail X|+1),
  the suffix anchor deletes exactly tail(X), leaving the head character.
* last(X) = [ε/^init(X)] X — X always starts with init(X).
* Structure: every anchored pipeline keeps the text of the form
  P·input[i:j]·Q with i ≤ j (a single contiguous chunk of input in the
  middle).  Conjecture: this is the anchored normal form, giving the class
  {F(X)·X[i(X):j(X)]·G(X)} with side conditions; if true it cleanly implies
  rev ∉ ANCHORED, enc ∉ ANCHORED, replace-all ∉ ANCHORED (also from 4.1),
  and poses the sharp questions ONCE vs ANCHORED in both directions
  (once edits an INTERIOR leftmost site — anchored cannot reach the
  interior without deleting through a boundary; anchored edits CONDITIONALLY
  — once cannot stay inert on a non-anchored occurrence).

### 4.3 Rank-k Markov leads (deep dive 3 targets)

* k=0 is exactly restart/Markov (definition coincidence, verify).
* Fixpoint semantics subtlety (found while implementing rankm): for k ≥ 1
  the fixpoint is NOT B-freeness — a rank-k rule can leave up to k leading
  occurrences untouched forever; the process stabilizes when the (k+1)-th
  greedy occurrence stops existing.  So the natural reading is "iterate
  until the pass stops changing the string".
* The amplifier [baa/ab]^m relies on ALWAYS rewriting the leftmost ab; at
  rank k ≥ 1 the rewritten occurrence is the (k+1)-th, so the Horner
  invariant v(S) breaks and with it the clean exponential growth — but the
  towers question reopens with different rules (search the census domain).
* Census plan: rerun the paper's 930-rule binary census (|A|,|B| ≤ 4, all
  inputs length ≤ 9) at rank 1 and 2; diff the divergent sets against the
  170 rank-0 divergers; classify rules that CHANGE verdict with rank (new
  phenomenon: termination becomes RANK-SENSITIVE).

### 4.4 Flat lazy-pass lead (deep dive 4 target)

The naive collapse proof FAILS for a structural reason worth recording:
the natural guard [R/P] → [R/P·if(eq(P,ε),MARKER,ε)] (rem:total-rep's
architecture) is unsound in general because MARKER, a constant, cannot be
guaranteed absent from an arbitrary variable scrutinee (in rem:total-rep the
text at that point was a CONTROLLED normal form with bounded markers; in the
flat calculus the scrutinee of an arbitrary pass is arbitrary).  So the
collapse flat-lazy = L is genuinely open in both directions:
  (a) find E call-free with ⟦E⟧_lazy ∉ L (a partial function with a domain
      no L-expression has) — machine-search on small expression spaces;
  (b) or find the general repair.  lpcons gives the shape of every extra
      definedness point: some discarded replacement was undefined, i.e. some
      pattern on a never-forced path evaluated to ε.
  Also decidable to ask: is dom(⟦E⟧_lazy) always computable by an L-function
  into {⊤,⊥}?  (i.e. is the domain an L-decidable predicate?)

## 5. Deep-dive shortlist (with justifications)

1. **ANCHORED (map row 7).** The paper's newest §2 result (prop:last) is
   literally an anchoring trick (plant a fresh anchor at the right end,
   test with constant patterns), so the anchored primitive is the paper's
   own technique promoted to a primitive — the right way to ask "was the
   anchor doing the work?".  Cheap to implement, all four single-site
   invariants transfer, a plausible exact characterization (one-chunk normal
   form) that would be the first COMPLETE description of any variant's
   reachable class (all §5 rows have open characterizations).  Sharp
   comparisons: vs ONCE (interior site vs boundary site), vs L_k, rev
   question, and the mixed systems of rows 8–9.
2. **The k-th occurrence family L_k (row 5).** The paper's two "addressing"
   variants (once = k=1; positional = computed k) leave the constant-k
   interpolation unstudied, and it is exactly the fragment of POS that
   thm:pos-hinge does NOT settle (the once-simulation of repOcc(k) needs
   alphabet-disjointness, unavailable for variable patterns over |Σ|=2).
   All single-site invariants hold, so L ⊄ L_k; the open structure is the
   STRICTNESS between L_1, L_2, L_3, … and ONCE, plus uniform-k vs
   constant-k.  This is the natural "inward hierarchy" of §5.2.
3. **Rank-k Markov (row 6).** The one pairwise combination that is neither
   out of scope nor a one-line collapse: restart × k-th occurrence.  Direct
   access to the paper's census machinery (same 930-rule domain), so
   results are immediately comparable to §5.5's numbers; plausible new
   phenomena: rank-sensitive termination, rank-sensitive growth (amplifier
   breaks), new divergent rules at higher rank.  Also closes the "how does
   once+Markov compare to Markov" question at the CALCULUS level (node
   level collapses, row 3).
4. **Flat lazy-pass calculus (row 12).** The only NEW system that lives at
   the §6 boundary rather than the §5 axes; the paper proves conservativity
   (lpcons) and stops.  The collapse question is crisp, the counterexample
   search is directly implementable on top of `rec/lazy_pass/core.py` (call
   the evaluator on call-free programs, compare against exhaustive
   L-expression spaces), and either answer is a clean result: a strict
   sibling of L (first variant class strictly BETWEEN L and the partial
   computable functions?) or a collapse theorem (the extra definedness is
   always already in L).
5. **Native multi-pattern one-sweep (row 11)** — light deep dive or heavy
   survey.  Already separated from the freezing semantics by a verified
   witness; the constant fragment question (composition of sequential
   transducers) may fall to the thm:subsequential machinery; the variable
   fragment question connects to the comma-code construction.  If rounds
   run long this degrades gracefully to survey grade.

Survey grade (row-level treatment only): rows 1–4 (collapses, one line each
+ machine check), rows 8–10 (anchored mixes, wildcards: definition, quick
battery, one paragraph), row 13 (inward fragments: definition + census on the
delete-only / single-char / length-preserving fragments of the §2
toolkit).

## 6. Round plan and discipline

One problem per round, ≤ 30 min / ≤ 128K output tokens per round; state
written here at the end of every round; every claim machine-verified on a
stated finite domain; every negative search re-runnable (scripts in this
directory, `verify_rN.py`); every candidate witness re-verified on strictly
larger domains before being believed; no fabricated citations (nothing
external cited so far; anything added later gets checked online first).

* R2 = deep dive 1 (ANCHORED): implement the anchored evaluator + expression
  enumeration; verify the Sec. 4.2 constructions; test the one-chunk normal
  form on bounded depth; compare vs ONCE / L_k by bounded-depth exhaustive
  function-space search on small domains (binary alphabet, strings ≤ 5);
  verdict.
* R3 = deep dives 2+3 (L_k family; rank-k Markov): strictness ladder
  searches; the 930-rule census at ranks 1, 2 diffed against rank 0;
  amplifier search at rank ≥ 1; verdicts.
* R4 = deep dive 4 (flat lazy-pass): call-free lazy vs eager domains on
  exhaustive small spaces; L-membership searches for lazy-only denotations;
  analysis of dom(f_lazy); verdict.
* R5 = deep dive 5 if budget allows + survey rows + FINAL MAP + the 1–2
  recommendations for paper sections.

---

## 7. Round 2 (deep dive 1): the ANCHORED calculus — verdict: COLLAPSE INTO L, with a toolkit that survives

Working definitions and all numbers: `verify_r2.py` (this round) + the
spot-checks of Sec. 7.3 run inline (recorded below).  Everything below marked
**[V]** was executed; domains stated inline.

### 7.1 Definition

For $B \neq \epsilon$ or $B = \epsilon$ alike (see the flag below):

$$[A/\hat{B}]\,E \;=\; \begin{cases} A\cdot E[|B|{:}] & B \sqsubset E\\ E & \text{else}\end{cases}
\qquad [A/B\$]\,E \;=\; \begin{cases} E[:|E|{-}|B|]\cdot A & B \sqsupset E\\ E & \text{else}\end{cases}$$

The calculus $\mathrm{ANC}$ = the paper's expression grammar with the node
$[R/P]\,E$ replaced by these two anchored nodes (both sides available; the
$-only and $-only fragments are rev-conjugate, Theorem thm:conjugation
applies verbatim).

**SEMANTIC CHOICE, flagged prominently (coordinator's request):** the empty
pattern is **defined** when anchored — $[\,A/\hat{\epsilon}\,]E = A\,E$ and
$[\,A/\epsilon\$\,]E = E\,A$ — because the anchored occurrence of $\epsilon$
is unique (position 0 / the end), unlike "all occurrences of $\epsilon$"
which is what makes the baseline $[A/\epsilon]$ ill-posed.  This choice is
load-bearing: it gives prepend/append for free, it makes the guard of the
L-simulation total (Sec. 7.4), and it is what lets `head`/`isne` handle the
$\epsilon$ edge cases without scaffolds.  A paper section would need to state
it as the definition's edge clause.

### 7.2 Toolkit — what survives (all constructions machine-verified)

* **tail / init.**  The naive products $\prod_{\sigma}[\epsilon/\hat{\sigma}]$
  and $\prod_\sigma [\epsilon/\sigma\$]$ are **wrong** — caught by the machine
  check, not by my hand derivation: the factors interfere ($[\epsilon/\hat
  a][\epsilon/\hat b]$ deletes TWO characters on `ba`; each order is killed
  by one input).  The correct construction is the once-toolkit's Doubled
  Marker lemma (paper lem:doubled) transplanted onto the scaffold $XXX$:
  $XX\sigma$ is a prefix of $XXX$ iff $\sigma = X[0]$, $\sigma XX$ a suffix
  iff $\sigma = X[-1]$, and after a factor fires the others are inert BY
  LENGTH.  So
  $$\mathtt{tail}(X) = \prod_\sigma [\epsilon/\widehat{XX\sigma}](XXX),
  \qquad \mathtt{init}(X) = \prod_\sigma [\epsilon/(\sigma XX)\$](XXX).$$
  **[V]** all 511 strings $\le 8$ over $|\Sigma|=2$, exact.
* **cat** $= [\,X/\hat a\,][\,Y/b\$\,](ab)$ — same shape as the once-toolkit's
  cat.  **head** $= [\epsilon/\mathtt{tail}(X)\$]\,X$ (the tail of $X$ is
  always a suffix of $X$).  **last** $= [\epsilon/\widehat{\mathtt{init}(X)}]\,X$
  (the init is always a prefix).  **doubling** $=[\,XX/\hat X\,]X$ — ONE pass.
  **rest**$(X,Y) = [\epsilon/\widehat{Y d}][\,Yd/\hat Y\,]X = X[|Y|:]$ if
  $Y \sqsubset X$, else $X$.  **[V]** cat/rest on all $63{\times}63$ pairs
  $\le 5$; unary items in the 511-string sweep.
* **isne**$(X) = [\epsilon/\mathtt{tail}(X)\$]([\top/\hat a][\top/\hat b]X)$:
  the head-passes mark a nonempty input $\top\cdot X[1:]$, whose suffix is
  exactly $\mathtt{tail}(X)$.  **[V]** exact on all 511 strings $\le 8$.
* **eq — the round's surprise.**  With $T = \mathtt{rest}(X,Y)\cdot\mathtt{rest}(Y,X)$
  (so $T = \epsilon \Leftrightarrow X = Y$, an easy case analysis):
  $$W = [\top/\hat T\,](a),\quad V = [\epsilon/(\top a)\$](W),\quad
    f = [\top/\hat V\,](b).$$
  Over $|\Sigma| = 2$: $f = \mathtt{ba}$ if $X = Y$, a single character
  otherwise — **equality with a two-valued false branch**.  **[V]** 1,245
  exhaustive pairs (all $|X|,|Y| \le 4$) + 3,000 random pairs $\le 7$.
  Over $|\Sigma| \ge 3$ the false branch collapses to a clean boolean
  $[\,c/\widehat{cb}\,][\,a/\hat b\,]f \in \{\top,\bot\}$.  **[V]** 16,427
  exhaustive pairs, all $|X|,|Y| \le 4$ over $\{a,b,c\}$.  The binary
  obstruction is structural in this family: every variant makes both false
  values *prefixes* of the true value, and with two letters there is no
  third character to break the collision.  **Clean binary eq: open**
  (absent from every searched space, Sec. 7.5).  `if` is likewise open
  (the conditional splice $[A/\widehat{\top d}](C\,d)$ — fires iff the
  computed condition equals $\top$ — is the seed; over $|\Sigma|\ge 4$ a
  two-scaffold construction is sketched but NOT verified: do not claim).

### 7.3 The web: strict containment in L, unconditionally

**Theorem (ANCHORED $\sqsubseteq$ L).**  Every anchored expression is an
L-expression.  Translation: with the comma code ($\mathtt{enc}^2_x$, code
words $xc$, images $aa$-free) and ONE marker per side
($m_0 = xb^2$, $m_1 = xb^3$, both containing $bb$):

$$[\,A/\hat B\,]E \;\mapsto\; \mathtt{dec}^2\big([\epsilon/m_0]\,
  [\,m_0\,\mathtt{enc}^2(A)/\,m_0\,\mathtt{enc}^2(B)\,]\,(m_0\,\mathtt{enc}^2(E))\big)$$

and mirrored for $\$$.  **Guard lemma:** $m_0\,\mathtt{enc}^2(B)$ occurs in
$m_0\,\mathtt{enc}^2(S)$ *iff* $B \sqsubset S$; $\mathtt{enc}^2(B)\,m_1$
occurs in $\mathtt{enc}^2(S)\,m_1$ iff $B \sqsupset S$.  (The guard needs
ONE marker, not two: with markers at both ends the pattern straddles the
$m_0 m_1$ junction when the code is short — a real bug the machine check
caught at $S = \epsilon$, $B = a$: $m_1$ begins with the valid code block
$xa$.  One marker kills all straddling: the pattern must contain $m_i$,
which occurs exactly once.)  **[V]** guard lemma 3,810 biconditional checks
($|S| \le 6$, $|B| \le 3$); node-level simulation 28,350/28,350 exact
(all $|A|,|B| \le 3$, $|S| \le 5$, both sides); full translation of 400
random anchored ASTs (depth $\le 3$) 1,200/1,200 exact, cross-checked with
the independent evaluator of `rec/lazy_pass/core.py`.

**This is prop:last's technique, promoted from a trick to a theorem.**  The
proposition plants a fresh anchor ($bb$) at the right end and tests constant
patterns containing it; the translation plants the comma-code marker and
tests *variable* patterns containing it.  The echo the coordinator asked
about is exact: the anchor does precisely the work of the marker, and the
price of the promotion is the code (escape, test, unescape) — which is why
$\mathrm{ANC}$ keeps $\mathtt{last}$/$\mathtt{init}$ natively in one pass
but pays a full encoding round trip for everything else.

### 7.4 The measure lemma (a single generalization of the four once-invariants)

**Lemma (CORRECTED after coordinator review — the one-sided split of the
R2 draft was refuted).**  Let $\mu$ be nonnegative with (i) $\mu(xy) \le
\mu(x) + \mu(y) + k_\mu$ and the TWO-SIDED split (ii) $\mu(y) \le
\mu(xy) + \mu(x)$ and (ii') $\mu(x) \le \mu(xy) + \mu(y)$.  Then for
every anchored expression $E$:
$$\mu\big(\llbracket E \rrbracket(\vec S)\big) \;\le\;
  \textstyle\sum_{\text{leaves of } R,P,E \text{ subtrees}} \mu(\text{leaf value})
  \;+\; k_\mu\cdot\#\text{nodes}(E).$$
For suffix-monotone $\mu$ (substrings never exceed: $\#c$, length, max run,
occurrence counts) the pattern subtree can be dropped.
*Why two-sided:* the $\hat{}$-node keeps a SUFFIX of the scrutinee (bounded
by (ii)), the $\$$-node keeps a PREFIX (bounded by (ii')); neither split
implies the other.  **Counterexample to the one-sided version (coordinator's,
machine-confirmed in R3):** $\mu(w) = 1$ if $w$ ends with $a$ else $0$
satisfies (i) with $k_\mu = 0$ and (ii), but violates (ii') ($\mu(a) = 1
\not\le \mu(ab) + \mu(b) = 0$), and the single node
$[\epsilon/b\$](ab)$ — which fires — has $\mu(\text{output}) = 1$ against
a leaf budget of $0$.  All 8 measures tested in R2 satisfy (ii')
(equality for counts and length, embedding-monotonicity for max run and
occurrence counts, the triangle inequality for $|\mathrm{bal}|$), so the
360,000 R2 checks remain valid verbatim under the corrected statement.
The ONCE/$L_k$ node keeps a prefix AND a suffix of the scrutinee, so the
same two-sided hypothesis is what the classical four invariants need —
in R3 the family version is stated with it.  The four
once-invariants of thm:once-invariants are the instances $\#c$, max run,
$|\Psi|$, length; the lemma adds e.g. occurrence counts of any fixed word.
**[V]** 192,000 uniform + 168,000 tight checks over 3,000 random anchored
expressions (depth $\le 3$) $\times$ 8 input pairs $\times$ 8 measures
($\#a$, $\#b$, len, maxrun, $|\mathrm{bal}|$, $\#occ(ab)$, $\#occ(aab)$,
$\#occ(ba)$): ALL HOLD.  **The same lemma holds verbatim for ONCE and every
$L_k$** (one splice per pass, same node computation) — this is the uniform
separation for the whole single-site family, and it is R3's starting point.

**Corollary (placement).**  None of $[a/b]$, $\mathtt{enc}$, $\mathtt{dec}$,
$[xx/x]$, $S\mapsto\sigma^{|S|}$, $X \mapsto X^{|X|}$, $\mathtt{escape}_f$ is
anchored-reachable (the paper's cor:once-sep transfers verbatim); together
with Sec. 7.3, $\mathrm{ANC} \sqsubset L$ **strictly and unconditionally**
— the first §5-family variant with a *proven* placement relative to L
(once/positional/right-to-left all hinge on open problems).

### 7.5 Searches (re-runnable: `verify_r2.py` part E)

* Anchored const-pattern space (patterns, replacements of length $\le 2$ incl.
  $\epsilon$, both sides), depth $\le 3$: **279,521** distinct functions on
  the 62 test strings ($\le 5$ over $|\Sigma|=2$).  ABSENT: `isne`, `rev`,
  once-$[a/b]_1$, $\sigma^{|S|}$, is-$\epsilon$.  Depth $\le 4$ with the
  reduced vocabulary $\{\epsilon,a,b,ab,ba\}$: **688,499** functions; same
  targets ABSENT.
* Anchored variable-pattern space (vocabulary $\{X, Xa, Xb, aX, bX, a, b,
  \epsilon\}$ in pattern and replacement), depth $\le 2$: **1,298** functions;
  same targets ABSENT (consistent: the real constructions are deeper — `isne`
  needs the $XXX$ scaffold inside its *pattern*).
* Once const-pattern space, depth $\le 3$: **38,959** functions; the anchored
  conditional $[a/\hat{ab}]$ ABSENT, $[a/b]_1$ FOUND at depth 1 (sanity).
  Note: $[a/\hat{ab}]$ IS once-expressible by the once-toolkit
  ($\mathtt{if}(\mathtt{eq}(\mathtt{prefix}_2 S, ab), \ldots)$ — all parts
  once-reachable), just not shallowly; the const-pattern once search only
  rules out shallow pipelines.  **Derived (not machine-verified): every
  CONSTANT-pattern anchored pass is once-expressible**; the open question
  is the variable-pattern prefix/suffix test (it needs variable-length
  prefix extraction — the once-calculus's own open hinge flavor).
* **rev: absent everywhere searched.**  The one-chunk normal form
  (output = $F(X)\cdot X[i{:}j]\cdot G(X)$, pieces = input chunks /
  prefixes-suffixes of sub-expression values / constant fragments, count
  bounded by the variable-leaf count) is the proposed obstruction; formal
  statement deferred to R5 (the piece-level induction needs the
  "which chunks are computable" analysis sketched in R1 Sec. 4.2).

### 7.6 Round-2 verdict for the map (row 7)

**ANCHORED = COLLAPSE (into L): a proper, provably strict, toolkit-rich
fragment.**  New knowledge produced: (1) the first unconditional strict
placement of any §5-family variant inside L; (2) the anchor-as-marker
theorem that IS prop:last generalized; (3) the measure lemma unifying the
four once-invariants for the whole single-site family; (4) eq-in-ANC with
the binary/ternary split (a new alphabet-sensitive boundary *within* a
variant, echoing §5.2's unary dichotomy); (5) two machine-caught
near-misses worth recording in the paper's methodology voice: the
interfering $\Sigma$-products and the two-marker guard.  Rows 8–9
(anchored mixes) stay for R5: the conditional-splice seed suggests
anchored+once may exceed both, but nothing verified yet.

---

## 8. Round 3 (deep dives 2+3): the k-th-occurrence family and rank-k Markov

All numbers: `verify_r3.py` (parts A–D), re-runnable.  The corrected
two-sided measure lemma (Sec. 7.4) is this round's part A and the shared
tool for the whole single-site family.

### 8.1 The two-sided measure lemma, machine-confirmed (part A)

* **Hypotheses checked** over all 127×127 string pairs (|x|, |y| ≤ 6 over
  binary): all 8 measures satisfy (i) μ(xy) ≤ μ(x)+μ(y)+k and the two-sided
  split (ii) μ(y) ≤ μ(xy)+μ(x), (ii') μ(x) ≤ μ(xy)+μ(y); the coordinator's
  counterexample measure *ends-with-a* satisfies (i), (ii) and **violates
  (ii') exactly at (a, b)** — and the negative control reproduces the bound
  violation on the single node [ε/b$](ab) (μ(out) = 1, leaf budget 0).
  One-sided split ⇒ no lemma; two-sided ⇒ lemma.
* **Family corpus:** 2,500 random expressions over the MIXED single-site
  node types (anchored ^/$, once, repOcc 0/1/2), depth ≤ 3, 8 input pairs
  each: general two-sided lemma **135,136 checks, 0 violations** (budget =
  R,P,E leaves + 2·k_μ per splicing node — once/L_k nodes have two
  junctions, anchored one); the four classical invariants (with the
  explicit recursions of thm:once-invariants, incl. the β-multiplicity for
  max run, which DOUBLES the variable contribution at every node): **0
  violations**.  (An earlier draft of the check with coefficient 1 for max
  run had 7 violations — the multiplicity is necessary; the paper's own β_i
  exists for exactly this reason.)
* **Asymmetry recorded:** ε-patterns are *undefined* for once/L_k (the
  greedy occurrence list of ε is ill-posed) but *defined* for anchored (the
  anchored occurrence of ε is unique).  3,108 undefined evaluations were
  skipped in the corpus accordingly.

**Consequence:** the paper's cor:once-sep transfers to every L_k: none of
replace-all, enc, dec, [xx/x], σ^|S|, X^|X|, escape_f is L_k-reachable.
The single-site family (once, every L_k, anchored, and their rev-mirrors)
is uniformly separated from L by one lemma.

### 8.2 The L_k ladder (part B) — an incomparability mosaic, not a hierarchy

Constant-pattern spaces (repOcc(k−1, pat, rep), patterns ≤ 2 chars,
replacements incl. ε), depth ≤ 3, 62 test strings ≤ 5 over binary:

| space | functions | [a/b]_1 | [a/b]_2 | [a/b]_3 | [aa/b]_2 | rev | σ^|S| | isne |
|-------|-----------|---------|---------|---------|----------|-----|-------|------|
| L_1 (= once) | 38,959 | **Y** | . | . | . | . | . | . |
| L_2 | 28,090 | . | **Y** | . | **Y** | . | . | . |
| L_3 | 2,307 | . | . | **Y** | . | . | . | . |

The membership matrix at this depth: **each [A/B]_j lives in its own L_j
and in no other L_k** — no simulation between constant-pattern L_j and L_k
(j ≠ k) exists at depth ≤ 3.  So the constant-k fragments are pairwise
incomparable (at bounded depth), not nested: the addressing axis does not
collapse inward.  rev/σ^|S|/isne absent everywhere (consistent with the
measure lemma).  Note the spaces SHRINK with k (38,959 → 28,090 → 2,307):
higher-rank passes fire less often, so the k-th-occurrence fragments get
poorer, not richer — addressing power does not buy breadth.

### 8.3 k=2 vs ONCE (part C) — the sharp question, both sides probed

* **The disjoint-marker route re-verified** (thm:pos-hinge(ii)):
  repOcc(k,B,A) = [M/B]₁^k[A/B]₁[B/M]₁^k with M a constant disjoint from
  B's alphabet: **18,522 exact agreements** (B over {a,b}^≤3, |A| ≤ 2,
  |S| ≤ 5, k ≤ 2, M = c over ternary).  So over |Σ| ≥ 3, k-th-occurrence is
  once-simulable whenever B misses a letter.
* **Over binary (no fresh marker exists):** the functions [a/b]_2, [a/ab]_2,
  [aa/b]_2 are **ABSENT** from (i) the once constant-pattern space of depth
  ≤ 4 — **969,321** distinct functions on the 31 test strings ≤ 4 (sanity:
  [a/b]_1 found at depth 1) — and (ii) the once variable-pattern space
  (vocabulary X, Xa, Xb, aX, bX, a, b) of depth ≤ 3 — **3,773** functions.
  Together with the ladder of 8.2 this is strong evidence that the
  constant-k calculi are a genuinely NEW sub-family: they are separated
  from ONCE at the node level over the binary alphabet (bounded evidence;
  no proof — the once-toolkit's eq/if might still simulate repOcc(k,B,A)
  for constant B via conditionals, the way it does for constant anchored
  passes).
* **Sharp statement for the paper:** over |Σ| ≥ 2, is [A/B]_2 (variable
  patterns) once-reachable?  The marking simulation needs an alphabet-
  disjoint marker, which cannot exist for variable B over |Σ| = 2; every
  bounded search fails; the once-toolkit route (condition on "≥ 2
  occurrences, remember the first") needs variable-length prefix
  extraction, the same open hinge flavor as once ∈ L.

### 8.4 Rank-k Markov (part D) — verdict: RANK-ROBUST COLLAPSE of the §5.5
phenomena; the census's own cap-sensitivity independently confirmed and
sharpened (lim agent's R1.8 cross-referenced)

* **Semantics correction (machine-caught by the D1 identity check):** the
  R1 reading "iterate until the string stops changing" is WRONG for A = B:
  a firing that changes nothing never becomes INERT, and the process
  diverges (the paper's own Markov agrees: A = B diverges, thm:termination
  (iii)).  Correct fixpoint: iterate while the pass FIRES (≥ k+1 greedy
  occurrences); k = 0 then coincides with restart VERBATIM, A = B
  included.  `systems.py` rankm and `verify_r3.py` run_rank both
  corrected.

* **D1 (identity).** rank-0 ≡ `restart` verbatim (corrected semantics):
  8,000 exact agreements (`verify_r3.py` part D).
* **D2 (termination census, 930 binary rules |A| ≤ 4 incl. ε, 1 ≤ |B| ≤ 4,
  all 1,023 inputs |S| ≤ 9; `verify_r3.py` part D, cross-checked by
  `census_par.py` with Pool(24) — identical numbers).**
  * rank 0: **170 divergent at caps below (3,280 steps / 6,569 length);
    166 at adequate caps** — reproducing BOTH the paper text (170; its
    verify scripts run at caps 2,500–4,000) and the paper's own scripts +
    `restart.md` + the lim census (166; `restart.md` records 764 total /
    166 divergent at cap 200k).  The 4-rule difference is the
    **cap-sensitive family [aaab/ba], [abbb/ba], [baaa/ab], [bbba/ab]**.
  * **The cap-sensitive family** (`probe_slow.py`, `probe_boundary.py`):
    TOTAL on all inputs ≤ 9 — worst **3,280 steps, output length 6,569**,
    on the 1-parameter family b^n·a (for [aaab/ba]); the cascade obeys
    **steps(n+1) = 3·steps(n) + 1 exactly** (3,280 → 9,841 → 29,524 →
    88,573 for n = 8…11) with output length 2·steps + n + 1: a TOTAL rule
    with exponential runtime, inside the paper's open class (v).  From
    input length 12–14 on, sampled inputs exceed every practical cap
    (witnesses: [baaa/ab] at length 12, the others at 14; length-18
    witnesses exceed (10^5 steps, 10^6 length)); true divergence
    unproven.  This independently confirms and sharpens the lim agent's
    R1.8/R1.5 erratum (paper text: 170 → should be 166 + four; my
    additions: the exact worst-case numbers on the domain and the
    tripling law).
  * rank 1: **166 divergent = the SAME set as adequate-cap rank 0** (162
    with B ⊂ A + [aabb/ba], [abba/bab], [baab/aba], [bbaa/ab]); robust at
    5× caps.  The "4 cures at rank 1" seen at low caps are precisely the
    cap-sensitive family — not cures: their slow ≤ 9 inputs carry a
    SINGLE greedy occurrence (rank ≥ 1 never fires: 0 steps), and at rank
    1 the family still fails on longer inputs (witnesses at length 20–23,
    caps (10^4, 10^5)).
  * rank 2: **148 divergent; the 18 "cures" vs rank 1 are ALL short-domain
    artifacts**: 16 A = B, |A| = 4 rules (need ≥ 3 non-overlapping
    occurrences = 12+ chars: never fire on ≤ 9; on 24 chars they diverge
    genuinely — [aaaa/aaaa] on a²⁴ fires forever) plus [abba/bab],
    [baab/aba] (fail at caps (2·10^4, 2·10^5) on 24-char inputs; genuine
    divergence unproven).
  * **created: none at either step** — and robust beyond the domain: 200
    random rank-0-total rules × 8 random inputs of length 10–24 at caps
    (10^4, 10^5): **0 flags** (`verify_r3c.py` D6).
* **D3′ (growth census, `verify_r3c.py`; criterion: exponential iff
  max-output f satisfies f(9) ≥ 64 ∧ f(7) ≥ 16 ∧ f(5) ≥ 4; superlinear iff
  f(n) > n+5; caps 50,000 with an 80%-of-cap recheck — none triggered).**
  Among the 162 rules |A|,|B| ≤ 3, B ⊄ A (the paper's growth subdomain):
  * rank 0: 146 linear / 12 superlinear / **4 exponential — the amplifier
    family [baa/ab], [aab/ba], [abb/ba], [bba/ab], exactly the paper's 4**
    (paper: 140/18/4; same 158-rule non-exponential set and same 4
    exponential rules — the 140/18 vs 146/12 difference is purely the
    linear/superlinear calibration, no rule-level disagreement).
  * **rank 1: IDENTICAL buckets and IDENTICAL rule lists.**  The growth
    classification is rank-invariant.
* **D4′ (amplifier at rank k on FIRING inputs (ab)^m).**  Output lengths
  m = 1…8: rank 0: 2^{m+1} − 2 + m (518 at m = 8); rank 1: 2^m − 1 + m
  (263); rank 2: 2^{m−1} + m (136) — **exponential at EVERY rank, the
  leading term halving as k grows.**  The earlier D4 reading ("amplifier
  breaks at rank 1 — linear on ab^{n−1}") was an input-family artifact:
  ab^{n−1} carries a single occurrence, so rank ≥ 1 is inert there.  The
  rank-1 output is NOT of the clean b^#b·a^{v′} closed form (all strings
  ≤ 8 checked): the Horner invariant breaks as a formula, but the growth
  survives.
* **Verdict (row 6).**  **rank-k Markov = COLLAPSE (rank-robust) on the
  census domain:** k = 1, 2 reproduce rank 0's termination census (at
  adequate caps) and growth buckets exactly; every apparent difference
  (170 → 166 → 148) dissolves under cap- and domain-sensitivity analysis.
  The FUNCTIONS differ with k (single-rule outputs: 263 vs 518 on (ab)^8),
  so the operators are distinct as function classes — but the §5.5
  phenomena (divergence census, growth dichotomy shape, amplifier) are
  rank-invariant.  New knowledge produced: (a) the census cap-sensitivity
  map (thresholds 3,280 steps / 6,569 length; the tripling law of the
  slow family — independent re-derivation + sharpening of the lim
  agent's erratum); (b) rank-invariance of the growth census; (c) the
  amplifier's rank-robust exponential growth with halving constant;
  (d) the semantics correction (inertness = "the pass fires", not "the
  string changes" — A = B).

### 8.5 Round-3 verdicts for the map

* **Row 5 (L_k): NEW — an incomparability mosaic, separated from ONCE.**
  Not a hierarchy (spaces shrink with k; each [A/B]_j in its own L_j at
  depth ≤ 3); separated from ONCE at the node level over binary by
  exhaustive absence ([a/b]_2-type absent from 969,321 + 3,773 + 688,499
  + 1,298 once-functions); over |Σ| ≥ 3 the marking chain simulates
  repOcc(k) (18,522 agreements), so the ONCE-vs-L_2 question reduces to
  marker freshness — the §5.2 hinge's alphabet-sensitivity reappearing
  inside the k-th-occurrence axis.  L ⊄ L_k by the two-sided measure
  lemma.
* **Row 6 (rank-k Markov): COLLAPSE (rank-robust) — Sec. 8.4.**  With the
  erratum-grade byproduct: the paper's census number is cap-sensitive
  (170 below 3,280 steps, 166 above; the lim agent's R1.8 found this
  first — my numbers agree and add the tripling law).


---

## 9. Round 4 (deep dive 4): the FLAT LAZY-PASS calculus — verdict:
COLLAPSE into L as PARTIAL FUNCTIONS, via an explicit translation; laziness
adds DEFINEDNESS, not power

All numbers: `verify_r4.py` (parts A/B), `verify_r4b.py` (the translation),
`verify_r4c.py` (depth-3 + occurrence unit test), `r4_analysis.py` (the
denotation-space census).  My flat evaluator is cross-checked against the
paper's own machines (`rec/lazy_pass/core.py` `run_lazy`/`run_eager`):
1,500 random expressions x 15 inputs x both runtimes: **0 mismatches**.

### 9.1 The system

The call-free slice of the paper's lazy-pass runtime (Sec. 6 / prop:lpcons):
node $[R/P]E$ forces the scrutinee $E$ and the pattern $P$; the replacement
$R$ is forced only if $P$ occurs in $E$'s value; $P = \epsilon$ is
undefined in BOTH runtimes (the pattern is forced).  Eager forces $R$
always.  Flat = no calls, so no divergence: the only undefinedness is the
$\epsilon$-pattern.

### 9.2 lpcons, re-verified far beyond the paper's 9,000 expressions

Exhaustive depth $\leq 2$ space (599,844 expressions over
$\{\epsilon, a, b, X, C, S\}$) x all 31 inputs $|S| \leq 4$:
* **exact value agreement on every eager-defined point: 7,242,300**
  (paper: 9,000 random expressions);
* **1,141,408 lazy-only definedness points** (~6% of the space);
* faithful mechanism check (the eager-undefined node lies inside a
  subtree the lazy run discarded): 374,364 sampled points, **0
  violations** — "strictly more defined only through discarded
  replacements" confirmed.

### 9.3 The denotation spaces at depth 2 (r4_analysis.py)

4,834 distinct lazy denotations vs 4,837 eager (same syntax pool); 193
lazy-only denotations; only 7 distinct eager domains exist at depth 2
(star-complement shapes from $\epsilon$-valued depth-1 patterns).  The 193
lazy-only denotations' domains: 77 shapes, 76 not eager-realizable AT
DEPTH 2 — e.g. a-free/$b^*$ (witness $[[\epsilon/\epsilon]\epsilon/a]X$),
singletons, $S \not\vdash W$ complements — but every one value-extends
some eager denotation or has an eager domain shape.  Conclusion: the
difference at equal depth is real but shallow; the question is realizability
at ANY depth.

### 9.4 The collapse translation (NEW; machine-verified)

Three small lemmas make an explicit translation work (all over binary,
all in the paper's calculus via `rec/lazy_pass/toolkit.py` eq/if/cat):
* **Coercion** $g(X) = \mathtt{if}(\mathtt{eq}(X,\epsilon), a, X)$: total,
  $\epsilon \mapsto a$ — makes every pattern nonempty.
* **Occurrence** for TOTAL computed values $u, v$:
  $O(u,v) = \mathtt{if}(\mathtt{eq}(u,b),\ [bb/b]v \neq v,\ [b/g(u)]v
  \neq v)$ — sound because the replacement $b$ differs from the pattern
  on the else-branch, and $[bb/b]$ grows on firing.  (Unit test: 225
  value pairs, 0 undefined, 0 wrong.)
* **Guard** $[a/F]\,W$ with $F$ total $\{a,\epsilon\}$-valued: identity
  on $F = a$ ($[a/a]$ is the identity pass), undefined on $F = \epsilon$.

Recursive definitions (by structural induction on the flat expression):
* $\Phi(E)$ = value-part totalized: $\Phi([R/P]T) = [\Phi R / g(\Phi
  P)]\ \Phi T$ — TOTAL (no pattern is ever $\epsilon$), agrees with the
  lazy denotation on its domain.
* $F(E) \in \{\top,\bot\}$ = domain indicator: $F([R/P]T) = F_T \wedge
  F_P \wedge \mathtt{isne}(\Phi P) \wedge (\neg O(\Phi P, \Phi T) \vee
  F_R)$ — a CONJUNCTION (an implication would make an $\epsilon$-pattern
  vacuously defined); with $F$ of leaves $= \top$ and concatenation $=
  \wedge$.
* **$\mathrm{TR}(E) = [\,a\,/\,\mathtt{if}(F(E), a, \epsilon)\,]\ \Phi(E)$.**

**Theorem (machine-verified): for every flat expression $E$,
$\mathrm{TR}(E)$ under EAGER evaluation equals $\llbracket E \rrbracket$
under LAZY evaluation as a partial function** — same graph AND same domain:
* 193/193 lazy-only witnesses x 31 inputs: 0 mismatches; $\Phi$ total
  (0 undefinedness);
* 250 random depth $\leq 2$ + 120 random depth-3 expressions: 0
  mismatches (TR sizes up to ~31K nodes — polynomial blowup);
* escalation: 25 witnesses x all 127 inputs $|S| \leq 6$: 0 mismatches;
* TR cross-checked against the paper's own `run_eager` machine: 0
  mismatches.

So the flat lazy-pass calculus $=$ L as partial functions: the paper's
lpcons characterized the mechanism of the extra definedness; TR shows the
extra definedness is always eagerly realizable.  "Laziness adds
definedness, not power" — the call-free slice of the §6 border is exactly
on the L side, and the universality of lazy passes is genuinely a
RECURSION phenomenon (needs the gate), not a flat one.

### 9.5 Verdict for the map (row 12)


---

## 10. Round 5 (final): rows closed, the two paper drafts, the map

* **Rows 1–3 closed** (`verify_r5.py`, `verify_r5b.py`): row 1
  once+rescan = ONCE (2,646 checks, 0 mismatches); row 3 once+restart
  (node) = MARKOV (2,646 agreements, 0 mismatches); row 2 CORRECTED —
  the R1 hand-derivation held only for step-granularity; pass-granularity
  (iterate the full unsafe pass) differs from MARKOV ([aba/bab] on
  'bbabb': 'baaba' vs 'abaab'; 9,322 agreements, 2 differences) — a small
  new fact recorded in the map.
* **Draft (a)** `draft_flatlazy.tex`: Theorem (flat lazy passes denote L)
  for the paper's §6, in the paper's voice and notation — the TR
  construction with the coercion, occurrence and guard lemmas, the
  conjunction-scoped domain indicator (the coordinator's R5 catch),
  the verification note, and the placing paragraph against
  thm:lazyargs/prop:lpcons (the gate needs the loop).
* **Draft (b)** `draft_Lk.tex`: Proposition (k-th-occurrence family) for
  the §5 landscape — invariants transfer (L ⊄ L_k), the mosaic ladder
  (diagonal membership, shrinking spaces), the marker-freshness hinge vs
  ONCE — plus a landscape-table row.
* **Survey rows 8–11, 13: NOT REACHED** — honestly marked in the map; the
  shortlist rationale (Sec. 5) remains for any future round.
* **The map (Sec. 3) is final** — all rows carry verdicts and pointers to
  the verification scripts.

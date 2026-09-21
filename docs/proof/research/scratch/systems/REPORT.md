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
* R2: deep dive 1 — ANCHORED.
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
| 1 | once + rescan ([A/B]₁^u) | B=once × C=rescan | **COLLAPSES to ONCE** | a once-pass performs ≤1 match; unsafe vs safe differ only in where the scan RESUMES after a match — with no further match, identical. 1-line proof, verify on small grid. |
| 2 | rescan + restart ([A/B]^um) | C=rescan × C=restart | **COLLAPSES to MARKOV** | restarting from 0 re-scans everything, inserted text included; the rescan clause is subsumed. |
| 3 | once + restart, node level ([A/B]₁ iterated to fixpoint) | B=once × C=restart | **COLLAPSES to MARKOV** | iterate "replace leftmost occurrence, rescan from 0" = Definition def:markov verbatim. |
| 4 | once + restart, expression level (whole once-pipeline to fixpoint) | B=once × C=restart × E | **COLLAPSES to KNOWN: multi-rule Markov / semi-Thue** | iterating a k-pass pipeline to its joint fixpoint = leftmost-strategy normalization of a k-rule system; classically Turing-complete for enough rules (post47, markov54). No new phenomenon; record only. |
| 5 | once + positional (= constant-k repOcc, no setAt) — the family **L_k** | B=k-th | **NEW-? (deep dive 2)** | single-splice invariants all hold (Sec. 4.1) ⇒ L ⊄ L_k as for ONCE; fine structure L_j vs L_k open; thm:pos-hinge(ii) simulates repOcc(k) with onces ONLY under alphabet-disjointness, so variable-pattern k=2 vs ONCE is sharp. |
| 6 | positional + restart — **rank-k Markov** | B=k-th × C=restart | **NEW-? (deep dive 3)** | iterate repOcc(k,B,A,·) to its fixpoint. k=0 = Markov. Termination/growth censuses comparable to the paper's 170-rule census; the amplifier's Horner invariant BREAKS at k ≥ 1. |
| 7 | **anchored** calculus ([A/^B], [A/B$]) | B=anchored | **NEW-? (deep dive 1)** | boundary-only splices; single-site invariants hold; cat/tail/init/head/last appear reachable (Sec. 4.2); rev conjecturally NOT anchored; relation to ONCE and L_k sharp. |
| 8 | anchored + once ([A/^B] + [A/B]₁ mixed) | B=anchored × B=once | NEW-?, survey after deep dive 1 | does anchoring give once-power cheaply, or vice versa? |
| 9 | anchored + k-th | B=anchored × B=k-th | NEW-?, survey | "replace the last occurrence of B" — anchors make rightmost addressing expressible in a LEFT-to-right scan; worth one paragraph. |
| 10 | **wildcard patterns** ([A/B′], B′ has don't-care characters) | D=pattern language | NEW-?, survey-grade | does [A/X1*], [A/**] collapse to L (Σ-fold expansion for trailing wildcards; comma-code parity for [A/**])? quick battery. |
| 11 | **native multi-pattern one-sweep** (first-match-wins per position, priority list) | D=multipattern | NEW-?, (deep dive 5 if time) | provably ≠ freezing semantics: pairs [(b,X),(ab,Y)] on "aab": native = aY, freezing = aaX (verified in systems.py smoke test). Is the constant-pattern fragment inside constant-L (both are left-subsequential; composition question)? Is the variable fragment inside L? |
| 12 | flat lazy-pass calculus (no calls, lazy replacement forcing) | §6 runtime axis, flattened | **NEW-? (deep dive 4)** | by lpcons it extends L's partial functions by definedness on discarded replacements exactly; question: does it COLLAPSE back to L as partial functions? dom(f_lazy) vs L-domains; the rem:total-rep guard trick does not obviously generalize. |
| 13 | inward fragments of L: delete-only ([ε/B]); single-char patterns; length-preserving (|A|=|B|); insert-only | G | NEW-?, survey | which retain cat/head/tail/eq? census methodology turned inward. |
| 14 | L+R union | A† | other agent | — |
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

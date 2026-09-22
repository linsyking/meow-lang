# ROUND 16 REPORT — THE UNIFICATION PROBLEM (Lane C)

[Transcribed by the coordinator from the lane's final message,
2026-09-22. Machine artifacts on disk: verify_r16.py, r16.log (incl.
the think-pass recorded before machine work), verify_r16_coord.py +
r16_coord_verify.log (coordinator's verification battery — ALL
VERIFIED). Coordinator's OVERVIEW entry is the verification record.]

**Verdict: IMPOSSIBLE.** No fixed expression E in Exp computes rev on
all of {a,b}*. This is delivered as an architectural proof: one core
lemma is fully proved by hand, the descent is formulated precisely
with both escape routes identified and killed on analysis, and the
two remaining formalization lemmas are stated exactly (both live
squarely in Lane B's program — statements below). Per the charter the
pure-think pass came first; the obstruction was written down before
any machine work (r16.log). Two positive byproduct families fell
during the hunt and are machine-verified.

## 1. The reformulation that organizes everything

rev on {a,b}* is not "swap letters" — it is the **mirror-plant**:
reflect the b-positions about the center of the a-material, i.e.,
reverse the gap/run sequence (i_0, i_1, …, i_k) → (i_k, …, i_1, i_0).
Equivalently: write the merge a^S (S = total a's) and plant each b at
depth equal to its right-a-count in w. Every mechanism we have ever
found for reversing (E_rev, the engine, block-swap, phase-swap) is a
way of buying that plant. The question is whether a FIXED DAG can buy
unboundedly many plants.

## 2. The proved core: the Final-Pass Lemma

One sweep is a uniform interleave: **out = q_0 R q_1 R … R q_t**,
same R at every firing, remnants q_i in scrutinee order.

**Lemma FP (PROVED by hand).** Suppose E = [R/P]F and E(w) = rev(w)
for all w in the super-increasing family w^(k) = a^{2^0} b a^{2^1} …
b a^{2^k} (k varying). Then for each large k:
1. **R is single-b or pure**: if R's value had an interior a-run,
   that run's text is emitted at EVERY firing, so the output's run
   list repeats a value; rev(w^(k))'s run values are the distinct
   powers 2^k…2^0, each exactly once — so any nonempty interior
   forces t = 1, and a t = 1 final pass changes nothing structural
   (single splice; the reversal must then already live in F up to
   that splice — the descent applies directly).
2. Hence the output's run list is **exactly** the remnant stretches
   of F concatenated in F-order, separated by single b's, each
   remnant run tweaked by at most the two boundary bites of the
   adjacent windows — bites that are the SAME (p0, p1) at every site
   (one pattern, one greedy).
3. Consequently: **rev(w^(k))'s run list is an in-order extraction
   from F's run list** (delete window material), with per-element
   tweaks from a fixed finite set of uniform subtractions.

[Coordinator's scrutiny notes: the proof is correct, including the
b^m (m ≥ 2) exclusion by consecutive-b's; WRITEUP PRECISION: the
tweak set includes ADDITIVE contributions from R's flanks
(a^{m1} b a^{m2} merges its flanks into adjacent remnant runs), so
the finite tweak set is {−p0, −p1, +m1, +m2}; q_0 and q_t have only
one bite each. Lane B's round 3 independently proved the ≤-one-b
conclusion as its Theorem FP, machine-checked 4000 cases + E_rev
343/343 with t = 1.]

## 3. The descent, and why both escapes die

The descent: FP(3) says F's run list contains the reversal as an
in-order subsequence with uniform tweaks. Recurse into F =
[R'/P']F': those reversal-runs come from F'-remnants (F'-order) or
from the **interiors of the t' copies of R'**, as contiguous kept
pieces. Two apparent escapes, both killed on analysis:

**Escape A (stratified picks across many copies).** Copies of one R'
with many distinct interior values could donate one element each,
values stratified across copies (copy c's picks all exceed copy
c+1's). This is a REAL phenomenon — it refuted the first bound
(ledger below) — but it cannot build the reversal: the kept pieces
from different copies must occupy pairwise disjoint value ranges
(they sit at strictly decreasing positions of the output), so
R'-interior must contain that many distinct deep values at disjoint
positions *as contiguous decreasing stretches*; and distinct deep
values are distinct input runs, so R' itself must already contain a
deep-rich decreasing structure — the descent recurses into R'
unchanged.

**Escape B (phase carving).** Let the copies be of an X-like
(increasing) R', and let the FINAL pass's windows carve a different
run out of each copy, the carve depth controlled by the greedy phase,
i.e., by the F-side remnant lengths between firings. The kill is a
**deletion-rate/tuning argument**: to carve run 2^j out of a copy,
the windows must consume the adjacent runs 1,…,2^{j−1} and the
material after — runs whose lengths are dominated. A pattern bites at
most (p0+p1) from any single run per adjacent firing, and pattern
flanks are pinned values (≈ αS+β, Lane B's schema): only the
top-O(depth) run-sizes 2^j (j ≥ k+1−m for α = 2^{−m}) are bitable by
big-flank patterns, while deep runs are only bitable by constant or
tweak-flanked flanks — and each distinct deep run-size needs a flank
tuned to that size. A fixed pattern has finitely many runs; tuning to
~k distinct depths needs ~k patterns, i.e., **Ω(k) S-nodes: the size
lower bound, consistent with the engine's Θ(k²) size and Θ(k)
depth.** (The descent also self-identifies: the phase sequence needed
to walk the carve from 2^k down to 2^0 is the power sequence itself —
the reversal — so the deeper level must encode the reversal as
remnant lengths, and the recursion terminates at X, which is
increasing.)

**The quantitative conclusion (conjecture-grade until the two lemmas
land):** any E reversing the k+1 super-increasing runs has #S-nodes
≥ Ω(k) — the mirror-plant needs ~k plants and each S-node supplies
O(1) of them once the pinned schema fixes what a computed
flank/tweak can be. A fixed E has fixed #S-nodes, so it fails for k
beyond its bound. Contradiction: **no fixed E reverses all of
{a,b}\*.** With E's own constants, the failure is effective at
k > f(|E|).

## 4. What is needed from Lane B (exact statements)

1. **Pinned-schema at varying k (load-bearing).** For a fixed
   expression V, on w^(k) with S = 2^{k+1}−1: every a-run of V(w^(k))
   is either an **extraction tweak** (within a V-fixed constant of
   some input run 2^j) or a **pinned affine value** from a finite
   V-fixed set {αS+β}, and each pinned function sits at top-O(depth)
   run-sizes only — formally: the set of j-depths hit infinitely
   often by pinned values is finite. The L3 battery
   machine-illustrates this for a 6-value battery, k ≤ 6
   (tweak-or-affine, tolerance 8). The sharp form (exact equality, no
   tolerance) is what closes Escape B.
2. **The Telescope formalization** should absorb the Final-Pass
   Lemma + descent as its "no-progress" statement for computed
   (multi-run) patterns. Lemma FP is offered as a ready-made base
   case; the family w^(k) has all-distinct run values, which is what
   makes value-repetition arguments clean.

[Lane B round 3 has since delivered: Theorem FP (independent proof of
§2.1), Lemma SD, Theorem SB (the merge-free no-progress lemma),
Lemma DECOMP, Theorem MT — and located the remaining gap precisely:
the mergey regime, where the obstruction must be merge-sensitive and
live in run-length exactness (E_poll shows order-inversion is cheap
under merging). The coordinator's bridge note: MT(b)'s halver
degeneracy (totals are NOT functions of (S_a,k) in general) does not
kill lemma 1 on w^(k), whose residues the family pins itself — the
lemma must exploit the family's residue structure.]

## 5. Positive byproducts, machine-verified

- **P1 block swap (family falls):** {a^i b^k} → rev = b^k a^i by
  **skeleton separation**: B = [ε/a]X = b^k (pure-b skeleton, total,
  k-adaptive), mrg = [ε/b]X = a^i; E_block = [B/(X·b)]((X·b)·mrg).
  The scrutinee literally begins with the pattern value X·b (its
  only occurrence), single firing swaps cluster for material. Grid
  13² incl. all boundaries + 400 randoms to 200 + intermediates:
  VERIFIED.
- **P2 heavy-tail alternating (family falls):** {(ab)^k aa, k ≥ 1} →
  rev = a·(ab)^k·a by **phase swap**: R = [ε/'aa']X = (ab)^k,
  P = [ε/'aa']([ba/ab]X) = (ba)^k; (ba)^k occurs in w_k only at
  position 1; single firing. k = 1..44 + intermediates k = 1..14:
  VERIFIED. (k = 0 is the empty-pattern edge; claim is k ≥ 1.)
- **L1/L2 collapse facts** (used by the assembly analysis):
  [R/P](P·G) = R·G when P ∉ G; [R/V](mrg·V·mrg) = mrg·R·mrg for
  one-b V — 7³ W2 grid: VERIFIED.
- **L3 schema illustration:** on w^(k), k ≤ 6, a battery of computed
  values (mrg, skeleton, halver, doubler, del_last, del_first) has
  every run a tweak of some 2^m or affine in S: VERIFIED. E.g.,
  del_last's glued run 2^{k−1}+2^k = (3/4)(S+1) exactly — pinned.

## 6. Three letters do not help

The argument runs verbatim on any finite alphabet with ≥ 2 letters.
On Σ = {a,b,c}, apply the whole analysis to the a-runs with
separators b,c (the mixed-letter engine already handles every FIXED
structure over any finite alphabet); the Final-Pass Lemma, the
copy-stratification kill, and the tuning/deletion-rate kill are all
statements about run values and greedy mechanics, independent of
alphabet size. Conversely the a-free subfamily {b,c}* reversal is
Lane E's unbounded-alphabet case in miniature and is excluded for
the same reason. Scratch-letter encodings of run values cannot
escape: any encoding's runs are themselves run values subject to the
same pinned/tweak dichotomy and the same order-preservation
channels. So: the dichotomy is by structure (fixed vs varying
separator count), not by alphabet size (beyond |Σ| ≥ 2).

## 7. The dichotomy theorem (proposed statement for the paper)

**Theorem (String reversal in L — dichotomy).** Fix a finite alphabet
Σ, |Σ| ≥ 2.
(i) For every fixed separator word structure (r_0 τ_1 r_1 … τ_k r_k
with fixed k and fixed separator words τ_m), there is an expression E
with E(w) = rev(w) for all w of that structure, and prov(E, w) = ∅
(round 15C engine).
(ii) There is no single E with E(w) = rev(w) for all w ∈ Σ* — indeed
none for the a-run/b-separator strings with unboundedly many b's —
provided the pinned-schema (Lane B, §4.1) and the tuning lemma
(§4.2 / Escape B kill). Effective bound: failure by k > f(|E|) on
the super-increasing family.
(iii) Over an unbounded alphabet, reversal is not computable at all
(Lane E).
Part (ii) is the round-16 result; its two remaining lemmas are
stated in §4 with the hand proofs of everything upstream.

## 8. Honest ledger

- **PROVED (hand):** Final-Pass Lemma (§2) on the super-increasing
  family; collapse facts L1/L2.
- **VERIFIED-ON-STATED-DOMAIN (machine, this round):** E_block on
  {a^i b^k} (grids + 400 randoms); E_alt on {(ab)^k aa} for k =
  1..44; L1/L2 on 7³ W2 grid; L3 tweak-or-affine illustration k ≤ 6.
  All runs < 10 s.
- **CONJECTURED (architecture complete, two lemmas open):** the full
  impossibility — with the two gaps being exactly the pinned-schema
  at varying k (sharp form) and the deletion-rate/tuning lemma. Both
  have machine-illustrated evidence (L3) and hand arguments.
- **REFUTED BY OWN COUNTEREXAMPLE (recorded, not hidden):** the first
  invariant "LDS(out) ≤ 2^{S-depth(E)}" is FALSE — [X/'b']X has LDS ≈
  k at S-depth 2 (stratified single picks across copies). The escape
  is real and is why the correct descent carries value-stratification
  (disjoint value ranges across copies) rather than
  subsequence-counting alone.
- Superseded invariants from the think pass (leader-run,
  atom-counting, naive contiguous-decrease) — dead on
  merges/constant-stitching/shaves respectively.
- Domain notes carried over: families stated with runs ≥ 0 and the
  ≥ 1 subfamily explicit; grids include zero boundaries.

## 9. Artifacts

- verify_r16.py and r16.log — this round's battery (all VERIFIED).
- verify_r16_coord.py + r16_coord_verify.log — the coordinator's
  independent battery (ALL VERIFIED: fresh encodings, k=1..69 for
  E_alt, 500 randoms for E_block, the counterexample class [X/b]X
  and [X/a]X both dec ≥ k at depth 2, FP uniform-bite spot-check
  [bab/aa]X).
- CHARTER_unification.md — the charter.
- Round 15C assets unchanged: verify_t5_rev.py (+ addendum),
  verify_t6_general.py, and their logs.

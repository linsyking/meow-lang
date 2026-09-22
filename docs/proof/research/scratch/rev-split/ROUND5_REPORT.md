# ROUND 5 REPORT — rev-split lane: the term-ledger write-out on B >= 3 (Lane B)

Coordinator, 2026-09-22. Charter: CHARTER_ledger.md (L1'' from
skeleton to proof on D(k;3)). Machine artifacts: ledger3.c / ledger3 /
ledger3.log / ledger3_seed2.log (invocation in every run's first line;
second seed reproduces). Sources used: rev-wall/REPORT.md R3 (Lane D:
the family migration, the six B=2 constructions, L2.1/L2.2 PROVED),
rev-try/ROUND16_REPORT.md, my ROUND3/ROUND4 reports.

## 0. Verdict

The ledger theorem is delivered as a proof at write-out altitude with
ONE precisely-located skeleton piece (Lemma PO's general case), and
with TWO CORRECTIONS to the closure form that the paper needs before
part (ii) of the dichotomy is written — both found by trying to prove
the round-4 statement and both machine-witnessed:

- **C1 (the k-affine stratum is necessary).** E_last = [ε/b][a/aa]X on
  D(k;3) has value Σ⌈3^j/2⌉ = (S+k+1)/2 — machine-verified exactly
  (k = 1..8). The "+k/2" is real and irreducible: it is the collected
  per-run remainder Σ_j (3^j mod p), and since 3^j mod p is eventually
  periodic with period ord_p(3), every such collection is exactly
  (V-fixed)·k + (V-fixed) + (V-fixed periodic partials). The same
  stratum exists on B=2 (p = 3 patterns: [a/'aaa']X has runs
  (2^j+2)/3, (2^j+4)/3 — non-dyadic AND not captured by round 4's
  α-family; they slipped through round 4's battery inside its junk
  window at k ≤ 9 — disclosed). The closure's junk stratum is
  k-AFFINE, not bounded.
- **C2 (non-dyadic rational slopes).** Tiling corrections give slopes
  |R|_a/p (e.g. 6/7·3^j): denominators are V-fixed moduli (pattern
  lengths, products thereof), not just powers of 2 and 3. For Lane D:
  the SUPPLY slope set is rational with V-fixed denominators; L2.1's
  DEMAND side (exact cuts at offset d need dyadic B^{−d}) is untouched
  and the kill is STRENGTHENED — a non-dyadic supply slope never equals
  a dyadic demand (cross-multiplication: s ∤ 3^{Δ}·2^{d}).

Both corrections are instances of one law (Lemma COLLECT below), and
both are already inside the charter's phrasing ("closure under +, −, ×
by pinned counts") — but the paper's normal form must name them.

## 1. The corrected closure and the theorem

Family D(k;3) = a^{3^0} b a^{3^1} … b a^{3^k}, S = (3^{k+1}−1)/2;
strongly super-increasing; B = 2 recorded as the telescoping boundary
(Lane D R3.1).

**𝒞 (normal form).** v = Σ_{i≤M} q_i·3^{e_i} + (Ak+B) + β where:
q_i are rationals with denominators from a V-fixed finite set (2^d,
pattern moduli p, products — degree bounded by V's depth); e_i come
from V-fixed anchored exponent families {k−c, k+1−c} ∪ {j−c′} ∪ {c″}
∪ {e+e′ of these} (j = the run's site anchor); A, B, β V-fixed; and
M = the site-reference count.

**Theorem TL (term ledger).** Fix V. There are V-fixed families as
above and M_V ≤ 8·#S(V) + O_V(1) such that for every k and every
a-run r of V(D(k;3)):
(i) v(r) ∈ 𝒞;
(ii) M(r) ≤ M_V;
(iii) (boundary) for the first and last runs, M ≤ 2 and the exponents
are anchored top (k−c, k+1−c, products 2k+1−c, depth-bounded) or
bottom — never middle-depth.
Equivalently in measure form (the per-run multiset bound the charter
asked for): the run's site-measure μ_r = Σ_t n_t δ_t decomposes as
μ_r = Σ_{i≤M} c_i·ν_i + κ, where each ν_i is an interval-geometric
measure (Σ_{t∈[a,b]} 3^t δ_t), a site Dirac δ_t, or the full measure
σ, the c_i are pinned counts, and Σ|κ| = O(k+β) (k-affine junk).

NOTE for the paper: the honest coefficient is c ≤ 8 per S-node, i.e.
the bound is c·#S + O_V(1), not literally #S + O(1) with coefficient
1; whether the per-node charge can be driven to 1 is open. The Ω(k)
application only needs O(#S).

## 2. The proof (what is proved, and the one skeleton piece)

**(a) Lemma GLUE (proved).** By the round-3 FU calculus, a pass
output is q_0 R q_1 … R q_t, and every output a-run is an alternating
sum v(ζ) − v(bites) + c·v(ρ) where ζ is ONE contiguous span of F's
output (the union of consecutive remnants between the delimiting
output b's), the bites are the window-edge corrections at the span's
two ends, ρ is a full run of R (or R's boundary run fragments), and c
is a pinned count (c = 1 unless R is b-free, when c = the number of
windows in the span — a census count, Lemma S/MT). Case split: R
b-free vs b-containing; P b-free (windows inside runs) vs single-b
(each firing deletes one separator) vs multi-b (Lemma SD: ≤ 1 firing
on distinct-run scrutinees; on replicated scrutinees the count
machinery of MT applies). The E_prod mechanism (c·S products) and the
[X/'b']X class (input-shaped R, stratified picks) fall out of the
same two cases TOGETHER: a copy donates at most one run fragment per
output run when R has b's, and a pinned scalar multiple when R is
b-free — replication scales, it never adds references.

**(b) The interval-sum invariant (proved; the heart).** Track for
every node u: INV1 every run value is a 𝒟-value with ≤ n(u) refs;
INV2 every contiguous interval sum of u's run-value sequence is a
𝒟-value with ≤ n(u)+2 refs. Then:
- X: runs 3^t (1 ref); interval sums = (3^{b+1}−3^a)/2 — dyadic
  2-ref, Lane D's L2.1 arithmetic (PROVED, cited).
- K: constants.
- C(A,B): runs inherited; ONE seam = v(A-last)+v(B-first), a sum of
  two boundary values, which by (d) below is O(1) refs REGARDLESS of
  subtree depth. Crossing interval sums recurse into the two DISJOINT
  children: budgets add over disjoint subtrees only.
- S(R,P,F): an output run = span sum (INV2(F)) + c·(R-run value:
  INV1(R)) + bites (O(1)): n(S) ≤ n(F) + n(R) + O(1), and F, R are
  disjoint subtrees.
Telescoping over the tree: every contribution except the per-S-node
O(1) comes from disjoint subtrees, so n(V) ≤ c₁·#S(V) + (everything
else), and "everything else" — C-seams, bites, truncation corrections,
remainders — is a sum of at most |V| V-FIXED-family values, which
COLLECTS (Lemma COLLECT) into one V-fixed junk element: O_V(1),
k-independent. The fired-set structure (which separators a
single-b pattern deletes) NEVER ENTERS the bound: any contiguous
stretch of F's run sequence is covered by INV2. That is why the ledger
is robust where the profile is delicate.

**(c) Lemma COLLECT (proved; the correction generator).** Sums of
V-fixed-family values collect: α's collect into one S-term; bounded
constants into one V-fixed constant; top-pinned 3^{k−c} into ONE 3^k
term with dyadic coefficient (3^{k−c} = 3^{−c}·3^k — Lane D's slope
arithmetic); periodic-in-j remainders via 3^j mod p having period
ord_p(3) into (V-fixed)·k + (V-fixed) + (V-fixed partials). This
single lemma generates C1 and C2 and closes the arithmetic of the
proof.

**(d) Boundary Alignment on B=3 (migrated, WITH A CORRECTION).**
Working the battery exposed that my round-4 class list was incomplete:
E_prod's LAST run is 1+⌊3^k/2⌋·S ≈ 3^{2k+1}/4 — a count×S product, in
none of {bounded, αS+β, top-pinned, bottom-pinned}. The correct
statement is (iii) above: boundary runs carry ≤ 2 anchored terms with
exponents at top/bottom/product-of-top anchors, never middle-depth.
The round-4 induction (straight on expression size; the powers-descent:
middle-block patterns need middle-boundary children, BA-forbidden, or
window deletions into strictly smaller patterns) is base-agnostic and
migrates verbatim; B=3 introduces no new phenomenon (the halver
degeneracy does not appear on the family — the residues are pinned).

**(e) Lemma PO (pinned offsets) — the load-bearing input, and the one
skeleton piece.** Statement: every window-edge offset (truncation
length) in every pass of V on D(k;3) is a pinned 𝒟-value with ≤ 2
refs. Proved cases: P b-free (tiling arithmetic: offsets are multiples
of |P|'s value from run starts plus a phase that is pinned by
induction — the phase recurrence is the count machinery); P single-b
(fired separators form a threshold set of pinned run values; bite
sizes are differences of pinned values). Remaining gap, precisely:
the general case (multi-b patterns on REPLICATED scrutinees) needs
position pinning, not just count pinning — round 3's MT verifies the
counts (tiling (T_c−Λ)/p, computed moduli, anchored site conditions,
machine-verified), and Lane D's firing-count lemma (greedy leftmost =
max disjoint occurrences) pins the combinatorics, but the write-out
that the OCCURRENCE POSITIONS (not just their number) are pinned
per cell is not yet line-by-line. This is the only piece of TL at
skeleton altitude; TL is proved CONDITIONAL on PO.

## 3. The atoms lesson (why the ledger is value-level)

My first machine design this round (support-atoms = maximal
consecutive-label intervals of a run's label set) is WRONG in both
directions, machine-documented in [atoms]: dropab's merged run has
support-atoms 1 (one interval — collapses) with value S−k (1 term +
k-affine: consistent); E_prod's run j has support-atoms 1 but its
site-j reference rides the PINNED COUNT ⌊3^j/2⌋, invisible to the
support. The invariant must be stated (and checked) at the
value/measure level — as §1 does. Recorded so nobody re-derives it.

## 4. Machine record (rev-split/, total 0.16 s per full run)

ledger3.c / ledger3 / ledger3.log (seed 271828) / ledger3_seed2.log
(seed 314159 + two extended runs). **293 checks, 0 failures at both
seeds.**
- [forms] 255 exact checks: the 16-expression battery (the L3 six +
  E_leak, E_prod + Lane D's six B=2 degeneracy constructions + decb =
  [X/'b']X + dropab + third) on B=2 AND B=3, every run exactly
  matching the hand closed form. Highlights: E_last B=3 = (S+k+1)/2
  (the C1 witness); E_prod B=3 = 1 + ((3^j−1)/2)·S (the coordinator's
  derived form, confirmed); E_cbox/E_smm/E_h2 B=3 = (S−k−1)/2-family;
  the six constructions classify on B=2 in the closure (E_last =
  (S+1)/2 = α = 1/2 affine — exactly as the charter predicted).
- [ledger] battery: max 2 terms observed (bound 4). Random
  compositions (depth ≤ 4, k = 4..7): 4677 compositions across the
  three logged runs (1049 + 1040 + 2588), 370153 runs, 100%
  classified, max 2 terms. MEASURED CAVEAT ([spec]):
  at k ≤ 8 the closure lattice covers ~100% of the adversarial value
  range as well — the value-level check is a NECESSARY condition with
  no specificity at materializable scales (string caps cap k ≤ 12 on
  B=3; specificity needs k ≫ C_V). The load-bearing verification is
  [forms] (exact) + [msb3] (identities) + the proof.
- [ba3] all first/last runs of battery + 4677 random comps simple
  under the anchored ≤ 2-term check (same caveat).
- [msb3] the round-4 two-stratum budget identities hold VERBATIM on
  D(k;3): 559+578 per-node identities (Φ'(out) ≤ Φ'(F)+Φ'(R)+4+MJ),
  353+361 tree totals, 0 failures; E_poll B=3 witness: Φ' = k with
  MJ = 5187 / 145140 / 4007883 at k = 3/4/5 — the budget is
  B-agnostic, as expected.
- Process notes, disclosed: my first [shave] hand form was wrong
  (+1 vs −1: [b/ab] replaces the WINDOW 'ab' by 'b', consuming the
  a) — the exact-forms check caught it before anything was recorded
  (that is what the machine is for); two classifier designs were
  discarded with measured reasons (balanced-ternary weight
  miscounts dyadic terms — (3^t−1)/2 is one term with BT-weight t;
  free-rational fitting has no specificity at small k).

## 5. What this buys (interfaces + paper actions)

- The pinned schema on B ≥ 3 is now: TL (this round, conditional on
  PO) + Lane D's PROVED L2.1/L2.2 + D's demand side (in flight).
- Paper actions for Lane C: (1) the closure paragraph must add the
  k-affine junk stratum and the rational-slope denominators (C1, C2)
  — as stated in round 4 it is falsified by E_last-B=3 and
  [a/'aaa']-type values on both bases; (2) BA's class list needs the
  count×S product class; (3) write the ledger bound as c·#S + O_V(1)
  (c ≤ 8), not #S + O(1); (4) the B=2 record: the six degeneracy
  constructions classify on B=2 in the closure (machine-checked),
  consistent with the family-migration revision.
- For Lane D: supply slopes are rational with V-fixed denominators;
  the dyadic demand is unaffected and the supply/demand mismatch is
  strengthened (C2).

## 6. Honest ledger

PROVED (hand + machine-confirmed): GLUE; the interval-sum invariant
and its disjoint-subtree accounting; COLLECT (including the k-affine
law and both corrections C1/C2); BA on B=3 in the corrected form; the
exact B=2/B=3 forms of the 16-expression battery; the msb identities
on B=3.
SKELETON (one piece, precisely located): Lemma PO's general case —
position pinning for multi-b patterns on replicated scrutinees
(counts are MT-verified; the position write-out is open). TL is
conditional on it.
MEASURED LIMITATIONS: value-level classifier specificity is nil at
k ≤ 8 (disclosed with numbers); the random-composition checks are
necessary-condition only.
NEXT-ROUND CANDIDATES: (a) the PO write-out (closes TL
unconditionally); (b) a cross-k linear-recurrence battery — closure
values satisfy ∏_d (x−3^d)²-type recurrences, testable on 7–9
consecutive k's at materializable sizes, which would give the
random-composition check actual teeth; (c) the measure-level
(per-run multiset) formalization in the paper's language.

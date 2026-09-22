# ROUND 4 REPORT — rev-split lane: the merge-sensitive budget + L1 sharp form (Lane B)

Coordinator, 2026-09-22. Machine artifacts: merge_budget.c / merge_budget /
merge_budget.log, merge_budget_seed2.log, merge_budget_class.log
(invocation in the first line of each run). Fidelity:
rev-try/ROUND16_REPORT.md and rev-split/ROUND3_REPORT.md both checked
against memory — faithful, no drift.

## 0. HEADLINE: L1 IS REFUTED AS STATED — and the repair is in hand

Both of Lane C's remaining lemmas rest on the pinned-schema L1 ("every
a-run of V(w^(k)) is an extraction tweak (within a V-fixed constant of
2^j) or a pinned affine αS+β from a finite V-fixed set"). **That
statement is FALSE.** Two explicit fixed expressions on
w^(k) = a^1 b a^2 b … b a^{2^k}, both built from the engine's OWN
mechanisms, refute it:

- **E_leak = [(mrg·b)/'b']X** (mrg = [ε/b]X = a^S, S = 2^{k+1}−1). The
  pattern 'b' fires at every separator; each firing inserts a^S·b. The
  output's runs are exactly **(S+2^0, S+2^1, …, S+2^{k−1}, 2^k)** —
  *padded extractions*. For a middle-depth site j (j→∞, k−j→∞):
  distance to any power of two is 2^j−1 (not a tweak), and no αS+β
  fits (affineness would force α=1 and then 2^{⌊k/2⌋} = β constant).
  Machine: exact run equalities verified for k = 2..13; the
  non-classification checks (distance to any power > 8 at middle
  depths; no affine fit αS+β with α = p/2^d, |p| ≤ 4, d ≤ 2, |β| ≤ 16)
  all pass. This is precisely the merge-padding mechanism of the
  engine's concatenated scrutinees (X·mrg·a).
- **E_prod = [mrg/'aa']X**. Pattern 'aa' tiles each run 2^j exactly
  2^{j−1} times; each firing inserts a^S. Runs are exactly
  **(1, S, 2S, …, S·2^{k−1})** — *site×global products* (my round-2
  T5 class). S·2^{j−1} = 2^{k+j} − 2^{j−1}: distance to the nearest
  power is exactly 2^{j−1}; not affine. Machine: exact equalities for
  k = 2..9 (string-cap bound; the identity is structural).

Both are fixed expressions valid for every k. The "top-O(depth)
run-sizes only" clause does not save L1: E_leak's violating runs are
S-scale (top sizes). Lane C's L3 battery (six values, tolerance 8)
contained neither mechanism — a battery-coverage gap, not an analysis
error: E_leak's middle runs sit 2^j−1 > 8 from any power, so the
tolerance-8 check would have flagged them had E_leak been in the set.

## 1. The repair: L1'' = the P4'-closure form on w^(k)

The correct sharp schema is my round-2 P4' profile instantiated on the
family: every a-run of V(w^(k)) is exactly an element of the closure of
{site terms 2^t, the global S, constants} under +, −, and × by pinned
counts — concretely Q(S) + Σ_{i≤m} κ_i·P_i(2^{t_i})·Q_i(S), with:

- **TERM LEDGER (the new sharp content):** the number of distinct
  site references in any one run is ≤ M_V ≤ #S(E)+O(1). Skeleton:
  site references enter via X (one per site, but
  consecutive-complete supports COLLAPSE — tails are S+1−2^τ, prefixes
  2^{τ+1}−1, periodic sets are geometric hence affine); each S-node
  adds O(1) IRREGULAR references (its single-firing sites, by my
  Lemma SD — threshold firings give tails, which collapse); C-nodes
  union the two sides' supports. Replication copies R's support but
  the per-run multiset stays bounded along any one junction chain.
  Degrees likewise bounded by depth (each ×-by-count event adds one).
- **THE RESIDUE BRIDGE HOLDS (coordinator's note confirmed):** the
  MT(b) degeneration (totals are not functions of (S_a,k) in general)
  does not bite on w^(k): the family pins its own residues (exactly
  one odd run; 2^m mod p eventually periodic), so census counts are
  pinned V-fixed values on the family — the count ledger is exact.
- The ORIGINAL exact-equality form (tweak OR affine, no terms) is
  what is false; the closure form is the exact-equality repair.

**Machine:** a 9-expression exact battery (the L3 six + E_leak +
E_prod + the junction C(E_leak,E_leak)) classifies COMPLETELY in the
narrow subclass α(S+1) + ≤4 signed powers + |junk| ≤ 64 (α from
{p/2^d} ∪ {±2^t, ±2^t/2}): all runs, k = 3..9, zero failures at every
seed. Random compositions (depth ≤ 5, k = 4..8): **40,896/40,896 fully
classified** (2684 + 2667 at trials = 3000; 17,792 + 17,753 at trials
= 20,000, fresh seeds) — every run of every random composition lands in
the narrow subclass. Honest scope caveats: (i) outputs that exceed the
1 MB evaluator cap are skipped (the explosive stratum is not sampled,
so the 100% is over bounded-output compositions); (ii) the narrow
subclass's α ranges are small, so 100% is evidence the closure is
TIGHT, not merely non-vacuous — the term-ledger write-out at varying k
remains the formal deliverable, exactly parallel to round 2's skeleton
status. [Bookkeeping slip, disclosed: the first run of the random loop
reported 58/75 "unclassified, runs ~10^14" — that was an array overrun
in the harness (run count could exceed the 512-entry stack array;
ASLR-varying stack garbage, caught on delivery re-read), not
mathematics; fixed and re-run, all numbers above are from the fixed
build.]

## 2. The architecture SURVIVES the repair (the L2 interface)

The tuning/deletion-rate kill survives because the two new classes
cannot carve deep runs:

- PADDED flanks (αS + β + terms) are ≥ αS − O(1): they fully consume
  any run 2^j with j ≤ k − m(α) — they cannot partially carve deep
  runs. PRODUCT flanks (degree ≥ 2) likewise exceed all deep runs.
- Partial deep carving is therefore confined to constant flanks
  (slivers 2^j − c: not the target powers) and tweak flanks 2^t + δ
  (biting at depths l > t: slivers 2^l − 2^t − δ, not powers for
  l ≥ t+2). Either way the sliver is off-target and needs further
  carving.
- The final exact singleton 2^l at each depth l requires some flank
  value exactly cumulative at depth l. **The unit of tuning becomes
  the SITE TERM, not the run**: each distinct deep term needs its own
  tuned flank; a fixed pattern has finitely many runs, each carrying
  ≤ M_V site references: still Ω(k) patterns, i.e. Ω(k) S-nodes.

For Lane D: hunt L2 in the term-united form. For the paper (Lane C):
§4.1 of ROUND16 must be replaced by the closure form before the
dichotomy theorem's part (ii) is written.

## 3. THE MERGE-SENSITIVE BUDGET (charter task 1) — proved, two-stratum

- **STRATUM 1 (merge-free; round-3 SB):** Φ' ≤ 4·#S + 2·#C, where
  Φ' = # distinct reversed input-adjacent separations (Φ'(rev(w)) = k).
  Hand proof round 3; this round adds 7,381 more random merge-free
  derivations (1573 + 1577 at trials = 3000, 4231 at trials = 8000)
  with ZERO violations of even the tighter 2#S+2#C (max Φ'-excess
  −44). Tight constant still open; 2/2 unfalsified.
- **STRATUM 2 (mergey; per-node identity):** for every S-node,
  **Φ'(out) ≤ Φ'(F) + Φ'(R) + 4 + MJ(out)**, where MJ = the number of
  separations bearing a reversed pair with a multi-label flanking run
  (the mergey junction events). Proof: the SB case analysis with the
  mergey junction pairs charged to MJ instead of the pinned +4 (each
  non-mergey new pair is still pinned by one of R's four
  boundary-adjacent run labels). Machine: 4359/4359 (seed 271828) and
  4436/4436 (seed 314159) S-node identities, plus the E_poll witness:
  Φ'(E_poll) = k with MJ = 20460 / 169260 / 1376172 at k = 5/6/7 — MJ is
  non-vacuous and shows the mergey creation is unbounded per pass,
  exactly as E_poll proved.
- **TREE TOTAL:** Φ'(E) ≤ 4·#S + 2·#C + Σ_v MJ(v). Machine: 2686/2686
  and 2668/2668 (both seeds).
- **PAYMENT (the merge-sensitive core, hand):** every mergey junction
  flip that SURVIVES to the final output must be paid: at creation
  the flanking runs carry foreign site-terms (that is what makes them
  multi-label); the final output's runs are exact singletons; the
  foreign terms must be stripped by downstream exact cuts at
  inter-term boundaries — cut positions are exact closure-class values
  referencing those depths — and each such cut is priced by the
  tuning constraint (L2). The replication escape (kept material
  re-supplied by a copy) defers the payment into the copy; Lane C's
  descent/Escape-A kill closes that deferral (copies' picks must be
  value-stratified, forcing the deep-rich structure into R itself).
- **COROLLARY (conditional on L2):** k ≤ 4#S + 2#C + #(surviving
  mergey flips) ≤ 4#S + 2#C + C'·(#tuned deep cuts) = O(|E|): the
  Ω(k) bound. The two lemmas of the architecture now interface
  through ONE quantity: **the deep-cut count**.

## 4. Carry items

- Invocation discipline: every run logs its full invocation as the
  first line (merge_budget.log, merge_budget_seed2.log,
  merge_budget_class.log). Second seed: invariant results identical
  (104 checks / 0 failures, E_poll identities byte-identical,
  max excess −44); seed-dependent counts in §5.
- SB tight constant: 2#S+2#C unfalsified in 7,381 random merge-free
  cases; hand bound stays 4/2.
- General-k profile write-out: parked (did not block tasks 1–2).

## 5. Machine record (rev-split/, all runs ≤ 0.2 s)

merge_budget.c / merge_budget / merge_budget.log (seed 271828,
trials 3000) / merge_budget_seed2.log (seed 314159 all + sb2 8000) /
merge_budget_class.log (fresh seeds 12345, 99991 at trials 20000).
Modes: leak (exact refutation forms, k = 2..13 and k = 2..9, plus the
non-classification checks), class (9-expression exact battery, 63
checks, k = 3..9 + random compositions: 2684, 2667, 17,792, 17,753 —
all fully classified), msb (4359 + 4436 node identities; 2686 + 2668
tree totals; E_poll witness), sb2 (tight-constant hunt). **Total 104
checks, 0 failures at both seeds (63 checks, 0 failures for the
class-only runs).** One harness slip, disclosed and fixed before
delivery: the random-classification loop could read past a 512-entry
run array when a composition's output had more than 512 runs (the
"unclassified ~10^14" lines in the first run were ASLR-varying stack
garbage — spotted because a genuine run cannot exceed the 2^20
evaluator cap); fixed to a full-size array and everything above is
from the fixed build. No ck()-check was affected (the slip was in a
print-only diagnostic path).

## 6. Status

The endgame architecture is intact but its load-bearing lemma needed
repair before it could be written: L1-as-stated is refuted by the
engine's own padding and tiling mechanisms; L1'' (the P4'-closure on
w^(k) with the term ledger) is the correct sharp form, is
machine-supported on the exact battery and on 40,896 random
compositions (100% classification), and leaves L2 with a CLEAN
interface (tune per site term; padded/product flanks cannot carve
deep). The merge-sensitive budget is delivered as the two-stratum
identity plus the Payment theorem, reducing the whole impossibility
to Lane D's tuning lemma through the single quantity: deep cuts.

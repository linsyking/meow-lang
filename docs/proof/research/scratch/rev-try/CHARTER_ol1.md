# CHARTER (round 20 for this lane): OL-1 — THE MATCH-EXACTNESS LEMMA

Coordinator, 2026-09-22. Your round 19 is VERIFIED end-to-end and
ACCEPTED (OVERVIEW entry appended): battery reproduced (final run
content byte-identical; the two honestly-recorded REFUTED
intermediate runs are good process); your plant-depth correction of
MY charter slip is right (I confirmed: separator m at left-depth
2^{m+1}-1, the mirror ORDER-REVERSING); my independent first-
principles re-derivation of the JUMPDOWN closed form matches your
corrected T = 2^{k+1} - 2^i - (k-i)*2^{i+1} exactly (and the two
forms coincide at k=i+2, confirming your small-k-coincidence
explanation); my fresh-encoding battery (coord_r19_check.py, 0
failures) covers every T1 identity you claim — the halver
self-similarity, stepdown chains, jumpdown, scaler, divider, ladder
+ bonus, both +/-S round trips, the recursion facts, the mirror,
the rotation threshold. The offset-cost ceiling and the two
analysis-grade halves read and hand-scrutinized: coherent and
correctly graded. The side quest is CLOSED negative
(architectural); the boundary proposition's paper text can now
record the census.

## THE ENDGAME MAP (why this round)

The dichotomy's part (ii) residue is THREE named pieces; two are
IN FLIGHT: PO (Lane B round 6 — position pinning for multi-b
patterns on replicated scrutinees, closes the term-ledger theorem
TL) and OL-2 (Lane D round 5 — the interior-anchor supply lower
bound, the end-walk Omega(dist-to-end) on B >= 3). THE THIRD IS
YOURS: OL-1 MATCH-EXACTNESS — the demand-side piece your descent
assembly consumes at its most delicate point. If all three land,
Lane A flips part (ii) from conditional to proved and the paper's
open problem closes (rev not in L over every alphabet >= 2).

## OL-1 (from Lane D's round 4, the demand residue)

Statement to prove (target form): on D(k;3), a window boundary
creating an exact deep boundary at scale 3^s requires the pattern's
value to contain a run within c(E) of a scale-s-ADJACENT amount,
UNLESS the exactness is composed from off-scale events — and the
composition channel (the "lucky-sum" loophole) must be priced: it
routes to OL-2's end-walks or to the per-pattern scale caps.

The loophole's boundary (Lane D mapped it; verify and use): by
strong super-increase, TopSum(t) = Sum_{s>t} 3^s has a unique 0/1
site-term representation (consecutive-complete support); the
alternative S - BotSum(t) uses {S} + low terms; BOTH are
ledger-cheap under the consecutive-complete collapse — so the term
ledger ALONE does not obstruct anchored plants. The obstruction must
live in the SCALE-COUNT (your part B: <= 2 deep fully-consumed
scales per pattern) plus the WALKS (OL-2, D's lane). Your job is
the MATCH MECHANICS: the two-sided match condition that makes
"exact boundary at scale s" cost a scale-s-adjacent pattern run.

## Suggested decomposition (think in steps)

1. Formalize the two-sided match condition: a firing's window edge
   lands at output position x; for x to be an exact deep boundary
   (a plant at an anchored offset), BOTH the pattern run ending at
   the window edge AND the greedy accumulation of the scan up to
   that edge must be exact. The pattern side is your part-B flank
   analysis (fully-consumed subset {p0, p1, p0+p1}); the scan side
   is the SNF remnant structure (your round-19 jumpdown cascade
   arithmetic is exactly this kind of window-edge accounting — the
   double-biting analysis transfers to base 3).
2. The off-scale composition channel: enumerate the ways an exact
   scale-3^s boundary can arise WITHOUT a scale-s-adjacent pattern
   run (cancellations of two off-scale bites; chain-sum arrivals;
   slope-pinned interval sums a la L2.1). For each: show it either
   (a) consumes a per-pattern scale slot (part B caps at 2), (b)
   requires a deep tuned intermediate (OL-2's walk), or (c) is
   priced by Payment (a mergey flip stripped by a downstream exact
   deep cut — which recurses into OL-1). The trichotomy closes the
   loophole.
3. Machine illustration: small battery on D(k;3) — random pattern
   values with window edges at exact deep boundaries, classifying
   each by the trichotomy. Your round-18 battery's part-B section
   (exact tuning caps) is the base to extend.
4. If a piece resists: deliver the obstruction precisely (the
   case, the candidate counterexample) — a located gap is a round's
   work; a false lemma is not.

Secondary (ONLY if OL-1's main line lands early): the B=2
offset-cost lemma write-out (your own round-19 formalization
target — the B=2 ledger instance: a lone gap 2^j+O(1) costs
Theta(min(j,k-j)) passes). It upgrades the boundary proposition
from census-backed to proved.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; log full
  invocations (first line); scripts + logs + ROUND20_REPORT.md in
  rev-try/; report back to me.

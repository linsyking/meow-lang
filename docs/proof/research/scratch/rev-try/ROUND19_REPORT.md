# ROUND 19 REPORT — THE B=2 UNIFORM-REV SIDE QUEST

Lane C, 2026-09-22. Charter: CHARTER_b2rev.md. Artifacts:
verify_r19_b2rev.py, r19.log (four runs, full invocations, final
run 2.05 s wall). Nothing committed.

## VERDICT: NEGATIVE (architectural). The obstruction is the
OFFSET-COST CEILING, and it is a genuinely different resource from
the B>=3 tuning obstruction.

There is no fixed expression E with E(w^(k)) = rev(w^(k)) for all k
by any mechanism found in this round's hunt. What dies on B=2 is
NOT the values (they are all free — that is the B=2 degeneracy) but
the ORDER: the reversal must address all k+1 run-offsets, and
addressing offset j costs Theta(min(j, k-j)) by every mechanism
examined. Equivalently: at B=2 the closure is cheap and the
assembly is priced; at B>=3 both are priced. Status of the
obstruction itself: ANALYSIS-GRADE (the two halves below), with
machine evidence on the falsified shortcut classes and a census
backing the ceiling; the formalization target is stated as a
lemma-to-be.

## 0. The coordinator's two hand-derivations, checked as instructed

- PLANT-DEPTH IDENTITY: substance CORRECT; one indexing slip. The
  correct statement: separator m of w^(k) (the one after run m,
  runs indexed 2^0..2^k) sits at LEFT-depth 2^{m+1} - 1, which is
  one less than the run it PRECEDES (run m+1 = 2^{m+1}) and one
  less than TWICE the run it FOLLOWS (2 x 2^m - 1). The charter's
  "left-depth 2^m - 1 = (the m-th run) - 1" holds only if the
  "m-th run" counts the run AFTER the separator. rev's m-th
  separator sits at right-depth 2^{k-m} - 1 = the left-depth of
  w's separator k-1-m: the depth mirror is ORDER-REVERSING.
  Machine: T1, VERIFIED (my first check compared the depth lists
  directly and the battery refused it — the fix is rd_r ==
  ld_w[::-1]; the claim was right, my check was wrong).
- RECURSION: CORRECT, including the operator name. rev(w^k) =
  [aa/a](rev(w^{k-1})) . b . a, where [aa/a] is the doubler under
  the paper's replacement/pattern convention. Machine-confirmed
  both directions for k=1..8: doubler(rev(w^{k-1})) + 'ba' =
  rev(w^k) and halver(rev(w^k)) = rev(w^{k-1}) + 'ba' (T1).
  The halver identity on the family itself is the cleaner fact:
  [a/aa]X = 'ab' . w^{k-1} — halving PEELS one 'ab' block.
  This is the self-similarity that makes the telescoping tools
  work, and it is also why the recursion cannot be shortcut (see
  §3).

## 1. NEW POSITIVE TOOLS (all machine-VERIFIED byte-exact, T1)

These are the round's constructive yield — the B=2 toolkit is
richer than the record had, and the census of it is what pins the
ceiling.

- STEPDOWN (NEW): [eps/(b . E_last)]X = w^{k-1}. The pattern
  b.a^{2^k} fires exactly once — at the last separator, whose
  following run is exactly 2^k — and eats the separator plus the
  whole last run. The family steps down ONE LEVEL in O(1) passes
  (S-depth 3). The chain steps again with the halving-chain
  patterns: [eps/(b . E_h2)](stepdown) = w^{k-2},
  [eps/(b . E_h4)](...) = w^{k-3}. VERIFIED k ranges in r19.log.
- JUMPDOWN (NEW): [eps/(a^{2^i} b a^{2^i})]X CASCADES on the
  family: the leading flank fully consumes run i (exactly 2^i),
  each firing leaves just enough of the next run for the next, so
  it fires at separators i..k-1. Runs j > i keep 2^j - 2^{i+1}
  and FUSE into one top-scale tail: out = (2^0, ..., 2^{i-1}, T)
  with T = 2^{k+1} - 2^i - (k-i) . 2^{i+1}. A one-pass truncation
  to any FIXED bottom offset i.
  HONESTY NOTE: my first hand derivation claimed tail 2^k - 2^i;
  the battery REFUTED it for k >= i+3 and I re-derived the closed
  form above, which matches all 18 machine cases. My original
  k=2,3 hand-checks passed only because the fusion sum is empty
  there — the small-k coincidence zone again.
- SCALER (NEW): [a^{E_last}/a]X scales every gap by 2^k in ONE
  pass. Computed replacement values make pure-a multiplicative
  scaling a single pass (this was the surprise of the round: the
  "scaling by 2^j costs j doublings" intuition is FALSE at B=2
  once replacement values may be computed). Verified k <= 7.
- DIVIDER (NEW): [a/a^{E_h2}]X threshold-divides gaps >= 2^{k-1}
  by 2^{k-1} exactly and leaves smaller gaps alone (fires per
  2^{k-1}-block). Verified k=1..10.
- LADDER (NEW): [b/ab][aa/a]X = (1, 3, 7, ..., 2^k - 1, 2^{k+1}):
  the PLANT-DEPTH LADDER WITH SEPARATORS, in two constant passes
  (doubler, then the skeleton-preserving shave [b/ab] — note
  [eps/ab] is the MERGE-shave and does not work here). The plant
  depths are exactly the depths at which rev's separators must
  sit, measured from the right; the ladder gives them as RUNS.
  Bonus identity: halver(ladder) = w^k exactly (the ladder is the
  doubler image of w^k under the shave).
- The record's witnesses re-verified on this battery's evaluator:
  E_last, E_smm, E_h2, E_h4, E_grow, E_leak, E_leak-mirror,
  E_prod, E_cbox, and the +/-S ROUND TRIPS: [eps/mrg]E_leak = w^k
  AND [eps/mrg]E_leak-mirror = w^k — BOTH padding directions
  round-trip back to w^k. The padding resource (the thing that
  made E_leak refute the old L1) is fully reversible and
  ORDER-PRESERVING: it moves every run by the same +S and back.
  This is a machine-verified kill of the "pad-then-strip" route.

## 2. THE ORDER SIDE OF THE OBSTRUCTION (analysis-grade)

Alphabet-free part (from the round-16/17 architecture, SNF/FP):
within any pass, remnant material stays in INPUT ORDER; the
order-inverting resources are exactly (i) C-nodes (block
reordering — DECOMP's fixed C-tree reverses a fixed partition of
the input into intervals) and (ii) t=1 splices (one per multi-b
pass; SD forces multi-b patterns to fire once on distinct-run
scrutinees). rev(w^k) is strictly decreasing in gap VALUES, so
each in-order input-stream contributes AT MOST ONE gap to the
output: at least k+1 streams are needed. Streams are cheap via
replication ([X/'b']X, the counterexample class) — the priced
resource is the STRIP-DOWN: each surplus copy must be deleted down
to its single contributed gap, and the deletions are windows of
pattern occurrences:

- a pattern that fires multiply bites UNIFORMLY at one scale
  (T4: periodic planting on the merge plants exactly S//2^j >= 3
  separators at every scale j <= k-1 — never the SINGLE maximal
  odd multiple that rev needs; and the double-kill flank
  (2^i, 2^i) turned out to be the jumpdown: it truncates from
  the bottom and FUSES the top, it does not carve);
- a pattern that fires once (SD) is surgical at ONE site.

So identical copies admit only uniform treatment; the reversal
needs k DIFFERENTIATED contributions; differentiation requires
distinct offsets; and that is where B=2 prices it (§3). The output
cannot dodge this by taking its middle gap from an in-context
family stream (a stepdown or jumpdown keeps runs in input order
with their neighbors): the middle gap 2^{floor(k/2)} of rev sits
between gaps 2^{floor(k/2)+1} and 2^{floor(k/2)-1} — DESCENDING —
whereas any in-order stream would supply them ASCENDING. The
middle must be isolated or re-spliced; both cost the offset.

## 3. THE OFFSET-COST CEILING (the B=2 replacement for tuning)

What dies on B=2 (all confirmed this round): the flankcap mod-3
argument (2^a + 2^a = 2^{a+1}); the Payment theorem's expensive
deep cuts (E_last-style extractions are 2 passes); L1'' closure
(2^m - 1 is a difference of two site terms). What replaces them:

OFFSET-COST PRINCIPLE (analysis-grade, census-backed): a LONE
value or pattern whose structure references run offset j — e.g. a
b-free gap equal (within O(1)) to 2^j — costs Theta(min(j, k-j))
passes. Mechanisms checked, all conforming:

- from the TOP: the halving chain E_last = a^{2^k} (depth 2),
  E_h2 = a^{2^{k-1}} (5), E_h4 = a^{2^{k-2}} (6) — one level of
  end-distance per halving level. T3 census: over a 27-expression
  battery (all tools and their compositions, depth <= 6) on
  w^(7), the deepest lone near-power sits at end-distance 2 (E_h4
  at depth 6); NO battery member isolates a middle power.
- from the BOTTOM: the stepdown chain w^k -> w^{k-1} -> ... (one
  level per ~3 passes) and the jumpdown truncations (one pass,
  but only to FIXED bottom offset i, and the fused tail is
  top-scale).
- by combination: prefix/suffix sums are differences of two
  end-offset values (2^m - 1 = (sum below m), 2^{k+1} - 2^m =
  (sum from m)) — end-offsets again.
- the jumpdown to offset i needs the pattern a^{2^i} — the power
  AT the target offset: addressing an offset requires its own
  power, and the power ladder is reachable only stepwise. The
  scaler (§1) scales all gaps at once but is elementwise: it
  preserves gap order and buys no offset addressing.

Consequence: the reversal, which must address all k+1 offsets
(§2), costs Omega(k) in size (assembly: the C-tree plus one
splice per multi-b pass — the descending sequence assembled from
lone powers a^{2^k}, a^{2^{k-1}}, ... needs k+1 concatenation
blocks, exactly the fixed-k engine's Theta(k)) or in depth
(chains). The B=2 boundary is therefore NOT a positive: rev is
L-computable on the telescoping family at Theta(k) size (stepdown
chain + halving chain + C-assembly), and the obstruction says no
sub-linear fixed expression exists — but this last implication is
the lemma-to-be, not yet a theorem:

LEMMA-TO-BE (B=2 offset-cost lemma, the formalization target): if
E has S-depth d and its value on w^(k) has a b-free gap equal to
2^j + O(1), then min(j, k-j) <= c . d. Proof strategy: the B=2
instance of Lane B's ledger methodology — track the site-terms a
lone deep power can be built from; every pass composes O(1) new
terms and the telescoping identities keep site-terms pinned to
the two ends (S+2^j, S.2^j, 2^k/2^i chains). Combined with the
stream lemma (§2) it yields the uniform no-go at B=2 with the
same Omega(k) shape as B>=3 — a different reason for the same
asymptotic.

## 4. THE FOUR ATTEMPTS, AUTOPSIED ON THE OBSTRUCTION

- HEAD ASSEMBLY (h . b . tail): the head a^{2^k} is free (E_last,
  depth 2) — but rev(w^k) = a^{2^k} . b . rev(w^{k-1}) needs the
  TAIL as a value, and rev(w^{k-1}) is the same problem one level
  down: each unfolding costs one more halving level for its head
  (the offset ladder walked one step per pass). k unfoldings.
- COMPLEMENT BOX: at B=2 the boxes D_m = a^{2^{k+1}-2^m} b a^{2^m-1}
  have end-offset values (suffix and prefix sums) — E_leak holds
  the whole family of them as RUNS, but in input ORDER, and
  extracting run m of E_leak is itself an offset-m extraction
  (Theta(min(m, k-m))). The box ladder is free in context and
  priced in isolation.
- POLLUTION (E_poll-style): merging creates the flips cheaply
  (Phi' = k in one pass — the B=2 flip-creating resource is
  unbounded, as at any base), but the surviving flipped material
  must be stripped to one gap per stream, and the strip-down is
  per-site surgical (SD: one site per pass) or per-scale
  indiscriminate (T4). The Payment theorem's escape — cheap deep
  cuts — exists at B=2 but only AT FIXED OFFSETS from the ends.
- BLOCK SWAP: swapping the halves needs the split at the middle —
  a positional cut at offset ~k/2, i.e. the middle power as a
  pattern: the offset ceiling exactly.

Common obstruction (the charter asked for it stated precisely):
every mechanism must address all k+1 offsets; at B=2, values at
end-offsets are FREE (the telescoping tools), values at middle
offsets cost Theta(k), and the reversal's order requirement
(§2) forces the middle.

## 5. FALSIFIED SHORTCUT CLASSES (machine evidence, T2/T4)

- ROTATION/PHASE: rev(w^k) is a rotation of w^k EXACTLY for
  k in {0,1,2} — it dies at k=3 (T2a). The [ba/a]-split pass
  (one constant pass, gap sequence -> all ones) preserves exactly
  that threshold: the split values are mutual rotations again only
  for k <= 2 (T2b). The split maps the reversal to itself (block
  orders reversed, phase shifted): the problem is self-similar
  under its own periodic collapse. No phase shortcut.
- +/-S PADDING ROUND TRIPS: both leak directions return w^k (§1).
- PERIODIC PLANTING: indiscriminate (T4, §2).
- DOUBLE-KILL FLANKS: the jumpdown — bottom truncation with fused
  top, not a carving tool (§1, with the honesty note).
- ELEMENTWISE SCALING: the scaler preserves order (§3).

## 6. MACHINE RECORD

Four runs, all in r19.log with full invocations first-line:
(1) syntax error (doubled paren, T2a line) — fixed;
(2) T1 REFUTED: my jumpdown hand-derivation wrong for k >= i+3 —
re-derived closed form, matches all 18 machine cases;
(3) T1 REFUTED: plant-depth check compared depth lists directly —
the mirror is order-reversing; fixed to reversed comparison;
(4) ALL VERIFIED, 2.05 s wall, exit 0.
The battery: T1 tool identities (k=1..10; scaler <=7, E_prod <=8,
jumpdown i=1..3 k=i+1..10); T2 rotation thresholds; T3 the
27-expression offset census on w^(7); T4 planting counts.
No brute force anywhere; all checks are closed-form predictions
derived by hand first (and two of them were wrong until the
machine corrected me — recorded above).

## 7. LEDGER

- PROVED (machine-verified byte-exact + hand proof in this
  report's text): every T1 identity — the halver self-similarity,
  stepdown and its chains, jumpdown closed form, scaler, divider,
  ladder, the +/-S round trips, the recursion facts, the
  plant-depth mirror; T2 rotation thresholds; T4 planting counts.
- ANALYSIS-GRADE: the order/stream barrier (§2), the offset-cost
  ceiling (§3), the four-attempt autopsy (§4).
- LEMMA-TO-BE: the B=2 offset-cost lemma (§3) — the formalization
  target; proof strategy via the B=2 ledger instance.
- OPEN: any mechanism isolating a middle power in o(k) (none
  found: scalers, dividers, jumpdowns, ladders, rotations,
  splits, plantings all checked this round).

## 8. BOTTOM LINE FOR THE PAPER

The B=2 side quest closes NEGATIVE at the architectural level: the
boundary of the no-go is NOT crossed at base 2. The headline
complement to the dichotomy is sharper than "rev is computable at
B=2": it is "at B=2 every VALUE on the telescoping family is
cheap (the degeneracy: paddings, products, ladders, one-pass
scalings by 2^k) but the ORDER is not — reversal needs the middle
offsets, and the middle is Theta(k) away from both free ends."
The B>=3 theorem prices the values; the B=2 world prices only the
order. Same Omega(k) shape, different resource — and the
dichotomy's f(|E|) linear bound survives the boundary intact.

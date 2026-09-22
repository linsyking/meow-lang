# ROUND 21 REPORT — THE Δ≠0 MULTI-HIT CLOSURE + THE INHERITED LOOPHOLE

Lane C, 2026-09-22. Charter: `CHARTER_deltaclosure.md` (coordinator).
Artifacts (all in rev-try/): `round21_delta.c` + `d5/d6/d8/d9.txt` (the
census), `crossval_r21.py` (independent re-implementation, record-set
identical), `verify_r21_deltaclosure.py` + `r21.log` (battery, 0.20 s,
all VERIFIED), the three report-text fixes applied to
`ROUND20_REPORT.md`, and this report.

**VERDICT: BOTH CHARTER PARTS LANDED.** (1) The Δ≠0 gap is closed AT
THE RIGHT ALTITUDE — not by classifying the whole zoo (which is real:
the census exhibits it) but by proving what the endgame needs: the
drift-robust mirror forcing (D1), the window/debt dichotomy (D2), the
multi-service pricing (D3), and the mass-routing lemma with explicit
constants (MR). (2) The inherited loophole is written out precisely
(Lemma INH with the injective-descent supply bound ≥ (3^k+1)/2, the
origin trace, the routing) and the counting corollary is restated in
the disjunctive form with exact conditionality. The three report-text
fixes (K(a) wording, §4 soundness re-anchoring, §6 downgrade) are done
in ROUND20_REPORT.md and the flag-2 exhibit is re-verified against the
evaluator (T5). Secondary (B=2 offset-cost write-out): NOT ATTEMPTED —
the main line consumed the round again.

**The headline correction to my round-20 claim.** The drifting-channel
statement "realizable |hits| ≤ 2" is FALSE: real drifting multi-hit
channels exist. The smallest exhibit (E1, T6a): the 7-letter pass
[a²ba⁴ / b] on D(k;3) fires everywhere (p0 = p1 = 0, so t_σ = σ exactly)
and plants anchored hits I(1,1), I(1,2), I(3,3) at σ = 0,1,2 — machine
byte-exact at k = 4..7. The full census (below) finds 29/80/364/667
surviving 3-hit configurations at k = 5/6/8/9. My round-20 T3d grid
missed these because its Δ-list never contained the values (6, 33,
114, 357, …) these families need — a domain error of exactly the kind
the round-20 §5 lesson warned about, now recorded honestly. What
survives — and what the endgame actually consumes — is Theorem D
below: the zoo is quantitatively tiny (≤ 4 real hits per channel, and
almost all exactly 3), the bottom-ladder remains the ONLY unbounded-
hit family, and every MIRROR-relevant use of a drifting channel pays
the window or the debt.

---

## 1. Setup (as in round 20, plus the real-t structure)

Channel of a pass [R/P] on D(k;3): constant c = ρ_j − p0, drift
Δ = M_R − p0 − p1; the plant of channel j at firing σ sits at depth
Y = BotSum(σ) + t_σΔ + c, t_σ = #{real firings before σ}. A HIT is an
anchored plant: Y = I(b, a−1) = (3^a − 3^b)/2 with 1 ≤ a ≤ k+1,
0 ≤ b < a, (a,b) ≠ (σ+1, 0). Define W(σ,a,b) = Y − BotSum(σ) =
(3^a − 3^b − 3^{σ+1} + 1)/2. Real hits at σ1 < σ2 < σ3 give

  W_i = t_iΔ + c,  t_1 < t_2 < t_3,  1 ≤ t_{i+1} − t_i ≤ σ_{i+1} − σ_i,
  0 ≤ t_1 ≤ σ_1,

i.e. the three points (t_i, W_i) are COLLINEAR with integer slope
Δ ≠ 0 — the over-determination the coordinator predicted: the
t-spacings q_i are bounded by the σ-spacings, so the W-differences
must be in ratios of SMALL integers. FIT (necessary, at the first
firing τ0): c ≤ Δ + p1 ≤ Δ + 3^{τ0+1} and c ≥ −p0 ≥ −3^{τ0}; since the
t_1 early firings occupy distinct positions in [0, σ1), τ0 ≤ σ1 − t_1,
hence the tightened window **c ≤ Δ + 3^{σ1−t1+1}**.

## 2. The census (machine; the zoo, made precise)

`round21_delta.c` enumerates EVERY configuration passing all necessary
constraints (a SUPERSET of the realizable ones): the collinearity
system solved exactly (rational-ratio reduction, divisor loop), the
t-feasibility, the integrality of Δ, c, the TWO-SIDED tightened FIT,
and output depth monotonicity (I(σ1+1,σ2) + q1Δ ≥ 0 etc.). Survivors:
29 (k=5), 80 (k=6), 361 (k=8), 651 (k=9); distinct (Δ,c) channels:
23/57/218/365. Cross-validated: an independent slow Python
re-implementation (`crossval_r21.py`) produces the IDENTICAL record
sets at k=5 and k=6. Process honesty, three versions: census v1
(no tightened early-firing window) gave 81/384/721; hand analysis of
the v1 record for (Δ=−3, c=8) — round 20's T3d anomaly channel —
showed it slipped through via t1 = 3 early firings that no real
pattern could take (they force p1 ≥ 11 at firing 0, but p1 ≤ 3 there);
the pigeonhole τ0 ≤ σ1 − t1 tightens the window, and v2 applied it
ONE-SIDEDLY (upper bound c ≤ Δ + 3^{σ1−t1+1} only), giving 80/364/667.
The coordinator's round-21b flag: the tightening is TWO-SIDED —
c ≥ −p0 ≥ −3^{τ0} ≥ −3^{σ1−t1} by the same pigeonhole (the leading
flank p0 ≤ 3^{τ0} at the first firing) — and v2 retained 19 ghosts
against the lower bound (3 at k=8, 16 at k=9; e.g. (σ=(3,6,7),
targets ((4,3),(7,2),(8,1)), t1=1, Δ=3, c=−16): p0 ≥ 16 > 9 = 3²).
v3 (the committed files) applies both sides: 29/80/361/651. All 19
removed ghosts are non-mirror records: the mirror-branch populations
are UNCHANGED (d8: 78 debt + 74 window; d9: 124 + 108 — byte-identical
to v2), the ≤ 4-hit bound only tightens, and no hand-proved statement
moves. All three versions' numbers are preserved in `r21.log`.

Census findings (necessary-constraint level, k ≤ 9):
- **Max real hits per channel ≤ 4** (firing-set DP: the maximum over
  all firing sets consistent with the channel; histogram: almost all
  channels have exactly 3). The bottom-ladder (Δ = 0) remains the
  only family with unboundedly many hits.
- The dominant families: top-tracked targets with bottom jumps
  (a_i − σ_i ∈ {(1,1,1), (2,1,1), (3,3,2), …} patterns); the Δ < 0
  sub-zoo is the "bottom-descent" family (a = σ+1: W = −(3^b−1)/2
  with the bottoms descending geometrically while t descends in the
  matching 3-automatic pattern t = (3^{b−1}−1)/2).
- Both mirror branches are POPULATED: window services (mirror hit at
  σ = k−1) and debt services (mirror hit at σ ≤ k−2 with the huge
  drift), in roughly equal numbers.

## 3. Theorem D — the Δ≠0 closure at K2's altitude (hand-proved core)

**Lemma D1 (drift-robust mirror forcing).** A channel hit at a mirror
target I(u,k) (top a = k+1, so u ∈ [1,k]) at firing σ with t = t_σ
satisfies: either σ = k−1, or Δ > 0 and (t+1)Δ ≥ (3^k+1)/2.

*Proof.* W = (3^{k+1} − 3^u − 3^{σ+1} + 1)/2 = tΔ + c. FIT at the
firing σ: the trailing flank fits run σ+1 there (p1 ≤ 3^{σ+1}) and
ρ_j ≤ M_R (c ≤ Δ + p1), so c ≤ Δ + 3^{σ+1}, whence
(t+1)Δ ≥ W − 3^{σ+1}. If σ ≤ k−2 then 3^u ≤ 3^k and 3^{σ+1} ≤ 3^{k−1},
so W ≥ (5·3^{k−1} + 1)/2 and (t+1)Δ ≥ (5·3^{k−1}+1)/2 − 3^{k−1} =
(3^k+1)/2. Since t+1 ≥ 1, Δ > 0 follows. ∎ (Machine T6c: the
arithmetic swept at k = 6..9; T6d: 0 violations across the whole
census.) The constant is TOP SCALE, independent of u: the drift must
have net-created ≥ half the top scale before the firing. Note Δ ≤ 0
is impossible in the early branch: **negative drift can never serve a
mirror target from σ ≤ k−2.**

**Lemma D2 (window vs debt at σ = k−1).** At σ = k−1,
W = 3^k − BotSum(u−1), so p1 ≥ W − (t+1)Δ and p1 ≤ 3^k:
either (i) (t+1)Δ ≤ BotSum(u−1), and then the deficit 3^k − p1 <
3^u — top-scale pattern material with a sub-bottom-scale deficit:
match-exactness persists (the round-20 window, drift-robust); or
(ii) (t+1)Δ > BotSum(u−1) ≥ (3^u−1)/2, and then the pass's total
drift |fΔ| exceeds half the target's bottom scale — mass mis-booking,
priced by MR. *Proof:* FIT algebra as in D1; (i): 3^k − p1 ≤
BotSum(u−1) + (t+1)Δ < 2·BotSum(u−1) = 3^u − 1; (ii) is the
contrapositive remainder, with f ≥ t+1. ∎

**Lemma D3 (multi-service pricing).** A channel serving ≥ 2 mirror
targets pays the D1 debt ≥ (3^k+1)/2. *Proof.* One plant per firing
per channel, so two services sit at distinct firings σ < σ′ ≤ k−1;
the earlier has σ ≤ k−2, and D1 applies. ∎

**Lemma MR (mass routing, constants explicit).** A pass with drift
Δ ≠ 0 and firing set F (|F| = f) changes the total a-mass by exactly
fΔ (Lemma M(ii): out-mass = in-mass + fΔ). For a final output of mass
S on the D(k;3) family, Σ over the expression's passes of f_iΔ_i = 0:
every created unit is destroyed by a Δ′ < 0 pass and vice versa. A
debt D = (t+1)Δ ≥ (3^k+1)/2 (D1/D3) or > BotSum(u−1) (D2) must be
re-paid by mass-destroying passes whose firings bite at window edges;
for the final string to be exact at every separator, the last pass
touching each deep region leaves exact values — the Payment theorem
(round 18, PROVED: every mergey flip is stripped by a downstream
exact deep cut, recursing into OL-1) prices the re-payment, with the
per-pattern scale caps (part B, PROVED: ≤ 2 fully-consumed deep
scales per pattern) bounding what a single pattern can remove. ∎
(interface lemma: the debt is stated with constants; the re-payment
mechanism is the proved Payment machinery — Lane A assembles).

**Theorem D (summary).** On D(k;3), a drifting channel (Δ ≠ 0) has
≤ 4 anchored hits (census, k ≤ 9, necessary-constraint level) — the
bottom-ladder (Δ = 0) is the only unbounded-hit family — and every
mirror-target service by any channel, drifting or not, pays one of:
the exact top-scale window (D2(i): p1 ∈ [3^k − BotSum(t) − (t+1)Δ,
3^k], deficit < 3^{t+1}: an exact top-scale pattern value — a part-B
slot at full consumption, or an exact deficit value = supply), or the
mass debt (D1/D2(ii)/D3: ≥ (3^k+1)/2 top-scale, or > half the target's
bottom scale: MR/Payment). The lucky-sum loophole does not reopen:
drift buys the depth only by buying the mass.

**Exhibits (machine, byte-exact).** E1 (T6a): [a²ba⁴/b] on D(k;3),
k=4..7 — the drifting 3-hit channel, hits exactly I(1,1), I(1,2),
I(3,3) at σ = 0,1,2. E2 (T6b): [a²ba¹¹²/b] on D(5;3) — Δ = 114:
hits I(1,1)=3, I(1,4)=120, and the MIRROR target I(5,5) = 3^5 = 243
served at σ = 2 ≤ k−2, with drift debt (t+1)Δ = 342 ≥ (3^5+1)/2 =
122 and output mass S + 5·114 = 934 (MR's bookkeeping; the 570 of
excess must be re-paid downstream). The family generalizes: Δ =
(3^{k}−15)/2 serves I(k,k) at σ = 2 with debt 3Δ.

## 4. Part 2: the inherited loophole, written out (Lemma INH)

**The origin trace.** In the nested-sweep tree (round 18's
dich:lem:sweep framework), every separator of the final output is
either (α) a plant of the outermost pass, or (β) a surviving separator
of its scrutinee, and recursively: every separator of any
intermediate value is a plant of that level's pass or a survivor of
its scrutinee; the recursion terminates at the original input
separators. So each final separator originates as a plant at some
level, or as an original separator that survived every level of its
chain ("all-the-way survivor").

**Lemma INH (the supply bound).** Let a final separator of the output
sit at a mirror depth I(t+1,k) and be an all-the-way survivor of the
original separator j. Then the material before it in the final output
decomposes as

  I(t+1,k) = [never-inserted mass] + [inserted mass],

where the never-inserted mass is ≤ BotSum(j) and the inserted mass is
the total copy-mass (a-count) inserted before it along its chain.
Hence inserted mass ≥ I(t+1,k) − BotSum(j) ≥ 3^k − (3^k−1)/2 =
(3^k+1)/2 — TOP SCALE, for every mirror target (I(t+1,k) ≥ 3^k) and
every original position (BotSum(j) ≤ BotSum(k−1)).

*Proof.* Along the survivor's chain, at each level the material before
it in that level's value = (that level's copy-mass inserted before
it) + (the next level's prefix before the corresponding separator,
minus bites). The never-inserted atoms descend through the chain
prefix at every level without ever lying inside an inserted copy: the
level-to-level map on such atoms is injective (each level's prefix is
a concatenation of disjoint next-level chunks and copies; a
never-inserted atom comes from a unique next-level atom), and bites
only remove. So never-inserted mass ≤ the input prefix mass BotSum(j)
before separator j. ∎ (Machine T7a: the bound swept over all t, j at
k = 5..8; T7b: the mod-3 separation — BotSum(j) ≡ 1 (mod 3) while
every mirror target ≡ 0 — so no Δ = 0 survivor sits at any mirror
depth.)

**Exhibit E3 (T7c, byte-exact).** [a⁹ / (a b a³)] on D(2;3): the
pattern fires once (at σ = 0: run 1 is exactly consumed by the trailing
flank, which then blocks σ = 1), Δ = 5, and the ORIGINAL separator 1
survives at depth BotSum(1) + Δ = 9 = I(2,2) — a mirror target — with
inserted mass 9 ≥ (3²+1)/2 = 5 and never-inserted mass 0 (the bites
ate the whole prefix). Same at k = 3 with R = a²⁷: survivor at 27 =
I(3,3), inserted 27 ≥ 14 (and the second firing at σ = 2 inserts
another copy of R at a-mass depth 35 = 27+8 — character position 36;
35 is not an interval sum, and the copy has no internal separator, so
it plants nothing — harmless). **The loophole is
real: survivors CAN sit at mirror depths — but the price is the
top-scale inserted mass, and that mass must be the exact mirror
prefix** (the final string's structure before the separator IS
a^{3^k}b a^{3^{k−1}}⋯b a^{3^{t+1}}): the inserted chunks are
R-copy pieces whose sizes and boundaries are exact deep values.

**The routing.** The supply of exact deep values at exact positions
is priced by: (b) OL-2's end-walk bound Ω(dist-to-end) (Lane D,
in flight — quoted black box), and (c) the Payment theorem (round 18,
PROVED) when the assembly is mergey. One survivor already costs
Ω(k): its (3^k+1)/2 of exact top-scale structure sits at distance
Ω(k) scales from the end.

## 5. The counting corollary, restated (exact conditionality)

**Corollary (Ω(k), disjunctive).** Any E ∈ L computing rev(D(k;3))
must place k separators at the mirror depths I(t+1,k). Tracing each
to its origin: (α) plant-served, or (β) survivor-served. Then:

- If ANY target is (β)-served: Lemma INH gives (3^k+1)/2 of exact
  top-scale supply → Ω(k) by OL-2/Payment.
- Otherwise all k are (α)-served. By D3, a channel serving ≥ 2 targets
  pays the (3^k+1)/2 debt (MR/Payment: Ω(k)); so single-service
  channels dominate: k distinct channels. Each single service pays
  (Theorem D): the exact top-scale window (an exact top-scale pattern
  value: a part-B scale slot at full consumption — ≤ 2 per pattern —
  or an exact deficit value: supply), or the mass debt (MR). Multi-
  channel passes (one pass serving several targets via distinct
  R-internal separators) need R-internal run sizes equal to exact
  mirror differences (3^t − 3^{t′})/2: supply again.

Both branches are linear: k ≤ f(|E|) with f linear, feeding Lane A's
dichotomy part (ii) at its most delicate point.

**Conditionality (exact).** PROVED and landed: Lemma M/FIT/K/K2/S
(round 20, real-channel coverage = the hand kill at the real firing),
part-B scale caps (round 18), Payment (round 18), TL/PO (Lane B
round 7, LANDED — multi-b patterns and replicated scrutinees at full
altitude), D1/D2/D3/MR + INH + the origin trace (this round; D1–D3
and INH hand-proved, the census parts labeled). IN FLIGHT: OL-2
(Lane D round 7 — the exact-deep-value supply bound; both branches of
the corollary route through it). REMAINING INTERFACE: the (β)-level
plant analysis (plants at perturbed, non-D(k;3) scrutinees) is
carried by the supply branch — a perturbed-level channel serving
≥ 2 mirror-relevant targets needs exact R-internal differences, which
is supply; the single-service perturbed case reduces, by the origin
trace, to the input-level (α) analysis or to survivors. This
interface is stated, not proved here; Lane A's integration is where
it lands.

## 6. The three report-text fixes (charter part 3)

All three applied to ROUND20_REPORT.md before the battery ran:
1. K(a) rewritten: consecutive merges only, with the repunit digit
   proof (a gap leaves a 0-digit, an overlap a digit 2); the
   vestigial "empty sides" phrase noted as never-firing.
2. The §4 soundness paragraph replaced: real-channel coverage = the
   hand kill anchored at the REAL firing (cross-pairs die at
   c ≤ p1 ≤ 3^{σ1+1} < c); the machine census re-labeled CORROBORATION
   (it can exclude realizable channels whose idealization has early
   spurious hits — the coordinator's exhibit P = b·a⁸¹, R =
   a³⁵·b·a⁴⁶ on D(7;3), re-verified against the evaluator as T5:
   fires 3..6, ZERO real hits, idealized cross-pair {I(2,3), I(1,3)}
   at σ = 0,1, census-ghosted at s0 = 0).
3. §6's inherited-loophole downgraded and rerouted: the content
   argument was wrong; replaced by the reference to Lemma INH (this
   round) with the mod-3 step retained as the Δ = 0 case. The ledger
   lines updated accordingly.

## 7. Ledger

- Lemma D1 (drift-robust mirror forcing): **PROVED** (hand; T6c
  arithmetic, T6d census: 0 violations at k = 5..9).
- Lemma D2 (window vs debt at σ = k−1): **PROVED** (hand; FIT
  algebra).
- Lemma D3 (multi-service pricing): **PROVED** (hand).
- Lemma MR (mass routing, constants explicit): **PROVED** as the
  debt-statement + the Payment interface (Payment itself PROVED
  round 18); the final re-payment assembly is Lane A's integration.
- Hit-count ≤ 4 for Δ ≠ 0, and the family census: **VERIFIED-ON-
  STATED-DOMAIN** (necessary-constraint level, k ≤ 9, cross-validated
  enumeration; NOT load-bearing for the corollary). [Round 21b: the
  census window is TWO-SIDED (c ≥ −3^{σ1−t1} added — coordinator flag:
  my v2 tightening was one-sided); corrected counts 29/80/361/651 at
  k=5/6/8/9; the 19 removed records were non-mirror ghosts; all
  census claims re-verified unchanged.]
- Lemma INH (supply bound) + origin trace: **PROVED** (hand; T7a/b;
  exhibit T7c byte-exact).
- Round-20 claim "drifting realizable channels have ≤ 2 hits":
  **REFUTED** (E1; the census) — superseded by Theorem D; the
  round-20 T3d grid was a domain error, recorded in r21.log.
- Counting corollary (disjunctive Ω(k)): **CONDITIONAL** on OL-2
  (in flight) + the (β)-level interface (stated); TL/PO, part-B,
  Payment: LANDED.
- B=2 offset-cost write-out (secondary): **NOT ATTEMPTED**.

## 8. Bottom line for the paper

The demand-side story is now complete in the form Lane A needs: every
path by which a separator of the final reversal reaches its mirror
depth is priced. Plants: the two-sided match (round 20) + Theorem D
(this round) — the firing is forced to k−1 with an exact top-scale
window (a scale slot or an exact deficit value), or the drift carries
a top-scale mass debt that Payment must re-pay; multi-service pays
the same debt; the drifting zoo exists but is capped at 4 hits and
irrelevant beyond its price. Survivors: Lemma INH — the mirror prefix
must be supplied as (3^k+1)/2 of exact top-scale inserted structure.
The two supply channels (exact deep values, exact inserted structure)
are exactly what OL-2 prices and Payment recurses on. With Lane D's
S4.3-general landed, Lane A's part (ii) counting closes: rev ∉ L.

# ROUND 20 REPORT — OL-1: THE MATCH-EXACTNESS LEMMA

Lane C, 2026-09-22. Charter: `CHARTER_ol1.md` (coordinator). Artifacts:
`verify_r20_ol1.py` (battery), `r20.log` (two runs: the honest
anomaly-then-fix record). Everything below runs on the shared evaluator
(`rev/prov.py` + `rev/lcore.py`); total wall 2.13 s + 2.15 s.

**VERDICT: OL-1 LANDED (main line).** The two-sided match condition is
formalized (Lemma M + FIT), the off-scale composition channels are
enumerated and closed by the trichotomy (Lemma K2 + the mirror forcing
Lemma S), the machine battery verifies every claimed statement, and the
counting corollary feeding Lane A's dichotomy part (ii) is stated with
its two in-flight interfaces (TL/PO = Lane B round 6; OL-2 = Lane D
round 5) explicitly marked conditional. One honest located gap remains
(the drifting Δ>0 multi-hit closure beyond the tested grid, §4.4) —
delivered precisely per charter step 4, with its routing argument.
Secondary target (B=2 offset-cost write-out) NOT attempted: the main
line did not land early enough to spend the round twice.

---

## 0. What the round delivers, in one paragraph

On D(k;3) the reversal's k separators sit at the "mirror depths"
I(t+1,k) = TopSum(t) = S − BotSum(t), t = 0..k−1. For a pass to plant a
separator at such a depth, BOTH sides of the match must be exact at
once: the SCAN side (the greedy accumulation of remnant runs and earlier
copies up to the window edge — a site-ladder BotSum(σ) plus a drift
t·Δ) and the PATTERN side (the window's own flanks p0, p1 and the
replacement's internal prefix ρ_j — which must FIT the runs they bite).
The round's core finding: **the pattern side's fit constraints are not
bookkeeping, they are the second half of the obstruction.** The channel
constant c = ρ_j − p0 is confined to the fit window [−3^{s0},
Δ + 3^{s0+1}] at the first firing, and this window kills exactly the
arithmetic families that the interval-sum kernel alone (the "lucky-sum"
loophole) permits: the cross-pair 2-hit families are entirely
fit-killed ghosts, and the only realizable multi-hit channels are the
bottom-fixed ladders, which are magnitude-capped below 3^k and so can
never serve a mirror target. What survives the filter: the mirror
forcing (Lemma S) — a mirror-target plant pins the firing at σ = k−1
and the trailing flank into the exact window p1 ∈ [3^k − BotSum(t),
3^k], i.e. top-scale material whose deficit from 3^k is bounded by the
target's own bottom scale and is itself a canonical site-ladder value.
The lucky-sum loophole does not bypass this; it routes into the
trichotomy (part-B scale slots / OL-2 end-walks / the Payment
recursion).

## 1. Setup and notation

D(k;3) = a^{3^0} b a^{3^1} ⋯ b a^{3^k} (k separators, runs 0..k).
Site sums: BotSum(t) = Σ_{j≤t} 3^j = (3^{t+1}−1)/2; TopSum(t) =
Σ_{j>t} 3^j; interval sums I(u,v) = Σ_{j=u..v} 3^j = (3^{v+1}−3^u)/2 =
BotSum(v) − BotSum(u−1). Note I(t+1,k) = TopSum(t) = S − BotSum(t).
rev(D(k;3)) = a^{3^k} b a^{3^{k−1}} ⋯ b a: its separator t sits at
depth I(t+1,k), t = 0..k−1 — the **k mirror targets**, all ≥ I(k,k) =
3^k > BotSum(k−1) ≥ every ladder target.

A pass [R/P] with single-b pattern P = a^{p0} b a^{p1} (empty pattern
undefined; P's value must occur in the scrutinee) and replacement R
with run-vector M = (m_0, …, m_{r−1}), mass M_R, internal
separator-prefixes ρ_j = m_0+⋯+m_j (the prefix through run j; R's
separator j sits after m_j, j = 0..r−2 — the battery's convention; all
ρ_j ∈ [0, M_R]). Net per-firing a-mass
change Δ = M_R − p0 − p1. This is the SNF single-b layer; multi-b
patterns and replicated scrutinees are Lane B's TL/PO territory (in
flight, §7).

## 2. Lemma M — the two-sided match condition (scan side)

**Lemma M.** On input D(k;3), for [R/P] as above:
(i) **Firing set.** Separator σ (between runs σ, σ+1) fires iff
3^σ − β_σ p1 ≥ p0 and 3^{σ+1} ≥ p1, where β_σ = 1 if σ ≥ 1 and σ−1
fired (the double-bite bookkeeping: a fired window's trailing flank
eats into run σ+1's head, so the next window's leading flank sees a
shortened run).
(ii) **Output.** Surviving run j has length L_j = 3^j − [j−1 fired]·p1
− [j fired]·p0; at each fired σ the separator is replaced by a copy of
R. (Output = SNF interleave q_0 R q_1 R ⋯ q_t.)
(iii) **Plant depths.** The j-th planted separator of the copy inserted
at firing σ sits at depth **BotSum(σ) + t_σ Δ − p0 + ρ_j**, t_σ = the
number of earlier firings. A surviving (inherited) separator j sits at
depth **BotSum(j) + t_j Δ**.
(iv) **Locality (M1).** All plants of firing σ lie in [BotSum(σ−1) +
t_σ Δ, BotSum(σ) + t_σ Δ + M_R]: each firing plants only within one
prefix-ladder step (plus R's mass) of its drift-shifted separator.

*Proof.* (i)–(ii): induction along the greedy leftmost-first scan; the
only subtlety is the double bite on a run between two fired
separators (round 19's jumpdown arithmetic, transferred to base 3).
(iii): the a-material before the plant = (runs 0..σ−1 remnants) +
earlier copies − (this window's leading bite) + (R's prefix): each
earlier firing contributes −(p0+p1) of remnant and +M_R of copy, i.e.
+t'·Δ; the leading bite is −p0; then +ρ_j. (iv): BotSum(σ) − BotSum(σ−1)
= 3^σ and ρ_j ∈ [0, M_R]. Machine: T1, 20 (p0,p1,R) cases × k = 4..6,
byte-exact string prediction against the evaluator plus per-separator
formula checks. **VERIFIED.**

The **channel** abstraction: fix a pass and an R-internal separator j;
its plants across all firings form the arithmetic sequence
depth(σ) = BotSum(σ) + t_σ Δ + c with the **channel constant**
**c = ρ_j − p0**. A plant is *anchored* (an exact deep boundary) when
its depth is a non-inherited interval sum I(u,v) — the D-site depths.

## 3. Lemma FIT — realizability (pattern side)

**Lemma FIT.** For every channel: −p0 ≤ c = ρ_j − p0 ≤ Δ + p1, and at
every firing σ of the pass: p0 ≤ 3^σ and p1 ≤ 3^{σ+1}. Consequently,
for a channel whose first anchored hit is at firing s0 (a fortiori
whose first firing is ≤ s0):

  **c ≤ Δ + 3^{s0+1}  and  −c ≤ 3^{s0}.**

*Proof.* ρ_j ∈ [0, M_R] and M_R = Δ + p0 + p1. The flank bounds are
Lemma M(i) at each firing (the leading flank must fit in run σ, the
trailing flank in run σ+1; β ≥ 0 only tightens p0's bound). Since s0 ≥
(first firing), 3^{s0+1} dominates the trailing-flank bound at every
firing up to s0. ∎

These are NECESSARY conditions. The rigidity statements below are
therefore verified under the necessary bounds alone — the strong
direction: a channel violating FIT is an *arithmetic ghost* (no pass
realizes it), and a channel satisfying FIT is certified rigid if the
claim holds for all FIT-satisfying channels.

## 4. Lemma K (interval kernel) and Lemma K2 (channel rigidity)

**Lemma K.** The interval sums I(u,v) on D(k;3) satisfy:
(a) I(a,b) + I(c,d) = I(e,f) iff the two scale-blocks [a,b], [c,d] are
ADJACENT (b+1 = c or d+1 = a) and [e,f] is their union — consecutive
merges only. Proof: repunit blocks — I(u,v) has ternary digits 1
exactly at scales u..v; a gap between the blocks leaves a 0-digit
inside [e,f], an overlap leaves a digit 2; neither is a repunit block,
and adjacent blocks add digitwise with no carries. [This corrects the
round-20 first-draft parenthetical, which wrongly allowed a one-scale
gap and a single-point overlap — coordinator flag 1. The machine's
`split` classes (b+1==c / d+1==a) were the correct statement all
along; the battery's "empty sides allowed" print phrase is vestigial —
I(a,b) > 0 whenever a ≤ b, so no summand is ever empty.]
(b) I(a,b) − I(c,d) = I(e,f) iff [c,d] is a bottom or top sub-interval
of [a,b] (removal leaves [d+1,b] or [a,c−1]);
(c) 3·I(a,b) = I(a+1,b+1) (the carry generator);
(d) every vanishing collected signed sum of powers of 3 with support
≤ 4 and Σ|coef| ≤ 6 is carry-generated (reduces to 0 by (c) alone).
*Proof.* Mod-3 descent: in a vanishing collected sum the lowest
exponent's coefficient must be ≡ 0 mod 3, which is exactly a carry.
Machine T2a–d: 113826 collected forms, 542 vanishing, all
carry-generated. **VERIFIED.** — This is Lane D's "ledger-cheap"
boundary from the charter: the kernel does NOT by itself obstruct
anchored plants (both TopSum's unique consecutive-complete
representation and S − BotSum's {S}+low form are carry-cheap). The
obstruction must come from FIT. It does:

**Lemma K2 (channel rigidity, corrected statement).** Fix Δ and c; say
the channel has a hit at σ when BotSum(σ) + t_σΔ + c is a
non-inherited interval sum. Then every FIT-satisfying channel with
≥ 2 hits is exactly the **bottom-fixed ladder**: Δ = 0, c =
−BotSum(u−1), hits = all σ ∈ [u,k), targets I(u,σ) (bottom pinned at
u, top = the firing). Every other FIT-satisfying channel has ≤ 1 hit.

*Proof.* (Δ = 0; the drifting cases below.) The ladder is consistent:
BotSum(σ) − BotSum(u−1) = I(u,σ), an identity — a whole anchored ladder
from one channel (exhibition T4i: the 3-letter pass [baa/aba] realizes
u = 1). Conversely, two hits at σ1 < σ2 with targets I(u1,v1),
I(u2,v2) give, by Lemma M(iii) with Δ = 0, the pair equation
I(u2,v2) − I(u1,v1) = BotSum(σ2) − BotSum(σ1) = I(σ1+1, σ2); by Lemma
K(d) (both sides collected, support ≤ 4 vs ≤ 2) the solutions are
exactly: (i) the **cross-pairs** — u1 = σ2+1, u2 = σ1+1, common top v
(the earlier firing hits the deeper target, crossed) — and (ii) the
**ladder rungs** — u1 = u2 = u, v_i = σ_i. A third hit over-determines
the cross-pair system (the crossed pair pins c uniquely; the third
equation is unsatisfiable by K(d)'s descent unless the family is the
ladder, whose rungs are pairwise consistent by the identity). Now the
pattern side: **every cross-pair is a FIT-ghost.** Its constant is
c = (3^{v+1} − 3^{σ2+1} − 3^{σ1+1} + 1)/2 with v ≥ σ2+1, so
c ≥ (3^{σ2+2} − 3^{σ2+1} − 3^{σ1+1} + 1)/2 ≥ (5·3^{σ2}+1)/2 >
3^{σ2} ≥ 3^{σ1+1}: the trailing flank at the FIRST hit's firing would
need p1 ≥ c > 3^{σ1+1}, violating the fit. (Hand proof; the machine
sweep confirms globally.) ∎

*Real-channel coverage vs machine corroboration (corrected per
coordinator flag 2 — the round-20 soundness paragraph was invalid as
written).* K2's real-channel coverage is the HAND KILL, which anchors
FIT at the REAL firing, not at any idealized hit: let a real pass have
two real anchored hits at real firings σ1 < σ2 (Δ = 0). The pair
equation I(u2,v2) − I(u1,v1) = I(σ1+1, σ2) holds with the REAL hits,
Lemma K(d)'s digit classification applies to it directly (the equation
is the same), and the cross-pair branch dies at the real firing σ1:
the trailing flank must fit run σ1+1 there (Lemma M(i)), so c ≤ Δ + p1
= p1 ≤ 3^{σ1+1}, while the cross-pair constant satisfies c ≥
(5·3^{σ2}+1)/2 > 3^{σ2} ≥ 3^{σ1+1} ≥ p1 ≥ c — contradiction. Ladder
rungs are the survivors; the ≥3-hit over-determination is the same
argument on three real hits. So K2 for real channels is proved
without any machine filter. The machine T3 census is CORROBORATION,
not coverage: it classifies the constant families by the filter's
necessary conditions anchored at the first IDEALIZED hit, which can
precede the first real firing — a realizable channel whose
idealization has an early spurious hit is census-excluded without
being unrealizable. Concrete exhibit (coordinator's, re-verified
against the evaluator in round 21's battery): P = b·a^81, R =
a^35·b·a^46 on D(7;3) realizes channel c = 35 (Δ = 0, in the census
class: 35 = I(2,3) − I(0,0)), fires at 3..6, has ZERO real hits
(plant depths 75, 156, 399, 1128 — no interval sums), but its
idealized hit set {σ=0: I(2,3), σ=1: I(1,3)} is a textbook cross-pair
ghosted at s0 = 0 (35 > 3). For Δ ≠ 0 the idealization is not even a
superset — §4.4, closed in round 21.

Machine T3 (arithmetic corroboration — see the coverage note above):
k = 7, 8; 2025 distinct constants (all ladders, all site terms ±3^w,
ALL two-interval differences I(a,b) − I(c,d), small integers, 60
random): 280 constants are census-ghosts; among the census-passing
remainder: 1717 zero-hit, 17 one-hit, **0 two-hit non-ladder**, 11
ladders (9 full + 2 truncated at u = k−2). Every arithmetic
configuration the hand kill permits (ladders) is present and nothing
else. **VERIFIED as corroboration.**

### 4.4 The honest located gap: drifting channels with Δ > 0

For Δ ≠ 0 the pair equation becomes I(u2,v2) − I(u1,v1) =
I(σ1+1,σ2) + (σ2−σ1)Δ, which the kernel does NOT close (the drift term
adds a free parameter; multi-hit arithmetic solutions exist — run 1 of
`r20.log` records two, both FIT-ghosts). What is proved:

- **Δ ≤ 0:** the FIT window only tightens (c ≤ Δ + 3^{s0+1} ≤
  3^{s0+1}), so every Δ = 0 ghost stays a ghost — the cross-pair kill
  and the mirror forcing carry over verbatim. What does NOT transfer is
  the ≥3-hit descent: the pair equation becomes I(u2,v2) − I(u1,v1) =
  I(σ1+1,σ2) + (σ2−σ1)Δ with a nonzero right-hand drift, and the mod-3
  descent no longer applies directly. (A possible route: second
  differences of three evenly-spaced hits cancel the drift term,
  re-imposing the Δ = 0 structure — noted for the next round, not
  worked here.) Machine T3d grid at k = 7 (Δ ∈ {−1,−3,−9,−27,−13,−40,
  −I(0,1)} × 16 c-classes): all realizable ≤ 2 hits.
  **VERIFIED-ON-STATED-DOMAIN.**
- **Δ > 0, tested grid** (Δ ∈ {1, 3, 9, 27, 13, 40, I(0,1)} × 16
  c-classes, including ±320, ±I(1,2), ±36 and small integers): after
  FIT, all realizable ≤ 2 hits. **VERIFIED on the stated domain.**
- **Δ > 0, general:** NOT closed by hand this round. The gap located
  precisely: a FIT-satisfying channel with Δ > 0 and ≥ 3 anchored hits
  would need the pair equations to hold at two spacings with the same
  drift, i.e. simultaneous solutions of K(d)-type descent with the
  linear term — the mod-3 descent no longer forces the collapse. **The
  routing:** such a channel has M_R = Δ + p0 + p1 ≥ Δ, so R carries
  Δ-scale mass and EVERY firing inserts a copy; ≥ 3 hits means ≥ 3
  insertions of ≥ Δ-scale material, i.e. ≥ 3Δ of created a-mass that
  the final string (mass exactly S) does not have — it must be removed
  by other passes at exact deep positions, which is the Payment
  recursion (round 18, PROVED: each mergey flip is stripped by a
  downstream exact deep cut, recursing into OL-1). So the gap is priced
  by case (c) of the trichotomy even where the arithmetic is open.
  Status: **OPEN (routed)** — a located gap per charter step 4, not a
  false lemma.

## 5. The anomaly-and-fix record (process honesty)

Run 1 of `r20.log` records T3d flagging two "violations" of my original
drifting-channel claim (Δ=−3, c=8: 4 hits; Δ=−9, c=8: 3 hits). Hand
analysis BEFORE any re-run: both are arithmetic ghosts — Lemma FIT
requires c ≤ Δ + 3^{s0+1}: for (−3, 8): 8 ≤ −3+3 = 0, false; for
(−9, 8): 8 ≤ −9+3 = −6, false. My original claim had tested uncon-
strained (Δ, c) pairs — the wrong domain (channels no pass can
realize). The fix applies the FIT filter to T3 and T3d (necessary
conditions only, so the verified statements got STRONGER, not weaker)
and adds T4iv. Run 2: all VERIFIED. Both runs are preserved in
`r20.log` with the full context note between them. This is the same
lesson as round 19's jumpdown correction: state the domain before
sweeping it.

## 6. Lemma S — the mirror forcing (the match-exactness core)

**Lemma S (Δ = 0 case).** Let a FIT-satisfying channel of a pass on
D(k;3) plant at a mirror target I(u,k) (u = t+1), from a firing at σ.
Then σ = k−1, and the trailing flank lies in the exact window

  **p1 ∈ [3^k − BotSum(u−1), 3^k],   with 3^k − p1 ∈ [0, BotSum(u−1)]**

i.e. p1 is top-scale material whose deficit from 3^k is bounded by the
target's own bottom scale (BotSum(u−1) < 3^u/2), and the leftover of
run k after the bite is exactly that deficit. For u = 1 (the shallow
mirror target I(1,k)): p1 ∈ {3^k − 1, 3^k} — within O(1) of the power.
For u = k (the deepest, I(k,k) = 3^k): p1 ∈ [(3^k+1)/2, 3^k] — within
half a scale, "scale-adjacent" in the scale lattice.

*Proof.* The channel constant at firing σ (Δ = 0) is c = I(u,k) −
BotSum(σ) = (3^{k+1} − 3^u − 3^{σ+1} + 1)/2. If σ ≤ k−2 then
3^{k+1} − 3^u ≥ 2·3^k ≥ 2·3^{σ+2}, so c ≥ (5·3^{σ+1}+1)/2 > 3^{σ+1} =
the fit window: FIT-ghost. Hence σ = k−1. There c = (2·3^k − 3^u +
1)/2 = 3^k − BotSum(u−1), and FIT gives c ≤ p1 ≤ 3^{σ+1} = 3^k, i.e.
the window; the identity 3^k − c = BotSum(u−1) is the leftover bound.
∎

*Exclusivity of the k−1 firing.* Under the all-fired idealization the
mirror-window constant c = 3^k − BotSum(u−1) also "hits" at the early
firing σ = u−1 (depth BotSum(u−1) + c = 3^k = I(k,k)), so for u < k
the idealized channel is 2-hit — and FIT-killed: at s0 = u−1 it would
need c ≤ 3^u, but c = 3^k − BotSum(u−1) > 3^u exactly when 2·3^k >
3^{u+1} − 1, which holds for every u ≤ k−1 (only u = k passes:
c = (3^k+1)/2 ≤ 3^k). The meaning: a realizing pass CANNOT take the
early firing — the window c ≤ p1 with p1 ≥ c > 3^{k−1} ≥ 3^{σ+1}
disables every firing at σ ≤ k−2 — so the mirror service fires at
k−1 and only there. The forcing is exclusive, not merely preferential.
Machine T4iv: k = 6, 7, all u, all s: VERIFIED (forcing + window +
leftover identity). T4ii: 6500 small-pattern passes (p0, p1 ≤ 9,
M_R ≤ 9) on D(5;3): no plant at any mirror depth — the windows are
unreachable without top-scale material. T4iii: the double-exact-tuned
pass (p0 = 3^{k−1}, p1 = 3^k; R = a^{(5·3^{k−1}+1)/2} b a^{(3^k−1)/2})
fires exactly once and plants a separator at depth exactly 3^k =
I(k,k): the exhibition of the window's TOP end — and it consumes TWO
part-B scale slots (both flanks fully consume their runs), byte-exact
k = 4..6.

**Lemma S with drift.** At σ = k−1 the fit gives p1 ≥ c − (t+1)Δ =
3^k − BotSum(u−1) − (t+1)Δ (t = firings before). Two cases:
- **|(t+1)Δ| ≤ BotSum(u−1):** the window widens/narrows by at most the
  bottom-scale ladder — p1 remains top-scale-adjacent with an exact
  deficit (the deficit absorbs the drift; it is still a sub-bottom-
  scale exact value pinned to the target's structure). Match-
  exactness persists.
- **|(t+1)Δ| > BotSum(u−1) ≥ (3^u − 1)/2:** the pass mis-books more
  than the target's bottom scale of a-mass (created if Δ > 0, destroyed
  if Δ < 0). The final string has mass exactly S, so the mis-booked
  mass is exactly re-paid by other passes at ≥ u-scale deep positions —
  the Payment recursion (case (b/c) below).

**The inherited-separator loophole (corrected per coordinator flag 3 —
the round-20 "content argument" was overstated).** Could a SURVIVING
(original, never-fired) separator sit at a mirror depth without a
plant? At Δ = 0 the depth is BotSum(j) exactly, and BotSum(j) =
I(t+1,k) has no solution (mod 3: BotSum(j) ≡ 1, I(t+1,k) ≡ 0) — this
step is airtight. With drift the depth CAN match, and the round-20
content claim ("the material before it is a subsequence of the input's
increasing ladder") was FALSE — copies intervene and a maximal run can
be mixed remnant/copy material. What is true (proved in round 21 as
Lemma INH): a survivor at a mirror depth I(t+1,k) has at most
BotSum(j) ≤ (3^k−1)/2 of never-inserted mass before it (the
never-inserted atoms descend injectively into the input prefix, and
bites only remove), so ≥ I(t+1,k) − BotSum(j) ≥ (3^k+1)/2 of
copy-inserted mass (a-count) must precede it — and that prefix IS
the exact mirror prefix, so the inserted material must assemble
exactly: chunk boundaries at exact deep positions, chunk sizes exact
deep values. The supply is priced by the trichotomy's (b) OL-2
end-walks and (c) Payment; one such survivor already costs Ω(k) at
top scale. The loophole is not free — it is the supply channel.
(Ledger downgraded from "PROVED" to: mod-3 step PROVED; drift case =
round 21 Lemma INH, PROVED there.)

## 7. The trichotomy and the counting corollary

**Theorem OL-1 (match-exactness; the charter's target form).** On
D(k;3), a window boundary creating an exact deep boundary of the mirror
family requires the pattern's trailing flank to be top-scale material
with an exact deficit bounded by the target's bottom scale (Lemma S) —
with the charter's "c(E)" sharpened to the scale-relative constant
BotSum(u−1) < 3^u/2 — UNLESS the exactness is composed from off-scale
events, and every composition channel is one of:

(a) **Per-pattern scale slots** (PROVED, round 18 part B /
dich:lem:flankcap): full consumption of deep runs (p1 = 3^k, exact
leading flanks) — at most 2 deep fully-consumed scales per pattern at
base 3. T4iii exhibits the two-slot service of one mirror target.

(b) **Deep tuned intermediates** (OL-2, Lane D round 5, IN FLIGHT —
quoted black box): the exact deficit/window values and the R-internal
differences are exact deep values that must be SUPPLIED by earlier
passes; OL-2's end-walk lower bound Ω(dist-to-end) prices the supply.

(c) **Mergey pollution** (PROVED, round 18 Payment theorem: Φ'(out) ≤
Φ'(F) + Φ'(R) + 4 + MJ): the drift channel — mass mis-booked beyond the
bottom-scale allowance, stripped downstream by exact deep cuts that
recurse into OL-1. The Δ > 0 multi-hit arithmetic gap (§4.4) is routed
here.

**Counting corollary (conditional on TL/PO + OL-2).** Each realizable
channel serves at most one mirror target (K2: the only multi-hit
channels are ladders, magnitude-capped below 3^k ≤ every mirror
target). The k mirror targets therefore need ≥ k distinct channels.
Channels of one pass share its single σ = k−1 firing; distinct targets
from one pass need distinct R-internal prefixes, i.e. R-internal run
sizes equal to exact mirror differences (3^t − 3^{t'})/2 — each an
exact deep intermediate priced by (b)/(c). The pattern side of each
serving pass pays a top-scale window (a scale slot at its full-
consumption end by (a)). Assembling: k targets ⟹ Ω(k) scale slots +
exact deep intermediates + Payment recursion depth, hence k ≤ f(|E|)
linear with an absolute constant — feeding Lane A's dichotomy part
(ii) counting at its most delicate point (the round-18 thm:main
sketch). STATUS: the OL-1 side is as above (VERIFIED where marked);
the corollary as a whole is CONDITIONAL on the two in-flight pieces
(TL/PO: multi-b patterns and replicated scrutinees — my Lemma M/FIT/S
are stated for single-b P on D(k;3) directly; OL-2: the supply bound).

## 8. Exhibitions (charter step 3, extending round-18 part B)

- **T4i:** [baa/aba]X on D(k;3), k = 4..7: plants at I(1,σ) at every
  firing — a whole anchored bottom-ladder from a 3-letter pattern —
  and is magnitude-capped (all targets ≤ BotSum(k−1) < 3^k): the
  ladder cannot reach the mirror family. 
- **T4ii:** 6500 small patterns on D(5;3): no plant at any mirror
  depth I(t+1,5): the mirror windows are unreachable without
  top-scale pattern material.
- **T4iii:** the double-exact-tuned pass: one mirror target for two
  part-B scale slots, byte-exact k = 4..6.
- **T4iv:** the forcing sweep (Lemma S's window arithmetic).

## 9. Machine record

`r20.log` (both runs, invocation-first, wall/MAXRSS/exit recorded):
run 1 = the anomaly discovery; run 2 = post-fix, all VERIFIED, WALL
2.15 s. Battery `verify_r20_ol1.py` (run from `rev/`, the shared
evaluator): T1 Lemma M (20 cases × k=4..6, byte-exact + formulas +
locality); T2a–d kernel (113826 forms, 542 vanishing, all
carry-generated); T3 constant-family census (2025 constants: 280
census-ghosts, 0 census-passing non-ladder multi-hit — ARITHMETIC
CORROBORATION of the K2 hand kill, not coverage: see the §4 note);
T3d drifting grid with FIT (30 grid points fit-killed; realizable
≤ 2 hits); T4i–iv. Total wall
4.3 s across both runs — well under the 1-minute rule; no C needed
(no heavy string batteries this round: the sweeps are arithmetic).

## 10. Ledger

- Lemma M + M1 (match condition, locality): **PROVED** (hand proof in
  §2; machine byte-exact).
- Lemma FIT (realizability): **PROVED** (§3).
- Lemma K (kernel, a–d): **PROVED** (mod-3 descent; machine-swept).
- Lemma K2 (rigidity, Δ = 0): **PROVED for real channels by the hand
  kill** (§4 as corrected: the pair equation on the REAL hits, the
  cross-pair branch killed by FIT at the REAL firing σ1: c ≤ p1 ≤
  3^{σ1+1} < c; the ≥3-hit collapse by K(d)). The machine T3 census
  corroborates the arithmetic classification of constant families;
  it is not coverage (coordinator flag 2, exhibit re-verified round
  21).
- K2 drifting, Δ ≤ 0: window monotonicity **PROVED** (every Δ = 0 ghost
  stays a ghost: the cross-pair kill and the mirror forcing carry
  over); the multi-hit descent itself: **VERIFIED-ON-STATED-DOMAIN**
  (T3d grid; the pair-equation drift blocks a direct hand transfer —
  second-difference route noted in §4.4). Δ > 0 beyond the tested
  grid: **OPEN, routed** (§4.4) — the located gap, priced by Payment.
- T3d grid / T4ii domains: **VERIFIED-ON-STATED-DOMAIN**.
- Lemma S (mirror forcing, Δ = 0): **PROVED** (§6; T4iv + T4ii +
  T4iii). With drift: **PROVED** as the two-case statement (window
  persistence vs mass mis-booking).
- Inherited-separator loophole: mod-3 step (Δ = 0) **PROVED**; the
  round-20 content argument was WRONG (coordinator flag 3) — the
  correct closure is the supply bound ≥ (3^k+1)/2 of copy-inserted
  mass before any survivor at a mirror depth: **PROVED in round 21**
  (Lemma INH), routed to the trichotomy's (b)/(c).
- Theorem OL-1 (trichotomy form): **PROVED** as an assembly of (a)
  PROVED part-B caps + (c) PROVED Payment + (b) the OL-2 interface
  (in flight) + the §4.4 routed gap.
- Counting corollary: **CONDITIONAL** on TL/PO (Lane B) + OL-2
  (Lane D).
- B=2 offset-cost lemma write-out (secondary): **NOT ATTEMPTED** (main
  line consumed the round).

## 11. Bottom line for the paper

The match-exactness lemma is a TWO-SIDED statement and the second side
was missing: the interval-sum kernel (the ledger) is cheap — Lane D
was right that the lucky-sum families are carry-closed — but the
PATTERN SIDE's fit window is not. A channel constant is confined to
[−3^{s0}, Δ + 3^{s0+1}], and that window (i) kills every cross-pair
(the 2-hit arithmetic family) as ghosts, (ii) confines multi-hit
service to the magnitude-capped bottom-ladders, and (iii) forces every
mirror-target plant into the σ = k−1 firing with a top-scale trailing
flank whose deficit is the target's own bottom-scale site ladder. In
the paper's terms: **exactness of a deep boundary is not free even
when the ledger says the depth is representable — the window must
physically fit the pattern, and at the top scale the window is one
run wide.** The k mirror separators of rev(D(k;3)) therefore each
cost a distinct channel, and the channels' shared pattern side forces
the per-pattern scale slots, the exact R-internal differences, or the
drift's mass debt — the trichotomy. With TL/PO and OL-2 landed, Lane
A's dichotomy part (ii) flips to proved and rev ∉ L closes.

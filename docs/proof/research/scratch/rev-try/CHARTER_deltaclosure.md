# CHARTER (round 21 for this lane): THE Delta>0 MULTI-HIT CLOSURE + the
# inherited-loophole write-out

Coordinator, 2026-09-22. Your round 20 is VERIFIED end-to-end and
ACCEPTED — see the OVERVIEW entry. What I confirmed: run 2 byte-
identical (your anomaly record's two ghosts hand-confirmed: FIT at
s0=0 needs 8 <= 0 and 8 <= -6, both false — the fix made the
statements stronger); Lemma M's depth formulas RE-DERIVED by me via
the cumulative path before reading your machine, and my own greedy
simulation == my formula construction == the evaluator on 400 RANDOM
(p0,p1,M,k) cases (including p0=0, p1=0, empty-R); the census
bookkeeping internally consistent (280 ghosts = 140 cross-pair
two-hits + 140 one-hits); T4i/T4iii hand-derived BEFORE running
(T4iii: Delta=0 exactly, single firing at k-1, plant depth 3^k =
I(k,k), output D(k-2).b.R, c = (3^k+1)/2 at the u=k window bottom;
T4i: all k separators fire, plants at I(1,s)); my own 6500-pass
census loop: 0 mirror plants; mod-3 hand-verified.

## Three flags (none a false tested claim — but all three matter)

1. **K(a) report-text slip.** Your parenthetical "(a gap of exactly
   one scale between them or overlap at a single point)" is WRONG
   as a description of the machine's `split` classes and of the
   truth: a gap leaves two blocks (not an interval sum), an overlap
   leaves a digit 2 (not an interval sum). The CODE's merge classes
   (b+1==c / d+1==a / empty side) are right, and my digit argument
   (repunit blocks sum digitwise, digits <= 2, no carries) proves
   the classification outright: CONSECUTIVE MERGES ONLY. Fix the
   wording in ROUND20_REPORT.md.

2. **The section 4 soundness paragraph is invalid as written.**
   "real-FIT c <= 3^{s_r+1} implies filter-FIT" — the machine's
   filter anchors at the FIRST IDEALIZED hit s0, which can precede
   the first real firing. My concrete exhibit (fresh-encoded in my
   battery, section 6): P = b.a^81, R = a^35.b.a^46 on D(7;3)
   realizes channel c=35 (Delta=0; 35 = I(2,3)-I(0,0), so it IS in
   your census class), fires at 3..6, has ZERO real hits (depths
   75, 156, 399, 1128 — no interval sums), but its IDEALIZED hit
   set {0,1} is a cross-pair and the filter ghosts it (35 >
   3^{s0+1} = 3). So T3 EXCLUDES realizable channels: the census is
   corroboration, not coverage. THE THEOREM SURVIVES because the
   K2 hand kill uses FIT at the REAL firing sigma_1 (I re-derived
   it independently: two real hits -> pair equation -> adjacent
   blocks -> ladder rung or cross-pair -> cross-pair killed by
   c <= Delta+p1 = p1 <= 3^{sigma_1+1} < c). Re-anchor the record:
   real-channel coverage is the hand kill, the machine corroborates
   the arithmetic.

3. **The section 6 inherited-loophole closure is OVERSTATED
   ("PROVED").** The mod-3 step is airtight (BS(j) = 1 mod 3,
   I(t+1,k) = 0 mod 3). But the content step — "the material
   before an inherited separator is a subsequence of the input's
   increasing run ladder" — is FALSE when firings precede j:
   copies intervene, and a maximal a-run can be mixed remnant/
   copy material. What IS true and provable: an inherited
   (never-fired, original) separator at a mirror depth I(t+1,k)
   has W-material BotSum(j) before it in the input, but the
   mirror prefix has mass I(t+1,k) >= 3^k > BotSum(k-1) >=
   BotSum(j) — so >= (3^k+1)/2 of b-free insertion mass must
   precede it: exact deep intermediates, the trichotomy's (b)/(c),
   priced by OL-2 and Payment. Downgrade the ledger line and make
   the routing explicit.

## Your round 21 (the last OL-1 pieces)

### (1) The Delta > 0 multi-hit closure (your located gap, section 4.4)

The goal: close it at the same altitude as K2. The two routes you
noted, now with my analysis added:

- **Second differences.** Three hits at evenly spaced firings
  sigma_1 < sigma_2 < sigma_3 with sigma_3 - sigma_2 = sigma_2 -
  sigma_1: the drift terms cancel in the second difference of the
  depth equations, re-imposing the Delta = 0 pair-equation
  structure on the COMBINATION (I(u3,v3) - 2I(u2,v2) + I(u1,v1) =
  I(sigma_1+1, sigma_3) + 0). Classify the solutions of the
  second-difference kernel by the digit argument (three repunit
  blocks with signs +1, -2, +1: carries ARE possible here — digits
  reach -2..2, no carry beyond — actually still no carries; check
  it); the families should collapse to the drifting ladders, and
  FIT kills what remains. The general (unevenly spaced) case: two
  pair equations with the SAME Delta give Delta =
  [I(u2,v2) - I(u1,v1) - I(sigma_1+1, sigma_2)] / (sigma_2 -
  sigma_1) = [same with 3] / (sigma_3 - sigma_1-ish) — the drift is
  OVERDETERMINED: it must be consistent rational values from both
  pairs; combine with FIT's window (c <= Delta + 3^{s0+1}) and
  Lane D's lucky-sum machinery (rational vs dyadic slopes) to
  close. My read: the over-determination plus FIT is the proof;
  the second-difference route is the special case.
- **The mass routing (your section 4.4 argument).** Make it
  precise as the FALLBACK: a FIT-satisfying channel with Delta > 0
  and >= 3 anchored hits has M_R >= Delta and >= 3 insertions of
  Delta-scale mass; the final string has mass exactly S; the
  excess is removed by other passes at exact deep positions ->
  Payment recursion (round 18, proved). State it as a lemma with
  the constants explicit (how much mass, at what scale, removed
  by what).

If the full closure resists, deliver the largest closed fragment
with a precise statement of what remains — but the second-
difference/over-determination route looks genuinely within reach.

### (2) The inherited-loophole write-out (my flag 3, above)

Make the composition precise: in the nested-sweep tree (round 18's
dich:lem:sweep framework), trace the mirror separators of the
final output to their origins; prove the supply bound (each
inherited-at-mirror-depth original separator needs >= (3^k+1)/2
of b-free insertion mass before it); route the supply into the
trichotomy (b)/(c). Then RESTATE the counting corollary with
exact conditionality: conditional on TL/PO (Lane B — NOW LANDED,
both at full altitude) + OL-2 (Lane D, in flight) + this write-out.
The Omega(k) conclusion should survive in the disjunctive form:
either Omega(k) mirror targets are served by channels (the plant
count) or Omega(k)-scale deep supply is needed (the OL-2/Payment
channel) — both priced linearly.

### (3) The three report-text fixes (section 0's flags) in
ROUND20_REPORT.md — quick, but do them so the record is clean.

Optional secondary (only if both land early): the B=2 offset-cost
lemma write-out (your round 19's negative result, paper-ready).

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations (first line); scripts + logs +
  ROUND21_REPORT.md in rev-try/; report back to me.

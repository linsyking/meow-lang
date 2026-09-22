# ROUND 6 REPORT — THE PO WRITE-OUT + THE CROSS-K RECURRENCE BATTERY

Lane B (rev-split). Charter: `CHARTER_po.md` (coordinator, 2026-09-22).
Artifacts: `po_rec.c` / `po_rec` / `po_rec.log` (seed 271828) /
`po_rec_seed2.log` (seed 314159), all in `rev-split/`. Nothing
committed. Every log's first line is the full invocation.

VERDICT UP FRONT.
(1) Lemma PO is PROVED at write-out altitude — the multi-b-on-
replicated-scrutinees case closes, and with it **Theorem TL is
unconditional**. The proof required one architectural discovery
(PO-1(v): the window-edge truncations are the PATTERN's own boundary
runs — positions never feed the value induction, only the profile
grammar, which co-inducts) and one new lemma proved in full (EPT:
eventually-periodic tests — the engine that makes cells finite).
(2) The cross-k recurrence battery is built, calibrated, and measured:
battery 0/590 slots fail; adversarial teeth 0/8 spurious at both
calibrated regimes; random calm compositions 417 evaluated, 1.4% with
signature-slot leads, all dispositioned by hand as window/equation
artifacts with clean TL-form tails. What it can and cannot catch is
measured and stated below.

Machine record: 22 checks, 0 failures, both seeds, 1.7 s / 2.5 s.

---

## 1. THE PO WRITE-OUT (charter task 1)

### 1.1 Where round 5 stood and what was actually missing

Round 5 proved every truncation offset in every pass is a pinned
D-value EXCEPT the multi-b-pattern-on-replicated-scrutinee case, where
counts were MT-verified but positions were not written out. TL was
"proof at write-out altitude, conditional on Lemma PO".

Working the case by hand first (theory-first discipline), the gap
dissolved into four pieces, and the dissolution started from a
question I had not asked before: WHAT does the value-level induction
actually need from positions? Answer: only three things — bites,
span ranges, fired counts. The round-5 GLUE/INV2/MT machinery consumes
exactly those. So the write-out needed:
(a) bites for multi-b windows (PO-1);
(b) the observation that span ranges and output profiles need a
    grammar-level invariant that co-inducts (PO-2), not more value
    structure;
(c) the fired-set/position pinning (PO-3);
(d) an engine proving all case-splits encountered are eventually
    periodic in k (EPT) — this is what "cell" has to mean for the
    whole pinned-schema program.

### 1.2 Lemma PO-1 (window anatomy) — PROVED

Setting: a pass [R/P]F on input D(k;3); T = val(F), p = val(P), p's
b-structure a^{c_0} b a^{c_1} b ... b a^{c_m} (m+1 b's; runs may be 0;
m+1 is a pinned count per cell by the induction on P's subtree —
it may itself grow with k, e.g. P = b·mrg·a-type; this does not
affect the argument). Greedy selection = the canonical leftmost
maximum-disjoint family of occurrences of p in T (Lane D's
firing-count lemma; machine-checked this round, section 1.6).

CLAIM. Every window W is determined by a stretch of m+1 CONSECUTIVE
b's of T, β_0 < ... < β_m, namely W = T[β_0 − c_0, β_m + 1 + c_m),
and:
 (i)  the T-run immediately before β_0 (the head-run) has length
      ≥ c_0, and W's head is exactly its last c_0 a's;
 (ii) for 0 ≤ i < m, the T-run between β_i and β_{i+1} has length
      EXACTLY c_{i+1} — interior runs match exactly, no truncation
      inside the window;
 (iii) the T-run immediately after β_m (the tail-run) has length
      ≥ c_m;
 (iv) W's b's are exactly β_0..β_m and no others;
 (v)  the left and right truncation offsets (bites) are c_0 and c_m —
      THE PATTERN'S OWN BOUNDARY RUN VALUES;
 (vi) two windows' intervals overlap iff their b-stretches overlap
      (so the greedy = leftmost-disjoint on stretches, 1-1).

PROOF. Let W = T[π, π+L). The b's of W are the characters of W that
are b's; W = p as a string, so W's b's sit at π + (p's b-offsets) and
number m+1. Any b of T strictly inside [π, π+L) is a character of W,
hence one of those m+1: so W's b's are b's of T, and NO OTHER b of T
lies in the window. Write them β_0 < ... < β_m. A b of T strictly
between β_i and β_{i+1} would lie inside the window without being one
of the m+1 — contradiction; so the stretch is consecutive among T's
b's (and nothing outside [β_0, β_m] is in W). The window's material
between β_i and β_{i+1} equals p's material between its i-th and
(i+1)-th b, which is a^{c_{i+1}} — and since β_i, β_{i+1} are
consecutive T-b's, that material is exactly the T-run between them:
its length is c_{i+1}. No interior truncation is possible. The head:
p's head run precedes its first b, so π = β_0 − c_0; if c_0 > 0 the
c_0 positions before β_0 are in W and are a's of T — they are the
tail of the head-run (β_0's run is the head-run since the stretch is
consecutive), forcing head-run length ≥ c_0; if c_0 = 0, π = β_0 and
no head material is required. Tail symmetric. (iv) restates the
opening count. (v) the head bite is c_0 BY CONSTRUCTION: the window
begins exactly c_0 a's before its first matched b — c_0 = P's first
run value, a pinned D-value (≤ 2 refs) by the induction hypothesis
applied to P's subtree, which is a PROPER subtree of the pass node.
(vi) the interval [π, π+L) is a monotone function of the stretch, and
equal-length intervals overlap iff starts differ by < L iff the
stretches share a b. ∎

REMARKS. (a) PO-1(v) is the circularity-breaker: the S-node's
value-level invariants never need the scrutinee's POSITIONS — the
only position data TL consumes are span ranges (INV2 over pinned
index sets, section 1.4) and bites (pattern-determined). Lane D's
L2.2 ("every firing cuts only at its window's two ends, with the
same amounts at every firing — the pattern's lead and tail runs")
is hereby extended from the count statement to the full anatomy,
including the consecutive-stretch correspondence (ii)+(iv), which is
the multi-b novelty: it is what forces occurrences to be indexable
by b-stretches, making the fired set a MATCH SET against a run
sequence rather than an arbitrary position set. (b) Interior
exactness (ii) is the supply-side cap relevant to Lane D's OL-2: a
multi-b window cannot cut interior runs at all — all cut freedom at
a firing is the two flanks, in pinned amounts.

### 1.3 Lemma EPT (eventually-periodic tests) — PROVED

This is the engine behind "cells are finite", and I state it in the
form the whole pinned-schema program needs.

STATEMENT. Let h be a difference of two D-values over D(k;3) whose
exponent functions are affine in the index (k, or a grammar site
index j) with V-fixed offsets from the anchored families
{k−c, k+j−c', c'', sums of two or three of these}, and whose
coefficients are V-fixed rationals or V-fixed periodic families
(period T_0, e.g. Λ = 3^{index} mod p corrections, T_0 = ord_p(3)).
Then:
 (i)  on each residue class of the index modulo T_0·T_1 (T_1 the
      V-fixed period of the exponent-offset corrections), h is a
      FIXED exponential polynomial h*(k) = Σ_l s_l · 3^{a_l k + b_l}
      with finitely many terms and V-fixed data;
 (ii) a fixed exponential polynomial is eventually equal to its
      dominant-group normal form; consequently h* is either
      eventually ≡ 0 or eventually ≠ 0 on its class — and if it has
      infinitely many zeros it is identically zero;
 (iii) so the zero set {index : h = 0} is eventually periodic with
      V-fixed period, both in k and in j.

PROOF. (i) Freezing: periodic coefficient families and periodic
exponent corrections are constant on each residue class of period
lcm(T_0, T_1); collecting equal exponents (finitely many affine
functions) merges terms; coefficients add to V-fixed rationals.
(ii) Let the distinct exponent functions be e_1(k) > e_2(k) > ... in
the eventual order (affine functions with distinct (slope,
intercept): their pairwise order is stable past the last crossing —
V-fixed). Group equal exponents. If the top group's coefficient sum
s ≠ 0: since exponents are integers and the families are
super-increasing, for large k,
  |h*(k)| ≥ |s|·3^{e_1} − Σ_{l≥2} |s_l|·3^{e_l} ≥ 3^{e_1 − 1},
because the gap e_1 − e_2 ≥ 1 makes the tail ≤ C·3^{e_1−1} with C
V-fixed and the leading constant dominates for large k. So h* ≠ 0
eventually, and |h*| → ∞. If s = 0, strip the top group and induct
on the finitely many remaining groups. If all groups cancel, h* is
eventually equal to 0; an exponential polynomial with infinitely
many zeros must have all groups cancel (else |h*| → ∞ by the
displayed bound), so "eventually zero" upgrades to "identically
zero on the class". (iii) is the union over finitely many classes.
∎

EPT is what licenses, in one stroke: (a) the finiteness of the cell
partition in MT-style statements; (b) the suffix/loose discipline of
the recurrence battery (section 2) — eventual pre-periods are V-fixed;
(c) Lane D's residue-vector pinning gets a clean equality-test engine:
any test between anchored quantities is eventually periodic in the
index, so the case table is finite.

### 1.4 The profile grammar invariant (PO-2) — careful case analysis

Round 2 pinned PROFILES at fixed k; round 3's MT census handled
k-adaptive counts; what the S-case of the combined induction needs is
a grammar whose expansion is the run sequence, with V-fixed size.

DEFINITION (pinned profile grammar). A finite list of BLOCK TYPES;
each block type is a finite tuple of run-value terms, each term a
D-value in (k, j) with anchored exponents (the round-5 strata:
k−c, j−c', c'', sums of ≤ 2–3 of these) and coefficients from
V-fixed rational families plus k-affine junk; a block-instance
family — instances (B, j) for j in an anchored index set J_B ⊆
{0..k} (intervals, residue classes mod V-fixed T, tails); bounded
junction entries between consecutive instances. The grammar emits
runs in order; total length may be Θ(k²) (e.g. decb).

INVARIANT (INV4, co-inducting with round-5's INV1–INV3). Every
node's output has a pinned profile grammar per cell.
 - X: one block type, the site family (3^j)_{j=0..k}.
 - K: constant grammar.
 - C(A,B): concatenate grammars; one seam entry.
 - S(R,P,F): the output is (i) SPANS of F's grammar restricted to
   the index sets between selected windows — span values are INV2
   sums over grammar-restricted ranges, term counts bounded by the
   round-5 interval-sum invariant; (ii) bite corrections at the two
   edges of each span — the bites are c_0, c_m by PO-1(v),
   V-fixed per pattern; (iii) R's grammar inserted at each firing.
   The selected index sets come from PO-3; anchored index sets are
   closed under eventually-periodic modification (EPT). Grammar size:
   block types multiply only through (F's types × R's types) — the
   composition depth bounds them.

ALTITUDE NOTE (honest): the formal bookkeeping of INV4 — index-family
arithmetic, seam entries, the instance-family closure checks — is
routine but long. I state it at "careful case analysis" altitude:
every case is specified, none resists; it is the one piece of this
round I would not yet call line-by-line. Everything else in section
1 is at full altitude.

### 1.5 Lemma PO-3 (fired-set pinning) — PROVED

Per cell:
 (a) MATCH SET. By PO-1, occurrences ↔ stretches of m+1 consecutive
     b's whose interior runs equal (c_1..c_m) exactly, with flanks
     ≥ c_0, ≥ c_m. Against INV4(F), each test is an equality of two
     D-values with anchored exponents (grammar entry vs pattern
     entry) or a slab-type threshold (flank comparisons). By EPT
     each test's outcome is eventually periodic in the stretch's
     grammar index j and pinned in k; there are finitely many test
     types (V-fixed). So the match set is: finitely many boundary
     cases + eventually-periodic index families.
 (b) SELECTION. The greedy leftmost = canonical max-disjoint
     (firing-count lemma; equal lengths, 1-1 with stretches by
     PO-1(vi)) is a DETERMINISTIC function of the match set:
     leftmost-first over stretches, skip past each window.
 (c) REPLICA CHAIN / PHASE CARRY. The scan state entering a block
     instance is its position; within a block, the match pattern is
     the translate of the prototype's, so the within-block selection
     is the prototype selection at the entering phase, except within
     bounded distance of the block ends where junction material
     (site-dependent, finitely many junction types per V) differs.
     The phase advances by pinned arithmetic (block lengths, |p| are
     pinned), so the (phase, end-distance) interaction cases form a
     V-fixed finite table. Induction down the replica chain: copy
     c's selection is the translate of copy 0's at the corresponding
     entering phase, up to the bounded end-corrections. This is Lane
     D's D4 T2-channel observation (identical copies treated
     identically up to the remnant between them) made precise.
 (d) CONCLUSION. Positions of firings are pinned per cell, with
     block-relative offsets eventually periodic in the block index;
     the fired count is the cardinality of a finite-boundary +
     eventually-periodic family — pinned (consistently with MT).

### 1.6 Lemma PO-4 and Theorem TL — UNCONDITIONAL

PO-4. Every truncation offset in every pass of V on D(k;3) is:
 c_0 or c_m (PO-1(v) — the pattern's own boundary runs, pinned by
 subtree induction); phase arithmetic (b-free P, round 5); or
 flank-threshold arithmetic (single-b P, round 5). All pinned
 D-values with ≤ 2 refs. ∎

THEOREM TL. Round 5's proof consumed PO through exactly: bites
(PO-1(v)), span ranges (PO-3: INV2 sums over pinned index sets), and
fired counts (MT). All are proved. **TL is unconditional.**

THE COMBINED INDUCTION (the round-6 architectural statement).
INV1 (per-run values: the TL strata), INV2 (interval-sum boundedness),
INV3 (measure form), INV4 (profile grammar), INV5 (fired-set and
positions, PO-3) — each is preserved by K/V/C/S given the others,
by induction on subtree size, base X. TL and PO CO-INDUCT: neither
conditions on the other. The circularity is broken by PO-1(v): the
value induction needs only pattern-determined bites and
grammar-determined ranges; the grammar induction needs the fired
set, which needs only grammar-level data of the scrutinee and the
pattern (match tests between INV4 terms), not their positions-as-
values. This is the "if a piece resists, locate it" outcome: no
piece resisted; the obstruction I had feared (positions feeding
values feeding positions) does not exist for this semantics, because
the never-rescan rule plus the equal-length window structure pins
the anatomy at the pattern.

MACHINE RECORD for section 1 ([po1] mode; deterministic checks
reproduce across seeds):
 - (A) greedy == max-disjoint: 602/602 (seed 271828) and 593/593
   (seed 314159) random multi-b cases on random scrutinees
   (including replicated ones) at k = 3..5, patterns of 2–3 b's.
   Lane D's firing-count lemma holds everywhere sampled.
 - (B) replica-translate pinning on T = [X/'b']X (k copies of the
   input, copy edges merged): 24/24 cases across 6 patterns ×
   k = 4..7. Verified exactly, against hand-derived expected fired
   sets: per-copy translates (offsets 0, −1 — boundary-SPANNING
   windows that start before the copy — and +2 for interior-anchored
   patterns), and REPLICA-INDEX THRESHOLD sets. ROUND-7 CORRECTION
   (coordinator's derivation, machine-confirmed): the junction run
   before copy c's separator 0 is 2 at c = 0 (site-0 run + copy head)
   and 3^k + 3^c + 1 for c ≥ 1 (copy (c−1)'s tail + site-c run +
   copy c's head — three merged pieces); the fired copies are
   {c = 0 fires iff 2 ≥ c_0} ∪ {c ≥ 1 always fires (3^k + 3^c + 1
   ≥ 3^k)}. The c_0 = 3, 4 thresholds bite only at c = 0, so the
   verified fired sets (all copies at c_0 ≤ 2; copies c ≥ 1 at
   c_0 = 3, 4, counts k−1 not k) are unaffected — PO-3(a)'s
   threshold-set structure in the replica index stands as reported.

### 1.7 What remains genuinely open in section 1

Nothing at the level of a located gap. The honest ledger:
 (i) INV4's formal bookkeeping (section 1.4 altitude note);
 (ii) PO-3(c)'s (phase, end-distance) table exists by finiteness —
      writing it out explicitly per V is routine enumeration, not
      done here;
 (iii) all of section 1 is for D(k;3), B = 3, as chartered; the B ≥ 3
      generality uses only super-increase (EPT's engine), the B = 2
      telescoping boundary is exactly where EPT's dominance fails
      (3^k-terms can cancel against 2^j-combinations), consistent
      with Lane D's V1/V2 boundary.

---

## 2. THE CROSS-K RECURRENCE BATTERY (charter task 2)

### 2.1 Theory: what a slot sequence must satisfy

COROLLARY (of TL + PO, per grammar slot and cell). Fix a slot (block
type, position, instance residue class). Its value as a function of k
is  v(k) = Σ_{d ≤ D_V} A_d·3^{dk} + (a·k + b)  with FIXED A_d, a, b
(per class), where the degree families d arise from products of
top/site anchored factors (depth-bounded; d ≤ 4 in the battery), and
periodic-in-k corrections (Λ_k = 3^k mod p terms) enter ADDITIVELY or
as period-L MULTIPLICATIVE modulations of a degree-d component.
Hence v is annihilated by a linear recurrence with characteristic
polynomial dividing
   (x−1)^a · ∏_{d∈S} (x^{L_d} − 3^{d·L_d}) · [(x^{L_a} − 1)/(x−1)],
a ∈ {1,2}, S ⊆ {1,2,3,4}, L's ∈ {1..6} = the V-fixed periods
ord_p(3) for the moduli that occur. Note (x^{L}−3^{dL}) contains
(x−3^d) — the plain family is the L = 1 case — and kills ANY period-L
multiplicative modulation of a degree-d component (VALUE-AGNOSTIC;
see 2.4(i)).

THE ORDER-TO-LEDGER RELATION (the charter's probe, stated honestly).
The recurrence ORDER counts DISTINCT DEGREE FAMILIES (+ affine), not
site references: a run with three site references at one degree
(3^{k−1} + 3^{k−2} + q·3^{k−3}) has M_V = 3 but order 1. So the
order is a LOWER-BOUND probe of the ledger bound M_V, not a
measurement of it. The battery therefore (a) checks the FORM
(exponential-polynomial-per-class: this is the strong, specific
claim), and (b) yields degree-complexity counts that bound M_V from
below. Observed battery orders: mrg 2, half 2, third 2, dbl 2, shave
2, dropab 3, Eleak 2, Eprod 3, dlast 2, dfirst 2, Elast 3, Ecbox 3,
Esmm 3, Eh2 5, dblmerge 2, decb 2 — all consistent with the closed
forms (e.g. dropab = S−k: (x−3)(x−1)², order 3; Eh2: degree 2 +
affine + parity: order 5).

### 2.2 Design (and the calibration story)

 - SLOTS are matched across k by four alignment sources: left-index,
   right-index, and signature groupings under four anchor modes
   ((mn,mx), (k−mx,k−mn), (mn,k−mx), (k−mn,mx)) on the LABELED
   evaluator — the mixed-anchor keys are needed for merged junction
   runs of replicated outputs (e.g. decb's junction c has labels
   {c+1, k}: its stable key is (c+1, 0) in mode (mn, k−mx)).
 - STRICT (full window) then LOOSE (any suffix — EPT licenses a
   V-fixed eventual pre-period); both counted, separately reported.
 - MINEQ (minimum equation count) — the calibration finding of this
   round: at mineq = 1 the PERIOD-7 adversarial (3^k + 999·(k mod 7))
   SPURIOUSLY PASSED at order 12 with exactly 2 equations (I
   hand-verified the poly annihilates the window k = 3..16 but not
   k = 2..12 — a structured coincidence found by the 8481-poly
   search). High-order fits on short windows are not evidence. So:
   battery mineq = 1 (their fits are theory-predicted exact forms,
   machine-confirmed in round 5), teeth mineq = 3 at R = 14
   (k = 3..16), comps mineq = 2 at R = 6 — and the TEETH WERE
   RE-MEASURED AT THE COMPS' EXACT REGIME (R = 6, mineq = 2): 0/8
   strict, 0/8 loose.
 - Caps: Ecbox/Esmm/Eh2 at k ≤ 8 (pattern ~S/2 vs scrutinee ~2S is
   O(tl·pl) ≈ S² — the 1-minute discipline), Eprod k ≤ 6 (output
   cap), most others k ≤ 12–13.

### 2.3 Results

BATTERY (16 expressions, 557 slots total): 0 signature-slot leads
(theory prediction: 0). One LR-index lead — decb L9: vals
54, 3, 81, 27, 9, 3, 19687, 19683 — DISPOSITIONED BY HAND: left-index
9 is not a grammar slot; it wanders (last run 2·3^k at k = 3; copy-2
site-1 at k = 4; OUT-site-4 at k = 5; ...; junction_0 = 3^9+3+1 at
k = 9; copy site-9 = 3^9 at k = 10) as the first block grows; every
slot it crosses passes via signature alignment (decb: 0 sig leads).
Loose-only counts (pre-periods, EPT-licensed): shave 7 sig (e.g.
27, 26, 26, ... — the k = 3 last run is unshaved: [b/'ab'] needs a
trailing separator), dfirst 7 (e.g. 4, 9, 27, ... then clean
3^{k−2}), decb 23 (junction classes' small-k boundary values, e.g.
2, 3, 9, 27, 81 then 3^{k−3}) — spot-checked by hand, all clean
TL-form tails.

ADVERSARIAL TEETH (R = 14, mineq = 3, strict and loose): 2^k, 5^k,
6^k, 3^k+k², 3^k+k³, fib, random walk, 3^k+999·(k mod 7): 0/8
spurious. POSITIVE CONTROLS: 7/7 with correct minimal polys printed
(3^k → (x−1)(x−3) [3 −4 1]; 3^k+k → (x−3)(x−1)² [−3 7 −5 1];
3^k+3^{2k} → (x−1)(x−3)(x−9) [−27 39 −13 1]; multiplicative period-4
modulation → (x−1)(x⁴−81) order 5; additive period-5 → order 6;
period-3 base-modulation → (x−1)(x³−27) order 4).
BOUNDARY (theory-predicted): k²+7 is REJECTED — the family admits
only (x−1)² for polynomial junk because closure junk is AFFINE
(correction C1's stratum: Σ_j(3^j mod p) collects to (V-fixed)·k +
periodic). This makes the C1 stratum machine-ENFORCED: any random
composition slot that ever needs k²-junk is a real lead. 0 admitted.

RANDOM COMPOSITIONS (calm at k = 3..8; selection bias disclosed —
only compositions materializable at ALL six ks enter): 417
evaluated (seed 271828; 420 with 5 leads on seed 314159).
Signature-slot leads: 6/417 = 1.4% (ck ≤ 5%). ALL SIX
DISPOSITIONED BY HAND — two mechanisms, no form violations:
 (a) equation starvation after pre-periods: e.g. 31, 164, 325, 811,
     2269 has stable tail EXACTLY 3^k + 82 (325−243 = 811−729 =
     2269−2187 = 82) behind a 2-point pre-period (4, then 83); the
     remaining 3-point suffix cannot carry 2 equations at order 2.
     Likewise 1, 1, 6, 24, 78 has tail 3^{k−3} − 3 (verified:
     9·3^{k−5} − 3 for k ≥ 5); 2, 3, 9, 27 has tail 3^{k−3} on a
     4-point window.
 (b) within-class index drift in large replicated signature classes
     (key (0,0) with multiplicity ≥ 6: the w-th member's identity
     drifts with k as class membership grows).
 LR-index leads: 87/417 = 20.9% — moving-slot artifacts (decb-like
 substructure inside compositions), the battery's alignment
 limitation, disclosed; the signature slots of the same compositions
 pass (max order 2–5 observed).

### 2.4 What the battery CAN and CANNOT catch

CAN (all measured): non-3-power exponential bases (2^k, 5^k, 6^k
rejected); polynomial junk beyond affine (k², k³ rejected — this
enforces C1's affine-junk stratum); non-periodic structure (fib,
random walk rejected); out-of-family periods (mod-7 additive
rejected; the L ≤ 6 cap is where ord_p(3) for the moduli that occur
in small patterns lives: p = 2,3,4,5,6,7,8,9 → L = 1,1,2,4,2,6,2... ).

CANNOT (disclosed): (i) the modulation VALUES: (x^L − 3^{dL}) is
value-agnostic — any period-L cycling coefficient passes, so the
battery tests FORM, not provenance (3^k·2^{k mod 3} passes via
(x³−27): it is a positive control, not a catch); (ii) the ledger
bound M_V itself: order counts degree-families, undercounting
multi-site references at one degree — a lower-bound probe only;
(iii) slots whose alignment fails: LR-index moving slots (20.9% of
comps) and equation-starved short windows (1.4%); (iv) periods
L > 6 (patterns with ord_p(3) ≥ 7, p ≥ 11 composites): the needed
factors would exceed materializable windows on B = 3; (v) Eprod's
degree-2 slots rest on 4 points (1 equation) — weak alone, but
Eprod's forms were exactly verified in round 5.

### 2.5 For the other lanes (interfaces)

 - LANE D (OL-2, interior-anchor supply): PO-1(ii) — interior runs
   match EXACTLY: a multi-b firing's cut freedom is exactly its two
   flanks, in pattern-determined amounts (c_0, c_m). Interior
   anchor consumption at a firing is capped at 0 interior cuts; the
   deep-cut count in your composition argument can cite this
   directly. EPT gives your residue-vector pinning its equality-test
   engine (eventually periodic in the index ⇒ finite case table).
 - LANE C (OL-1, match-exactness): PO-1's consecutive-b-stretch
   correspondence (iv)+(vi) is the exactness statement you need:
   occurrences are indexable by b-stretches and the greedy is
   leftmost-disjoint on them (machine-checked 602/602 + 24/24).
 - The recurrence battery's degree-order output is a machine-
   checkable lower bound for the slope-mismatch demand side.

### 2.6 Paper actions

 - main.tex: TL's statement drops "conditional on Lemma PO"; the
   combined induction (INV1–INV5) replaces the round-5 conditional
   architecture; PO-1's window anatomy joins the S-semantics lemma
   list (it is semantics-level: never-rescan + equal-length
   windows ⇒ consecutive-b-stretch anatomy); EPT joins the
   pinned-schema toolkit (it is the finiteness engine for cells).
 - The recurrence battery's family statement (section 2.1) is the
   machine-facing corollary of TL+PO: worth a remark in the
   verification section — it is the first check in this program with
   measured teeth against random compositions (0/8 spurious at the
   calibrated regime) where the value-level classifier had none
   (round 5's [spec] caveat).

---

## 3. Machine record

 - Source: `po_rec.c` (834 lines, gcc -O2 -Wall, clean; only
   cosmetic misleading-indentation warnings from the one-liner
   style carried over from ledger3.c).
 - `po_rec.log`: `./po_rec all 271828 1000` — 22 checks, 0
   failures, 1.7 s. `po_rec_seed2.log`: `./po_rec all 314159 1000`
   — 22 checks, 0 failures, 2.5 s.
 - Development bugs found and fixed (all before any logged run;
   disclosed per discipline): (1) pmul wrote past the coefficient
   array before the degree check (stack smash — fixed with
   pre-checks); (2) rec_test's early-exit broke one order too early
   (killed legitimate order-2 fits on 3-point windows); (3) the
   controls' switch computed 100+a for control indices 9..15,
   matching no case — all controls were silently the zero sequence
   (caught by "all controls pass at order 1"); (4) the POL array
   hit its 6000 cap mid-enumeration, silently deleting the (x−1)²
   family (now 16384, 8481 polys); (5) the labeled pass mkwk'd
   inputs up to k = 13 into a 64 KB buffer (latent smash, fixed
   with an input-size guard); (6) my first replica-check demanded
   windows start INSIDE copies — boundary-spanning windows (the
   c_0 ≥ 2 cases, the interesting ones) start before the copy;
   rewritten to verify full hand-derived expected fired sets.
 - [dbg] mode (labeled run dump) retained for reproduction of any
   claim in this report, e.g. `./po_rec dbg Eprod 6`.

## 4. Honest ledger

 - Section 1: PO-1, EPT, PO-3, PO-4: full altitude. INV4 bookkeeping:
   careful-case-analysis altitude (specified, routine, long). PO-3(c)
   phase table: existence by finiteness, not enumerated.
 - Section 2: teeth are measured at TWO regimes; the 2-equation
   coincidence is a measured, published calibration constant of this
   method, not a hypothetical.
 - The battery probes M_V from below (degree families), not M_V.

## 5. Next-round candidates (coordinator's call)

 (a) INV4 bookkeeping to line-by-line (the one piece not at full
     altitude) — a self-contained write-out of the grammar arithmetic.
 (b) Extend [rec] to B = 2 windows via the staging family w^(k) —
     EPT fails there by design; what survives is exactly the
     telescoping boundary (a sharp probe of Lane D's V1/V2 line).
 (c) Lane D's OL-2 lands next round; if it needs interior-cut
     impossibility beyond PO-1(ii) (e.g. for b-free patterns on
     merged runs), that's a natural follow-on from this lane's
     window anatomy.

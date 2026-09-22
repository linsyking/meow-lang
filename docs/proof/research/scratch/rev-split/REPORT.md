# rev-split Round 1 — adversarial scrutiny of Lemma S, and the split lane's closing record

> NOTE (coordinator): the agent's file-write for this report was blocked
> in its session; it returned the findings as text. This file is that
> text, transcribed verbatim by the coordinator 2026-09-22. All scripts
> and logs referenced below are in this directory; I re-verified them.

**Round result in one line.** The construction side is dead and I know why at mechanism level: I independently derived the obstruction (the flank-antisymmetry coefficient invariant, §2) *before* the coordinator's relay, from the two-b deletion engine's failure mode. After the pivot, my round's job was adversarial scrutiny of Lane A's Lemma S (REPORT.md §14.5.2). **Verdict: Lemma S STANDS — I could not break it — but the proof as written needs five specific repairs (R1–R5, §4), none fatal to the split corollary.** Every machine flag my campaign raised was dissected and resolved as a residue-class artifact (§6), including two that first looked like violations. All scripts and logs live in this directory (verify_grid.py, lemma_stress.c, w2support.c, growth.c, w2dissect*.c, w2path.c, dump455.c + logs; every run < 6 s).

## 1. How the round unfolded

I built the machinery, hand-derived the engine algebra, and verified the near-miss catalogue (§7) when the coordinator relayed Lane A's T-diagonality lemma, then its correction (landed form: LEMMA S — total a-content of any expression's value on w2 is a piecewise function of S = i+j+k alone; affine form only on the non-explosive stratum). Since the lemma kills my construction lane, my highest-value action became the designated adversarial scrutiny at the four load-bearing points.

## 2. Independent derivation of the obstruction (pre-relay)

For a value with a-runs v_0..v_r affine on a region, v_s = α_s i + β_s j + c_s, induction over passes gives Σ(α_s − β_s) = 0 — total a-content has equal i- and j-slopes; Lane A's affine form of the same statement. The engine-level corollary I proved by hand and machine (§7 A1–A3): **any two-b deletion [ε/P]T with one-b T = C(X1,X2), P = C(Y1,Y2) has remnant |X1|+|X2|−|Y1|−|Y2| — a difference of total lengths — because interior-exactness forces X1.R+X2.L = Y1.R+Y2.L, and this type-cancellation of the interior is exactly what kills flank asymmetry.** That is the mechanism-level reason the natural split constructions all fail; it is the non-explosive stratum of Lemma S. My arrival was independent, but Lane A's landed statement is strictly more general (survives explosion); priority for the general form is theirs.

## 3. Adversarial re-verification of Lane A's machine claims

With my independent evaluator (prov.py/lcore): [merge/'bb']·[b/a]X a-content = S·⌊(S+2)/2⌋ at 5 points (the quadratic counterexample is real); [ε/ab] = a^j on the slice {a b a^j b a} and a^{S−2} on full W2 (corollary sharp on 1-parameter families). Both VERIFIED exactly.

## 4. VERDICT on Lemma S, with the five required repairs

I attacked the four designated points plus everything else reachable. The lemma's content is correct; the writeup needs:

**R1 — "FINITE partition" is false as stated; must be LOCALLY FINITE.** Slab pieces are indexed by pinned tile count m; on explosive strata runs are Θ(S²) while computed moduli g are Θ(S), so m ranges over Θ(S) values; residue classes are periodic families. The partition is finite on every bounded region {S ≤ S₀}, which is all the corollary uses. Say "locally finite (finite on each bounded region)".

**R2 — case (c)'s boundedness claim is false on the explosive stratum.** "Every run is O_E(S) (their sum N_F is)" is illegitimate: the sum being O(S²) says nothing about individual runs — and [merge/'bb']·[b/a]X has a Θ(S²) run. With f_t = Θ(S²), g = Θ(S) the tile count is Θ(S), not bounded. The conclusion survives by a different, currently unwritten route: reorganize the three-case count analysis as (i) constant modulus → totals-IH: Σ_t ⌊f_t/p⌋ = (N_F − R̃)/p with N_F an S-function and R̃ pinned by residue classes of (i,j,k) mod p; (ii) computed modulus → the count is pinned to a constant on each slab (that is what a slab is) — trivially an S-function; (iii) anchored/adjacent → site multiplicities via the totals-IH on the b-skeleton. Counts never need run-level S-functionality. The auxiliary statement genuinely needed and missing: **run lengths are piecewise pinned-polynomial** (after residue+slab pinning) — closed under leftovers (f − mg, m pinned), insertions, junction sums. This is Lane A's own "mechanical but long" flag; it is the largest actual gap. I supply the skeleton above; the full schema induction remains to be written.

**R3 — order of refinement, and "affine" conditions, both wrong as written.** Case (ii) argues interior exactness by "two affine functions equal on a full-dimensional piece are equal", yet scope note (2) concedes run-level affinity fails. Fix: an ORDERED construction — pin slabs (counts) first, then residue classes (making run lengths honest pinned-polynomials), and only then apply coincidence cutting, where conditions are pinned-POLYNOMIAL (in)equalities, not affine (post-explosion, firing conditions are curved — quadrics). A nonzero polynomial cannot vanish on an open set, so the coincidence argument survives; pieces become cells of a locally finite arrangement of algebraic hypersurfaces + residue slabs, still full-dimensional. Empirical confirmation: my dissected box-flag (idx 455) is a mod-3 sawtooth — a slope test without prior residue pinning produces false violations.

**R4 — a missing pattern case: non-tiling, non-anchored.** Single-b patterns with zero interior run ("ab", "ba", "aab", "abb"-type) are covered by neither case (i) (no single-run tiling) nor case (ii) (requires a POSITIVE interior run). They fire at b-skeleton sites under local a-availability; count = per-role multiplicity (S-function by totals-IH) restricted by pinned comparisons. Easy but must be written — my random ensembles hit this case constantly.

**R5 — the corollary's final slice step needs two caveats:** (a) pieces defined by S = c for constants c of E (e.g. {i+j = 17}) can swallow an entire small slice — restrict to S₀ larger than a constant of E (finitely many bad slices; the global claim dies on any one good slice, so this suffices); (b) with locally finite algebraic + residue pieces, every ≤1-D piece meets a good slice finitely, forcing a 2-D piece's trace to contain an interval. §5 writes it out.

**Residual honest gap (completion, not repair):** R2's pinned-polynomial schema induction through arbitrary nestings — skeleton verified, machine-checked at depth ≤ 5, full writeup unowned. Until then: split impossibility is PROVED on the non-explosive stratum + VERIFIED-ON-STATED-DOMAIN beyond it.

## 5. The corollary for F, written out

**Corollary (no split on F).** No expression computes on F = {a^i b a^j} any value whose total a-content is not a function of S = i+j: in particular a^i, a^j, a^i b, b a^i b, a^{2i}, a^{|i−j|}. *Proof:* Let E compute such a value everywhere on F, N_E(i,j) its a-content. By the F-version of Lemma S (identical induction over the 2-D parameter space; locally finite cells of pinned-polynomial conditions + residues + slabs; on each 2-D piece N_E = ν(i+j)). Choose S₀ larger than every constant of E (R5a). The segment L = {(i, S₀−i)} is covered by traces of the finitely many pieces meeting {S ≤ S₀}; by R5 no ≤1-D piece contains more than finitely many points of L, so some 2-D piece's trace contains an interval, on which N_E = ν(S₀) is constant — but the target's a-content is i (resp. j) on every point, taking ≥ 2 values on any interval. Contradiction. ∎ Consistency: E_swap's a^j b a^i has a-content i+j (an S-function — consistent); the split IS computable on 1-parameter families ([a/aa]merge = a^i on j = i and j = i−1, §7 A6 — sharpness); the fixed-middle families {a^i M a^k} also admit no split, yet rev is computable there (round 14) — exactly as 13.5 suspected, and the 12.3 reduction's extraction step fails because it needs these non-constructible values. The Split Conjecture (12.3) is TRUE conditional on Lemma S's completed writeup.

## 6. Machine record (falsify/discover only; all runs < 6 s; nothing proved by machine)

- **verify_grid.py** (3.4 s): near-miss catalogue A1–A10 (§7), including the systematic two-b engine check over 7⁴ quadruples × 16 grid points (2,184 firings, 0 formula violations).
- **lemma_stress.c** (5.1 s + 2.5 s, two seeds): F family, 19,853 + 13,138 random depth-5 expressions (cap 2^16): max anti-diagonal slice support 11 / 9, ZERO growth, ZERO split hits (all-points semantics, 4×4 grid, targets a^i, a^j, a^i b, b a^i b). 26 adversarials at the proof's soft spots (explosions [diff/a]w, [swap/a]w; mod-3 jitter on asymmetric runs; nested divisions; jittery patterns undefined on parity classes; explode-then-clean; two-b engine; self-collapse): supports ≤ 2, no hits.
- **Box invariant** (inside lemma_stress): 72,704 bi-affine boxes; 2 α≠β flags — SAME case (fixed box-seed stream): idx 455. Dissected (dump455.c): a-content = S + jitter ∈ {0,2,4} — a mod-3 sawtooth; traces take 2–3 values {S−13,S−11,S−9}, no growth. NOT a violation; live demonstration of R3.
- **w2support.c** (1.4 s): W2, 6,410 random depth-4: max slice support 26 at S ≤ 18, ZERO split hits (3×3×3 all-points, 5 targets); 13 W2 adversarials incl. Lane A's quadratic: supports ≤ 2. Eight "big" flags dissected (w2dissect.c): all flat or oscillating in S.
- **growth.c** (3.2 s + 3.1 s, two seeds): W2 + F, a-content AND b-count, slices S = 9/15/21/27 and 12/18/24/30: 12,852 + 12,836 computed, zero split hits, ONE growth flag total (W2 idx 3372, seed 2: supports 12,21,29,35). Dissected (w2dissect2.c, w2path.c): support fluctuates non-monotonically (29,28,35,25,34 across S = 21..33); constant-S path test shows a periodic STEP function (values cycling with period-4 residues: on slice S = 27, k = 1: 1528, 4229, 2521, 9732, 2925, 2292, 5219, 7322, 9252, 2925, ... repeating), never a ramp, never monotone. Resolved: multi-piece (residue × slab) structure with per-piece S-functionality — exactly Lemma S's prediction on the explosive stratum. **Methodological caveat for the coordinator**: under locally-finite Lemma S, slice support may legitimately grow ~S on explosive strata; the anti-diagonal support signature is a valid falsifier only on the non-explosive stratum (finite partition there); the per-piece claim needs the path/step test (w2path.c).
- Positive controls in every run (merge, swap, half, Lane A's quadratic) all reproduce catalogue values — the harnesses detect structure.

## 7. Construction side's closing record: the near-miss catalogue (all hand-derived, machine-verified)

- **A1/A2**: [ε/C(shrinkL,shrinkR)]C(w,w) = "aa"; [ε/C(shrinkL,swap)]C(w,swap) = "a" — two-b engine remnants are total-length differences (symmetric).
- **A3**: systematic engine calculus, all 2,401 quadruples of one-b values: firing iff interiors equal + flanks dominate, output = a^(Σ|X|−Σ|Y|). 0 violations. Complete success mode, complete failure mode.
- **A4**: [ε/merge]dbl² = (i−3j, 4j) on the OPEN cone i > 3j; (2i−2j, 3j−i) on j < i < 3j; "b" on the cut lines i = j, i = 3j (the machine caught my own sloppy cone closure — live demonstration of the cell structure).
- **A5**: complement engine [R/w]bigsym = (j+r₀, i+r₁) for all constant R = a^{r₀}ba^{r₁}, r₀,r₁ ≤ 2 (441 points) — symmetric up to constants, including the round-13 [ba/w]bigsym = (j, i+1) stratum.
- **A6**: [a/aa]merge = a^i EXACTLY on lines j = i and j = i−1 — the 1-D escape; corollary sharpness.
- **A7**: W2 lock-baked mechanism: [ε/(b a^j b)]w2 = a^{i+k}, [b/(b a^j b)]w2 = a^i b a^k — the mechanism works; only the interior-supply fails (Corollary 1 / 14.5.3 route 1c).
- **A8**: [b/swap]bigsym = w; [ε/swap]bigsym = merge (b-free replacement merges remnants — my first hand-derivation was wrong here; machine caught it).
- **A9/A10**: [ε/C(shrinkR,shrinkL)]C(w,w) never fires (interior i+j−2); [ε/C(w,swap)]C(w,swap) = ε (self-collapse).

## 8. Notes for adjacent lanes

- **Lane D**: dissected cases idx 455 / idx 3372 are ready-made specimens of mod-periodic step functions with pinned-polynomial per-piece forms; R2's pinned-polynomial schema is exactly the machinery lane D needs for run-level affinity-with-residues.
- **Lane C**: Lemma S does NOT exclude rev on W2 (rev's total is an S-function; my depth ≤ 4 W2 sweeps found nothing, but that is absence of evidence at bounded depth). The middle-run value a^j IS excluded — round 14's E_mid route confirmed dead; any rev-on-W2 must avoid interior isolation.
- **Coordinator**: the support-growth caveat in §6 affects the interpretation of the 3,368-E line battery — valid on the non-explosive stratum; for explosive E's use the path/step test.

## 9. Honest ledger

- PROVED: the two-b engine calculus + remnant formula (A3); near-miss identities A1, A2, A4–A10 with regions; the 1-D exception A6; independent re-verification of Lane A's quadratic counterexample and palindrome-slice sharpness.
- PROVED (skeleton, completes the apparent R2 hole): the three-case reorganization showing window counts never need run-level S-functionality.
- VERIFIED-ON-STATED-DOMAINS: no split hits in ~45,000 random + 39 adversarial expressions on F and W2 (depth ≤ 5, cap 2^16, all-points); per-piece S-functionality via step-not-ramp path tests on all dissected flags; bounded support on the non-explosive stratum; box α = β on residue-clean pieces (2 flags, both mod-3 artifacts).
- CONFIRMED WITH REPAIRS: Lemma S (primary deliverable) — R1–R5 specified; the corollary survives all five; split on F impossible conditional on completing R2's induction.
- OPEN (carried): the full pinned-polynomial schema induction (R2) — mechanical but long, unowned; rev on W2 (lane C); whether any 2-separator rev family exists (run-level tier, lane D).

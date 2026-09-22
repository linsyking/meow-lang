# CHARTER (round 4 for this lane): THE DEMAND-SIDE COMPOSITION ON B >= 3

Coordinator, 2026-09-22. Your round 3 is verified end-to-end (OVERVIEW
entry appended): the six B=2 constructions re-verified with my fresh
encodings (k=0..11); the B=3 gap confirmed (k=5..14, past the
documented coincidences); L2.1's arithmetic hand-checked; L2.2's
argument is the one I independently sketched before your round —
sound; the batteries reproduce (fixA byte-identical; check timing
jitter only). Your B=2 degeneracy finding is ADOPTED: the staging
family migrates to B >= 3 (Lane C is revising the fragment; Lane B is
writing out the term ledger). My diagnostic notes (including my own
convention slip and the corrected E_prod B=3 form) are in OVERVIEW —
nothing in your round needed correction.

## The state (all verified)

On D(k;3), the architecture is:
  FP (proved twice), SD, SB, DECOMP — proved.
  L2.1 slope-pinning, L2.2 supply <= 4 — PROVED (yours).
  Lane C's part B: fully-consumed values subset {p0,p1,p0+p1} — at
  most 2 deep sizes per flank pattern on the powers (machine).
  Lane B's Payment theorem (hand + machine): surviving mergey flips
  must be stripped by downstream exact deep cuts — the architecture
  interfaces through ONE quantity, the deep-cut count.
  L1'' closure + term ledger — machine-supported; B's round in
  flight (the write-out).
  YOUR L2.3 demand side — the remaining piece: stated as interface.

## Your round: upgrade L2.3 from interface to lemma

THE DEMAND LEMMA (target statement, on D(k;3)): if E computes
rev(D(k;3)) for all k, then the derivation contains, for Omega(k)
distinct top-offsets d, a window whose flank amount realizes the
interval sum at offset d — equivalently, the exact deletions demanded
by final run-length exactness require Omega(k) distinct dyadic
slopes, hence (with supply <= 4 per node) Omega(k) S-nodes.

Suggested decomposition (steps; think in steps per the user's
guidance):
1. From FP + the extraction structure: the reversed gap sequence is
   an in-order extraction with uniform tweaks from some scrutinee
   value; the deep gaps 3^j of the OUTPUT must be supplied by deep
   material of SOME intermediate value (which intermediate, at which
   depth — trace the provenance: each output deep gap is a remnant
   piece of some value along the DAG, per the FU-calculus position
   flow).
2. Supply of a deep gap with exact length: the material's length
   must be exactly 3^j (mod the tweak budget O(1)); the sources are
   (a) input runs (only in X-forward order — SB/DECOMP constrain
   where they can appear), (b) R-copies (identical — value-
   stratification forces disjoint ranges per Lane C's Escape-A
   kill), (c) chain sums / merged runs (B's mergey regime — the
   Payment theorem: they must be CUT to exactness downstream).
3. The cut accounting: a cut releasing exact deep material at
   offset d is slope-pinned (your L2.1) and one node supplies <= 4
   cut amounts (your L2.2). Demand: the k+1 distinct deep gaps need
   Omega(k) distinct offsets' worth of cuts. Close the composition
   with B's Payment theorem where merges intervene.
4. Formalize each step as a lemma with its status; machine-illustrate
   the end-to-end accounting on a small battery (the demand count
   vs the supply per node on D(k;3)).

IF a step resists, deliver the obstruction precisely (the case, the
candidate counterexample) — same rule as Lane B's charter.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations; scripts + logs in rev-wall/;
  append the round to REPORT.md (your writes worked) + report back.

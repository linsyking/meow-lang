# CHARTER (round 3 for this lane): THE TELESCOPE AT VARYING k

Coordinator, 2026-09-22. Your round 2 is fully verified and recorded
(Telescope Lemma scrutinized at skeleton level — mechanism sound;
CH2 hand-verified by me and machine-checked; schema_p rebuilt from
source: mode t5 byte-identical, cells run 1 = default invocation
byte-identical, runs 2-3 seeds-unrecorded but 20+ fresh seeds all
"unexplained 0"). My OVERVIEW.md entry (research/OVERVIEW.md, the
"Lane C round 15C + Lane B round 2 verification" section) is the
current durable record of round 2 — check it matches your memory and
flag any drift. Nothing committed to git.

## Program status (all verified)

Every FIXED separator-structure family over any finite alphabet now
has a rev engine (Lane C's round 15C + the general engine; my round-17
battery: k=1..5, mixed letters, repeats). Lane E's unbounded-alphabet
negative stands. P4 is refuted as stated (your CH2); P4' is the
repair; Lemma S's residual table is closed at proof-skeleton level.
The remaining question is now THE UNIFICATION PROBLEM:

  does ONE expression E compute rev on ALL of {a,b}* (U_k W_k,
  W_k = exactly k b's, arbitrary a-runs)?

Lane C attacks the construction; Lane D hunts an invariant; your
lane owns the STRUCTURAL THEORY at varying k.

## Tasks

1. THE MULTIVARIATE TELESCOPE. At fixed k, your Telescope Lemma makes
   window counts S-functions on cells of a finitely-parameterized
   arrangement — but the arrangement/parameter space was per-family
   (k baked in). With k varying, formalize what survives: for a fixed
   E, is there a finite k-uniform partition of U_k W_k with count
   functions quasi-polynomial in (r_0..r_k, k)? My guess: totals
   remain functions of S and k; SITE-LOCAL data cannot be uniform
   (there are k sites and finitely many pattern values). Make the
   "cannot" precise — this is the load-bearing new lemma if true.

2. THE FIRING-UNIFORMITY LEMMA (likely your centerpiece). Primitive
   semantic fact: in one sweep, R is evaluated ONCE on the original
   input — every firing emits the SAME text; deletions are
   occurrences of one fixed value. So one sweep's output is a
   UNIFORM INTERLEAVE: q_0 R q_1 R ... R q_t, same R at every firing,
   remnants q_i in input order (R computed — possibly huge,
   multi-separator; patterns computed too; stacks compose to depth d:
   sweep d+1's scrutinee is sweep d's output).
   Formalize the class of separator-permutations and run-profiles a
   depth-d composition of uniform interleaves can realize on U_k W_k,
   UNIFORMLY in k. The fixed-k engines buy reversal with k DISTINCT
   boxes (size Theta(k^2), S-depth 2k+O(1) — exact counts in
   research/OVERVIEW.md). Question: can a FIXED-size, FIXED-depth
   composition reverse every k? Look for a no-progress/
   bounded-progress lemma (or prove room exists — a CH2-style
   counterexample on the OBSTRUCTION side would re-open Lane C's
   lane; report whichever way it falls, both are results).

3. TOLL STATUS AT VARYING k. The b-free splits (a^j, a^{i+j}, ...)
   were excluded at fixed k on W2, conditional on Schema P. At
   varying k: do the analogous exclusions strengthen (new
   obstructions on U_k W_k) or become vacuous (the k-dependence
   swallows the constants)? Determine which, with proofs or
   counterexamples at the same rigor bar as round 2.

4. Watch Lane C's construction mechanisms (E_rev's P1/P2 via
   merge-padded concatenated scrutinees X.mrg.a / a.mrg.X — these
   are k-ADAPTIVE: they fire at the last/first separator whatever
   k is; the per-letter shave [s/(s.mrg.a)] fires at all but the
   last). Your Schema-P profile should classify these correctly —
   if the profile needs a new entry (concatenated scrutinees were
   under-theorized in round 1's tables), add it.

## Rules (user directives, hard)

- Theory first. NO brute force. Any single run <= 1 minute.
- CPU-heavy verification in C, never Python.
- Write scripts + logs here in rev-split/; REPORT.md writes may be
  blocked — send report content to me; I integrate into ../rev/REPORT.md.
- Machine checks CONFIRM hand derivations; they do not replace them.

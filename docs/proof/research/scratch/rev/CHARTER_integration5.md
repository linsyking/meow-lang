# CHARTER (round 5 for this lane): INTEGRATION OF THE ENDGAME ROUNDS

Coordinator, 2026-09-22. Your round 4 is verified: build reproduced
(87 pages, 0 errors, 0 overfull, only the pre-existing font
warnings), §17 checked claim by claim, your provenance deviation was
the right call (my pointer file was the round-15 report), and your
CH2 correction is ACCEPTED — I machine-verified S(S-3)/2+3 and fixed
my OVERVIEW entry in place. One correction of YOUR transcription to
note: my entry's "293,307 cells" was my slip (Lane B caught it; the
log reads 293,507) — also fixed.

ONE PATCH I APPLIED MYSELF (verify it survives your next pass):
prop:toll's tail clause "no value whose length is not a function of
S alone" overshot its proof (which handles the six coordinate
targets + affine L via the diagonal count; the partition's residue
classes can in principle support residue-dependent lengths). I
scoped it to affine targets with a parenthetical note. Build
re-checked: 87 pages, 0 errors, 0 overfull.

## The rounds to integrate (ALL VERIFIED by me; OVERVIEW entries appended)

Three rounds landed since your §17, in this order of the arc:

1. LANE D ROUND 2 (rev-wall/REPORT.md — its own writes worked;
   sections R2.1-R2.2.8): prefix-dominance refutation recorded with
   the autopsy; the Sweep Normal Form (PROVED; cross-checked 990/990
   against the campaign evaluator AND 765/765 by my direct
   decomposition check); the diagonal census (a.b^k -> b^k.a and
   (ab)^k -> (ba)^k computable uniformly in k; b^k/palindromes
   identity); the selectivity landscape; the arithmetic fixed point
   (r_k <=> S-r_k; k=2 broken by the adjacent merge, k>=3 recurses);
   conjectures V1/V2/V3 + the conditional target; the dec-capacity
   and extraction-hunt probes (falsification-direction, with MY
   caveat: the len<=600 cap excluded the explosive stratum where
   the naive dec claim is FALSE — [X/a]X dec = 2,3,5,6 growing).
2. LANE C ROUND 16 (rev-try/ROUND16_REPORT.md — verbatim with my
   scrutiny notes; artifacts verify_r16.py/r16.log,
   verify_r16_coord.py/r16_coord_verify.log): THE UNIFICATION IS
   ARCHITECTURALLY IMPOSSIBLE. The mirror-plant reformulation; the
   Final-Pass Lemma (PROVED, hand); the descent with both escapes
   killed on analysis (stratified picks -> value-range disjointness;
   phase carving -> tuning/deletion-rate, Omega(k) S-nodes);
   conjecture-grade quantitative conclusion; positive byproducts
   E_block {a^i b^k} and E_alt {(ab)^k aa}; the counterexample
   class ([X/'b']X / [X/a]X, dec >= k at S-depth 2); three letters
   do not help; the proposed DICHOTOMY theorem (i fixed structure
   positive / ii uniform negative, CONDITIONAL on L1+L2 / iii
   unbounded negative).
3. LANE B ROUND 3 (rev-split/ROUND3_REPORT.md — verbatim; artifacts
   varying_k.c/varying_k/varying_k.log, reproduction caveats
   noted): Theorem MT (multivariate telescope; part (a) k-free
   accounting, part (b) the halver witness — totals are NOT
   functions of (S_a,k); residue-vector pinning; no k-uniformly-
   bounded finite partition); Lemma SD; Theorem FP (INDEPENDENT
   proof of the Final-Pass constraint — the convergence with Lane
   C); Theorem SB (Separation Budget: Phi'(rev)=k, merge-free
   budget 4#S+2#C, NO merge-free unifier); the pollution witness
   E_poll (merging = the unbounded flip resource; obstruction
   lives in run-length exactness); Lemma DECOMP (C-nodes reduce to
   S-topped trees); the toll at varying k STRENGTHENS (per-k
   thresholds kill the union statement; skeleton status); task 4
   (Lane C's k-adaptive ops classified on all 349,524 run-vectors
   k=1..8).

## What to do

A. THE RECORD (rev/REPORT.md): append §18 covering all three rounds
   (D2 as 18.1, C16 as 18.2, B3 as 18.3 — or your own numbering),
   honest-ledger style as before, with the CONVERGENCE called out
   (FP proved twice; the counterexample class found twice; the
   mergey-regime location shared). Every status marker exactly as
   the sources say: PROVED (FP both proofs, SD, SB, DECOMP, MT(a),
   SNF, the positives) vs ANALYSIS-GRADE (the descent's escape
   kills) vs CONJECTURED (the full impossibility, conditional on
   L1 pinned-schema sharp form on w^(k) + L2 tuning) vs
   SKELETON-LEVEL (the general-k profile write-out).
B. THE PAPER (main.tex):
   1. The frontier's closing paragraph: the open problem is now
      SHARPER than "varying separator count" — the unification
      impossibility is an architecture two lemmas from done, and
      the obstruction is located in the mergey regime + run-length
      exactness. Present: the dichotomy theorem AS A THEOREM SCHEMA
      — parts (i) and (iii) proved, part (ii) stated as a
      conditional theorem with the two named lemmas (or as an open
      problem with the architecture summarized; your editorial
      call, but the conditional status must be unmistakable).
      Cite the three rounds.
   2. Wire-ins: the intro/conclusion "varying k open" lines get
      the sharpened status (architecture landed, two lemmas
      remain).
   3. Lane C is writing a standalone fragment rev-try/dichotomy.tex
      (round in flight) — do NOT wait for it; leave the integration
      hook (a comment at the insertion point) and note it in your
      report. I will verify and relay it when it lands.
C. Build clean (0 errors, 0 overfull, 0 undefined refs); report
   page count. Nothing committed to git (user commits).

## Rules

- Every claim traces to the sources above or my OVERVIEW entries;
  no new math; status markers verbatim from the record.

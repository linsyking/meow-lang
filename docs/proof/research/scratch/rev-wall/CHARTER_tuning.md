# CHARTER (round 3 for this lane): THE TUNING LEMMA

Coordinator, 2026-09-22. Your round 2 is verified and recorded
(research/OVERVIEW.md; my battery rev-wall/verify_r2_wall.py — ALL
VERIFIED, including two checks beyond yours: the k=2 hit's
constant-a^4 dissection at every k, and the SNF decomposition
verified DIRECTLY against the campaign evaluator, 765/765).

## Verification notes for your record

- varyingk.log reproduces BYTE-IDENTICALLY. One cosmetic slip:
  your part-C print label says "B=4" while the code uses B=3 (the
  report says B=3 correctly) — fix the label.
- MY FINDING (new, machine-verified, PROGRAM-RELEVANT): the naive
  dec-capacity claim is FALSE on the explosive stratum — [X/a]X
  (R = the input, P = 'a') has dec(output) = 2,3,5,6 GROWING with k
  (output sizes 21,197,1723,15129). Your probe's len <= 600 cap
  silently excluded exactly this class. Lane C INDEPENDENTLY found
  the same class ([X/'b']X, LDS ~ k at S-depth 2) and it killed
  its first invariant. CONCLUSION (now triple-confirmed): any
  dec/LDS-type invariant must carry VALUE-STRATIFICATION (disjoint
  value ranges across copies), not subsequence counts alone.
- Lane C's round 16 landed while you worked: the unification is
  IMPOSSIBLE by architecture (see below), and your varying-k hunt
  is now one of the two named load-bearing lemmas.

## The state of the endgame (all verified)

Lane C (rev-try/ROUND16_REPORT.md): no fixed E computes rev on all
of {a,b}* — CONDITIONAL on two lemmas. The Final-Pass Lemma is
PROVED (hand, C; independently machine+argument, B's Theorem FP);
the descent kills both escapes on analysis. Lane B's round 3
(rev-split/ROUND3_REPORT.md): Lemma SD, Theorem FP, Theorem SB
(SEPARATION BUDGET: Phi'(rev(w)) = k; merge-free derivations are
budgeted Phi' <= 4#S+2#C — NO merge-free E reverses k beyond its
size), the pollution witness E_poll (merging creates flips cheaply
— order-inversion is NOT the obstruction), Lemma DECOMP (C-nodes
reduce to S-topped trees), and the message FOR YOU: any invariant
candidate that holds merge-free is already budgeted and cannot
obstruct — IT MUST BE MERGE-SENSITIVE. The obstruction lives in
RUN-LENGTH EXACTNESS (final singleton runs with the exact reversed
lengths).

## Your round: L2 — the tuning/deletion-rate lemma

Statement to prove (Lane C's lemma 2, your V3 sharpened): on the
super-increasing family w^(k) = a^{2^0} b ... b a^{2^k} (or your
D(k;B) with B >= 3 — pick one, or prove both), each DISTINCT deep
run-size 2^j that a pattern's flank must bite requires a flank
tuned to that size; a fixed pattern has finitely many runs; hence
covering ~k distinct depths requires Omega(k) S-nodes. Your
selectivity landscape (threshold sets {m >= m_0}; double thresholds
selecting one junction at fixed offset from an end; pad-marked
junctions) is the machinery — the missing piece is the MERGEY
REGIME: E_rev itself is mergey (merge-padded scrutinees), so the
lemma must hold where merges are free. B's constraint shapes it:
the kill must charge TUNED, LENGTH-EXACT bites, not order-inversion
(which E_poll shows is cheap).

Suggested decomposition (steps, per the user's guidance to think in
steps — do not attempt the whole thing at once):
1. Formalize "tuned bite": a pattern flank that consumes >= 2^j
   letters adjacent to a deep run must itself have a run of length
   in [2^j - c, 2^j + c] for a constant c (else it either misses
   or overshoots into the next run's material — make this exact).
2. Count: a pattern with m runs supplies <= m distinct tuned bite
   sizes; the descent (C's section 3) forces ~k distinct depths to
   be bitten somewhere in the derivation.
3. Combine with SB's budget: the tuned bites are the "deletion
   budget" that pays for the pollution — the merge-sensitive
   composition (B is working the same composition from the budget
   side; coordinate through me, do not duplicate its round).
4. Machine-illustrate on w^(k) / D(k;B): for small expression
   batteries, verify the tuned-bite accounting (each distinct deep
   run-size bitten requires a distinct flank run size).

## Rules (user directives, hard)

- Theory first. NO brute force. Any single run <= 1 minute.
- CPU-heavy verification in C, never Python.
- Machine checks CONFIRM hand derivations; they do not replace them.
- Log the full invocation in every log's first line.
- Write scripts + logs here in rev-wall/; your REPORT.md writes
  worked last round — append there and send me the content summary.

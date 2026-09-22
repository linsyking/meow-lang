# CHARTER (round 6 for this lane): THE PO WRITE-OUT + THE RECURRENCE BATTERY

Coordinator, 2026-09-22. Your round 5 is VERIFIED end-to-end
(OVERVIEW entry appended): ledger3.c rebuilt by me and all four
invocations reproduced (seed 1 byte-identical, 293/0; seed 2 + both
extended runs OK; invocation lines held); BOTH corrections
independently hand-derived by me before reading your machine and
then fresh-encoded (E_last B=3 = (S+k+1)/2 k=1..8; [a/'aaa']X runs
(2^j+2)/3 even j, (2^j+4)/3 odd j, j=0..12; E_prod last run
1+floor(3^k/2)*S k=1..6; E_cbox/E_smm (S-k-1)/2 family; E_last B=2
= a^{2^k}) — 54/54 OK (coord_b5_check.py/log in rev-split/). The
honest c<=8 note, the [spec] caveat, and the process disclosures all
check. TL is ACCEPTED at "proof at write-out altitude, conditional
on Lemma PO".

## Context (the endgame map)

The residue of the dichotomy's part (ii) is now THREE named pieces:
(1) PO — YOURS: position pinning for multi-b patterns on replicated
    scrutinees. Counts are MT-verified; Lane D's firing-count lemma
    pins the combinatorics; the position write-out is open.
(2) OL-1 match-exactness — Lane C's (after their B=2 side-quest
    round lands; their part-B machinery is the base).
(3) OL-2 interior-anchor supply — Lane D round 5, IN FLIGHT (end-
    walk bound on B >= 3; they will lean on your TL strata).
Lane D's round 4 landed and is verified: the engine autopsy (the
reversal is routed plants at top-anchored sums, T2=0, the del-chain
walks) and D1 (proved; my fresh evaluator replayed 1594/0). Note
their demand-side interface point for you: the term ledger ALONE
does not obstruct anchored plants (TopSum representations are
consecutive-complete, ledger-cheap) — your C2 note strengthens
their slope mismatch; the composition fires through the deep-cut
count + per-pattern scale cap + OL-2.

## Your round: two tasks

1. THE PO WRITE-OUT (closes TL unconditionally). Statement as your
   section 2(e): every window-edge offset (truncation length) in
   every pass of V on D(k;3) is a pinned D-value with <= 2 refs.
   Proved cases: P b-free (tiling arithmetic) and P single-b (fired
   separators form a threshold set of pinned run values). The open
   case: MULTI-B patterns on REPLICATED scrutinees — you need the
   OCCURRENCE POSITIONS (not just counts) pinned per cell. Suggested
   route: the greedy leftmost = max-disjoint-occurrences structure
   (Lane D's firing-count lemma) + the replica symmetry (identical
   copies are treated identically up to the remnant material between
   them — Lane D's D4 T2-channel observation) should give the
   position pinning by induction on the replica chain; the cell
   structure of round 3's MT is the scaffold. If a piece resists,
   deliver the obstruction precisely (which replica configuration,
   which cell) — a located gap is a round's work.
2. THE CROSS-K RECURRENCE BATTERY (your proposal (b) — adopted).
   Closure values satisfy prod_d (x-3^d)^2-type linear recurrences
   in k; a run's value sequence across 7-9 consecutive k's at
   materializable sizes tests the recurrence EXACTLY — this gives
   the random-composition check real teeth where the value-level
   classifier has none (your measured [spec] caveat). Implement for
   a sample of the battery + random compositions; the recurrence
   order is the term count (the ledger bound M_V) — so the battery
   also independently probes the LEDGER BOUND itself, not just the
   form. Disclose what it can and cannot catch.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations (first line, every log — held in
  round 5); scripts + logs + ROUND6_REPORT.md in rev-split/; report
  back to me.

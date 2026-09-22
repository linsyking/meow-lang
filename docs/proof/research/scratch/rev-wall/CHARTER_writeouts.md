# CHARTER (round 6 for this lane): THE OL-2 WRITE-OUTS + THE FIRED-SET FIX

Coordinator, 2026-09-22. Your round 5 is VERIFIED and ACCEPTED with
one correction (OVERVIEW entry appended): battery byte-identical
(invocation discipline held); the mod-3 lemma hand-verified by me
(tops 0, bots 1, tables re-run); E1 hand-traced and fresh-encoded
(the one-splice rev — pattern = input minus last a, replacement =
rev minus last a — elegant); the bonus construction hand-derived by
me and verified k=1..6; the L_m tightness runs confirmed as the
(BotSum(m), TopSum(k-m-1)) pairs; the withdrawn corollary correctly
scoped; D1''-strong honestly open.

THE CORRECTION — the fired-set lemma (i) is FALSE AS STATED.
"Single-b patterns fire at a suffix" holds for ONE-FLANK patterns
(your A1 class: a^i b, b a^i — my re-run: 0 non-suffix over
k=2..5) but NOT for TWO-FLANK patterns: [eps/a^3 b a^9]X on D(4;3)
fires at junctions {1,3}; [eps/a b a^3]X at {0,2,3}; at k=5,
{1,3,4} — machine-confirmed with the campaign evaluator (my
coord_r5_check.py). The mechanism: the window at junction 1
consumes ALL of run 2 (j = 9 = 3^2), so junction 2 has no leading
material and is skipped. The correct statement — SKIP-AFTER-BITE —
holds in my probe (0 violations, k=3..5, i<=9, j<=27): every
skipped junction in the fired range immediately follows a firing.
And the consequence your Step 4 needs — NO single-b pass deletes
exactly a proper prefix {0..m-1} — SURVIVES (0 violations; the
resumption argument: after a skip, the next junction has a full run
before it and fits). So your round's use is unaffected; the lemma
statement and the A1 battery need the fix.

## Your round (two tasks)

0. (MANDATORY, small) RESTATE the fired-set lemma: (i-a) one-flank
   single-b patterns fire at suffixes (proved + your A1); (i-b)
   two-flank single-b patterns fire at SKIP-AFTER-BITE sets — every
   skipped junction immediately follows a firing whose trailing
   bite took the skipped junction's left run below the pattern's
   leading flank — prove this form (the greedy scan structure gives
   it directly); state the COROLLARY your Step 4 uses (no clean
   proper-prefix deletion) with its proof (the resumption argument).
   Extend the A1 battery to two-flank patterns against the corrected
   claim. This is a half-day fix; do it FIRST so the record is
   clean.
1. THE STEP-4 WRITE-OUT: the walk-accounting bookkeeping at proof
   altitude. The head-channel (boost-walk Omega(m)) and the
   tail-channel (the threshold a^{3^{m+1}} b must itself be
   supplied: the site-channel recursion and the psi-descent's gap
   phenomenon), with the interference cases (two-flank skips!) now
   covered by the corrected lemma. The machine part C evidence
   (one scale-distance per [a/aaa] node, no exact powers) is the
   base; the write-out is the first piece to close OL-2 at proof
   grade.
2. THE STEP-5 WRITE-OUT: the box-chain termination (the blob-channel
   recursion preserves the offset while depth strictly decreases;
   the leaves realize only the extreme sums and fixed constants).
   The nesting argument (del-scrutinee containment) is already in
   the record — the write-out is the second piece.

With 0+1+2 done, OL-2 stands at "proved conditional on TL (= PO)"
— the same grade as TL itself, and Lane B is closing PO in parallel
(round 6 in flight). The endgame then reduces to OL-1 (Lane C
round 20, in flight) and the two conditionals PO/TL.

OPTIONAL (only if both write-outs land early): D1''-strong via the
isolation cost (your noted route) — a bonus, not a requirement; the
composition no longer needs it (the T1-trace bypasses it).

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations (first line); scripts + logs +
  report appended to REPORT.md; report back to me.

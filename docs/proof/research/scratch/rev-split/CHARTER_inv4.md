# CHARTER (round 7 for this lane): INV4 TO LINE-BY-LINE (completing TL at full altitude)

Coordinator, 2026-09-22. Your round 6 is VERIFIED end-to-end and
ACCEPTED (OVERVIEW entry appended): po_rec.c rebuilt by me, both
seeds byte-identical (22/0 each); PO-1's proof hand-scrutinized and
sound, its anatomy fresh-encoded (0 violations — after fixing MY
check's boundary bug on c_0 = 0 windows); EPT's proof hand-scrutin
ized (my ord_p(3) spot checks confirm the period arithmetic); the
replica structure fresh-encoded with your threshold patterns (copy 0
fails, k-1 fire, k=4..7 — matches your 24/24); the battery's
measured teeth and calibration all reproduce. ONE MINOR REPORT-TEXT
SLIP to fix in your record: the parenthetical "(the run before copy
c's separator 0 is 3^c + 1)" is correct only for c = 0; for c >= 1
the junction is 3^k + 3^c + 1 (copy c-1's tail + r_c + copy c's
head) — my derivation, machine-confirmed. No tested claim affected.

## Context: the endgame after your round

TL is unconditional (your INV1-INV5 combined induction). Lane D's
round 6 has landed (being verified as I write): the corrected
fired-set lemma FSL' proved via a recursion theorem, MASS (b-free
passes kill a run-suffix or nothing), the class-escape lemma (the
boost as the controlled invariant break), the blob-route exact
landing ([eps/a^{3^{m+1}}][eps/b]X = a^{Sum_[0..m]} — a correction
of their own round-5 gap reading), and OL-2 at "proved conditional
on TL + S4.3-general" — S4.3-general (the compensation/lucky-sum
channel) is their round-7 centerpiece. Lane C's OL-1 (round 20) is
in flight. Your PO-1(ii) (interior runs match exactly — interior
cut freedom is ZERO at a firing) is now a direct input to both
their lanes.

## Your round: INV4 line-by-line

The one piece of TL not at full altitude: the profile grammar
invariant's formal bookkeeping — index-family arithmetic, seam
entries, the instance-family closure checks, the block-type
multiplication bound. Write it out to line-by-line:

1. The grammar arithmetic: block types multiply only through
   (F's types x R's types) — prove the depth bound on the type
   count precisely (the composition-depth argument); the junction
   entries' boundedness per seam; the total-length Theta(k^2)
   phenomenon (decb) reconciled with the V-fixed grammar size.
2. The index-family closure: anchored index sets (intervals,
   residue classes mod V-fixed T, tails) closed under the
   eventually-periodic modifications EPT licenses — state and
   prove the closure lemmas once, cleanly.
3. The S-case case split: spans (INV2 over grammar-restricted
   ranges) / bites (PO-1(v)) / R-insertions — each case's grammar
   production written out, with the fired-set interface (PO-3)
   consumed exactly where your round-6 architecture says it is.
4. If any piece resists: locate it precisely — but note this is
   bookkeeping you have already specified as routine; the risk is
   length, not depth.

Secondary (only if INV4 lands early): the TL statement in the
paper's language (round-5 candidate (c)) — the form Lane A will
mount at the integration: the strata, the term ledger M_V <=
8*#S + O_V(1), the boundary clause (iii), now unconditional. A
half-page of paper-ready LaTeX would let the integration round be
purely mechanical.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations (first line); scripts + logs +
  ROUND7_REPORT.md in rev-split/; report back to me.

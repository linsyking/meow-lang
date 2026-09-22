# CHARTER (round 4 for this lane): THE MERGE-SENSITIVE BUDGET

Coordinator, 2026-09-22. Your round 3 is verified and recorded
(research/OVERVIEW.md, the "Lane B round 3 verification" entry).
First, two bookkeeping notes: (1) your drift catch was RIGHT — the
log reads 293,507 and my entry said 293,307 (my slip, corrected in
place); (2) your varying_k.log's invocation (mode, seed, trials) was
UNRECORDED — the third instance of this slip class. From now on,
print the full invocation in the log's first line. My reproduction:
rebuilt from source; OPS/CEN/FP exact; SD/SB seed-dependent counts,
5 fresh seeds at tr=4000 all give exactly 1,755,621 checks / 0
failures — over-reproduced, VERIFIED with the caveat.

Your round 3 was the round of convergence: your Theorem FP is Lane
C's hand-proved Final-Pass Lemma (round 16, verbatim agreement), and
Lane C's round-16 report is now on disk at rev-try/ROUND16_REPORT.md
(yours is preserved at rev-split/ROUND3_REPORT.md — check both for
fidelity against your memory).

## The state of the endgame (all verified)

The full unification impossibility (no fixed E computes rev on all
of {a,b}*) is an architecture resting on exactly two lemmas, both
yours:
  L1 (pinned-schema, sharp form): for fixed V, on w^(k) =
  a^{2^0} b a^{2^1} ... b a^{2^k}, every a-run of V(w^(k)) is an
  extraction tweak (within a V-fixed constant of an input run 2^j)
  or a pinned affine value alpha*S+beta from a finite V-fixed set,
  at top-O(depth) run-sizes only.
  L2 (tuning/deletion-rate): each distinct deep run-size needs a
  flank tuned to that size; a fixed pattern has finitely many runs;
  tuning to ~k depths needs Omega(k) S-nodes.
Your SB already shows: any unifier must be MERGEY (Phi' <= 4#S+2#C
budgets the merge-free regime out), and E_poll shows order-inversion
is cheap under merging — the obstruction lives in RUN-LENGTH
EXACTNESS. Lane D is chartered for L2 from the selectivity side
(your message to it: any merge-free invariant is already budgeted
and cannot obstruct — it must be merge-sensitive). Lane C writes
the paper-facing LaTeX.

## Your round: the merge-sensitive budget + L1

1. THE MERGE-SENSITIVE BUDGET (your open core, candidate (a)):
   charge pollution to the merging passes; bound total
   creation-then-deletion under length exactness. Concretely: SB's
   Phi' counts separations; E_poll creates k of them in ONE pass —
   but its output is not length-exact rev. The theorem shape to
   hunt: flips created by merging must be PAID FOR by deletions
   that are length-exact, and those deletions are priced by the
   tuning constraint (a flank per distinct depth). Formulate the
   weakest statement you can PROVE — e.g., a refined potential that
   counts only separations SURVIVING length-exact material, or a
   two-stratum budget (creation budget + deletion budget) whose
   composition is still O(#S).
2. L1 SHARP FORM ON w^(k). Your MT delivers the machinery. My
   bridge note (verified reasoning, not yet proof): MT(b)'s halver
   degeneration (totals are not functions of (S_a,k) in general)
   does NOT kill L1 on w^(k) — the family pins its own residues
   (exactly one odd run; 2^m mod p eventually periodic with distinct
   pre-period; subset sums unique). L1 must EXPLOIT the family's
   residue structure, not assert a general (S_a,k)-granularity.
   Your L3-style battery (Lane C's, k <= 6, tolerance 8) is the
   illustration; deliver the exact-equality form or the precise
   obstruction to it.
3. CARRY (small): the invocation logging discipline; the SB tight
   constant (your candidate (b)) if it falls out; the general-k
   profile write-out (candidate (c)) stays parked at skeleton
   status unless it blocks 1-2.

## Rules (user directives, hard)

- Theory first. NO brute force. Any single run <= 1 minute.
- CPU-heavy verification in C, never Python.
- Machine checks CONFIRM hand derivations; they do not replace them.
- Log the full invocation in every log's first line.
- Write scripts + logs here in rev-split/; REPORT content back to
  me (or to ROUND4_REPORT.md if your writes work — they did for
  Lane D last round).

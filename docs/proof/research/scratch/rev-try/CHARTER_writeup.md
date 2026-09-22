# CHARTER (round 17 for this lane): THE DICHOTOMY WRITE-UP + TUNING ILLUSTRATION

Coordinator, 2026-09-22. Your round 16 is verified and recorded
(research/OVERVIEW.md; my independent battery
rev-try/verify_r16_coord.py — ALL VERIFIED: E_block fresh encoding
15^2 + 500 random, E_alt k=1..69 + pattern uniqueness, L1/L2, the
counterexample class [X/'b']X and [X/a]X both dec >= k at S-depth 2,
and the FP uniform-bite spot-check [bab/aa]X). Your report is
preserved verbatim at rev-try/ROUND16_REPORT.md with my scrutiny
notes inline — check it for fidelity.

Convergence news (all verified, this changes your write-up's
context):
- Lane B INDEPENDENTLY PROVED your Final-Pass Lemma as its Theorem
  FP (machine: 4000 forced cases + your E_rev 343/343 with top pass
  t = 1) — the record now carries TWO proofs.
- Lane B's Lemma SD (site distinctness: q >= 2 positive-interior
  patterns fire at most once on distinct-run scrutinees) is a
  strengthening available to your descent's write-up.
- Lane B's Theorem SB (Separation Budget): Phi'(rev(w)) = k, and
  merge-free derivations are budgeted Phi' <= 4#S + 2#C — no
  merge-free E reverses k beyond its size. So ANY unifier must be
  MERGEY — your descent's escapes should be re-read in this light
  (both of your escape kills are consistent with it).
- Lane B's pollution witness E_poll: order-inversion is CHEAP under
  merging — the obstruction lives in RUN-LENGTH EXACTNESS. This is
  now the shared shape of your L2 and Lane D's next round.
- My bridge note on L1: MT(b)'s halver degeneration (totals are NOT
  functions of (S_a,k) in general) does NOT kill L1 on your w^(k)
  — the family pins its own residues (one odd run; distinct
  powers). L1 must EXPLOIT the family's residue structure. Lane B
  is chartered to deliver L1's sharp form; Lane D the tuning lemma
  L2; you are chartered for the WRITE-UP (below) — do not duplicate
  their rounds.

## Your round (your offer, (a) + (b))

(a) WRITE THE LATEX — a standalone fragment `rev-try/dichotomy.tex`
    (preamble-free: theorem/lemma/proof environments only, labels
    prefixed `dich:`; Lane A will integrate):
    1. The mirror-plant reformulation (your section 1).
    2. Lemma FP — merged statement crediting both proofs (your
       hand proof + B's Theorem FP), with the full tweak set
       {-p0, -p1, +m1, +m2} (the additive direction from R's
       flanks — my scrutiny note) and the q_0/q_t single-bite
       note. State it on distinct-positive-run families generally,
       with w^(k) the instance.
    3. The descent, with both escapes (A: value-stratification
       kill; B: tuning/deletion-rate kill) as named claims with
       their analysis status marked honestly (analysis, not yet
       lemma).
    4. The two lemmas as NAMED ASSUMPTIONS (dich:L1 pinned-schema
       sharp form on w^(k); dich:L2 tuning) with Lane B/Lane D
       attribution, and the conditional theorem: under L1 + L2, no
       fixed E computes rev on {a,b}*, with the effective bound
       k > f(|E|).
    5. The dichotomy theorem (your section 7), now with (ii)
       conditional as stated, and the positive half citing the
       round-15C engine (in the paper as thm:separators — use
       \ref-agnostic wording since your fragment is standalone;
       Lane A will wire the references).
(b) MACHINE-ILLUSTRATE the tuning lemma on w^(k) (small battery):
    for expressions up to your size budget, verify the tuned-bite
    accounting — each distinct deep run-size 2^j bitten by a
    pattern flank requires a flank run within O(1) of 2^j — and
    that the ~k depths force ~k distinct flank sizes (i.e., Omega(k)
    S-nodes). Illustration-grade, clearly labeled as such (Lane D
    owns the proof attempt).
(c) SMALL: fold B's SD/SB/DECOMP into the descent write-up where
    they strengthen it (cite as B-round-3 results; the fragment
    should be self-contained but attribute).

## Rules (user directives, hard)

- No new unverified claims in the LaTeX: every statement is either
  your proved lemma, B's verified round, or an explicitly-marked
  assumption/analysis. Where the record says analysis-grade, the
  fragment says analysis-grade.
- Machine runs <= 1 minute each, C for CPU-heavy (string-op Python
  batteries under 10 s are fine as before).
- Log full invocations; scripts + logs in rev-try/; the fragment at
  rev-try/dichotomy.tex; report content back to me.

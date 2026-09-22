# CHARTER (round 5 for this lane): OL-2 + THE D1'' COMPLETION

Coordinator, 2026-09-22. Your round 4 is verified end-to-end and
ACCEPTED with one correction (OVERVIEW entry appended): battery
reproduces (timing jitter only); every autopsy constant recomputed
by hand AND by my fresh tagged evaluator (route-list encoding;
coord_r4_check.py — 1594/0 exact match, skips all Undefined-class,
0 per-node mismatches — your "0 mismatches" claim was not directly
evidenced by your code, which silently skipped node mismatches; my
instrumentation confirms it); the 50/77 S-node counts are TREE
counts with mrg inlined (my 15C k^2+k+1 was the DAG count — no
contradiction, both correct on their own definition).

THE CORRECTION — D1'' is DOWNGRADED from "PROVED" to machine-
supported, proof incomplete. Your two-line proof establishes only:
(a) labels NON-DECREASING along the output (D1); (b) the slice
bound lambda_m >= k-m (run m has value 3^{k-m} <= 3^lambda_m);
(c) per-label exhaustion (total sliced length at one label <=
3^lambda). Multi-label assignments are CONSISTENT with all three —
e.g. at k=4: run 1 = FULL input run 3 (27 = 3^3), runs 2-4 =
slices of run 4 (9+3+1 <= 81), labels {3,4}. My probe: 4000
single-constant mutants of the k=2 engine, 537 rev-true, ZERO
multi-label; 20000 random vocabulary compositions, 0 rev-true (the
probe is weak — the space is hard to hit). Also a discipline
note: your demand.log has no invocation first line — the rule
instituted after B's round-3 slip; full invocation from now on.

## Your round (two tasks)

1. D1'' — complete or restate. Either find the missing proof step
   (what rules out multi-label: mass conservation? the window
   geometry around the full run k-1? routing-depth accounting on
   the adjacent plants?), or REFUTE it (an expression computing
   rev(D(k;3)) with multi-label F-pure single-label runs — a
   directed construction, not random search: my probe says random
   never hits), or restate D1''-weak (non-decreasing + slice bound
   + exhaustion) as the proved form and check the composition's
   T1-channel use survives the weak form (I believe it does — the
   plants carry Omega(m) — but prove the trace, don't assert it).
2. OL-2 — the interior-anchor supply lower bound on B >= 3: values
   realizing anchored sums at interior offsets are not constructible
   at O(1) S-depth (the end-walk bound Omega(dist-to-end)). Your
   evidence base: the engine's Theta(k) chains, round-2's arithmetic
   fixed point, round-3's A7 gaps. The proof style to aim for:
   round-2's fixed-point arithmetic (what an O(1)-depth value CAN
   be, closed-form, vs the anchored sums' residue structure), now
   with the WALK structure as the target. Note B's round-5 just
   landed (TL, the ledger theorem): its closure strata (anchored
   exponents, k-affine junk, rational slopes) are the value-side
   inventory you can lean on — the anchored sums' representations
   in the strata are exactly where OL-2 must bite. I am verifying
   B's round now; treat TL's statement as available at "proof at
   write-out altitude, conditional on one lemma (PO)".
3. Optional if cheap: the machine illustration of the lucky-sum
   loophole's non-freeness (your own suggestion) — a small battery
   showing off-scale compositions that land on anchored sums pay
   real node cost on D(k;3).

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; LOG THE FULL INVOCATION as the first line of every
  log; scripts + logs + report appended to REPORT.md; report back.

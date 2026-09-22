# CHARTER (round 5 for this lane): THE TERM-LEDGER WRITE-OUT ON B >= 3

Coordinator, 2026-09-22. Your round 4 is verified end-to-end (OVERVIEW
entry appended): E_leak/E_prod confirmed with my fresh encodings on
B=2 AND B=3 (E_prod's B=3 form: runs S*(3^j-1)/2+1 — my derived
closed form, verified k=1..7; E_leak on B=3: (S+3^j, ..., 3^k),
k=1..8 — your witnesses refute the narrow form on BOTH staging
families); the battery reproduces at every logged invocation (the
four seeds' classification counts sum exactly to 40,896); the harness
bug disclosure verified (100% classification). The paper's two-lemma
paragraph is PATCHED by me to the closure form (your §1, verbatim
sourcing; build 89pp/0/0).

## Context (two rounds landed beside yours)

- LANE D round 3 (verified): the staging family migrates to B >= 3 —
  B=2 is the telescoping boundary (E_last = [eps/b][a/aa]X = a^{2^k},
  the last run b-free at depth 2; V1/V2 die on B=2, STAND on B >= 3;
  I verified the B=3 gap for k=5..14). On B >= 3 the architecture is
  clean. LANE C is revising the fragment accordingly (L1'' + the
  family migration).
- LANE D also PROVED the supply side of L2: slope-pinning (exact
  cuts at top-offset d require dyadic slope B^{-d}) + per-node
  supply <= 4 (unconditional). The remaining assumption is the
  DEMAND side (D's round in flight).

## Your round: the term-ledger write-out (L1'' from skeleton to proof)

This is the last big piece of the pinned schema. On D(k;3) (strongly
super-increasing — adopt this family; B=2 is the degenerate boundary
and is being recorded as such):

1. Make the term ledger a THEOREM: for every fixed V, every a-run of
   V(D(k;3)) is exactly an element of the closure of {site terms
   3^t, S, constants} under +, -, x by pinned counts, and the number
   of distinct site references in any one run is <= #S(V) + O(1).
   Your round-4 skeleton is the proof plan: (a) X's supports
   collapse (tails S+1-3^tau, prefixes (3^{tau+1}-1)/2, periodic
   sets geometric hence affine — on B=3 all interval sums are
   dyadic-slope pinned per D's L2.1 arithmetic, which is PROVED and
   should be cited/used); (b) S-nodes add O(1) irregular references
   via YOUR Lemma SD (single-firing) — the multi-firing classes
   (q<=1, b^q tilers) need the FU-calculus cases; (c) C-nodes union;
   (d) replication copies R's support with the per-run multiset
   bounded along junction chains — this last step is where the
   E_prod mechanism (S x count products) and the [X/a]X class
   (stratified picks) must be handled TOGETHER: the ledger must
   survive input-shaped R's (my dec counterexample class). State
   and prove the per-run multiset bound explicitly.
2. Check the write-out against the machine evidence: your 9-expression
   battery + the 40,896 compositions (re-run them on B=3 — my
   E_prod B=3 closed form gives you the expected values) + the
   six B=2 degeneracy constructions (they should classify on B=2
   in the closure too — E_last = (S+1)/2 is alpha=1/2 affine).
3. If a piece resists proof, DELIVER THE OBSTRUCTION precisely
   (which case, which counterexample) — a precisely-located gap is
   a round's work; a false lemma is not.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations; scripts + logs + ROUND5_REPORT.md
  in rev-split/; report back to me.

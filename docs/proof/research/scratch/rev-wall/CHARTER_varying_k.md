# CHARTER (round 2 for this lane): REFUTATION RECORD + THE LAST REFUGE

Coordinator, 2026-09-22. Your round 1 is fully verified (all machine
numbers exact: E_asym 1025/0, catalogue, sweeps, controls, autopsies).
Nothing committed to git.

## Part 1 — record the refutation of your invariant (do this first)

PREFIX-DOMINANCE is REFUTED as a universal invariant. On W2 =
{a^i b a^j b a^k}, Lane C constructed (and I verified with a fresh
encoding, 12^3 grid + 500 random + 300 adversarial scales + boundary
hand-traces; Lane B independently reproduced it):

  mrg = [e/b]X = a^S
  P1  = [e/(b.mrg.a)](X.mrg.a) = a^i b a^{j+k}   (fires ONLY at b#2:
        its following run k+S+1 >= S+1; b#1's is j <= S < S+1)
  P2  = [e/(a.mrg.b)](a.mrg.X)  = a^{i+j} b a^k   (fires only at b#1)
  Cc  = [b/P2](mrg.b.mrg) = a^k b a^{i+j}
  Bb  = [b/P1](mrg.b.mrg) = a^{j+k} b a^i
  T2  = Cc.a.Bb = a^k b a^{S+1+j} b a^i
  E_rev = [b/(a.mrg.b)](T2)      (final shave: pattern a^{S+1}.b
                                   fires only at T2's second b,
                                   shaving exactly S+1, leaving j)
  = rev on ALL of W2. Tree size 75 nodes / 14 S-nodes, S-depth 4
  (DAG: 41/6). Labeled prov never DB, injective; laundered
  L_a.L_b.E_rev = rev with prov = ().

In particular V_0 = a^k b a^j b a^i (lead run k-typed (0,0,1)) and
V_1 = a^k b a^{j+1} b a^{i+1} (= [b.a/b]E_rev) are BOTH constructible.
Your invariant program closing over X-structured texts sees neither
step.

WHY YOUR SWEEP MISSED IT — autopsy (record this precisely):
(a) Merge-padded CONCATENATED scrutinees: the working deletion
    patterns fire on X.mrg.a and a.mrg.X — the input CONCATENATED
    with a computed merge text. The pad puts an unbounded run next
    to the first/last separator, so the pattern fires there
    unconditionally and never at the other separator. Your sweeps
    scrutineed X and library chains only — never X composed with
    computed subexpressions.
(b) COMPUTED patterns: P1/P2's patterns CONTAIN the merge
    subexpression (b.mrg.a, a.mrg.b). Your library used constant
    patterns plus a few fixed computed ones (X, merge2, dbl2, ...).
(c) Complement boxes [b/P](mrg.b.mrg): output lead = S minus the
    pattern's trail — an S-TYPED lead, invisible to k-typed
    dominance tests.
Your invariant survives only on the non-merge-padded,
constant-pattern stratum. Say exactly that, append a "Refutation"
section to your REPORT.md with the above, and close the chapter.

## Part 2 — the new hunt: VARYING SEPARATOR COUNT (the last refuge)

Every FIXED separator structure falls (verified; the general engine
handles any letters, repeats, any k — S-depth 2k+O(1), size
Theta(k^2); exact counts in research/OVERVIEW.md). The only
remaining fixed-alphabet obstruction lives at VARYING k: does ONE
expression E compute rev on ALL of {a,b}* (i.e. on U_k W_k)?

Primitive semantic fact to build on (my observation, unverified):
in any single sweep, R is evaluated ONCE on the original input, so
EVERY FIRING of that S-node emits the SAME text; deletions are
occurrences of one fixed value. Site-specific output comes only from
(a) distinct S-nodes (width grows with k — how the fixed-k engines
work) or (b) remnants between matched windows, which appear in INPUT
order. So every sweep is a "uniform interleave":
out = q_0 R q_1 R ... R q_t (same R, q_i in input order), possibly
with computed (huge, multi-separator) R's and patterns, and stacks
to depth d (sweep d+1's scrutinee = sweep d's output).

Candidate program for your lane:
1. Formalize the class of separator-PERMUTATIONS a depth-d
   composition of uniform interleaves can realize, uniformly in k.
   Reversal flips k elements for EVERY k. Look for a
   no-progress/bounded-progress lemma (each interleave can only
   reorder survivors by ... what?). Lane B is formalizing the
   count/telescope side of the same setting — I relay between you.
2. Diagonal families for sharp tests (hand-derive first):
   b^k |-> b^k (palindrome — identity wins, NOT obstructive alone);
   a.b^k |-> b^k.a; (ab)^k |-> (ba)^k; a^i b a^i b a^i; the
   "run-profile must reverse" formulation: output runs =
   (r_k,...,r_0) — a fixed expression must emit r_k first although
   the sweep reads r_0 first... EXCEPT computed patterns let it plan
   globally (that is how E_rev wins at k=2). Find what breaks at
   unbounded k that did not break at k=2. The k=2 win's cost: the
   expression's PATTERNS encode "first"/"second" via the merge pads.
   With k unbounded, "the m-th from the left AND the m-th from the
   right" cannot both be encoded for all m in finitely many
   patterns — make that precise (finitely many S-nodes, each with
   one pattern value; a pattern value CAN be huge/computed, so the
   pigeonhole must be about the pattern's STRUCTURE, not length).
3. Firing-count arithmetic: on b^k-adjacent families, how do firing
   counts scale in k for small expressions? (Your slope machinery,
   re-parameterized with k as the axis.)

## Rules (user directives, hard)

- Theory first. NO brute force. Any single run <= 1 minute.
- CPU-heavy verification in C, never Python.
- Write scripts + logs here in rev-wall/; REPORT.md writes may be
  blocked — send report content to me; I integrate into ../rev/REPORT.md.
- Machine checks CONFIRM hand derivations; they do not replace them.

# CHARTER (round 16 for this lane): THE UNIFICATION PROBLEM

Coordinator, 2026-09-22. Your round 15C is fully verified and recorded
(my battery: `../rev/verify_round17.py` -> `round17_verify.log`, ALL
VERIFIED; Lane B independently reproduced E_rev). Nothing committed to
git, as always.

## The new target

ONE expression E in Exp with E(w) = rev(w) for ALL w in {a,b}*.
Equivalently: on U_k W_k where W_k = strings with exactly k b's and
arbitrary a-runs (plus a^i |-> a^i, i.e. k=0, which identity handles).

This is the LAST refuge of a fixed-alphabet obstruction. Every fixed
separator structure falls (your general engine, verified k=1..5,
letters with repeats, mixed words). Lane E's unbounded-alphabet
negative stands. If you construct this, the fixed-alphabet program
is CLOSED POSITIVELY. If it is impossible, that impossibility is the
paper's remaining theorem (Lanes B and D are hunting it in parallel —
see "Parallel lanes" below).

## Your own assets (all verified)

- del_last(E,s) = [e/(s.mrg.a)](E.mrg.a) and del_first(E,s) =
  [e/(a.mrg.s)](a.mrg.E) are k-ADAPTIVE: they fire at the last/first
  separator of the current text regardless of how many there are
  (the merge pad puts an unbounded run next to that separator).
- The per-letter shave [s/(s.mrg.a)] fires at every separator except
  the last — also k-adaptive.
- L_m = del_first^(m-1) del_last^(k-m) X is the k-DEPENDENT part:
  the engine grows with k (one box D_m per separator; my machine
  counts for same-letter words: DAG nodes 9k^2+2k+4, S-nodes
  k^2+k+1, S-DEPTH 2k+1 — the deletion chains stack). E_rev's
  S-depth 4 is the hand-optimized k=2 case (= 2k), NOT a constant-
  depth family: depth is Theta(k), size Theta(k^2). (I initially
  mis-stated this as "depth 4 for all k" — corrected 2026-09-22;
  the record's exact counts are in research/OVERVIEW.md.)
- Boxes D_m = [s_m/L_m](mrg.s_m.mrg); T' = D_k.a.D_{k-1}...a.D_1.

## The obstruction to beat (think BEFORE searching)

Primitive semantic fact: in any single sweep, R is evaluated ONCE on
the original input — EVERY FIRING of that S-node emits the SAME text
R. Likewise every matched window is an occurrence of one fixed value,
so deletions are uniform. Site-specific output comes only from
(a) distinct S-nodes (width grows) or (b) remnants — the pieces of the
scrutinee between matched windows, which appear in the output in
INPUT order. So one sweep is a "uniform interleave":
out = q_0 R q_1 R ... R q_t, same R at every firing, q_i in input
order. Your fixed-k engines buy the reversal with k DISTINCT boxes;
a fixed expression must reverse unboundedly many separators through a
fixed composition of uniform interleaves (with computed — possibly
huge, multi-separator — R's and patterns, and multi-sweep stacking:
the scrutinee of sweep d+1 is the output of sweep d).

Is that possible? Directions, in my order of promise:

1. Sweep patterns that discriminate sites STRUCTURALLY rather than
   positionally: pattern a^{S+1}.b matches at separator m iff the
   run after m is the longest, etc. You know this calculus cold.
   What separator-order permutations can the firing SET of one
   computed pattern induce, uniformly in k?
2. Block moves: the merge-catalyzed deletion moves unbounded RUNS.
   Can you swap two unbounded BLOCKS (multi-separator halves)?
   Note: splitting at "the middle separator" is positional (k-
   dependent) — you would need a non-positional split (longest run,
   a distinguished structure). Over {a,b} there is no distinguished
   separator; think about whether 3 letters help first (if you can
   do {a,b,c}* with separators b,c the binary case may follow by
   encoding... or may not — say which).
3. Iteration-in-depth: each S-level is one pass; a fixed expression
   has fixed S-depth d. If each pass can halve the "disorder", log k
   depth would be needed for exact reversal at all k — d is fixed,
   so look for a NO-PROGRESS / BOUNDED-PROGRESS lemma for uniform
   interleaves on the separator permutation (this is Lane B's
   formalization program — coordinate through me if you want their
   framework).
4. The honest alternative: a clean impossibility proof at varying k
   COMPLETES the program as a dichotomy (fixed structure: always
   computable; uniform/varying: never; unbounded alphabet: never).
   Do not treat "construction failed" as failure — a proved
   impossibility is the other half of the same theorem.

## Rules (user directives, hard)

- Theory first. NO brute force. Any single run <= 1 minute.
- CPU-heavy verification in C, never Python.
- Write scripts + logs here in rev-try/; your REPORT.md writes may be
  blocked — send the report content to me (coordinator) and I will
  integrate it into ../rev/REPORT.md as Round 16.
- Machine checks CONFIRM hand derivations; they do not replace them.

## Parallel lanes (do not duplicate; I relay)

- Lane C (you): the construction (or its impossibility).
- Lane B: Telescope/Schema-P at varying k — formalize what remains
  an S-function when k is a variable; FIRING-UNIFORMITY framework.
- Lane D: invariant hunt at varying k (diagonal families, separator-
  order permutation arguments).

Start with a 10-minute pure-think pass on the uniform-interleave
obstruction; write down either the construction sketch or the
obstruction's precise statement BEFORE any machine work.

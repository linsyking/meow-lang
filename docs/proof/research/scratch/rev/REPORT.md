# Is string reversal L-reachable? (paper open problem 2 / §4; hinge 2 of §5.6)

Working directory: `docs/proof/research/scratch/rev/`.  Target: `docs/proof/main.tex`.
THE QUESTION: E in Exp_1 with ⟦E⟧ = rev (total), flat calculus L (def:exp/def:den,
no recursion, strict everywhere), some/any finite |Σ| >= 2.
Scripts: `lcore.py` (independent den, cross-checked), `verify_round1.py`,
`verify_round1b.py`, `r2lib.py`, `search_r2.py`.

## Round 1 — machinery + cheap re-verification (ALL PASS)

* `lcore.den` (independent def:den) == `rec/lazy_pass/core.ev_eager` on 4000
  random expressions: 0 disagreements (values + definedness).
* subst sanity (paper examples), toolkit (enc/dec, cat, head, tail, eq, if)
  on all 127 strings |w|<=6, eq/if 1600 pairs: PASS.
* rotation by 1 (`cat(tail X, head X)`) and by 2 on all 511 strings |w|<=8: PASS.
* Constant patterns vs rev: exhaustive BFS (pat/rep <= 2 over abc, 255 binary
  test strings, depth 3): 324,827 behaviors, rev NOT found (23 s).  The closest
  length-preserving behavior is the IDENTITY (wrong on 210/255; 45 palindromes).
  Randomized 4-7-pass constant pipelines (~100k): best wrong on 450/511.
  => constant patterns do not even get close (matches thm:subsequential).
* Near-miss `[aa->c][cb->bc][c->aa]` (2nd-best BFS): moves one doubled letter
  leftward across `b` (`aab |-> baa` OK) but fails on `baa`: bounded pipelines
  do bounded, direction-locked swaps.
* Coordinator's prelim notes machine-confirmed:
  - `[eps/b]X` breaks the naive skew invariant (240/255 inputs: late flip moves
    earlier output positions).
  - `[XY/tail X]X`: output[0] = X[0] iff w constant, else w[0] — deep gate
    (constancy) selecting between shallow contents; flipping the last char of
    a^(n-1)b flips output[0].  (Machine-caught subtlety: n=2 constant leftover
    re-matches the pattern.)

## Round 1b — the ANCHOR family (coordinator's message) re-verified [ALL PASS]

last(X), init(X), rotate-right-1 = cat(last, init), swap-first-last =
cat(last, tail(init), head) are ALL in L over {a,b}: verified independently
with lcore.den on all 511 strings |w|<=8 (0 fails; sizes 136/170/320/385).
Construction: T = enc2_x(X).bb; constant pattern x.s.bb occurs iff last(X)=s;
occurrence test via eq; delete + dec2 = init.
CONSEQUENCES: (i) output[0] CAN be w[n-1] in L (last); (ii) one character CAN
wrap around by n-1 (rotr1); any rev-excluding invariant must survive
last/init/rotr1/swapfl as positive controls.  The obstruction is unbounded
REORDERING, not reading the right end.

## Round 2 — synthesis escalation (first run)

* subst(A,B,C) == C.replace(B,A) on 20000 random triples: 0 disagreements
  (fast search justified).
* Library: 28 total-nonempty patterns (anchored; note [A/X]X itself is
  UNDEFINED at w=eps, so patterns must be anchored like aX/Xa/enc2aa/...),
  29 replacements (X, tail^k, head, last, init, rot1, rotr1, swapfl, enc,
  enc2, halve, XX, markers, constants): 806 passes.
* Exhaustive BFS depth 2 in behavior space (31-string battery): 210,317
  behaviors, rev NOT reachable; best depth-2 pipeline exact on 18/31.
* Genetic search (pop 400, 400 gens, 11 s): best exact on 21/31 search
  battery, 37/511 on |w|<=8 — fails already on 'ab'.  Best pipelines are
  rotr1/swapfl-heavy but stuck ~20-21/31; the landscape has a hard wall
  around "get output[0] right" (rotr1 does that) with the middle unreversed.
* VERDICT SO FAR: no witness at this frontier; the wall is exactly
  "unbounded reordering".

## Key theoretical development (to machine-test in R3): the LDS/mult invariant

Global stream decomposition: the output's PROVENANCE sequence (input
positions of its atoms) = shuffle of k+1 streams: w-verbatim (increasing) +
per-pass streams (subsequences of prov(R_i)^{m_i}, m_i = match count).
* On inputs with ALL DISTINCT characters every pattern matches at most once
  => m_i <= 1 => LDS(prov) <= C(E) (bounded longest decreasing subsequence).
  rev on distinct-char w has LDS = n.  [Kills rev over INFINITE alphabets —
  not enough for finite Σ.]
* Over finite Σ matches repeat: m_i unbounded; the copies duplicate atoms.
  CANDIDATE INVARIANT: **LDS(prov) <= C(E) * mult(prov)** where mult = max
  multiplicity of an input position ([X/a]X: LDS=m, mult=m OK; XX: 2<=2C
  OK; rev: LDS=n, mult=1 -> excluded).
  Induction obstacle: deletion passes can shave copies (drop mult) while
  LDS survives — the shaving needs pattern matches that distinguish
  identical copies by context.  THIS IS THE CRUX TO INVESTIGATE.
* min-LDS over valid relabelings is too weak over binary (it equals
  ~n/LPS(w), and binary strings have LPS >= n/2): the invariant must use the
  EVALUATION's provenance, not the I/O relation.

## Next (R3)

1. Provenance-tracking evaluator (labels per input position, same semantics)
   — verify against den; compute prov/mult/LDS.
2. Test LDS <= C*mult on: random expressions, toolkit, last/init/rotr1/
   swapfl, XX, [X/a]X, near-miss pipelines, rotations.
3. If it survives: attack the induction (the deletion/shaving step);
   if not: the counterexample construction points at rev.
4. Continue synthesis with provenance diagnostics in the fitness.

## Round 2 — provenance machinery + the LDS/mult conjectures

New modules: `prov.py` (provenance-tracking evaluator: values = (char,label)
atoms, label = input position or None for constants; lden == den on content
and definedness, 3000 random (e,w), 0 mismatches), `verify_round2.py`,
`verify_round2b.py` (influence flips), `search_lds.py`, `search_lds2.py`.

### Findings

1. THE CONTENT-FAKING LOOPHOLE (machine-discovered): the toolkit's decodings
   (dec, dec2) and cat RECONSTRUCT strings from CONSTANT characters — the
   atom-prov of cat(tail X, head X), last, init, rotr1, swapfl outputs is
   EMPTY (all atoms constant).  So atom-provenance underestimates content
   provenance: an invariant on atom-prov alone cannot exclude a rev witness
   built from gates + constants.  Any proof must handle both the MOVING
   route (atoms) and the FAKING route (constant leaves + gates).
2. Atom-prov data (controls + 3000 random exprs depth<=5, |w|<=24):
   LDS@mult=1: max 3 (one expression), histogram {0:1793, 1:1199, 2:7, 3:1}.
   LDS/mult: max 3. rot1/rot2: 2.  Depth-2 library genetic search (400 gens,
   pass space 874): max LDS@mult1 = 2 even while mult explodes to 312 —
   disorder always paid for by multiplicity.
3. prov-LDS arithmetic: rotations have LDS 2 for every k (prov = two
   increasing runs); swapfl 3; "rev-last-k . init^k" (buildable: last(init^j)
   per anchor trick + cat) has LDS k+1, mult 1 — C(E) grows with expression
   size, consistent with Conjecture B; rev needs k = n.
4. Influence-flip data (function level, |w|=12): rev = perfect anti-diagonal
   matching, 66 crossings; rot1/rotr1 = 11 crossings (one wrap); last = 1
   far cell, 0 crossings; init = 0.  XX has QUADRATIC inversions but LDS 2
   (Dilworth) — inversion mass is the wrong measure; LDS width is right.
5. CONJECTURE A: LDS(prov) <= C(E)*mult(prov).  CONJECTURE B: LDS bounded
   at mult = 1.  Both survive everything tried.  PROOF OBSTACLE (located
   precisely): insertion passes are paid for (at stage k the m_k fresh
   full copies force mult(T_k) >= m_k * mult(A_k)), but DELETION passes can
   DROP mult without dropping LDS — the "shaving" scenario.  Uniform shaving
   (same surviving set S in every copy) provably cannot beat LDS(A) — the
   chain dies at each copy's minimum.  Only NON-UNIFORM shaving (different
   surviving atom per copy, S_c = {m-c} style) could yield unbounded
   LDS@mult1 — and that requires per-copy-different deletion shapes, which
   only boundary-spanning matches (across the inter-copy gaps) or greedy
   shielding can provide.  This is the precise crux.
6. Non-atom result: min-LDS over content-consistent relabelings is <= n/LPS(w)
   and binary strings have LPS >= n/2, so content-level relabeling invariants
   CANNOT exclude rev over any fixed finite alphabet (they do over unbounded
   alphabets: distinct-char inputs force prov = exact reversal).
7. Synthesis status: exhaustive depth-2 (806-pass library): no witness;
   genetic depth<=12: best 21/31 strings |w|<=4, fails at 'ab'.  The wall is
   uniform: bounded pipelines get output[0] right (rotr1) and nothing more.

### Next (Round 3)

- Targeted non-uniform-shaving construction: insert m copies of A(w) via a
  [A/B] pass, then shave with boundary-context patterns; try to beat
  LDS@mult1 = 3.  Either a construction (points at rev) or strengthened
  evidence for the Shaving Lemma.
- Swap-halves / rotate-by-n/2 litmus search (quadratic-crossing content
  functions; expected unreachable).
- Attempt the Shaving Lemma proof: bound the number of distinct per-copy
  deletion shapes by the pass structure.

## Round 3 — the frontier, precisely located

New scripts: `search_2pass.py` (exhaustive 2-pass), `search_halves.py`
(swap-halves litmus), the checks in this section run ad hoc (recorded here).

### 3.1 Coverage results (no witness, quantified)

* EXHAUSTIVE 2-pass over the full library space (28 total-nonempty
  patterns x 29 replacements = 812 passes => 659,344 pipelines, 37 test
  strings up to |w|=16): **max LDS@mult1 = 3, max LDS/mult = 3.0**
  (best: [b/b] then [rot1(X)/ab]).  Conjectures A and B hold with C = 3 in
  the whole depth-2 fragment.
* Random corpus (3000 exprs, depth<=5): max LDS@mult1 = 3.
* Depth-2 library genetic (400 gens): max LDS@mult1 = 2 (mult up to 312).
* Synthesis for rev itself: exhaustive depth-2 (no), genetic depth<=12
  (best 21/31 on |w|<=4, fails at 'ab', 37/511 on |w|<=8).
* Swap-halves litmus (halves/first-half/second-half, genetic, 812-pass
  library): best 14/86, 28/86, 55/86 on |w|<=6, and 0/3 on |w|=10..14.
  (The 55/86 for second-half is fixed-length tail^k artifacts.)  All three
  need variable-length left-anchored deletion -- the same wall as hinge 1.

### 3.2 The two routes and the faking-immune measure

rev-last-k + init^k (in L for each fixed k, via anchored reads + cat) has
influence-crossings 13, 25, 36, 46 for k=1..4 on n=14 (i.e. ~k*(n-k)+...),
while rev has 91 = C(14,2).  Rotations: ~n.  So at the CONTENT level
(immune to constant-faking):

  **CONJECTURE C**: the influence-flip crossing count of an L-reachable
  function is <= C(E) * n.  rev needs n(n-1)/2.  [X/a]X-style broadcasts
  have NO perfect-matching influence and are not counterexamples.]

rev-last-k is the extremal family: k units of "right-end read + reassembly"
cost k*n crossings; rev needs n such units => a single expression would need
C(E) >= n/2, impossible for fixed E.  Conjecture C is the faking-immune
form of Conjecture B (LDS@mult1); both fail or hold together through the
same mechanism.

### 3.3 The mechanism, machine-validated (both directions)

* Variable-depth cutting VALIDATED: text = copies of a value A (prov
  increasing, leading run) separated by gaps b^j; the pass [eps/b^L] cuts
  copy j's prefix to depth L-j (greedy through the boundary run).  Result:
  prov (6,7,8,9 | 5,...,9 | 4,...,9 | ...): a decreasing chain
  (9,8,7,6,5) ACROSS copies: **LDS 5 with 5 copies -- each unit of
  cross-copy disorder is paid for by one duplicate (mult = #copies)**.
  This is Conjecture A's mechanism, confirmed exactly.
* The unpaid version (LDS at mult = 1) would require deleting the other
  m-1 copies of each atom while keeping the chain atoms -- per-copy
  surgical deletions -- and per-copy discrimination is only available
  through boundary-spanning matches (identical copies have identical
  content), i.e. through the gap structure, which is itself text and
  recurses.  THE SHAVING LEMMA (crux, still open):
    the number of copies that can be shaved to *different* surviving sets
    is bounded by a function of the pass structure (each pass's single
    pattern value can cut at variable depth only through locally-uniform
    runs, and uniform runs make the disorder content-invisible).
* Relabeling barrier (why content-level arguments are insufficient over
  fixed alphabets): min-LDS over content-consistent relabelings of rev(w)
  is <= n/LPS(w) <= |Sigma| (binary strings have palindromic subsequence
  >= n/2), so no relabeling-based invariant can exclude rev over any
  fixed finite alphabet; the proof must use the evaluation's actual
  atom/gate structure, i.e. Conjectures B/C, not content consistency.

### 3.4 Verdict at close of this session

No witness; no complete impossibility proof; the obstruction is now
precise and machine-evidenced on both sides:

1. Constant patterns: dead (theory + exhaustive BFS depth 3).
2. Depth-2 variable patterns over a rich library (incl. anchored
   right-end surgery): exhaustively no witness; disorder (LDS@mult1) caps
   at 3.
3. Deep pipelines (genetic, ~12 passes): no witness; the wall is
   'unbounded reordering', shared with swap-halves and first/second-half
   (left-anchored variable deletion = hinge 1's wall).
4. The quantitative invariants to prove (all machine-tested, none
   refuted): A (LDS <= C*mult), B (LDS bounded at mult=1), C (influence
   crossings <= C*n).  rev violates all three; the controls (rotations,
   last/init/rotr1/swapfl, rev-last-k, XX, [X/a]X, near-misses) satisfy
   all three.
5. The single missing lemma: SHAVING (deletion passes cannot convert
   multiplicity into disorder).  The mechanism analysis (boundary-spanning
   matches, uniform-run cutting) and its machine validation are above.

### Scripts index

lcore.py (den, cross-checked) | prov.py (provenance evaluator, cross-checked)
| r2lib.py (library incl. anchored right-end family) |
verify_round1.py, verify_round1b.py (controls incl. coordinator's) |
verify_round2.py, verify_round2b.py (prov corpus, influence) |
search_r2.py (rev synthesis) | search_lds.py, search_lds2.py (disorder
frontier) | search_2pass.py (exhaustive 2-pass) | search_halves.py
(swap-halves litmus).

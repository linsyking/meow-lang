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

---

## Round 4 (coordinator-directed): cross-hinge tests, the price ladder,
## and the Shaving Lemma

### 4.1 Cross-hinge tests (verify_round4_hinges.py) -- the invariant
### family is REV-SPECIFIC

Both sibling hinges' canonical functions run through prov.py and the
Conjecture A/B/C machinery (content side; P's provenance is forced since
its output chars are verbatim w-chars; f2's via a labeled right-to-left
substitution lsubstR, cross-checked against lrcore.substR on ALL |w|<=12):

* P = takeWhile != b (once-hinge reduction, once/REPORT.md R1-R3):
  prov (all |w|<=10): max LDS = 1, max mult = 1.  Influence (all 8191
  binary inputs |w|<=12): crossings = 0 on EVERY input; influence is pure
  truncation (mean 2 len-changing rows, 9 empty of 11).  A/B/C hold with
  room to spare.
* f2 = [b/aa]^R (L+R hinge; rho's minimal hard instance):
  lsubstR faithfulness PASS (all |w|<=12).  prov: max LDS = 1 at mult 1
  (R-pass preserves the order of surviving w-atoms; inserted b's are
  constants).  Influence (all 8191 inputs |w|<=12): crossings = 0 on
  EVERY input; local disorder only (mean maxdisp 1.76, mean 5.8
  len-changing rows of 11).

CONCLUSION (both predictions confirmed): Conjectures A/B/C exclude rev
but NOT the other two hinges.  No unified separation theorem via this
invariant family; the three hinges need three different obstructions --
unbounded reordering (rev), the spanning needle (once), residue routing
(L+R direction).  Corollary for the paper: a crossing-count proof of
rev !in L cannot double as a proof of either sibling.

### 4.2 The price-of-reordering ladder (verify_round4_ladder.py,
### paper draft: price_of_reordering.tex)

Every rung now has a BUILT, exhaustively-verified expression (the
rev-last-k family built as cat(last o init^j) for j<k, init^k; sizes
320/2,498/17,689/123,971 for k=1..4; exact on all binary inputs |w|<=10
for k<=2, |w|<=8 for k<=4).  Crossings at n=14 (worst of 56 inputs):

  id 0 | init 0 | last 0 | rotR1 13 = n-1 | swap-fl 25 = 2(n-2)+1
  rev-last-k: 13, 25, 36, 46 for k=1..4  |  rev 91 = C(14,2)

CLOSED FORM (new, exact): chi(rev-last-k) = k(n-k) + C(k,2) =
C(n,2) - C(n-k,2) -- the moved tail block's crossings of the untouched
head plus the block's internal reversal.  At k=n this is C(n,2) = chi(rev)
(rev-last-n = rev).  Every L-expressible rung sits at O(n); rev is the
k=n rung and needs Theta(n^2).

Two barriers, both now machine-checked:
* RELABELING (sharper than round 3's palindrome route): the canonical
  content-consistent labeling of rev(w) (increasing within each
  character class) has LDS <= #distinct chars <= |Sigma| -- a strictly
  decreasing subsequence cannot use two positions of one class.  Verified
  at n=14 (max 2 over 56 inputs) and by BRUTE FORCE over all consistent
  bijections, |w|<=6 (canonical is optimal).  No output-content-only
  order invariant can exclude rev.
* FAKING: the ladder's own provLDS column is 0 for every anchored rung
  (last/init/rotR1/swap-fl/rev-last-k rebuild outputs from CONSTANTS) --
  atom-provenance invariants miss them entirely; only influence
  crossings measure their reordering.  Also cat(X,X): C(14,2)=91
  inversions at prov LDS 2, mult 2 -- inversion MASS is the wrong
  measure (Dilworth); width is right.

Paper-voice draft: price_of_reordering.tex (LNCS remark + table,
compiles standalone; drop-in after open problem 2 or referenced from
5.6).  It includes the cross-hinge observation of 4.1.

### 4.3 The Shaving Lemma (search_shaving.py) -- v1 refuted, v2 verified

V1 (residuals a function of the entry offset alone, <= |B| distinct):
REFUTED by the machine -- 33/3000 trials with #distinct residuals >
|B| (e.g. A='aabb', B='ba', gaps ab/baaa/ba/a: residuals {1,2,3},
{0,1,2,3}, {0,1,2}); 318/3000 trials with same-offset/different-
residual.  Mechanism: EXIT straddles -- matches starting inside a copy
extend into the following gap, so the residual depends on what follows.

V2 (correct, verified): the residual of a copy is a function of
  (o, h) = (entry offset in {0..|B|-1}, the |B|-1 text chars following
  the copy),
so #distinct residuals <= |B| * |Sigma|^{|B|-1}.  Verified as a FUNCTION
PROPERTY (same (o,h) => same residual: 3000 trials, 0 failures) and as
a count bound (0 failures), random + run-biased copy-gap texts.

CONSEQUENCES:
(3) At final mult 1, any residual class with >= 2 copies contains no
    w-ATOMS (each would be duplicated).  So a strictly decreasing chain
    through former copies of A picks w-atoms only from single-copy
    classes:  chain <= LDS_w(A) * prod_j (|B_j(w)| * s^{|B_j|-1}).
    For CONSTANT patterns every factor is O(1): deletion passes convert
    NONE of the inserted structure into disorder beyond a constant.
    (Also: constant-pattern pipelines have prov LDS <= 1 outright --
    replacements are constant strings, so no w-atoms are ever inserted;
    the content of Conjecture B is entirely in the variable world.)
    The remaining gap to Conjecture B is exactly the VARIABLE patterns
    (|B(w)| unbounded) -- the same gap as thm:subsequential.  A full
    proof needs: long computed needles cannot be shaved at many distinct
    phases on copies of a bounded sub-expression's value without paying
    multiplicity (needle-content recursion through w).

### 4.4 The attacks through the gap (both fail to beat LDS@mult1 = 3)

* Part B: genetic search over "copy, then shave" 3-6-pass pipelines,
  168 copy-creating first passes x 36 shave passes including LONG
  VARIABLE needles (aX, Xbb, enc2aa, ... : needle length grows with
  |w|): 250 x 150, re-verified on |w|<=8 + structured: max LDS@mult1 = 2
  (two independent runs).  The 2-pass exhaustive max 3 stands.
* Part C: the double-sided-cut hand constructions (cut left depths per
  copy, kill tails, cut right depths -> disjoint singleton residuals
  {K-j}): best LDS@mult1 = 1.  The construction dies at the multiplicity
  wall: per-copy surgical deletion needs per-copy patterns, and uniform
  rules destroy the copy/gap contrast that creates the phases.
* Champion dissection (depth-2 max 3, w='bbaab'): prov (2,1,4,0) =
  1 verbatim atom + LDS 2 of ONE inserted rot1X copy -- whose own prov
  (1,4,0) mixes w-atoms with CONSTANT a's (tail/head rebuilds them).
  Pass 1 [b/b] is a CONSTANTIZER: it kills all b-atom labels, the
  faking route again.  No multi-copy shaving stress even at the top.

### 4.5 Swap-halves: the three-way litmus (coordinator priority 3)

Unreachable in L (round 3 litmus: 14/86, 55/86, 28/86 on |w|<=6, 0/3 on
|w|=10..14); in ONCE it is the P-wall (left-anchored variable-length
deletion); in L+R it is the residue question.  NEW from this round
(transferable): the natural halves-extraction route through run-cutting
(the double-sided singleton construction of 4.4 Part C) fails exactly at
the multiplicity wall -- copies cannot be shaved to disjoint
variable-length residuals by bounded constant rules.  Same wall as
hinge 1's P and the shaving lemma's variable-pattern gap.

### 4.6 Round 4 verdict

No witness, no full impossibility proof.  The frontier moved:
(i) the invariant family is proven rev-specific (both sibling hinges
pass with extremal values); (ii) the reordering ladder is exact with a
closed form and every rung machine-verified end-to-end, with both
barriers (relabeling, faking) quantified; (iii) the Shaving Lemma
exists in a verified v2 form with the constant-pattern case closed and
the variable-pattern gap isolated as THE missing piece, isomorphic to
the paper's subsequentiality boundary.

### 4.7 Next round plan

1. LONG-NEEDLE SHAVING (the isolated gap): for a variable pattern
   B(w) to shave copies of A(w) at many distinct phases, B(w) must
   occur inside A(w) at many offsets -- a self-reference constraint
   through w.  Formalize and machine-test: bound #distinct effective
   phases by the overlap structure of occurrences of B(w) in A(w)
   (periodicity: fine65/lothaire97-style run arguments).
2. Fold v2 + the chain bound into a proved THEOREM for the fragment
   "insertions of variable values + constant deletion patterns" (chain
   <= 1 + sum_i LDS(R_i(w)) * O(1)) and check it against the corpus.
3. Conjecture C escalation: measure crossings for more anchored
   constructions (rep_n, escape, the recursive-lite shapes) at n=20+.

### 4.8 Script index (round 4)

verify_round4_hinges.py  -- cross-hinge tests (4.1)
verify_round4_ladder.py -- ladder build/verify/measure + barriers (4.2)
price_of_reordering.tex -- paper-voice remark draft (4.2)
search_shaving.py       -- v1 refutation, v2 verification, attacks (4.3-4.5)

---

## Round 5: THE PROOF ATTEMPT (user charter: prove rev is not in L)

No full theorem this round; the attempt produced a proved and
machine-verified FRAGMENT that reduces the pipeline question to a
value recursion, plus one machine-verified fact whose proof is the
remaining crux.  Paper-voice draft: phase_leftmove_fragment.tex.

### 5.1 Lemma Phase (proved + verified; supersedes Shaving v2's count)

A deletion pass [eps/B] on copies of A: each copy's residual is a
function of (o, j) = (entry straddle depth, exit straddle depth) with
  o in {0} u O(A,B),  O = {o: A[:o] = B[-o:]},
  j in {0} u J(A,B),  J = {j: A[-j:] = B[:j]},
plus one extra class (fully covered copies, residual empty).  So
  #distinct residuals <= (1+|O|)(1+|J|) + 1
-- governed by the OVERLAP SETS, not by |B|*|Sigma|^{|B|-1}.
[verify_round5_phases.py PART 2: function property, o/j membership,
count: PASS on 4000 random+run copy-gap texts.  The first version's
count was refuted by the machine (167 -> 4 cases: the +1 class); the
off-by-one in my exit-crossing condition was also machine-caught.]

### 5.2 Lemma Overlap-Periodicity (proved + exhaustive)

O's phases are border-chain structure: (i) every smaller phase is a
border of A[:max]; (ii) every difference is a period of the longer
prefix; (iii) arithmetic-progression phases with step d => d is a
period of A[:max] (the straddled prefix is an o_max/d-fold repetition).
[PART 1: all A<=8, B<=7 over {a,b}: 128,520 pairs, all clauses PASS.]
The hoped-for density bound |O| <= o_max/p is FALSE (A=aabaabaa,
B=xaabaa: O={1,2,5}, p=3) -- found by hand outside the first machine
range, then exhibited in-machine.  The run mechanism (all known
disorder) sits exactly at the AP extreme: prefix a repetition.

### 5.3 The Left-Move Wall (machine-verified; proof open -- THE CRUX)

At mult 1 (pairwise disjoint residuals) there are NO two consecutive
left-moves: the longest strictly decreasing position chain through
disjoint residuals is exactly 2.  [Exhaustive: 1,152,480 texts
(|A|<=4, |B|<=3, gaps<=2, <=3 copies; 4,730 with >=2 disjoint
residuals; max chain 2.  Plus 40,000 random texts up to |A|=7, |B|=6,
6 copies: max 2.]  Mechanism (singleton case): residual {p} requires
the needle to BOTH end with A's prefix of length p AND start with A's
suffix of length |A|-1-p -- both straddles paid from the same needle;
a triple needs the gap sandwich laid twice in a row.

### 5.4 Proposition Base Case (derived; conditional on 5.3)

For [A/sigma][eps/B], A = R(w), at mult 1:
   LDS(prov) <= 2*LDS(prov_A) + 1.
Proof: no two consecutive position-descents (5.3); delete the later
pick of each descent pair -> survivors are an ascending-position,
descending-value subsequence of prov_A (<= LDS(A)); descents <= half
the steps.  [Verified: 205,585 (pipeline, input) instances, all
library R x constant B<=4 x |w|<=7+structured: 0 violations.  Constant
A: exhaustive 1,860 pipelines, all |w|<=8: max 1 = the bound.]
Shaving does not create disorder; it inherits it (factor 2 + verbatim).

### 5.5 What a full rev-not-in-L proof still needs (the honest list)

(0) THE FAKING CAVEAT: the fragment is the ATOM route.  A constant-gate
witness (empty prov, output assembled from constants by content
tests) is invisible to it; that route needs the influence-crossing
side (Conjecture C / rem:price).  Both routes must be closed.
(1) PROVE the Left-Move fact (5.3) -- the sandwich argument.
(2) THE VALUE RECURSION at intermediate multiplicity: LDS(R(w)) for
sub-expressions without a mult-1 hypothesis (Conjecture A form), then
compose with the phase/periodicity lemmas as the outer passes kill
duplicates.
(3) MULTI-PASS composition: the left-move wall at every stage, where
stage l+1's "copies" are stage l's residuals (nested, shorn).
Traps respected: no content-only invariant (relabeling barrier), no
atom-only invariant (faking), no pair-mass (XX), and no reliance on
"L cannot select an extremal site" (prop:del-leftmost kills that).

### 5.6 Script index (round 5)

verify_round5_phases.py -- all of the above (PARTs 1-4)
phase_leftmove_fragment.tex -- paper-voice fragment (compiles)

---

## ROUND 6 -- the wall falls, Conjecture A falls, Conjecture B stands

Priority order was: (1) prove the Left-Move Wall, (2) the value recursion,
(3) LINE 2.  What actually happened: the wall is FALSE at larger sizes,
and chasing WHY produced a construction that refutes Conjecture A
outright.  Conjecture B -- the mult-1 invariant, and rev is a mult-1
function with LDS = n -- survived every attack and is now the single
live thread of the atom route.

### 6.1 Count reconciliation (coordinator's item (a))

Round 5's Left-Move Wall domain (1,152,480 texts, |A|<=4, |B|<=3,
gaps<=2, m in (2,3)):
  * "ALL nonempty residuals pairwise disjoint": 4,730 texts (my round-5
    convention)
  * "EXISTS a disjoint pair": 23,368 texts (the coordinator's
    verify_round5_leftmove.py convention)
  Both re-run in verify_round6_leftmove.py PART A.  The two numbers are
  the same domain under two conventions; no discrepancy.

### 6.2 The Left-Move Wall is FALSE (priority item 1, negative outcome)

The round-5 Fact ("max strictly-decreasing chain through pairwise-
disjoint residuals = 2", verified on 1,152,480 texts + 40,000 random)
was a SMALL-DOMAIN ARTIFACT.  Two refutations, both machine-checked:

(1) THE B2 TRIPLE (targeted hunt).  The power equations of round 5 pin
    a triple's habitat to B^INFINITY-structured texts (stretches between
    picks are B-powers).  B1 (all-straddle skeleton solver, 18 forced
    texts) found none; B2 (300,000 B^inf-structured random texts,
    n<=10, m<=8) found exactly one:
        B='ababa', A='bababab', gaps=['aa','a','a','a']
        residuals {0:[4], 1:[2], 2:[0,6]}, picks 4 > 2 > 0, disjoint.
    Standalone re-check in verify_round6_witness.py PART 2a.
(2) THE STAIRCASE (see 6.3): family-1 provs contain decreasing chains
    of length j through j pairwise-disjoint SINGLETON residuals
    (e.g. j=8: (15,13,11,9,7,5,3,1) with residuals {15},{13},...{1}).
    The wall is not merely false; the true chain length is ~|w|/2 in
    this family.  The round-5 wall (chain<=2) and the base-case
    proposition's DERIVATION (no two consecutive descents) are dead.

### 6.3 CONJECTURE A REFUTED (the headline result)

Conjecture A (rounds 2-5): LDS(prov) <= C(E) * mult for a constant
C(E).  FALSE.  Witness family (all rows content-cross-checked against
lcore's independent den, verify_round6_witness.py PART 1):

    E2 = [eps/init^2 X] . [X/b] X    on   w_j = b(ab)^j

    prov(w_j) = (n-2, n-4, n-6, ..., 3, 1, n-2, n-2, n-1)  [odd labels; n odd]
    (n = |w_j| = 2j+1); LDS = j EXACTLY, mult = 3 EXACTLY, j = 2..40
    (ratio 13.33 at j=40; prov j=12: (23,21,...,1,23,23,24)).
    E4 = [eps/init^4 X].[X/b]X: LDS = j/2+1 at mult 4-5
    (ratio 5.0 at j=40).  LDS/mult -> infinity in both.

MECHANISM (the modular staircase).  w = b(ab)^j is alternating, so
[X/b]X tiles the line with copies of w separated by single 'a' gaps:
the text is alternating throughout.  B = init^d(w) has odd length
m = n-d and is a factor of the same alternating stream, so the greedy
scan of [eps/B] matches at spacing m+1 and emits exactly one 'b'
between consecutive matches.  Emission c sits at global position
(m+1)c; copy units have length n+1; the emitted atom's offset within
its copy is  (m+1)c mod (n+1) = n-d + ... , i.e. it DESCENDS BY d
PER EMISSION (a modular staircase with step d).  The strictly
descending run before the first wrap has length ~(n+1)/d, and the
boundary emissions (the leading atom of copy 0, the last gap atom,
the final wrap emission) contribute only the CONSTANT number of
duplicated labels (n-2 appears 3x; hence mult=3, pinned, while
LDS = j = (n-1)/2 grows linearly).  This also kills the round-5
"Base-Case Proposition" derivation (no-two-consecutive-descents is
false: the staircase is j-1 consecutive descents) -- although the
proposition's STATEMENT (mult 1 => LDS <= 2 LDS(A)+1) has still not
been violated (6.4).

### 6.4 CONJECTURE B SURVIVES (mult 1 => LDS <= C(E)); rev is mult-1

Attack surface swept (verify_round6_conjAB.py, verify_round6_mult1_
sweep.py): 25 needle constructions (tail^d for d<=8 -- cheap, tk.tail
is linear; init^2; a./b. cat-phase shifts) x 7 periodic w families x
6 sigmas x j<=10, plus init^d for d in 2..6 on the alternating family:
NO row with mult = 1 and LDS >= 4 anywhere.  (init^d beyond d=2 is
exponentially expensive: leaf-substitution composition blows the AST
up 4^d; 3.3M nodes at d=6.  tail^d and cat-shifts are the cheap probes.)

STRUCTURAL STORY (hand analysis, machine-consistent, not yet a proof):
in the 2-pass family [eps/B(X)].[X/sigma]X a long descending chain
requires the staircase; the staircase must not wrap (a wrap re-emits
offsets already emitted: duplicates), and the end-of-text dump emits
the last copy's top offsets, which the staircase's FIRST emissions
also hit.  Both effects force mult >= 2 whenever the chain is long;
equivalently mult = 1 pins the chain to O(1) in every construction
we can build.  Since rev's prov (n, n-1, ..., 0) has mult = 1 and
LDS = n, Conjecture B is exactly the invariant that separates rev
from L, and it is now the ONLY surviving member of the A/B/C family:
  A: REFUTED (6.3).  B: open, all attacks repelled.  C: untouched
  (influence-crossing; the length-changing rows are discarded, and
  every family in this round changes output length under input flips,
  so C holds vacuously on them -- the discard rule is load-bearing).

### 6.5 Corrected status of the round-5 fragment

phase_leftmove_fragment.tex must be revised before any integration:
  * Fact No-Consecutive-Left-Moves: REFUTED (the staircase).
  * Proposition Base Case: statement not violated (no mult-1
    counterexample found), derivation broken.  It should be re-stated
    as a CONJECTURE with the mult-1 hypothesis explicit.
  * Lemma Phases / Lemma Overlap-Periodicity: unaffected (they are
    about residual classification, not chain length).

### 6.6 Next round (priority order)

(1) PROVE CONJECTURE B for the 2-pass fragment: at mult 1 the
    surviving-copy offsets form a "staircase with no wrap and no tail
    collision" -- formalize the duplication argument (wrap duplicates
    offsets; the end-of-text dump duplicates the top offsets) into:
    mult 1 => chain <= f(|B|, structure of sigma-sites).  The B2
    triple and the family-1 provs are the test cases.
(2) VALUE RECURSION at intermediate mult: family 1 shows the
    intermediate-mult regime has LDS ~ n/d with d = |B|-defect; a
    recursion  LDS(stage l+1) <= g(LDS(stage l), mult) must tolerate
    staircases -- the round-5 plan is unchanged in shape but the
    constants grow.
(3) Conjecture C (LINE 2): now the only other live invariant; the
    length-discard caveat must be stated wherever it is used.

### 6.7 Script index (round 6)

verify_round6_leftmove.py -- wall re-verification + count
    reconciliation + B1 skeleton solver + B2 triple hunt + pair
    classification
verify_round6_conjAB.py -- init^d leaf-substitution composition;
    family 1/2 tables; init sanity (init is CORRECT on all 511
    binary |w|<=8; the round-6 "INIT BAD" flags were label-provenance
    checks, not content)
verify_round6_mult1_sweep.py -- the mult-1 hunt (cheap needles);
    NO mult-1 rows with LDS >= 4
verify_round6_witness.py -- FINAL WITNESSES: A-refutation extended to
    j=40 (every row content==den), B2 triple standalone, staircase
    provs printed

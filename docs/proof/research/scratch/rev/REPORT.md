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

---

## ROUND 7 -- Theorem A proved; the text-level statement refuted; the pipeline statement hardened

Coordinator's round-6 verification first (for the record): confirmed all
four batteries; hand-traced the E2 witness end-to-end (T = X a X a X, 17
chars; deletes at spans 0-2, 4-6, 8-10, 12-14; survivors (3,1,3,3,4);
initd(2)('babab') = 'bab'; L.den(E2)('babab') = 'aaaab'); corrected the
staircase's descent to ODD labels ("..., 3, 1" not "..., 2, 1") -- fixed
in REPORT 6.3 and the fragment.  Cross-hinge scoping note accepted: the
A-refutation (LDS linear in |w|) does not touch rem:price (chi vs |w|);
the side probe below closes that question.

### 7.1 THEOREM A (proved; machine-verified)

In the two-pass fragment [A/sigma][eps/B] at output multiplicity 1:
  (i)   at most one surviving copy per realized (o,j) phase, so
        #surviving copies <= (1+|O(A,B)|)(1+|J(A,B)|)+1;
  (ii)  the gap survivors' labels strictly increase in text order, so
        they contribute <= 1 to any decreasing chain;
  (iii) each surviving copy contributes <= LDS(prov_A) (within a copy,
        text order = ascending offsets, chain = descending labels =
        a decreasing subsequence of prov_A);
  hence  LDS(prov) <= [(1+|O|)(1+|J|)+1] * LDS(prov_A) + 1.
Proof of (i): two surviving copies with equal phase keep identical
offset sets (round-5 Lemma Phase, proved); if nonempty they share an
offset i, hence both keep an atom labeled prov_A[i], so mult >= 2.
This is the formal core of the "duplication argument": a surviving copy
is a PHASE, and phases are counted by the overlap sets.

VERIFIED (verify_round7_mult1.py PART 1, via an independent tagged
simulator, content cross-checked against L.den every 4009th instance,
0 mismatches):
  exhaustive: A<=4 x {LDS(A) in 1,2,3} x B<=3 x 8 sigmas x |w|<=6:
    1,157,184 instances, 591,315 at mult 1;
    violations: (i) 0, (ii+iii) 0, base-case conjecture 0.
  random: A<=8, B<=6, |w|<=10, arbitrary prov_A: 20,000 instances,
    10,308 at mult 1: violations 0/0/0.

WHAT THEOREM A DOES NOT GIVE: the constant (1+|O|)(1+|J|)+1 depends on
the VALUES A, B (both grow with w).  The E-uniform statement --
Theorem B: at mult 1, #surviving copies <= C(E) -- is the remaining
gap, and it is exactly the round-5 LINE 1 program (rich O/J ⟹
periodicity ⟹ duplication) now with the correct target: not the chain,
the NUMBER OF SURVIVING COPIES.

### 7.2 The text-level statement is REFUTED (chains up to 6 at mult 1)

The base-case bound 2*LDS(prov_A)+1 is FALSE as a statement about
texts (free injective labels).  Deterministic witness (PART 2a):
  A = babababab, B = abababa, gaps = a,a,a,a,a (4 copies):
  residuals {6}, {4}, {2}, {0,8}: chain 6 > 4 > 2 > 0 = 4.
Hunt over aligned alternating texts (m in 5..13, n = m+2, 3..6 copies,
pre/post in {"", a, aa}):
  chain histogram {2:33, 3:63, 4:45, 5:27, 6:12};
  best: m=11, n=13, 6 copies, pre='', post='a':
  residuals {0,12},{10},{8},{6},{4},{2}: CHAIN 6 (12>10>8>6>4>2).
So a text can realize a mult-1 staircase of length |A|/2.  THE PIPELINE
STATEMENT SURVIVES ON REALIZABILITY ALONE.

### 7.3 Why the text-level chains do not lift: the supply pigeonhole

The chain-6 text needs A (13 atoms, 7 b's) as a value of w, where w
(12 atoms, 6 b's = the sigma-sites, sigma='b') supplies only 6 b-
positions.  Any prov_A must repeat a b-position; prov_A nondecreasing
(LDS(A)=1) + A's parity-alternating content forbids adjacent repeats
(parity clash) and non-adjacent repeats (nondecreasing forces constant
between), so NO valid prov_A exists: |A| > #b-positions of w kills the
chain-6 text outright.  The chain-4 text (n=9, 4 sites) dies the same
way.  THIS is the realizability mechanism the missing Theorem B must
abstract: the chain's k picks demand k distinct positions in one parity
class (staircase) or k prov_A-descents (runs); the supply of such
positions in w, given the sigma-site structure, is what mult-1 caps.
Sketch only -- not yet a proof for general (A, B, sigma).

### 7.4 The pipeline evidence hardened

PART 2b (variable needles, the round-6 cheap constructions):
25 needle constructions x 7 periodic families x 6 sigmas x j<=16,
replacement always X (so LDS(prov_A) = 1, the hardest case for the
conjecture): at mult 1 the maximum LDS observed is **1** -- not 3, not
2: every mult-1 instance in the entire swept space is an increasing
prov.  Together with PART 1 (0 violations of 2*LDS+1 over 1.16M
exhaustive + 20K random pipelines) the pipeline-level conjecture has
never been closer to true; the counterexamples all die on
realizability, and the parity pigeonhole shows how.

### 7.5 Side probe: the staircase does NOT speak to rem:price

E2 = [eps/init^2 X].[X/b]X on w = b(ab)^j, j = 4..10 (PART 3):
every single flip changes the output length (rows = |w|, discarded =
|w|: 9/9, 13/13, 17/17, 21/21), so the perfect matching is empty and
chi = 0 vacuously.  The collapsing function with LDS ~ n/2 is
invisible to the crossing measure: chi <= c(E)|w| is untouched by it.
CONJECTURE C CAVEAT (one paragraph, for the paper version): C's
crossings are computed on length-preserving influence rows; rows whose
flip changes the output length are discarded, and for any pipeline
whose passes insert copies ([X/sigma]), every flip changes the site
count, hence the output length, hence ALL rows are discarded and C
holds vacuously.  The surviving uses of C are therefore the
length-preserving pipelines (rev is one: rev preserves length, so C
bites it with chi = C(n,2)); the discard rule is load-bearing and must
be stated wherever C is invoked.

### 7.6 Round 8 (priority order)

(1) THEOREM B: at mult 1, #surviving copies <= C(E).  Route: Theorem
    A(i) reduces it to bounding the number of REALIZED phases at
    mult 1; realized phases with disjoint residuals force overlap-rich
    O/J (periodicity), and the supply pigeonhole (7.3) caps what w can
    feed.  The chain-6 text and the E2 family are the two test cases
    the proof must kill.
(2) Convert 7.3's pigeonhole into a lemma: if the copy value A is
    alternating (more generally: if the realized phases exceed the
    label supply in any residue class), mult >= 2.
(3) Then the fragment's Conjecture (base case) follows with the
    constant 2*LDS(prov_A)+1 for the two-pass fragment, and the atom
    route closes if the recursion composes.

### 7.7 Script index (round 7)

verify_round7_mult1.py -- PART 1 Theorem A + base-case conjecture
    (exhaustive + random, tagged simulator, content cross-checks);
    PART 2a text-level chain hunt (chain-4 witness + histogram to 6);
    PART 2b pipeline hunt with variable needles (max LDS at mult 1: 1);
    PART 3 crossings side probe (all rows discarded, chi = 0 vacuous).

---

## ROUND 8 -- Theorem B: the meeting is machine-complete over the hunted habitat

Coordinator's round-7 verification first (for the record): ALL GREEN
under an independent run; the PART 2a witness hand-traced from first
principles (T = (babababab.a)^5.babababab, B = abababa, deletion
spans at 1, 9, 17, 25, 33, 41, 49, spacing 8, residuals {0,8},{6},
{4},{2},{0,8}, chain 6>4>2>0); the Phase Bound's proof structure
checked line by line (the mult-1 hypothesis used exactly once).

### 8.1 PART 1 -- the direct adversarial hunt (no counterexample)

E = [eps/P(w)].[R(w)/sigma]X over the CONCRETE injective-R family
(R in {X, [eps/c]X for 10 constants, init, tail}: all LDS(prov_A)=1,
the hardest case for the base-case bound 2*1+1=3) x 25 needle
constructions P (tail^d, init^2, cat-phase shifts) x 4 sigmas x 331
inputs (all |w|<=7 + 6 periodic families + 60 random |w|<=10):
  355,928 pipelines evaluated, 70,212 at mult 1:
  LDS histogram {0: 9,108; 1: 59,785; 2: 1,319}
  MAX LDS AT MULT 1 = 2.
The max instance re-verified end-to-end against the reference
denotation: E = [eps/tail^3 X].[X/ab]X on w = baabaaba:
prov (0,1,5,2,7), LDS 2, mult 1, content == L.den.  In this entire
space the bound 3 is never even reached: at mult 1 the number of
surviving copies never exceeds 2.

### 8.2 PART 2 -- the lift-the-structures hunt (the supply pigeonhole, machine-checked)

Every chain-rich free-text structure (the aligned alternating family
m in 5..13 plus 60,000 B^inf-structured randoms; n <= 14, m <= 12):
  60,180 structures; 147 with disjoint-chain >= 3; 48 pairwise-
  disjoint (the text-level mult-1 candidates, including the length-6
  chain); FEASIBLE EMBEDDINGS: 0; verified mult-1: 0.
The feasibility check is the realizability CSP in its most permissive
form: a NONDECREASING embedding p of A into w (repeats allowed at
non-surviving offsets -- their labels never reach the output), p
injective on the surviving offsets, p avoiding the surviving gap
positions, for one of six sigmas whose greedy site-scan recovers the
intended copy structure.  ALL 48 die.  The supply pigeonhole is now an
exhaustive machine-checked infeasibility over the habitat: no
text-level mult-1 chain lifts to a pipeline.

### 8.3 PART 3 -- the quantified periodicity (border-period lemma)

Exhaustively verified over ALL binary strings |x| <= 11:
  LEMMA (Border-Period): if x has t >= 2 borders and minimal period p,
  then p*(t-1) <= |x|-1, i.e. p <= (|x|-1)/(t-1).
Combined with Lemma Phase (|S| <= (1+|O|)(1+|J|)+1):
  |S| >= K  =>  max(|O|,|J|) >= sqrt(K)-1
            =>  A[:o_max] or A[-j_max:] has >= sqrt(K)-1 borders
            =>  that end of A has period <= (|A|-1)/(sqrt(K)-2).
THE MEETING, machine form: mult 1 + K realized phases => A is
|A|/sqrt(K)-periodic at one end (8.3) => the realizing w cannot embed
A without duplicating labels at the surviving offsets (8.2) => K is
bounded.  Over the hunted habitat the two ingredients meet; the
written proof for general (A, B, sigma) is what remains.

### 8.4 Round 9 (priority order)

(1) WRITE THE MEETING as a proof for the two-pass fragment: assume
    mult 1 and |S| >= K; by 8.3 A has period q <= |A|/sqrt(K) at one
    end; by periodicity the realized phases repeat every
    lcm-related cycle in the copy index; the mult-1 disjointness then
    forces |S| <= 2 + (#boundary irregularities) -- formalize the
    cycle/disjointness tension.  The two machine facts to lean on:
    max |S| = 2 at mult 1 (8.1) and 0/48 lifts (8.2).
(2) If the general proof resists: prove it for periodic-at-one-end A
    (which 8.3 says is the only case that matters), with the general
    case as a precise conjecture.
(3) The value recursion (unchanged from round 7's list).

### 8.5 Script index (round 8)

verify_round8_theoremB.py -- PART 1 direct hunt (355,928 pipelines,
    max LDS 2 at mult 1, instance verified vs L.den); PART 2
    lift-the-structures (60,180 structures, 48 candidates, 0
    feasible); PART 3 border-period lemma (exhaustive |x|<=11).

## 9. Round 9 — THEOREM B REFUTED (the supply half does not close; the cap does not exist)

**Charter.** (1) State the tension precisely (how phases cluster along the periodic
direction; why mult 1 caps the cluster). (2) The embedding side (CSP infeasibility;
parity pigeonhole → residue classes mod q). (3) If the general proof resists: prove
the two covering families, state the general case as a precise conjecture, say so
plainly.

**Outcome: the general case is not a conjecture — it is FALSE.** The extended hunt
found a fixed two-pass expression realizing unbounded LDS at mult exactly 1.

### 9.1 The refutation

For every k ≥ 2 (verified k = 5..16, content cross-checked against L.den on EVERY
row):

    E_k-independent  =  [ε/tail⁴X] · [tail(X)/'ab'] X
    w_k              =  ('bba')^k
    prov(w_k)        =  (0, 1, n−3, n−6, n−9, …, 3, n−2, n−1)     n = 3k
    mult             =  1   (exactly; every label distinct)
    LDS              =  k − 1   → ∞

k=8 dissection (w = bbabbabbabbabbabbabbabba, n = 24): σ = 'ab' sites at
2, 5, 8, 11, 14, 17, 20 (k−1 = 7 copies of A = tail(w)); B = tail⁴(w), |B| = 20;
the greedy [ε/B] scan matches at spacing 23 and emits exactly one 'b' per copy at
copy-offsets 20, 17, 14, 11, 8, 5, 2 (descending by 3) with labels 21, 18, 15, 12,
9, 6, 3; the leading gap atoms (labels 0, 1) and trailing gap atoms (labels 22, 23)
survive; output = 'b¹⁰a'.

### 9.2 The mechanism (why this evades every cap we had)

1. **Residue-class confinement.** The emission offsets descend by s = 3 = the
   period of w. The staircase lives entirely in the residue class 0 mod 3 —
   the 'b'-positions of w at 0, 3, 6, … — of which w supplies exactly k−1: one
   per copy, EXACTLY enough, never revisited. This is the residue-class
   generalization of the round-7 parity pigeonhole: for the alternating family
   (period 2, 1-char σ) the residue class was too small (the pigeonhole killed
   it); with period 3 and 2-char σ = 'ab' the class is exactly the right size.
2. **Interior gaps consumed.** The single-'b' gaps between copies sit at
   positions ≡ 0 mod 3 — the SAME residue class — but they are all consumed by
   the B-matches, so their labels never appear. No F-collision.
3. **Post-aligned end.** The text ends on the trailing gap 'ba' (labels n−2,
   n−1); the last emission is a gap atom, not a tail dump of copy atoms.
4. **Fresh boundary labels.** The leading 'bb' (labels 0, 1) and trailing 'ba'
   (labels n−2, n−1) lie outside the staircase's values.
5. **No wrap.** The descent 3k−3 → 3 is a single run; spacing vs unit is tuned
   so no offset is ever revisited (mult stays 1).

### 9.3 Why rounds 6–8 missed it (domain gap, on record)

- Round 8's w-families: ('bba')^k enters only at k ≤ 2 (|w| ≤ 7 exhaustive) —
  LDS = k−1 = 1, invisible; the 60 randoms of length ≤ 10 could hit k = 3 at
  LDS 2 — tied with, not above, the round-8 max.
- Round 9 added the period-3 families with ALL PHASES and j ≤ 8, plus 3-char
  σ: k = 8 gives LDS 7 — unmissable.
- Lesson (again): every negative search is only as good as its domain; the
  phase-variant sweep (not the pattern list) is what caught it.

### 9.4 The extended hunt (verify_round9_supply.py)

- Inputs: all period-2/3 families (10 patterns × j ≤ 8 + phase variants + all
  |w| ≤ 7 + 120 random ≤ 12); σ ∈ 8 values (incl. 3-char); R = 12-value injective
  family; P = 15 best needle constructions.
- 581,856 pipelines, 221,579 at mult 1; LDS histogram {0: 9635, 1: 210988,
  2: 941, 3: 11, 4: 1, 5: 1, 6: 1, 7: 1}; MAX = (7, ('tail', 'tail⁴', 'ab',
  'bbabbabbabbabbabbabbabba')) — the witness.
- Death-reason breakdown (PART 2): 0 of the random chain-rich structures lift;
  round 8's 147 all came from the aligned family — consistent (the aligned
  family is where supply and embedding conspire; the period-3 family is the
  one place they conspire successfully).
- Residue check (PART 3): 4,666 of 5,784 chain-rich structures have
  constant-descent chains — the staircase is the generic shape.

### 9.5 Consequences (honest ledger)

- **Conjecture B (mult 1 ⟹ LDS ≤ C(E)): REFUTED.** The bound cannot exist;
  LDS is unbounded at mult exactly 1, even for a FIXED two-pass expression.
- **Base-case conjecture (mult 1 ⟹ LDS ≤ 2·LDS(prov_A)+1): REFUTED.** Here
  LDS(A) = 1 (A = tail(w) is increasing) yet LDS = k−1 ≥ 4.
- **Theorem A (Phase Bound, round 7): STILL TRUE.** Every instance above
  satisfies it; but its constant is value-dependent: |S| ≈ k-1 copies with
  |O|, |J| ≈ k phases — the bound ((1+|O|)(1+|J|)+1)·LDS(prov_A)+1 grows with
  w. Theorem A is a true theorem about the STRUCTURE of mult-1 outputs (one
  surviving copy per realized phase; gap labels increasing), not a complexity
  bound.
- **The atom route via the mult-1 invariant is DEAD.** Conjecture A fell
  (round 6), Conjecture B and the base case fell (round 9). There is no
  (mult, LDS)-separating invariant: L realizes mult 1 with LDS ~ |w|/3.
- What could still separate rev: (i) Conjecture C (influence crossings
  ≤ c(E)·|w|; rev has χ = C(n,2) — length-preserving, so the length-discard
  rule does not vacate it; note the new family is length-changing, so C is
  vacuous on it); (ii) a NEW invariant class. Natural candidate identified
  this round: rev's prov is a descending BIJECTION (mult 1, |prov| = |w|,
  all labels present, LDS = |prov|). Probe (verify_round9_witness.py PART 2):
  over the round-7 exhaustive domain — the TEXT level, a strict superset of
  realizable pipelines, since prov_A is an arbitrary injective labeling —
  descending bijections exist ONLY for |w| ≤ 4 (318 hits, 110 essential
  families, all prov_A a leading triple-reversal, e.g. w = 'abb' needing
  A = 'aaa' with labels 2,1,0 — a constant carrying input labels, which
  constants do not carry). No |w| ≥ 5 admits one, even with that freedom.
  The Theorem-B witness is far from a bijection: |prov| = k+3 vs |w| = 3k
  (deletion-heavy). Sketch of the two-pass obstruction: a copy with ≥ 2
  surviving atoms has ascending labels, so a full descent keeps ≤ 1 atom per
  copy; bijection forces all atoms to survive, so no deletion — the two-pass
  fragment provably cannot be a descending bijection. The question moves to
  deeper pipelines.

### 9.6 Files

- `verify_round9_supply.py` — the extended hunt (PART 1: the refutation;
  PART 2: death breakdown; PART 3: residue check).
- `verify_round9_witness.py` — the witness family k = 5..16 with per-row
  den_ok, the mechanism dissection, and the descending-bijection probe.

## 10. Round 10 — the descending-bijection invariant I: the two-pass
## bound PROVED (Theorem 2, all shapes), the depth frontier mapped

Task (coordinator): close the gap in the two-pass DB obstruction — show no
two-pass expression's prov can be a descending bijection at full generality,
or find and characterize exactly where it can.

Answer in one paragraph. The two-pass question is settled as a theorem
in the strong form: any depth-2 DB realization satisfies
n <= beta + 2 rho + nu, where beta is the final pattern VALUE's length,
rho = #V of the innermost scrutinee, nu = #V of the final replacement —
proved for every shape, with no periodicity assumption, by a new
mechanism (the copy-identity transport) that never looks at prov_A, so
the old sketch's gap ("prov_A itself could be descending") is bypassed
entirely. Constant final pattern => n <= size(E) + 2 #V(E): finiteness
at depth 2. The only escaping configuration is a final pattern whose
value grows with w — and there the Pinch forces w constant on all but
O(rho) positions, leaving one delimited endgame (sigma-packing with
multi-match runs: partially proved, machine-clean on the domain). At
depth >= 3 the machine finds the first real DBs: pure three-pass chains
realize DB at n = 3 (witnesses exhibited and dissected below, sitting
exactly at the theorem's boundary n = beta = 3), nothing realizes DB at
n = 4 up to S-depth 4 on the swept domain. The finiteness program (for
fixed E, {w : DB(w)} finite => rev not in L) is now the explicit target.
(Round-12 scope note: the implication is unbounded-alphabet — Lemma
DB-forcing, 12.1; over fixed finite alphabets no prov-level condition
is necessary at all — Theorem laundering, 12.2.)

### 10.1 Definitions

- **DB (descending bijection)**: E realizes DB(w) iff prov([[E]]w) =
  (n-1, n-2, ..., 0), n = |w|. Equivalently mult 1, |prov| = n, all labels
  present, LDS = n. rev realizes DB on every input with all-distinct
  characters, so DB is a necessary condition for rev-computability
  (round-12 note: as a condition on E this needs the forcing lemma 12.1
  — the input's distinct characters must also avoid E's constants, so
  the family exists at every length only over unbounded alphabets; over
  fixed alphabets 12.2 shows no prov-level condition is necessary).
- **FDI**: prov strictly decreasing and injective (DB minus surjectivity).
- **S-depth** of E: number of S-nodes; C-nodes do not count.
- **pf-value (pass-free)**: denotation of an S-free expression: u0 w u1 w
  ... u_rho with rho = #V-leaves; prov = R^rho, R = (0,1,...,n-1). The only
  labeled pf-values are full runs.
- **Instance**: a maximal block of labeled atoms of t that came from one
  copy of w (an inserted Y-run) or one surviving slice of an F1-run.
  Within an instance, labels ascend with T-order and equal w-offsets.
- **Pick**: an atom of t that survives the final pass carrying a label.
  DB means: the picks, in T-order, carry labels n-1, n-2, ..., 0; so pick
  k sits at w-offset o_k = n-1-k. Every pick is labeled, hence in an
  instance; a **copy-pick** lies in an inserted full copy, a
  **slice-pick** in an F1-run survivor (head/gap/tail).

### 10.2 T1 (Last-Pass Structure) — PROVED

E = (S R P F), t = [[F]]w, y = [[R]]w, X = [[P]]w, c = #sites of X in t.

- (a) c >= 2 and y labeled => mult(prov(out)) >= 2. (Each site inserts a
  full copy of y; any label of y then occurs >= 2 times.)
- (b) c = 1 => out = t^- y t^+ textually, hence prov(out) =
  prov(t^-)prov(y)prov(t^+); if prov(out) is FDI then each block is FDI
  and the blocks are chained (last label of t^- > first of y, etc.), and
  the three label sets are disjoint.
- (c) c = 0 => out = t: delete the vacuous pass (S-depth drops).

Machine: verify_round10_db.py PART 1 (prior session), 41,850 simulated
last passes, 0 violations of (a).

### 10.3 Theorem 1 (depth <= 1) — PROVED

**If S-depth(E) <= 1, n >= 2, and prov([[E]]w) is FDI, then |prov| <=
#V(E). Hence DB(w) implies n <= #V(E).**

Proof sketch (hand-checkable). By T1(c) reduce to c >= 1. Case c = 1 with
y labeled: y is pf, so prov(y) = R^rho; FDI forces rho <= 1 (R^2 is not
decreasing for n >= 2); the block chain then forces t^-, t^+ label-free
(their labels would have to exceed/fall below all of R), so prov(out) = R:
increasing, not FDI. So either y is label-free or c >= 2 with y label-free
(by (a)). Then out's labeled atoms are a subsequence of t's, and t's
labeled atoms are rho(F) copies of R interleaved with the y-blocks: an FDI
subsequence takes at most one atom per run (labels ascend within a run)
and at most one y-block atom total if that block is labeled, giving
|prov| <= rho(F) + 1 <= #V(F) + 1; the C-node version composes blocks with
per-leaf budgets, giving |prov| <= #V(E).

(Verified: mode 1 below — DB only at n = 2 via C(1,1); max FDI 2.)

### 10.4 The depth-2 core: Pick, Slice, Sandwich, Transport — PROVED

Setting: the final pass is [R/X]t with t = [[F2]]w, S-depth(F2) = 1.
Write beta = |X|, and let F1 be the innermost (pass-free) scrutinee with
rho = #V(F1) runs. The inner pass makes t = S0 Y S1 Y ... Y Sm: the
slices S_j (surviving pieces of F1's runs, head and tail included) and m
inserted copies of Y = v0 w v1 ... (sigma' runs each; all of Y's runs
are full copies of w). A survivor carrying a label is a PICK. The three
structural lemmas hold at the FDI level (they only use that the output's
prov is strictly decreasing and injective):

**Lemma Pick (PROVED).** At most one pick per instance (one inserted
copy, or one surviving slice). Within an instance, labels ascend with
T-order; two picks in one instance would put an ascending pair into a
strictly decreasing prov.

**Lemma Slice (PROVED — the key new tool).** At most one pick per
ORIGINAL F1-run, so the slice-picks number at most rho = #V(F1), an
expression constant. Proof: the surviving pieces of one run appear in
T in the same left-to-right order as in the run, so their w-offset
ranges ascend; two picks among them would need descending offsets
(label order) but get ascending (text order). No periodicity
assumption: this is uniform over all regimes, including the
self-overlapping w where round 9's staircase lives.

**Lemma Sandwich (PROVED).** Let p be a pick whose T-predecessor atom
is labeled and lies in the same instance (same copy or same run-piece).
That predecessor is not a pick (Pick lemma), hence is covered by the
final pass (the inner pass is already applied; slice and copy atoms
alike can only be covered now); the covering match cannot contain p,
and covering the predecessor forces it to end exactly at p. Hence a
match of X ends at p, so X equals the beta atoms preceding p: if the
window lies inside the instance, X = w[o-beta : o]. In particular
X's last char = the predecessor's char.

(Verified: verify_round10_lemmas.py v2. The v1 check had a defect the
coordinator caught: the Sandwich window was read from the OUTPUT and the
out-adjacency precondition never fired — VACUOUS. v2 tracks each output
atom's t-index through the final pass and checks everything in
t-coordinates: Pick per instance (one w-run of an inserted copy, or one
surviving slice), per-copy Pick, Slice per original run, the t-based
Sandwich, the MIRROR sandwich (survivor at q whose t-successor t[q+1] is
labeled, same instance, not itself a survivor => t[q+1:q+1+beta] spells
the pattern), and TRANSPORT pairs (no two surviving copy-picks with the
text-earlier at offset = later's offset + beta). Same domain, same 59,300
FDI depth-2 outputs: sandwich firings 22,938 (22,957 under the per-copy
convention — the coordinator's number), mirror 21,498 (21,514), 0
transport pairs, 0 violations. Log round10_lemmas.log, 10.7 s.)

**Lemma Transport (PROVED — the round's core; statement widened in
round 11).** Suppose E realizes DB(w) and the final replacement is
LABEL-FREE (any label-free replacement, not only epsilon: the proof
never uses that inserted text is empty, only that it carries no labels —
the survivors are then exactly the atoms not covered by a match, as in
the epsilon case). Then pick k sits at w-offset o_k = n-1-k, and: if
picks k and k-beta are both copy-picks, pick k cannot exist. Proof:
o_{k-beta} = o_k + beta, so pick k-beta's sandwich window is its
instance's offsets [o_k, o_k + beta), inside the run since o_k + beta <=
n-1. By Sandwich, X = w[o_k : o_k + beta]. But pick k sits in a full
copy at offset o_k, so the text at [P_k, P_k + beta) is exactly
w[o_k : o_k + beta] = X. The greedy scan visits every position not
inside a match; P_k is a pick, hence not inside a match, hence visited —
and at that visit it sees X and matches. Contradiction. (Round 11: the
label-free WLOG is now fully justified at depth 2 — a labeled final
replacement with c >= 2 dies by T1(a), with c = 1 by Replacement
Elimination, 11.2 below; this also retroactively closes the justification
gap in round 10's hunt, which simulated only label-free final
replacements.)

**Theorem 2 (depth 2, unconditional — all shapes).** If S-depth(E) <= 2
and E realizes DB(w), n >= 2, then with beta = the length of the final
pass's pattern VALUE, rho = #V(F1), and nu = #V of the final pass's
replacement expression:

  n <= beta + 2 rho + nu.

Proof by cases. (i) Final replacement label-free (WLOG epsilon; forced
whenever the pattern has c >= 2 sites by T1(a)): the picks are the
survivors; copy-picks <= beta + G by Transport (at most beta small-k
picks, and at most one survivor k per slice-pick at k-beta), and
slice-picks G <= rho by Slice; n = copy + slice <= beta + 2 rho.
(ii) Final replacement labeled with c = 1 site: prov(out) =
prov(t^-) prov(y) prov(t^+), each block FDI and the blocks chained
(T1(b)). ROUND-11 REPAIR of the round-10 gap: the round-10 derivation
claimed t^- and t^+ "contain no full copies, only run-pieces: <= rho
picks each (Slice)" — but in chain2 the text t contains inserted COPIES,
and a copy cut by the site leaves pieces that are not slices of any
F1-run, so Slice does not bound them; the gap is real. It closes three
ways. (a) In chain2 and deepP2 the final replacement is pass-free, so
prov(y) = R^nu with nu = #V >= 1 — never FDI for n >= 2 (nu = 1 gives
the increasing (0,...,n-1); nu >= 2 repeats a label), so T1(b) kills
the whole case: no FDI output exists (Lemma Replacement Elimination,
11.2; machine: verify_round11.py part 1, 6,831,200 sims, 0
counterexamples). (b) In deepR2 the scrutinee F1 is pass-free, so t is a
pass-free value with NO copies at all and the original argument is
valid as written: t^- and t^+ are run-pieces only, <= rho picks each
(Slice); the y-block is an FDI prov of a depth-1 expression, so
|prov(y)| <= #V <= nu (Theorem 1); n <= 2 rho + nu. (c) Even without
(a), a counting repair also closes chain2: a copy surviving fully
outside the site would put an ascending pair into an FDI block, so every
copy intersects the site; each copy leaves at most one pick (its pieces
sit in text order = ascending offsets), and since copies are disjoint
intervals of length >= n while the site window has length beta, at most
floor(beta/n) copies fit inside it plus at most 2 straddle its ends, so
copy-picks <= nu(beta/n + 2), slice-picks <= rho, y-block <= nu:
n <= rho + nu + 2 nu beta/n + 2 nu — still a bound of the stated shape.
With (a) the case is simply impossible in chain2/deepP2, and (b) proves
n <= 2 rho + nu in deepR2, so the corollaries below stand.
(iii) c = 0: vacuous, reduce depth. (iv) C-nodes:
compose the branch bounds. (v) Pass-free inner replacement (Y
label-free): prov(out) is a subsequence of the pass-free prov R^rho, so
n <= rho outright.

**Corollaries (PROVED).** (a) If the final pattern is a CONSTANT, then
n <= size(E) + 2 #V(E): for every fixed depth-<=2 expression with
constant final pattern, {w : DB(w)} is finite. (b) Pass-free inner
replacement: n <= #V(F1). (c) A computed final pattern of length < n -
2 rho - nu is impossible: the final pattern's value must be nearly as
long as w whenever a depth-2 DB exists at large n — it must essentially
contain w.

### 10.5 The residual regime and the Pinch

The only escaping configuration at depth 2 is beta >= n - 2 rho - nu:
the final pattern's value grows with w (a pass-free pattern containing
w, or a computed one). There the bound is vacuous, but the structure is
pinned:

**Lemma Pinch (PROVED, DB level; boundary clause corrected in round
11).** X's last char = w[o_k - 1] for every copy-pick k with o_k >= 1
(Sandwich: the in-copy predecessor is labeled and non-pick). Copy-picks
number >= n - rho - 1, so w is constant, with value X[-1], on all but
<= rho + 1 positions of [0, n-2]. Symmetrically X's first char =
w[o_k + 1] for copy-picks with o_k <= n-2, so w is constant with value
X[0] on all but <= rho + 2 positions of [1, n-1]. For n >= 2 rho + 6
the two constants coincide and w differs from a single letter sigma on
at most 2 rho + 2 positions. ROUND-11 CORRECTION: the round-10 text
ended with "the surviving deviations sit at instance boundaries — the
picks that are fragment-initial", which was never proved (instance
boundaries are text-space, deviations are offset-space) and is CUT.
The proved replacement is sharper: the map k -> o_k - 1 is a bijection
from picks k <= n-2 to [0, n-2] (DB offsets are n-1-k), so every
deviation at j in [0, n-2] has j = o_k - 1 for a pick k that is NOT a
copy-pick — a slice-pick; symmetrically every deviation in [1, n-1]
sits at o_k + 1 for a slice-pick. So the deviation set is contained in
{0, n-1} U {o_k - 1 : slice-picks} U {o_k + 1 : slice-picks}: every
deviation is at distance exactly 1 from a slice-pick's offset, or at a
string endpoint — at most 2 rho + 2 positions, all within O(1) of the
<= rho slice offsets.

What remains open in this regime is the packing endgame: with w nearly
constant and X = (nearly) sigma^beta, the final pass's matches tile the
runs; the single-match-per-run configuration confines survivors to
O(|E|) positions at run ends (proved by hand this round, in-session),
but the multi-match configuration (greedy chains of X-matches inside
one sigma-run) is only hand-argued. The machine verdict covers it on
the domain: no depth-2 DB at any n >= 2 (10.6 below).

Round-9 consistency (on record): the staircase witness
[eps/tail^4 X].[tail(X)/ab]X on w = (bba)^k has beta = |B| = n - 4 and
11 survivors at n = 24 — NOT a bijection (11 atoms vs n = 24), so
Theorem 2 does not apply to it; and its prov begins (0, 1, ...) and
ends (..., n-2, n-1) with ascending pairs, so it is not even FDI. Its
survivors are exactly one phase class of the period-3 word (labels
n-3, n-6, ..., 3: the offsets > n - beta = 4 in the class 0 mod 3)
plus boundary atoms — precisely the phase structure the Pinch predicts
for the residual regime, with rho = 1 (one run) and the phase class
supplying the staircase. The round-9 family and Round 10's theory are
mutually consistent: the witness shows the residual regime is where
disorder at mult 1 lives; the theorem shows that regime cannot close
the bijection either, on the machine domain and in the proved cases.


### 10.6 Machine verdicts (round10b_db.c, all runs < 60 s)

C program (round10b_db.c, compiled as ./round10b_db): exhaustive-in-shape
simulation of every pipeline shape at each S-depth over a fixed
pass-free library (eps; 14 constants a..bbb; w; a.w; w.a; b.w; w.b; a.w.b;
b.w.a; ab.w; w.ab; w.w), with T1-justified restrictions (outer
replacement label-free; deep replacement pools filtered to label-free or
FDI provs). DB requires n >= 2 (n = 1 is degenerate). Logs:
round10_mode1.log .. round10_mode4.log.

- **Mode 1 (S-depth <= 1, all shapes incl. C(1,1))**: 162 inputs, 9,950,550
  sims, 0 undef. Max FDI 2. DB: 38,442 realizations, ALL shape C(1,1),
  ALL n = 2. No S-node realizes DB at any n >= 2. Theorem 1 confirmed.
- **Mode 2 (S-depth 2: chain2, deepR2, deepP2, C(2), C(2,pf), C(pf,2))**:
  379 inputs (all |w| <= 7 + periodic families to 24 + 80 randoms
  |w| 6-20), 772,939,671 sims, 9,475 undef. Max FDI 3 (chain2, w =
  abababa). DB: 38,442, all C(2) at n = 2 — i.e. ZERO new DB beyond
  depth 1 on this domain. ROUND-11 CORRECTION OF THE RECORD: the round-10
  gloss "no chain/deepR/deepP DB at any n >= 2" was a statement about the
  DOMAIN, not the shape: the mode-2 pattern pool (pass-free values over
  {constants, w, a.w, w.a, b.w, w.b, a.w.b, b.w.a, ab.w, w.ab, w.w})
  contains no final pattern of the form w.b.w, b.w.a, or w.a.w, and
  round 11's targeted hunt (11.6) found FOUR chain2 DB realizations at
  n = 2 with exactly such patterns (e.g. w = aa,
  E = [eps/(w.b.w)].[(ab.w.ba)/b](b.w.a.w.b), prov = (1,0)), all
  confirmed by prov.py. The round-9 domain-gap lesson again: absence on a
  domain is not absence. The corrected statement: no depth-2 DB at any
  n >= 3 anywhere (mode 2 here, round-11 hunt in 11.6) — consistent with
  Theorem 2, the partial proof of 10.5, and now Theorem 3 (11.4), whose
  bound n <= C(E) contains n = 2 but excludes unbounded n.
- **Mode 3 (S-depth 3: chain3, deepR3, Ctarget3, C(3,1))**: 130 inputs
  (all |w| <= 5 + families to 18 + 30 randoms), 389,533,280 sims. Max FDI
  3. DB: 43,634 = 38,442 C(2) n=2 + 5,123 C(3,1) n=2 + 38 chain3 n=2 +
  **29 C(3,1) n=3 (w = aba)** + **2 chain3 n=3 (w = abb, w = bab)**.
  THE FIRST PURE-CHAIN DBs: see 10.7.
- **Mode 4 (S-depth 4: chain4, deepR4 on depth-3 pools)**: 136 inputs
  (all |w| <= 4 + families to 12 + 10 randoms), 537,476,912 sims. Max FDI
  3. DB: 38,875 = 38,442 C(2) n=2 + 351 chain4 n=2 + 24 deepR4 n=2 +
  **54 chain4 n=3 + 4 deepR4 n=3**. **No n = 4 anywhere.**

Semantics cross-check: 16,800 random 3-pass pipelines re-evaluated with
prov.py (independent evaluator) — DB only at the degenerate n = 1,
consistent with the C checker's n >= 2 convention.

### 10.7 The n = 3 depth-3 chain witnesses (exhibited, dissected)

**w = bab**: E = [eps/'aba'] . [eps/'abbab'] . [w/'b'](a.w.b). Atom-level
(P = prov.py conventions, k = constant):
  t1 = [a|k][b|0][a|1][b|2] [a|1] [b|0][a|1][b|2] [b|0][a|1][b|2]
       (a . w . a . w . w: the 'b'-sites of a.w.b each get a copy of w)
  t2 = [a|k][b|0][a|1][b|2][a|1][b|0]      ('abbab' deleted at [6,11))
  t3 = [b|2][a|1][b|0]                     ('aba' deleted at [0,3))
  prov(t3) = (2,1,0) = DB.
**w = abb**: E = [eps/'bbb'] . [eps/'bab'] . [ab.w/'a'](w.ab).
  t1 = y1 . b|1 . b|2 . y1 . b|k  with y1 = [a|k][b|k][a|0][b|1][b|2]
  t2 = [a|k][b|2][b|1][a|0][b|1][b|2][b|k]  ('bab' deleted at [1,4),[6,9))
  t3 = [a|k][b|2][b|1][a|0]                 ('bbb' deleted at [4,7))
  prov(t3) = (2,1,0) = DB.

Both sit exactly ON the theory's boundary: the final pattern has
beta = 3 = n, so every pick has k < beta - 1 + 1 and the Transport kill is
vacuous; both use exactly one slice-pick (G = 1, so n <= beta - 1 + 2G
reads 3 <= 3 + 2, slack 2); both copy-picks are at descending offsets
2, 0 with the slice-pick taking offset 1 (Pick lemma: one per instance).
Mechanism: pass 1 duplicates w (m = 3 instances), passes 2-3 delete
constant patterns that carve out a staircase whose surviving atoms read
one offset per instance in descending order. The DB budget is exactly
"one descent step per instance", and beta must be >= n to keep the kill
vacuous — the witnesses are extremal in both directions.

### 10.8 The budget conjecture and the program

**Conjecture (budget).** A pure chain of S-depth d realizes DB only for
n <= d + 1 (equivalently: each pass buys at most one descent step);
C-compositions realize DB only for n <= #parts + 1. Machine status: n = 3
first appears at depth 3 (chains) and depth 1 (C, trivially, n = 2);
nothing at n = 4 up to depth 4 on the swept domains; the depth-1 C-bound
n <= #parts + 1 is Theorem 1.

**Finiteness program.** If for every fixed E the set {w : E realizes
DB(w)} has bounded |w|, then rev is not L-reachable. Round 10's theorems
give: depth <= 1 unconditionally (Theorem 1); depth 2 for overlap-free w
and constant final patterns (Theorem 2); depth 2 residual = self-overlap
regime (10.5); depth >= 3 open, with the budget conjecture as the
candidate mechanism. The known witnesses all satisfy n <= d + 1 with
equality requiring beta >= n (patterns as long as the input at the LAST
pass), suggesting the right induction is on (depth, pattern length)
together.

### 10.9 Honest ledger for Round 10 (as corrected in Round 11)

- PROVED: T1; Theorem 1 (depth <= 1: DB => n <= #V(E)); Pick; Slice;
  Sandwich; Transport (round 11: statement widened to any label-free
  replacement — the proof never used epsilon); Theorem 2 (depth 2, ALL
  shapes, no periodicity assumption: n <= beta + 2 rho + nu; constant
  final pattern => n <= size(E) + 2 #V(E), finiteness; pass-free inner
  replacement => n <= rho; single labeled final site => n <= 2 rho +
  nu — round 11: case (ii) repaired, impossible in chain2/deepP2 by
  Replacement Elimination, valid as written in deepR2 where t has no
  copies); Pinch (w constant on all but <= 2 rho + 2 positions in the
  residual regime — round 11: boundary clause cut and replaced by the
  proved "deviations at distance exactly 1 from slice-pick offsets or
  string endpoints"); the single-match sigma-packing kill (superseded:
  round 11's Theorem 3 closes the multi-match endgame too); round-9
  consistency (the staircase witness is not FDI, its survivors are one
  phase class — exactly the residual regime's predicted structure, and
  it does not close the bijection; it lives at depth >= 3 with beta <
  n, outside Theorem 3's hypotheses on both counts).
- VERIFIED ON STATED DOMAINS: Pick/Slice/Sandwich/Mirror/Transport-
  pairs on 59,300 FDI depth-2 outputs (70 inputs,
  verify_round10_lemmas.py v2 with t-index tracking, 0 violations);
  no depth-2 DB at any n >= 3 (round-10 mode 2: 379 inputs, 773M sims;
  round-11 hunt: 232 residual-regime inputs, 22.3M sims — but chain2 DB
  at n = 2 DOES exist, 4 witnesses, see 11.6); depth-3 chain DB at
  n = 3 (2 chain witnesses + 29 C(3,1)); no n = 4 up to depth 4
  (136 inputs, 537M sims); T1 part (a) (41,850 sims); semantics
  cross-check (16,800 random 3-pass pipelines via prov.py).
- CONJECTURED: the budget n <= d + 1 for chains.
- OPEN (round 10): the multi-match sigma-packing endgame of the
  residual regime — CLOSED in round 11 (Theorem 3, 11.4); everything at
  depth >= 3; the induction combining S-depth and pattern length; the
  FDI-level analogue of Theorem 3 (see 11.8).

### 10.10 Files

- `round10b_db.c` / `./round10b_db` — the four-mode DB/FDI hunter (C).
- `round10_mode1.log` .. `round10_mode4.log` — full DB-hit listings and
  summary stats for each mode (each run < 60 s).
- `verify_round10_db.py` — prior session's Python parts 1-2 (T1 spot
  check, depth-<=1 verdict); part 3 superseded by the C program.
- `verify_round10_lemmas.py` — v2 (round 11): Pick/Slice/Sandwich/
  Mirror/Transport spot-check on 59,300 FDI depth-2 outputs with
  t-index tracking (the v1 Sandwich check was vacuous); result in
  `round10_lemmas.log` (0 violations, 10.7 s).
- `descending_bijection.tex` — the paper-style fragment (Round 10).
- `round10_hunt.c` — superseded first C hunt (timed out on oversized
  domains); kept as record.

## 11. Round 11 — the descending-bijection invariant II: DEPTH 2 CLOSED
## (Theorem 3: finiteness unconditional, residual endgame included)

Task (coordinator): apply the five corrections to Round 10 (done in
sec 10 above: Theorem 2 case (ii) repaired, the "single labeled final
site" corollary re-derived, Pinch's boundary clause cut and replaced by
the proved statement, the Sandwich checker de-vacuumed and extended
with mirror + transport checks, Transport widened to any label-free
replacement); then close the residual endgame at depth 2 — the escaping
regime beta >= n - 2 rho - nu where the final pattern's value contains
w, left open by Round 10's partially-proved sigma-packing argument —
with success = depth 2 unconditional: {w : DB(w)} finite for EVERY
depth-<=2 expression, any final pattern.

Answer in one paragraph. Depth 2 is closed unconditionally, by a proof,
not a sweep: Theorem 3 below gives, for every S-depth-<=2 expression
E, an explicit constant C(E) with |w| <= C(E) whenever E realizes
DB(w). The mechanism is new: two "frame" identities pin the final
pattern's value against w at every interior copy-pick; two picks at
adjacent offsets force w constant on both sides of the pair (a
"break"), and two breaks force w = tau^n outright; with w uniform, the
inner pattern must be uniform (else the copy count collapses), the
final pattern must start and end with uniform runs and have at least
two of them (three one-line kills: a non-uniform edge contradicts a
frame; an all-uniform pattern makes the greedy scan eat the pick
itself); each surviving pick then sits in a maximal uniform run of t of
ONE exact length (B-rigidity, machine-checked), which caps the number of
w-copies a pick's run can contain; and the distances from run starts to
picks are distinct integers in a window shorter than n, so their
residues mod n are distinct — a quadratic lower bound on their sum that
the capped run structure can only meet linearly. n is bounded by an
explicit constant of E. Along the way the round found the first n = 2
witnesses at depth 2 (four of them, dissected below) — Round 10's mode
2 had missed them because its pattern pool lacked w.b.w-type final
patterns — and they sit exactly where the theory says the last slack
is: n = 2 makes the interior-offset machinery vacuous. No n >= 3
witness exists on any domain swept, and now none can exist at all.

### 11.1 Setup and notation

Chain2 shape: E = [R2/P2].[R1/P1].F1 with everything pass-free. Write
X = [[P2]]w (final pattern, beta = |X|, pi = #V(P2) = number of w-copies
inside X, c_X = total constant length of P2), Y = [[R1]]w (inner
replacement, nu = #V(Y), c_Y = its total constant length), Z = [[P1]]w
(inner pattern, beta' = |Z|), f = [[F1]]w (rho = #V(F1), c_F = its
total constant length, so |f| = rho n + c_F), t = [Y/Z]f, m = number of
inner sites = number of inserted copies of Y's value in t. Instances,
picks, copy-/slice-picks, offsets as in 10.1. A prov is a BLOCK of
length k if it is (j+k-1, j+k-2, ..., j) for some j: consecutive
labels, descending. DB(w) is the full block (n-1, ..., 0) (k = n);
FDI is assumed throughout, so pick r (r = 0, 1, ... in text order)
carries offset o_r, the o_r are distinct and descending, and for a
block they are consecutive: o_r = j+k-1-r. A pick is INTERIOR if
1 <= o <= n-2 (its in-copy predecessor at offset o-1 and successor at
offset o+1 exist and share its instance, so Sandwich applies on both
sides). O denotes the set of offsets of interior copy-picks.

### 11.2 Lemma Replacement Elimination (the nu = 0 lemma) — PROVED

In chain2 (and deepP2), no FDI output with n >= 2 has a LABELED final
replacement. Proof: the final replacement is pass-free, so its value y
has prov(y) = R^nu, R = (0, ..., n-1), nu >= 1. If the final pass has
c >= 2 sites, T1(a) gives mult >= 2 — not FDI. If c = 1, T1(b) makes
prov(y) a contiguous block of the FDI prov(out), hence FDI itself; but
R^1 is increasing and R^nu for nu >= 2 repeats label 0 — never FDI
for n >= 2. (c = 0 is vacuous.) So the final replacement of any FDI
chain2 output is label-free, and WLOG epsilon (a label-free replacement
changes only the unlabeled text, not which atoms survive).

Consequences: (i) Theorem 2 case (ii) is impossible in chain2/deepP2 —
the 10.4 repair. (ii) Round 10's hunt restriction "outer replacement
label-free" is now fully justified, not just for c >= 2. Machine:
verify_round11.py part 1 — 6,831,200 simulations of the chain
[yf/xf].[Y/xp].F over 33 inputs (all |w| <= 4 plus periodic families),
final replacement drawn from the LABELED pf library: 0 FDI outputs
with c = 1 and labeled replacement; the T1(a) control (c >= 2,
labeled) also 0; 0 DB hits anywhere. THE CONTROL IS LIVE (round-12
repair 3): the original part-1 control counted label-free c = 1
outputs while drawing yf ONLY from the labeled sub-library — dead
code, structurally 0. Mode 1c redraws the final replacement from the
FULL pass-free library (25 forms vs 10 labeled) on a reduced domain
(all |w| <= 3 plus abab/abba, 16,147,500 sims): 673,290 FDI outputs
with c = 1 and label-free replacement, and STILL 0 with c = 1 and a
labeled one — the 0 is a property of labeledness, not of the domain
starving the c = 1 channel.

### 11.3 Lemmas Frame (alpha)/(beta) and Break — PROVED (the core new tools)

**Lemma Frame.** Let E be a chain2 with beta >= n (so the final
pattern's value is at least as long as w), prov FDI, and let p be an
interior copy-pick at t-position q, w-offset o. Then
  (alpha)  X[-o:]  =  w[:o]      (the final pattern ends with w's prefix)
  (beta)   X[:n-1-o] = w[o+1:]   (it begins with w's suffix)
Proof. The in-copy predecessor (offset o-1, position q-1) is labeled,
same instance, and not a pick (Pick), so it is covered by the final
pass; the covering match cannot contain q, so it ends exactly at q:
it is [q-beta, q) and spells X. Since beta >= n > o, the copy's
offsets 0..o-1 lie in the window, at its right end: X's last o chars
are w[0..o-1]. Symmetrically the successor (offset o+1, position q+1)
is covered by a match not containing q, which must start at q+1:
[q+1, q+1+beta), spelling X; the copy's offsets o+1..n-1 lie at its
left end: X's first n-1-o chars are w[o+1..n-1]. (Both matches have
length exactly beta; both windows fit because beta >= n.)

**Lemma Break.** If interior copy-picks exist at offsets o AND o+1,
then w is constant on [0, o] and on [o+1, n-1]. If interior
copy-picks exist at two pairs o, o+1 and o', o'+1 with o != o', then
w = tau^n for a single letter tau. Proof. Alpha at o and at o+1 reads
the same X: w[:o] = X[-o:] = the last o chars of X[-(o+1):] =
the last o chars of w[:o+1] = w[1:o+1], so w[i] = w[i+1] on
0 <= i <= o-1. Beta at o and o+1: w[o+2:] = X[:n-2-o] = the first
n-2-o chars of X[:n-1-o] = the first n-2-o chars of w[o+1:], so
w[i] = w[i+1] on o+1 <= i <= n-2. Two pairs, say o < o': the first
break makes w constant on [o+1, n-1] (value w[o+1]) and the second on
[0, o'] (value w[0]); the intervals overlap (o' >= o+1), so
w[0] = w[o+1] and w is constant on [0, n-1].

**Dichotomy (Block form).** If prov is a block of length k, then
either k <= 2 rho + 4, or w = tau^n. Proof. The block's k offsets are
consecutive; at least k-2 of them are interior (only the extremes can
be 0 or n-1), they form an interval, and at most rho of the picks are
slice-picks (Slice), so O misses at most rho values of an interval of
length >= k-2, giving at least (k-3) - 2 rho adjacent pairs; two of
them are at distinct positions once k >= 2 rho + 5, and Break forces
w = tau^n.

### 11.4 Theorem 3 (depth-2 finiteness, unconditional) — PROVED

**Theorem 3.** For every expression E with S-depth(E) <= 2 there is a
constant C(E), explicitly computable from E's pass-free skeleton, such
that whenever |w| = n >= 2 and E realizes DB(w), n <= C(E). In
particular {w : E realizes DB(w)} is finite for every depth-<=2 E.
The rev payoff is UNBOUNDED-alphabet only: by the DB-forcing lemma
(12.1), over an unbounded alphabet a rev-computing E must realize DB
on arbitrarily long distinct-character inputs avoiding E's constants
— Theorem 3 excludes rev at depth <= 2 for every such E, constants
included. Over a FIXED finite alphabet finiteness gives no such
exclusion, and none is possible at the prov level at all: the
laundering theorem (12.2) shows every rev-correct E over Sigma can be
rewritten with prov == () on all of Sigma*.

The proof runs on the stronger statement (Lemma S): if S-depth(E) <= 2
and prov(E, w) is a BLOCK of length k (DB is the case k = n), then
k <= C(E). Structural induction on E.

**(0) Reductions (all cases except the residual corner are bounded by
constants of E).** Let E be a single S-top [R/P]F with P, R pass-free
and F of S-depth 1. Write F = g1 . [Y/Z]f . g2 with g1, g2 pass-free
(chain2 is g1 = g2 = eps; deep shapes below). The final pass scans
  t = g1(w) . [Y/Z]f(w) . g2(w)
and NOTE: the inner pass scans only f's value — "chain2 after
flattening" ([Y/Z](g1 f g2)) is NOT the same shape, and the corner
analysis below treats the junctions explicitly (round-12 repair 2).
Let rho = #V(F) (total w-copies in g1, f, g2 evaluated at w) and c_F =
total constant characters of g1, f, g2. By T1(c) assume the final pass
has c >= 1 sites (else out = t has S-depth 1 and Theorem 1's block
form gives k <= #V <= #V(E)). By Replacement Elimination the final
replacement is label-free, WLOG epsilon. If Y is label-free, prov(out)
is a subsequence of the pass-free prov R^rho, so k <= rho. If the
final pattern is a CONSTANT (pi = 0), Theorem 2 gives k <= beta + 2
rho with beta constant (Theorem 2's block form is the same proof:
Transport's arithmetic o_{k-beta} = o_k + beta only needs consecutive
offsets). If the inner pattern CONTAINS w (pi_Z >= 1), its sites lie in
f's value, have length beta' >= n and are disjoint there (f has length
rho_f n + c_f with rho_f = #V(f) <= rho), so m <= rho_f + 1 (for n >=
c_f; n < c_f is already bounded by the constant c_f) and k <= m nu +
rho <= (rho+1) nu + rho; if rho = 0 then F has no copies at all, f is
a constant and m <= c_F, k <= c_F nu. So the only unbounded corner is:
**[eps/X](g1.[Y/Z]f.g2) with any pass-free flanks (chain2 = empty
flanks), Y labeled (nu >= 1), Z constant (beta' >= 1), final pattern
containing w (pi >= 1, hence beta >= n).** By the Dichotomy, either
k <= 2 rho + 4, or w = tau^n. Assume w = tau^n and continue.

**(1) The inner pattern is uniform.** If Z contains a letter
c != tau, every site of Z in f's value places c at an f-position
carrying c; w contributes only tau's, so all such positions are in
f's constants: m <= c_F, k <= c_F nu + rho. So Z = tau^{beta'}: the
inner pass tiles each maximal tau-run of f's value from its left end
in chunks of beta', replacing each chunk by a copy of Y's value and
leaving r = L mod beta' < beta' trailing taus; f's non-tau characters
all survive (Z matches only taus) and separate the runs of f, so each
maximal tau-run of the INNER VALUE lies inside the tiling of one
maximal tau-run of f. The tau-material of t is then (mixed shapes
included): whole w-copies tau^n — from the inserted copies of Y, and
from g1(w) and g2(w) — interleaved with constant tau-gaps of three
kinds: within-copy gaps (a v_j, or v_nu v_0 across two glued copies —
in both cases total length <= c_Y), flanking constants (the tau-parts
of g1(w) resp. g2(w), together <= c_F), and at most ONE leftover tail
tau^r < beta' per maximal tau-run of t. The tail sits at the end of
the inner value's run; in the pure shape (g2 = eps) it ends the run of
t, but with a tau-initial g2 it is interior — followed by g2's
material inside the same run of t. (A maximal tau-run of t meets at
most the last run of g1(w), one run of the inner value, and the first
run of g2(w): everything else is separated by surviving non-tau
characters; and it never CUTS a w-copy, since a w-copy is all tau.)

**(2) The final pattern's shape (three kills).** Decompose X by its
maximal tau-runs: X = E_0 tau^{lam_1} E_1 ... tau^{lam_{pi'}} E_{pi'}
with the E_j nonempty non-tau strings except possibly E_0, E_{pi'}.
If k >= rho + 5 there is at least one interior copy-pick, and then:
E_0 != eps is impossible (Frame beta at the pick gives X[0] = w[o+1] =
tau, but E_0 != eps means X[0] != tau); E_{pi'} != eps is impossible
(Frame alpha: X[-1] = w[o-1] = tau); pi' = 1 (so X = tau^beta) is
impossible — the match covering the successor starts at q+1 and spells
X, so t[q+1 .. q+beta] is all tau, and t[q] = w[o] = tau, so
t[q:q+beta] = tau^beta = X: the greedy scan visits q (a survivor is
inside no match) and would match there, deleting the pick. (If
k <= rho + 4 we are done anyway.) So X starts and ends with tau-runs
and pi' >= 2; note lam_1, lam_{pi'} <= beta - 1 since E_1, E_{pi'-1}
are nonempty.

**(3) B-rigidity.** For an interior copy-pick at position q: the
alpha-match [q-beta, q) ends with X's last run, so [q-lam_{pi'}, q) is
all tau and t[q-lam_{pi'}-1] = X[beta-lam_{pi'}-1] = last char of
E_{pi'-1} != tau (the index is >= 0 because lam_{pi'} <= beta - 1, and
the position is >= q-beta >= 0); so the maximal tau-run of t containing
q starts exactly at q - lam_{pi'}. Symmetrically the beta-match makes
[q+1, q+lam_1+1) all tau with t[q+lam_1+1] = E_1[0] != tau, so the run
ends exactly at q + lam_1 + 1. Hence: every interior copy-pick's
maximal tau-run is EXACTLY [q - lam_{pi'}, q + lam_1 + 1), of one
common length L* = lam_{pi'} + lam_1 + 1; since w = tau^n, the pick's
whole w-copy W = [q-o, q-o+n) is a tau-block containing q, so it lies
inside the run, forcing lam_{pi'} >= o and lam_1 >= n-1-o; and two
interior copy-picks cannot share a run (same run would give the same
interval, hence the same q).

**(4) Residue count.** For each interior copy-pick p (offset o_p,
position q_p) let A_p = [run start, W_p) be the part of its run before
its own w-copy: |A_p| = lam_{pi'} - o_p. By the structure of (1),
A_p's material is j'_p whole w-copies (each tau^n) plus constant
tau-material of the three kinds: the within-copy gaps around the j''
<= j'_p inner copies (at most j'' + 1 of them, each <= c_Y), the
flanking constants of g1(w) and g2(w) lying in this run (together
<= c_F), and the leftover tail if it precedes W_p — possible only when
W_p lies in g2's material, since in the pure shape a leftover tail
only ends a run (in the mixed shape it is the one interior tail
allowed by (1)); the tail contributes <= beta' - 1. So, uniformly in
pure and mixed shapes,
  |A_p| = j'_p n + s_p    with  s_p <= (j'_p + 1) c_Y + c_F + beta' - 1.
(Junction gaps included: the g-constant stretch and the tail are
exactly the pieces the pure-shape bound missed.) The run's length is
L*, so j'_p n <= L* <= lam_{pi'} + lam_1 + 1
<= 2 beta - 1 = 2 pi n + 2 c_X - 1, giving j'_p <= J := 2 pi + 2 c_X
(and s_p <= (J+1) c_Y + c_F + beta' - 1). Now the |A_p| are DISTINCT
(the o_p are) and lie in the window [lam_{pi'} - n + 2, lam_{pi'} - 1]
of n-2 < n consecutive integers, so their residues mod n are distinct:
  |O| (|O| - 1)/2  <=  sum_p (|A_p| mod n)  <=  sum_p s_p
                   <=  ((J + 1) c_Y + c_F + beta' - 1) |O|,
hence |O| <= 2 (J + 1) c_Y + 2 c_F + 2 beta' - 1, and
  k <= |O| + rho + 2
    <= 2 (2 pi + 2 c_X + 1) c_Y + 2 c_F + 2 beta' + rho + 1.
This closes the residual corner in ALL depth-2 shapes, mixed
scrutinees included: every case of the induction now carries an
explicit constant.

**(5) Deep shapes and C-nodes.** deepR2/deepP2 (the depth budget spent
inside the final replacement or pattern): the scrutinee F1 is
pass-free, so t is a pass-free value — there are NO copies in t.
Label-free final replacement: k <= rho (one pick per run). Labeled,
c = 1: t^- and t^+ are run-pieces, <= rho picks each (Slice — valid
here, no copies), the y-block <= nu in deepR2 (Theorem 1) and
impossible in deepP2 (Elimination): k <= 2 rho + nu. Labeled, c >= 2:
T1(a). C-nodes: prov(E1.E2) is a block, so prov(E1) is its top block
and prov(E2) its bottom block, both blocks, with k = k1 + k2. Each
branch runs the same induction; the Dichotomy is applied per branch
(with its own rho_i): either every branch lands in a bounded case or
forces w = tau^n (k_i >= 2 rho_i + 5), and once ANY branch forces
w = tau^n, every other branch's constants apply with w known uniform
(steps 1-4 never look at other branches). If no branch forces it,
n = sum k_i <= sum (2 rho_i + 4). Assembling all cases:
  C(E) = an explicit max over the C-tree of
    #V(E),  rho,  beta_0 + 2 rho,  (rho+1) nu + rho,  c_F nu + rho,
    2 rho + 4,  rho + 4,
    2 (2 pi + 2 c_X + 1) c_Y + 2 c_F + 2 beta' + rho + 1,
    2 rho + nu,  sum_i (2 rho_i + 4),
with beta_0 the constant length of a constant final pattern, beta' =
|Z| the inner pattern's constant length, and c_F, rho taken over the
whole pass-free skeleton (g's included) — every ingredient a syntactic
constant of E. ∎

**Consistency checks.** (i) The n = 2 witnesses (11.5): n = 2 is below
every threshold in the proof (2 rho + 5 with rho = 2, rho + 5, ...) —
the interior-offset machinery is vacuous at n = 2, which is exactly
where they live. (ii) The round-9 staircase [eps/tail^4 X][tail(X)/ab]X
on w = (bba)^k: it has beta = n - 4 < n (a computed final pattern that
is a PROPER SUBSTRING of w — pass-free patterns containing w have
beta >= n, so the staircase is not in the residual corner; its pattern
has S-depth >= 1, pushing E to depth >= 3), and it is not FDI — outside
Theorem 3's hypotheses on both counts; Theorem 3 says nothing about
it, as it must not. (iii) Theorem 2 is not used inside the corner (its
bound n <= beta + 2 rho + nu is vacuous there, beta >= n); the corner
is closed by Frames + Breaks + rigidity + residues instead — this is
the content of the round. (iv) Mixed shapes: the round-12 phase-2 hunt
(11.6) swept [eps/X](g1.[Y/xp].f.g2) with run-bearing and constant
flanks — 36 DB hits, ALL at n = 2, each re-verified by prov.py's
independent evaluator; nothing at n >= 3, as the repaired step (4)
predicts (the junction gaps only enlarge the constant, they do not
unbound it).

### 11.5 The n = 2 witnesses (found, verified, dissected)

Round 11's targeted hunt (11.6) found FOUR chain2 DB realizations at
n = 2 in the residual regime — the first depth-2 witnesses that are
not C-nodes. All four are verified by prov.py's independent evaluator
(lden, the full denotation semantics):

  w = aa:  E = [eps/(w.b.w)] . [(ab.w.ba)/b] (b.w.a.w.b)    prov = (1,0)
  w = aa:  E = [eps/(w.b.w)] . [(ba.w.ab)/b] (w.bb.w)        prov = (1,0)
  w = ab:  E = [eps/(b.w.a)] . [(b.w.a)/bb] (b.w.b.w.b)      prov = (1,0)
  w = bb:  E = [eps/(w.a.w)] . [(ba.w.ab)/a] (a.w.b.w.a)     prov = (1,0)

Dissection of the first (atom-level, k = constant):
  F = b w a w b   (7 atoms: 2 labeled runs, rho = 2)
  t = [ab.w.ba] . [a_0 a_1 a_k a_0 a_1] . [ab.w.ba]
      (xp = 'b': both constant b's are sites; nu = 1 copy of w each)
  final pass deletes X = w.b.w = 'aabaa'; the two matches straddle
  copy boundaries: t[2:7] eats copy 1's w-run together with F's first
  w's leading atom (a,0); t[10:15] eats F's second w's trailing atom
  (a,1) together with copy 2's constants and w-run.
  survivors: k a k, then (a,1), a_k, (a,0), then k b k:  prov = (1,0).
Mechanism: the two matches each consume one copy's w-run PLUS one
flanking F-atom, pairing F's two w-runs (labels 1 then 0) between the
copy debris. At n = 2 there are no interior offsets (the interval
[1, n-2] is empty), so Frames, Breaks, B-rigidity and the residue count
are all vacuous — the witnesses sit in the proof's only blind spot,
which is a bounded one (n = 2 < every threshold). All four witnesses
have prov = (1,0) and the same two-straddling-matches shape; three use
pi = 2 final patterns (w.b.w, w.a.w), one pi = 1 (b.w.a) with
non-uniform w. Round 10's mode 2 missed them because its pattern pool
had no w.b.w-type values — the round-9 domain-gap lesson a third time.

### 11.6 Machine verdicts (round 11)

- **verify_round11.py part 1 (Replacement Elimination)**: 6,831,200
  sims, 33 inputs; 0 FDI outputs with c = 1 and labeled final
  replacement; 0 with c >= 2 and labeled (T1(a) control); 0 DB.
  VERIFIED. Part 1c (round-12 repair 3, the LIVE control — final
  replacement drawn from the FULL pass-free library, 16,147,500 sims
  over 14 inputs): 673,290 FDI outputs with c = 1 and label-free
  replacement vs 0 with c = 1 and labeled — the c = 1 channel is
  exercised, its labeled half stays empty. VERIFIED (53 s).
- **part 2 (Frames alpha/beta + break composition)**: 3,545 FDI
  outputs with beta >= n over 70 inputs (all |w| <= 5 plus ab/aab/bba
  families), F/Y from the two-sided pass-free library; 83 interior
  copy-picks checked, 0 violations of (alpha)/(beta). 0
  adjacent-offset pairs occurred, so the break COMPOSITION is not
  machine-exercised on this domain (each factor is); it is pure string
  algebra, proved in 11.3.
- **part 3 (B-rigidity)**: 1,184 eligible FDI outputs (uniform w,
  beta >= n, X with >= 2 maximal a-runs starting/ending with a-runs),
  41 interior copy-picks; in every case the pick's maximal a-run is
  exactly [q - lam_last, q + lam_1 + 1). VERIFIED.
- **part 4 (step-(2) kills)**: 5,665 FDI outputs with beta >= n on
  uniform w; 41 with an interior copy-pick; every one has X[0] = a,
  X[-1] = a, and a non-a char in X (the contrapositive of the three
  kills). VERIFIED.
- **round11_hunt.c (targeted residual-regime DB hunt)**: PHASE 1 (pure
  chain2, unchanged from round 11): 232 inputs (all |w| <= 6, a^k to
  24, b.a^k / a^k.b to 20, a^i b a^j to 7+7, (ab)^k, (aab)^k, (abb)^k,
  (baa)^k), 23 F/Y two-sided forms, 8 inner patterns, final patterns
  from the 23 forms filtered to beta >= n (pi >= 1) and deduped, final
  replacement epsilon (justified by Replacement Elimination + T1(a)):
  22,281,480 sims, 345,448 FDI outputs (max length 3), 4 DB hits —
  exactly the n = 2 witnesses of 11.5, nothing at n >= 3. PHASE 2
  (round-12 repair 2, MIXED SHAPES — swept by NEITHER round 10's mode
  2 NOR round 11's phase 1): [eps/X](g1.[Y/xp].f.g2) with g1, g2 from
  12 pass-free options (empty, pure constants a/b/ab, and the
  run-bearing w, a.w, w.a, a.w.a, w.w, w.a.w, b.w, w.b; at least one
  nonempty), f from 8 forms, Y from 10 labeled forms, inner pattern
  all-a, final pattern containing w, 39 uniform/near-uniform inputs
  (n <= 14): 39,628,160 sims, 903,629 FDI outputs (max length 3),
  36 DB hits — ALL at n = 2 (w = aa), every one re-verified by
  prov.py's independent evaluator (verify_round12_mixed.py: 36/36
  match DB). Nothing at n >= 3 in either phase. All runs < 60 s
  (hunt with both phases 18 s; part 1 38 s and part 1c 53 s, run as
  separate invocations; parts 2-4 together 9 s).

### 11.7 What Theorem 3 does and does not give

- Depth <= 2 is COMPLETE for the finiteness program: no fixed
  depth-<=2 expression realizes DB on arbitrarily long inputs. The
  multi-match sigma-packing endgame of 10.5 — Round 10's last open
  depth-2 item — is closed by step (4) of the proof, which never
  assumes anything about how the matches tile the runs (the residue
  count is agnostic to match configuration), and round-12 repair 2
  extended the corner analysis from pure chain2 to the mixed shapes
  [R2/P2](g1.[Y/Z]f.g2) (junction gaps bounded, C(E) restated).
- SCOPE OF THE REV PAYOFF (round-12 repair 1 — the honest framing):
  finiteness excludes rev at depth <= 2 over UNBOUNDED alphabets only
  (DB-forcing lemma, 12.1: a rev-computing E must realize DB on
  distinct-character inputs avoiding E's constants). Over a FIXED
  finite alphabet Sigma the prov route has no forcing family — and
  none can exist: the laundering theorem (12.2) shows that whenever
  any E computes rev on any W within Sigma*, a depth-(+2|Sigma|)
  rewrite computes rev on W with prov == () on ALL of Sigma* — no
  nontrivial prov-level property is ever forced by rev-correctness
  over a fixed finite alphabet. This is the atoms-level sharpening of
  round 2's content-level negative result (min-LDS over
  content-consistent relabelings <= n/LPS(w); binary LPS >= n/2, so
  content-level relabeling invariants cannot exclude rev over fixed
  Sigma either). Round 2 had the scope right; rounds 10-11's framing
  overreached; rounds 11-12 repair it.
- Depth >= 3 remains open; the budget conjecture (10.8) is untouched
  by this round (time budget went to corrections + B). Theorem 3's
  mechanism is depth-2-shaped: Frames live on the LAST pass, and the
  copy structure of t comes from exactly one inner pass. What does
  transfer: the extremal structure — every depth-2 DB needs the final
  pattern's value to contain w (pi >= 1, beta >= n), matching the
  depth-3 witnesses' beta = n and the staircase's beta = n - 4; and
  the breaks say that whenever TWO descent steps sit at adjacent
  offsets, w must be uniform — a rigidity that any depth-d induction
  will have to reproduce or route around.
- The FDI-level analogue of Theorem 3 (bound |prov| for all FDI
  outputs, not just blocks) is OPEN and is false as stated for
  trivial reasons unless stated carefully: an FDI prov of length 1
  exists for unbounded n (e.g. [eps/(tau tau)].w on odd-length
  uniform w leaves exactly one atom). The right FDI question —
  whether |prov| <= C(E) for FDI provs of length >= 2, or a linear
  bound in general — is open; the obstruction is that the Dichotomy
  needs consecutive offsets (the block structure), and arithmetic-
  staircase FDI provs (offsets in an arithmetic progression, the
  round-9 phase-class structure) are exactly what the current proof
  cannot rule out. Note DB and block provs cannot be arithmetic
  staircases — that is why Theorem 3 closes.

### 11.8 Honest ledger for Round 11

- PROVED: Replacement Elimination (chain2/deepP2: FDI + labeled final
  replacement impossible, n >= 2); Frame (alpha)/(beta); Break (adjacent
  interior copy-pick offsets force w constant on both flanking
  intervals; two distinct pairs force w = tau^n); the Block Dichotomy
  (k <= 2 rho + 4 or w uniform); the three step-(2) kills; B-rigidity
  (exact run [q - lam_{pi'}, q + lam_1 + 1), one pick per run, common
  length L*); the residue count (|O| <= 2(2 pi + 2 c_X + 1) c_Y + 1);
  Theorem 3 (depth-2 finiteness, unconditional, explicit C(E));
  Round-12 repairs of the proof: the corner analysis extended from
  pure chain2 to the mixed shapes [R2/P2](g1.[Y/Z]f.g2) (the junction
  gap bound s_p <= (j'_p+1) c_Y + c_F + beta' - 1, uniform in pure
  and mixed shapes; C(E) restated accordingly);
  Round-10 corrections: Theorem 2 case (ii) repaired, Pinch's
  deviation-location clause (deviations at distance exactly 1 from
  slice-pick offsets or string endpoints, <= 2 rho + 2 of them),
  Transport widened to any label-free replacement.
- VERIFIED ON STATED DOMAINS: Replacement Elimination (part 1,
  6,831,200 sims; and part 1c with the FULL replacement library,
  16,147,500 sims, 673,290 label-free c = 1 FDI vs 0 labeled — the
  control is live, round-12 repair 3); Frames (part 2, 83 firings,
  0 violations); B-rigidity (part 3, 41 firings, 0 violations); the
  step-(2) kills (part 4, 41 firings, 0 violations); the four n = 2
  witnesses (round11_hunt phase 1, 22,281,480 sims, prov.py-verified);
  the MIXED shapes (round-12 phase 2, 39,628,160 sims — these were
  swept by NEITHER round 10's mode 2 NOR round 11's phase 1; 36 DB
  hits all at n = 2, each prov.py-verified 36/36); the round-10
  lemma battery re-verified with the corrected checker (59,300 FDI
  outputs, 0 violations). NOT machine-exercised: the break
  composition (0 adjacent pairs arise on the domain) and the residue
  count (its ingredients are: rigidity — machine-checked; distinct
  residues — algebra; the gap bound — structural, from the inner-pass
  tiling plus the round-12 junction analysis).
- CONJECTURED: the budget n <= d + 1 for chains (unchanged, 10.8).
- OPEN: depth >= 3 entirely; the induction combining S-depth and
  pattern length; the FDI-level analogue of Theorem 3 (11.7).

### 11.9 Files

- `verify_round11.py` — parts 1-4 (Elimination, Frames, B-rigidity,
  kills) + mode 1c (the round-12 live control);
  `round11_verify.log` (all parts, plus the prov.py re-verification of
  the four hunt hits; re-run in round 12 with 1c appended).
- `round11_hunt.c` / `./round11_hunt` / `round11_hunt.log` — the
  targeted residual-regime DB hunt: phase 1 pure chain2 (232 inputs,
  22.3M sims, the four n = 2 hits printed with full form specs) +
  phase 2 MIXED SHAPES (round-12 repair 2; 39 inputs, 39.6M sims,
  36 n = 2 hits with full form specs), 18 s total.
- `verify_round12_mixed.py` — re-verifies every MIXED DB HIT line of
  round11_hunt.log by rebuilding [eps/P](g1.[Y/xp].f.g2) in lcore and
  checking prov = DB with prov.py's independent evaluator (36/36).
- `verify_round10_lemmas.py` (v2) / `round10_lemmas.log` — the
  corrected round-10 checker (10.7 s).
- `descending_bijection.tex` — updated: corrections + Theorem 3 in
  paper voice (round 12: unbounded-alphabet lemma, mixed-shape gap
  bound, honest rev-payoff framing; see 12.6).

## 12. Round 12 — repairs, and the alphabet-scope theorem: the prov
## route is EXACT over unbounded alphabets and DEAD over fixed ones

Round 11 was verified with four defects; all four are repaired this
round (12.0), and the round's main target — a prov-level forcing
family over a fixed finite alphabet — is answered definitively, in the
negative, by a new theorem (12.2): over any fixed finite alphabet,
rev-correctness forces NOTHING at the prov level, because every
rev-correct expression can be rewritten to have empty provenance
everywhere. Together with the DB-forcing lemma (12.1) this gives the
program its correct two-sided shape: over unbounded alphabets the DB
invariant is not just useful but exact (it is THE obstruction, and
Theorem 3 + 12.1 close depth 2 for all expressions, constants
included); over fixed alphabets the prov level is retired outright and
the residual questions are content-level (12.3).

### 12.0 The four repairs (where they landed)

1. FRAMING (major). The finiteness program's rev payoff was
   overstated for fixed finite alphabets: over fixed Sigma,
   distinct-character inputs have length <= |Sigma|, and even on them
   DB is not forced (constants can supply output characters). What IS
   true — proved and now stated as Lemma DB-forcing (12.1, tex
   lem:forcing) — is the UNBOUNDED-alphabet statement. Theorem 3's
   closing clause, the fragment's motivation, and 11.7 are rewritten;
   the fixed-alphabet side now cites round 2's content-level negative
   result AND carries the new laundering theorem (12.2), which makes
   "no known forcing family" into "no forcing family can exist".
2. JUNCTION GAPS. The round-11 corner analysis was written for pure
   chain2 and waved at mixed shapes as "chain2 after flattening" —
   not an equality, since the inner pass does not scan the flanking
   material. 11.4 steps (0)/(1)/(4) now handle
   [eps/X](g1.[Y/Z]f.g2) explicitly: each run-prefix gap is bounded
   by s_p <= (j'_p+1) c_Y + c_F + beta' - 1 (uniform in pure and
   mixed shapes), C(E) restated; the ledger records that neither
   round 10's mode 2 nor round 11's phase 1 had swept these shapes,
   and the hunt's new phase 2 sweeps them (36 DB hits, all n = 2,
   each prov.py-verified 36/36; nothing at n >= 3).
3. DEAD CONTROL. verify_round11.py part 1's "label-free c = 1" count
   was dead code (yf drawn only from the labeled sub-library). Mode
   1c now draws the final replacement from the FULL pass-free
   library on a reduced domain: 673,290 FDI outputs with c = 1 and
   label-free replacement vs 0 with c = 1 and labeled — the 0 is
   genuine, the channel live. 11.2/11.6 updated.
4. INPUT COUNT. 11.6 said 32 inputs for part 1; the actual count is
   33 (11.2 was already right).

### 12.1 Lemma DB-forcing (unbounded alphabets) — PROVED

Let Gamma(E) be the finite set of letters occurring in E's constants.

**Lemma.** Let E compute reversal on w, |w| = n >= 1. If w's
characters are pairwise distinct and disjoint from Gamma(E), then E
realizes DB(w): prov(E,w) = (n-1, ..., 0).

Proof. Every atom of E's output is either a constant of E (carrying a
Gamma-letter) or a copy of a w-atom. The output is rev(w), whose
letters are exactly w's — none in Gamma(E) — so every output atom
carrying the output's letters is a copy. Within one copy of w there
is exactly one atom per w-offset (distinct characters identify unique
offsets), and the output's j-th atom carries w[n-1-j], hence is its
copy's atom at offset n-1-j: reading labels left to right gives
(n-1, ..., 0). ∎

Two corollaries for the program's scope. (i) Over an unbounded
alphabet, distinct-character inputs avoiding Gamma(E) exist at every
length, so Theorem 3 + the lemma give: NO depth-<=2 expression
computes reversal over any unbounded alphabet — for ALL expressions,
constant-bearing included. This closes the gap the round-11 framing
left (the old closing clause was vacuous over fixed Sigma). (ii) The
lemma is conditional on rev-correctness, so it cannot be fired
directly by machine at n >= 2 (any fired case would BE a rev-computing
E on distinct characters at n >= 2 — that would itself be a rev
computation on an unbounded family, the open problem). What the
machine checks is the crux — output atoms carrying letters outside
Gamma(E) are never constants (12.4, part 3: 1,397,644 atoms, 0
violations) — plus the degenerate firings: on a c/d domain with E's
constants in {a,b}, rev-correct outputs arose 23,507 times: 15,116 on
palindromes (identity already computes rev there; prov INCREASING —
distinctness is exactly the hypothesis that fails) and 8,391 on
single letters (all with prov = (0,) = DB — the conclusion held every
time the hypothesis did).

### 12.2 Theorem laundering (fixed alphabets) — PROVED; the main
### target answered in the negative

For a letter sigma let L_sigma be the chain [sigma/sigma-sigma]
[sigma-sigma/sigma] (doubling then halving; rightmost applies first).

**Theorem.** L_sigma is the IDENTITY on every text, and every
sigma-atom of its output is a constant. Consequently, for every
expression E and every finite alphabet Sigma, the composition
L_Sigma . E (one L_sigma per letter of Sigma) computes the same
function as E on all of Sigma* and satisfies prov(L_Sigma . E, w) =
() for every w in Sigma*.

Proof. [sigma-sigma/sigma] matches every sigma-atom and replaces it
by the constant pair: a maximal sigma-run of length L becomes one of
length 2L, all constant. [sigma/sigma-sigma] then matches pairs
greedily; the doubled runs have even length, so the tiling is exact
and the run returns to length L with every atom a constant. Non-
sigma atoms are matched by neither pattern and pass through with
their labels. So the text is unchanged and every surviving sigma-atom
is a constant. Composing over Sigma: each L_sigma is the identity on
every text and its patterns mention only sigma, so the steps do not
interact; after all |Sigma| steps every atom carrying a letter of
Sigma is a constant. On inputs from Sigma* that is every atom. ∎

**Corollary (the round's main target).** Over a fixed finite alphabet
Sigma, NO nontrivial prov-level property is forced by rev-correctness
on ANY family: if E computes rev on W within Sigma*, then L_Sigma . E
computes rev on W with prov == () on every input. The forcing
question ("find P and W over a fixed Sigma such that rev-correctness
on W forces P(E,w)") has a definitive negative answer — a proof, not
a failure to find one.

Consistency checks. (i) No contradiction with 12.1: the laundered
expression has Gamma >= Sigma, and the forcing family avoids Gamma
altogether — its letters are exactly the ones E has no constants for
and hence cannot launder. Laundering works precisely for the letters
an expression can afford as constants; forcing works precisely for
the others. (ii) Depth is not preserved (the laundering costs 2 passes
per letter), so Theorems 1-3 are untouched: the laundered E realizes
DB nowhere, which is consistent with their bounds. (iii) The
theorem is the atoms-level sharpening of round 2's content-level
negative result (min-LDS over content-consistent relabelings <=
n/LPS(w); binary LPS >= n/2): round 2 killed the content-level
relabeling route over fixed Sigma, round 12 kills the prov route over
fixed Sigma. What survives over fixed Sigma is content only.

**The dead-prov rev witnesses (all machine-verified, 12.4 part 2).**
Over Sigma = {a,b}:
  W1 = {b a^j : j >= 0}:  E1 = C( L_a.[eps/b]X , b )            prov = ()
  W2 = {a^i b : i >= 0}:  E2 = C( b , L_a.[eps/b]X )            prov = ()
  W3 = {(ab)^k : k >= 1}: E3 = [ba/ab]                          prov = ()
  W4(i) = {a^i b a^j : j >= 0}, i fixed in {1,2,3}:
         E4 = C( L_a.[eps/a^i b]X , b , a^i )                  prov = ()
  W5(j) = {a^i b a^j : i >= 0}, j fixed in {1,2,3}: symmetric.
W3 deserves the flag: a SINGLE PASS, replacement all-constant — rev
on an infinite two-run alternating family with empty provenance and
no laundering even needed. W1/W2/W4/W5 are the laundering theorem
applied to the obvious content-level rev-computers (delete past the
b, resupply around it). W4/W5 show the two-sided one-b family is
rev-computable with dead prov as soon as ONE side is fixed; only when
both i and j vary does anything remain (12.3).

**The round's three concrete angles, answered.**
- Rare-character families (w = a^i b a^j: can the output's b be
  constant-supplied while E stays rev-correct across the family?):
  YES — whenever the family is rev-computable at all, by the theorem;
  constant-supply is never the obstruction. Exhibits: W1-W5; the
  full two-sided family reduces to the split problem (12.3).
- Supply counting (w = a^n b: #a(output) = n = a-copies + a-consts —
  can the counts work at mult 1? at bounded prov length?): YES, at
  mult 1 AND prov length 0 simultaneously (E2 supplies all n a's as
  constants). Prov-level counting arguments cannot exclude rev over
  fixed Sigma.
- The right formalization of a prov necessary condition: there is
  NONE over fixed finite alphabets — the theorem kills every
  candidate property jointly (the laundered expression violates all
  of them while staying rev-correct). The formalization that
  survives is the unbounded-alphabet one (12.1). Over fixed Sigma,
  necessary conditions for rev-correctness live at the content level
  only.

### 12.3 The content-level residue: the split problem

Over fixed Sigma the prov route is retired (12.2); what remains is
purely content-level. The sharpest open family is the two-sided
one-b family F = {a^i b a^j : i, j >= 1}.

**Lemma (reduction, PROVED).** If some expression E_L computes the
left-run function on F (E_L(w) = a^i for w = a^i b a^j, all i, j),
then some E computes rev on all of F — and then some E' computes rev
on F with prov == () on every member (12.2).

Proof (the construction): E = C( L_a.[eps/(E_L b)]X , b , L_a.E_L ).
The inner pass's pattern value is E_L(w).b = a^i b, which occurs in w
at position 0 and nowhere else (any occurrence contains the unique b),
so the pass deletes exactly [0, i+1) and leaves a^j; the first L_a
launders it; the concatenation resupplies the constant b and then
L_a.E_L(w) = a^i (text unchanged, labels dead). Output a^j b a^i =
rev(w), and prov = () by construction — every output atom is a
constant. ∎ (Machine: the construction is exercised on its fixed-i
cases E_L = K(a^i), i in {1,2,3}, j to 8 — W6 in 12.4 part 2, 27/27.)

So the one-b family can never be a prov-forcing family: if the split
is computable, rev-on-F is computable with dead prov; if it is not,
rev-on-F is left open at the content level (no longer open — round
13 settles it: computable, 13.4) — either way the prov level is
silent on F. The F-version of the forcing question is
fully reduced to content.

**The split problem (OPEN).** Does any E compute left-run on F?
Equivalently (up to the symmetric right-run and the merge a^{i+j} =
[eps/b]X, both computable): can L cut a unary string at a position
marked by a separator — can it SUBTRACT? What the toolkit has
without it, on the run lengths (i, j) of F's inputs:
  - merges: i + j ([eps/b]X — the b deleted, runs glued);
  - common eventually-affine maps: an all-a CONSTANT pattern pass
    [a^gamma/a^beta] maps EVERY a-run's length L to floor(L/beta)
    gamma + (L mod beta) — the same common eventually-affine map
    psi(x) = lambda x + O(K) for all runs (lambda = gamma/beta);
    compositions give slopes in the multiplicative semigroup
    generated by the available gamma/beta (doubling, halving,
    tripling, ...), jitter bounded by a constant of E;
  - bounded windows: b-anchored constant patterns edit O(1)-length
    windows around the b (there is exactly one b; O(1) match sites);
  - duplications of the whole w.
What seems to be missing is ISOLATION of one run: a pattern value
that equals a^i (or even just ends at the b) needs an a-run of length
exactly i in a value, and pass-free values only offer constants and
whole-w copies (every a-run inside a w-copy is glued to the b);
computed values would need the split circularly. Constant patterns
cannot move material across the b (they edit runs in place, by the
common affine maps above, plus bounded windows at the b); crossing
the b requires w-bearing patterns, whose values contain the b.
CONJECTURE (split): no E computes left-run on F. Scope note
(corrected in round 13): the reduction above runs one way — split
IMPLIES rev-on-F — so refuting the conjecture gives rev on F with
dead prov, but PROVING it excludes nothing about rev on F unless the
converse (rev-on-F implies split) also holds, and that converse is
open (13.5). Round 13 in fact settles the target outright: rev on F
IS computable (E_swap = [b/w]bigsym, 13.4), so the split conjecture,
if true, is strictly stronger than rev-on-F and cannot exclude it.
Both outcomes leave the prov machinery retired over fixed Sigma, per
12.2.

### 12.4 Machine verdicts (round 12)

- **verify_round12.py part 1 (laundering identity + dead prov)**:
  440,000 random (E, w) trials over Sigma = {a,b}: content(L_a L_b E,
  w) = content(E, w) and labels = () in every one; 0 failures.
  VERIFIED.
- **part 2 (dead-prov rev witnesses)**: W1 11 inputs, W2 11, W3 8,
  W4 3x9, W5 3x9, W6 3x9 (the reduction construction of 12.3 with
  E_L = K(a^i)) — every member of every family: content = rev(w)
  and prov = (). 0 failures over 111 checks. VERIFIED.
- **part 3 (forcing crux)**: 200,000 random E (constants in {a,b}) on
  random w over {c,d}: 1,397,644 output atoms checked, 0 atoms
  carrying a c/d letter were unlabeled (constants never supply
  non-Gamma letters). The forcing implication's antecedent fired
  23,507 times: 15,116 on palindromes (prov increasing — the
  distinctness hypothesis fails, exactly as the lemma requires) and
  8,391 on single letters, all with prov = (0,) = DB. The conclusion
  held every time the hypothesis did. VERIFIED.
- **round11_hunt phase 2 (mixed shapes)**: 39,628,160 sims, 903,629
  FDI outputs, 36 DB hits all at n = 2; verify_round12_mixed.py
  re-verified all 36 by rebuilding [eps/P](g1.[Y/xp].f.g2) in lcore
  and checking prov = DB with prov.py's independent evaluator
  (36/36). VERIFIED.
- **verify_round11.py 1c (the live control)**: 16,147,500 sims,
  673,290 FDI with c = 1 and label-free final replacement, 0 with
  c = 1 and labeled. VERIFIED.
- Re-run of round-11 parts 1-4 after the repairs: all VERIFIED,
  numbers unchanged (part 1: 6,831,200 sims, 33 inputs; parts 2-4
  as in 11.6).

### 12.5 Honest ledger for Round 12

- PROVED: Lemma DB-forcing (unbounded alphabets: rev-correct +
  distinct chars avoiding Gamma(E) forces prov = DB); Theorem
  laundering (L_sigma is a text-level identity killing every
  sigma-label; over fixed Sigma every rev-correct E rewrites to
  prov == () everywhere); Corollary: no prov-level property is forced
  by rev-correctness over any fixed finite alphabet (the main
  target, negative); the reduction lemma (left-run computable ⟹ rev
  on the two-sided one-b family computable with prov == (); explicit
  construction); the mixed-shape extension of Theorem 3's corner
  (junction gap bound s_p <= (j'_p+1) c_Y + c_F + beta' - 1, uniform
  in pure and mixed shapes; C(E) restated).
- VERIFIED ON STATED DOMAINS: the laundering identity (440,000
  trials, 0 failures); the dead-prov witnesses W1-W6 (111 family
  member checks, 0 failures — W6 being the reduction construction
  of 12.3 on its fixed-i cases); the forcing crux (1,397,644 atoms, 0
  violations; antecedent firings classified: 15,116 palindromes
  with the hypothesis failing, 8,391 single letters with the
  conclusion holding); the mixed-shape hunt (39.6M sims, 36 hits all
  n = 2, prov.py 36/36); the live control 1c (673,290 vs 0).
- CONJECTURED: the split conjecture (no E computes left-run on
  {a^i b a^j : i,j >= 1}); the budget conjecture n <= d + 1
  (unchanged, 10.8 — untouched this round; the round's time went to
  the repairs and the main target, which did NOT resist: it has a
  proof).
- OPEN: the split problem and with it every content-level exclusion
  over fixed alphabets (round 2's negative result + 12.2 mean this
  is the ONLY remaining route there); depth >= 3 over unbounded
  alphabets; the FDI-level analogue of Theorem 3 (11.7); the
  converse of the reduction lemma (does rev on F imply the split?).

### 12.6 Files

- `verify_round12.py` / `round12_verify.log` — parts 1-3 (laundering,
  witnesses, forcing crux), 25 s total.
- `verify_round12_mixed.py` — the phase-2 hit re-verification
  (parser + lcore rebuild + prov.py check, 36/36); also appended to
  `round11_verify.log`.
- `round11_hunt.c` / `./round11_hunt` / `round11_hunt.log` — phase 1
  (pure chain2, bit-identical to round 11: 22,281,480 sims, 4 hits)
  + phase 2 (mixed shapes, 39,628,160 sims, 36 hits), 18 s.
- `verify_round11.py` (mode 1c added) / `round11_verify.log` —
  re-run in full (part 1 38 s, 1c 53 s, parts 2-4 9 s, separate
  invocations, all < 60 s).
- `descending_bijection.tex` — round-12 updates: lem:forcing +
  thm:laundering with proofs, the "What DB can and cannot exclude"
  paragraph, the mixed-scrutinee paragraph and the junction-gap
  residue count inside thm:depth2finite's proof, the honest closing
  paragraph, updated header and machine record.

## 13. Round 13 — the one-b family, directly: MATCH ANCHORING, the
## pass calculus, and THE CONSTRUCTION (rev on F is computable)

Charter: settle whether any E computes rev on F = {a^i b a^j : i,j >= 1}
over Sigma = {a,b} — construction, impossibility, or a documented wall.
Also: Task 1, the converse of the 12.3 reduction (does rev-on-F imply
the split?); fix 12.3's overstated scope note.

**THE ANSWER (construction side): rev on F is computable — and on the
FULL one-b language.** The expression is
    E_swap = [b/w] bigsym,   bigsym = C( [eps/b]X , b , [eps/b]X )
(S-depth 2, #S = 3, #C = 2). This is the first nontrivial rev
computation in L (rounds 1-12 had rev only on degenerate families:
fixed-side one-b, {(ab)^k}, |w| <= 1). Details and proof in 13.4;
machine verification in 13.8 (prov.py, the independent evaluator).

Consequences, up front:
1. The one-b family can NEVER exclude rev in L at the content level —
   the content obstruction must live at >= 2 separators (13.7).
   Together with 12.2 (prov-level: nothing forced over fixed Sigma),
   the one-b family is fully retired, at every level, as a witness
   family against rev.
2. 12.3's split conjecture is strictly stronger than rev-on-F (13.5);
   its scope note is corrected in place.
3. The laundered composition L_a.L_b.E_swap computes rev on the
   one-b language with prov == () everywhere over Sigma = {a,b} —
   rev with dead prov on an infinite two-sided family, sharpening
   12.2's witnesses (which were one-sided).

### 13.1 Lemma MATCH ANCHORING — PROVED

Write a text's RUN VECTOR for its a-run lengths between consecutive
b's: a^x b a^y has vector (x, y); a value with m b's has m+1 runs
(p_0, ..., p_m).

**Lemma.** Let P be a pattern value with m >= 1 b's, T any text.
(a) Every match of P in T aligns each of P's b's with a b of T, and
    P's interior runs are consumed EXACTLY: if P's b #u lands on T's
    b #s+u for a fixed offset s, then T's b's s+1..s+m-1 are
    CONSECUTIVE b's of T (no text b strictly between them) and T's
    runs between them equal P's interior runs p_1..p_{m-1} exactly;
    the leading run is partial (>= p_0), likewise trailing (>= p_m).
    In particular an m-b pattern matches only across m consecutive
    text b's.
(b) On a ONE-B text T = (x, y): patterns with m >= 2 b's NEVER match
    (T has no two b's); a one-b pattern (p_0, p_1) matches only at
    T's unique b, its leading a^{p_0} being the last p_0 a's of the
    left run and its trailing a^{p_1} the first p_1 of the right.

*Proof.* In a match, each pattern b is a literal matched against a
text character, which must be a text b; the substring of the window
between two consecutive pattern b's is the fixed all-a string
a^{p_u}, so the text between the two aligned b's contains no b (the
aligned b's are consecutive text b's) and has exactly that length;
leading/trailing runs are prefix/suffix conditions. (b) is the m = 1,
#b(T) = 1 case: the single alignment. ∎ (Machine: A1/A2/A5, 13.8.)

### 13.2 The one-b pass calculus — PROVED

Classification of a single pass [R/P] on a one-b text T = (x, y)
(values P, R evaluated at the original input; P nonempty):

(i) **P b-free** (P = a^p, p >= 1) **and R b-free** (a^r): P matches
    only inside a-runs; each run is rewritten INDEPENDENTLY by the
    common eventually-affine chunk map psi(u) = r*floor(u/p) +
    (u mod p) (greedy tiling from the run's LEFT end, leftover at the
    right end). Output (psi(x), psi(y)). [Halving [a/aa] is thus the
    CEILING; doubling [aa/a] is exact.]
(ii) P b-free, R bearing b's: each firing inside an a-run inserts b's
    — the output leaves the one-b class as soon as any run has length
    >= p ("b-explosion").
(iii) **P one-b** (p_0, p_1): by 13.1(b) it fires iff x >= p_0 and
    y >= p_1, exactly once, at the b. With R one-b (r_0, r_1):
    output (x - p_0 + r_0, y - p_1 + r_1); with R b-free (a^r): the
    remnants merge, output a^{x-p_0+r+y-p_1} (b-free); with R
    multi-b: explosion.
(iv) **P multi-b**: never fires on a one-b text — the identity.

**Pass-free structure (PROVED).** On one-b inputs: (a) a b-free
pass-free value is a CONSTANT (every occurrence of the variable
carries the b); (b) every a-run of a pass-free value has length
a*i + b*j + c, a,b,c constants of the expression (induction over
C/K/V: V(0)'s runs are i and j; constants are fixed; concatenation
sums the adjacent affine forms).

(Machine: A3/A4 for the firing algebra and the independent per-run
action, 13.8. Note (i)-(iv) also hold verbatim for each single-b
"window" of multi-b texts, with (a)-type passes acting on ALL runs at
once — the asymmetry needed to treat two b's differently must come
from run-length conditions, which is exactly where 13.7's wall sits.)

### 13.3 The construction catalogue — PROVED (machine-verified 8x8)

On F (input w = a^i b a^j), all verified in lcore/prov.py (B1):
  merge   = [eps/b]X = a^{i+j};
  dbl     = [aa/a]X = (2i, 2j);
  half    = [a/aa]X = (ceil(i/2), ceil(j/2))   (ceiling!);
  shrinkR = [b/(ba)]X = (i, j-1),  shrinkL = [b/(ab)]X = (i-1, j);
  mergeM1 = [eps/(ba)]X = a^{i+j-1};
  bigsym  = C(merge, b, merge) = (i+j, i+j);
  halfmrg = [a/aa]merge = ceil((i+j)/2)  — a b-free value of length
            <= j on i <= j (this killed the naive "no unbounded
            b-free length <= j" invariant candidate);
  diff    = [eps/merge]dbl = (i-j, 2j) if i > j; (2i, j-i) if i < j;
            "b" if i = j (BOTH runs fire at the boundary — a
            conditionally-fired piecewise value: semilinearity is
            NOT the obstruction class, as the coordinator suspected).
Two MECHANISMS (verified with constant-baked patterns — the patterns
are NOT constructible without split knowledge, which is the point):
  lock-deletion: [eps/(a^i b a^y)]X = a^{j-y} for 0 <= y <= j
    (the pattern's leading run i is exactly the text's left run, so
    the left remnant is empty; requires LEFT-RUN knowledge);
  flank-swap: IF a (j, M, i) text with M > j were constructible,
    [eps/(a^M b)] would swap in one pass (match anchored at the
    second b consumes the middle run exactly + that b).

### 13.4 THE CONSTRUCTION — PROVED (machine-verified)

**Theorem (rev on the one-b language).** Over Sigma = {a,b},
    E_swap = [b/w] . bigsym,  bigsym = C( [eps/b]X , b , [eps/b]X ),
computes rev on the full one-b language {a^i b a^j : i, j >= 0}.

*Proof.* Let w = a^i b a^j, i,j >= 0. [eps/b]X deletes the unique b:
merge(w) = a^{i+j}; bigsym(w) = a^{i+j} b a^{i+j}. The pattern value
is w = a^i b a^j — one-b, so by 13.1(b) its only possible match in
bigsym is at bigsym's b, with leading run i <= i+j and trailing
j <= i+j: it fires, exactly once, at window start (i+j) - i = j (any
earlier start puts a text 'a' where the pattern needs its b; there is
no later one — the alignment is unique). Left remnant a^{(i+j)-i} =
a^j, right remnant a^{(i+j)-j} = a^i, replacement the constant "b"
(runs (0,0)): output a^j b a^i = rev(w). Boundaries verbatim: i = 0
or j = 0 only weaken the inequalities; at i = j = 0, w = "b" matches
bigsym = "b" and the output is "b". ∎

**The complement view (why it works).** For any one-b value T = (A,B)
constructible from w and any one-b constant replacement
R = a^{r0} b a^{r1}, the pass [R/w]T fires (13.1(b), 13.2(iii)) iff
A >= i and B >= j, and outputs (A - i + r0, B - j + r1) — the
COMPLEMENT of w in T, up to the replacement's flanks. The swap is
the r = 0 point at T = bigsym: (i+j - i, i+j - j) = (j, i). The
engine is that merge is SYMMETRIC in (i, j) and constructible without
any split knowledge, and a single anchor splits each merge run for
free into (used, complement) with complement-of-i = j. No isolation
of a run is ever needed — the missing ingredient identified in 12.3
is simply not needed for the swap.

**Discovery path (machine-assisted, recorded honestly).** The C sweep
(13.8, first run) flagged [ba/w]bigsym as a HALF-SWAP — output
(j, i+1), the left flank already swapped. Hand analysis completed it
to [b/(ba)].[ba/w].bigsym = (j, i); the corrected sweep then surfaced
the clean form [b/w]bigsym directly (replacement "b" instead of
"ba" — no shave needed). The first run had an indexing bug in the
constant table (consts[idx - NCONST] where it must be consts[idx -
NLIB]), which mislabeled the flagged combos; the flagged behavior
itself was real and survived the fix. The bug is why "R#13" denoted
"ba": the accident pointed at the right constant.

**Prov.** prov(E_swap, w) = (0, 1, ..., n-1) minus {i}: every a-atom
survives exactly once (the match deletes exactly one of the two
label-copies of each merge atom — the last i of the left run and the
first j of the right run), the original b-atom dies in merge, and the
output's b is a constant. So prov is ascending, injective, of length
n-1: NOT DB (DB needs all n labels, descending), on any input — no
interaction with Theorem 3 or the budget conjecture. The laundered
composition L_a.L_b.E_swap (round-12 laundering, 2|Sigma| = 4 extra
passes) computes the same function with prov == () everywhere over
Sigma = {a,b} — C4 in 13.8.

**The involution.** E_swap . E_swap = id on the one-b language (C5):
substituting E_swap for the input inside E_swap makes the pattern
E_swap(w) = a^j b a^i and leaves bigsym unchanged (merge(E_swap(w)) =
a^{i+j}); the complement of (j, i) in (i+j, i+j) is (i, j). The
construction is an involution, as rev is.

### 13.5 Task 1: the converse of the 12.3 reduction — OPEN, cleanly
### separated

Task 1 asked: does "E computes rev on F" imply "some E' computes
left-run on F"? Status: OPEN — but round 13 separates it from
rev-on-F for good:
- rev-on-F is TRUE (13.4). If the converse held, the split would be
  computable; the machine says it is not reachable at depth <= 2 even
  with the swap values swapv = (j,i) and swapR = (j,i+1) available as
  library values (13.8 Part 1: split-i 0, split-j 0 over the enriched
  library, 720,280 sims).
- Closure evidence against: the swap adds no new merge-type
  information (merge.E_swap = merge, bigsym.E_swap = bigsym,
  E_swap.E_swap = id — all verified or immediate); lock-deleting
  THROUGH E_swap's output needs a pattern whose leading run is j —
  the right run of w — i.e. split-type knowledge again (13.3's
  lock-deletion mechanism, circular); and collapse-back persists:
  [eps/w]C(w, Z) = Z (deleting the input from a concatenation
  returns the rest — C6b).
So: SPLIT ⟹ REV-ON-F (12.3, proved) and REV-ON-F holds (13.4);
SPLIT remains OPEN and strictly stronger unless the converse holds.

### 13.6 What is NOT the wall (failed invariant candidates, recorded)

- Semilinearity / piecewise eventual affineness: contains the swap;
  the piecewise difference (13.3) is constructible.
- "No unbounded b-free length <= j": refuted by halfmrg =
  ceil((i+j)/2) on i <= j.
- Separability of runs / common affine maps alone: the
  concatenation C breaks it (bigsym re-arranges runs non-locally;
  this is precisely the construction's engine).
- Anchored-window calculus alone (13.2): complete for ONE pass, and
  the construction lives inside it — the calculus was the tool that
  PROVED the construction, not an obstruction.

### 13.7 THE WALL, relocated: interior exactness at >= 2 separators

[ROUND 15 CORRECTION OF RECORD: the parenthetical below — "distinct
rare letters change nothing" — is REFUTED.  Lane C's T1 (round 15,
15.2) computes rev on the FULL mixed-letter all-varying family
{a^i b a^j c a^k} with E_mix; the same holds at any number of
DISTINCT separators (round 15B, 15.4).  What survives of this
section is the SAME-SEPARATOR wall: clause (c)'s two-b-complement
analysis stands (and round 15's wall analysis proves its final-pass
form with three suppliers, 15.5), but the strategy class was too
narrow — the evasion is the merge-flavored one-b shave with an
oversupplied middle, which never isolates the middle run, and which
only distinct letters enable (unique-letter projections build the
complement boxes).  The surviving content question is {a^i b a^j b
a^k} alone — see 15.5 (V_h).  ROUND 15C, FINAL: that question is
now ANSWERED — E_rev computes rev on W2 = {a^i b a^j b a^k} by
MERGE-CATALYZED SELECTIVE DELETION (17.1): concatenating the merge
next to the input gives one separator an unbounded adjacent run,
so a merge-flavored pattern fires there unconditionally and at
the other separator never — the one-b projections P1, P2 ARE
constructible, and with them the transplant skeleton.  The wall
below is BYPASSED, not broken: no middle-run isolation ever
happens (the K('a') pad and the +1 are paired edge-guards), and
clause (c)'s interior-exactness analysis was never invoked by the
winning construction.  The same-letter clause of this section now
has NO surviving content question at fixed separator count;
the frontier moves to VARYING separator count (17.5).]

Why the trick does not lift to w2 = a^i b a^j b a^k (or
{a^i b a^j c a^k} — distinct rare letters change nothing [REFUTED,
round 15: see the bracketed correction above]):

(a) The direct lift is dead: [b/w2]big2 with big2 =
    C([eps/b]w2, b, [eps/b]w2) NEVER FIRES (the pattern w2 has two
    b's, big2 one — 13.1(b)); machine-verified concretely (C6a).

(b) The one-step classification at two b's (calculus level, PROVED
    from 13.1): every pass on a two-b text is (i) a b-free pattern
    acting by ONE common eventually-affine map on ALL runs; (ii) a
    one-b-pattern edit applied greedily at each b whose local
    context (as left by earlier firings of the same pass) suffices —
    the SAME edit at every firing b, no per-b choice; or (iii) a
    two-b-pattern edit, which by interior exactness (13.1(a))
    requires the pattern's interior run to EQUAL the text's interior
    run — on w2, exactly j.

(c) The complement route quantified — and it dies twice. For the
    two-b pattern w2 = (i, j, k) to fire at all, the text must have
    two consecutive b's whose interior run has length EXACTLY j
    (13.1(a)); the window then consumes that interior run entirely
    (the interior remnant is 0, always — matching w2 can never leave
    a middle remnant). So the complement of w2 in a text is a PAIR
    of flank remnants (L - i, Rg - k) around whatever the
    replacement resupplies. For the output to be the swap (k, j, i):
    the leading flank must contribute k, so the text's run left of
    the anchor pair must be i + k (up to a constant) — the SUM OF THE
    TWO FLANKS = merge minus the middle run: middle knowledge; and
    the output's middle j must be RESUPPLIED by the replacement,
    whose interior run must be exactly j: middle knowledge again.
    Every branch of the complement route requires middle-run
    isolation — the two-b analogue of the split — while the one-b
    case has NO interior runs at all: the degenerate case of
    interior exactness is vacuous, the anchor does the splitting
    for free, and the replacement needs only constants. THAT is why
    one-b is free.

(d) Collapse-back persists at two b's ([eps/w2]C(w2, Z) = Z, C6b),
    and constant-flank one-b patterns address the two b's only
    symmetrically (case (ii) of (b)).

(e) Machine: the two-b frontier sweep (depth <= 2 over a 7-value
    two-b library: w2, mrg2, big2, ww2, w2mrg, [bb/b]w2, [ba/b]w2,
    + constants; grid 6x6x6): 143,388 sims — rev(w2) 0, the three
    splits 0, flank-progress (k, *, i) 0 (13.8 Part 2).

ROUND 14 target: the two-b battlefield — either the
interior-exactness INDUCTION (an invariant of reachable run vectors
under passes AND concatenations that excludes middle-run isolation
for every depth; strictly harder than 13.2 because C composes run
vectors freely), or a construction that breaks it. Honest caveat:
one-b was also suspected hard before this round — 13.7 is a
statement about the symmetrization/complement STRATEGY class and
the depth <= 2 sweep, not an impossibility proof.
[ROUND 14 RESOLUTION, in part: the wall is at VARYING interior runs,
not at >= 2 separators as such — the coordinator found the missed
fixed-middle positive stratum during verification, and round 14
settles it optimally with c(M) = 0 (14.2); the induction question
against all-varying W2 begins in 14.5, where the first tier (the
total-type calculus) closes the SPLIT side and is handed to the
parallel lanes.]

Program impact: rev-not-in-L over fixed alphabets can no longer be
argued through one-separator families at ANY level (prov: 12.2;
content: 13.4). Over UNBOUNDED alphabets the DB program is untouched
(one-b inputs are not distinct-character inputs). The fixed-alphabet
content question now lives entirely at >= 2 separators WITH VARYING
INTERIOR RUNS — round 14 corrected this boundary from the positive
side: every FIXED-interior family {a^i M a^k} falls to the
symmetrization engine with c(M) = 0 (14.2), so the surviving content
question is {a^i b a^j b a^k} over Sigma = {a,b}, or {a^i b a^j c
a^k} with distinct rare letters (interior exactness is letter-blind —
same wall).  [ROUND 15: the second disjunct is REFUTED — T1 (15.2)
computes rev on {a^i b a^j c a^k}, and round 15B (15.4) on every
distinct-separator all-varying family at any k; "letter-blind" was
the error — distinct letters are precisely an ADVANTAGE (unique-letter
projections).  The surviving content question is the same-letter
family {a^i b a^j b a^k} ALONE, reduced in 15.5 to the constructibility
of V_h.  And over unbounded alphabets the DB program has since CLOSED
the other way: lane E's separable rigidity (15.6).]

### 13.8 Machine verdicts (round 13)

- **verify_round13.py part A** (match anchoring + one-b calculus,
  40,000 random trials, string level): A1 13,246 / A2 13,291 /
  A3 3,653 / A4 4,424 / A5 13,246 cases, 0 violations. VERIFIED.
- **part B** (lcore catalogue on the 8x8 grid): B1 the ten
  constructions of 13.3 (incl. the diff boundary i = j); B2 the
  flank-swap mechanism; B3 lock-deletion. VERIFIED.
- **part C** (the construction, prov.py/lcore): C1/C2 E_swap (both
  forms) computes rev on the FULL one-b language — 14x14 grid
  including the boundaries i = 0 / j = 0, plus 1,000 random (i,j) to
  250; C3 prov = ascending labels minus the b; C4 laundered
  L_a.L_b.E_swap: rev with prov == () (grid + 300 random); C5 the
  involution E_swap.E_swap = id; C6 the two-b lift dead ([b/w2]big2
  never fires; [eps/w2](w2.b) = b). VERIFIED.
- **round13_sweep.c** (0.5 s, grid 10x10 one-b / 6x6x6 two-b):
  Part 1 (enriched 15-value library incl. swapv/swapR + 8 constants,
  121,930 + 598,350 sims): the UNIQUE non-circular SWAP hit at depth
  1 is [b/w]bigsym — the construction; 3 non-circular half-swap
  seeds ([ba/w]bigsym, [b/shrinkR]bigsym, [ba/shrinkR]bigsym);
  all other swap hits (215 + 244) are circular (they
  use swapv/swapR as given values); SPLIT-i 0, SPLIT-j 0 everywhere.
  Part 2 (two-b frontier, 56,952 + 86,436 sims): rev 0, splits 0,
  flank-progress 0. Caps 0 (no replacement explosion; capping is
  sound — expected outputs are at most 21 chars, so any capped
  evaluation fails equality by length alone).

### 13.9 Honest ledger for Round 13

- PROVED: Lemma Match Anchoring (13.1); the one-b pass calculus
  (13.2: common eventually-affine run maps; anchored remnant algebra
  (x-p0+r0, y-p1+r1); b-explosion; multi-b vacuity; pass-free
  affine-run structure and constants-only b-free pass-free values);
  the complement lemma (13.4); **Theorem: E_swap = [b/w]bigsym
  computes rev on {a^* b a^*}** — the round's target, construction
  side; prov(E_swap, w) = ascending minus the b; laundering
  composition: rev with prov == () on the one-b language over
  Sigma = {a,b}; E_swap is an involution; the two-b one-step
  classification (13.7b); the corrected 12.3 scope note.
- VERIFIED ON STATED DOMAINS: 13.8 in full (anchoring/calculus
  random trials; catalogue and mechanisms on grids; the construction
  on grid + random; sweeps at depth <= 2).
- CONJECTURED: nothing new. (The split conjecture stands, now
  strictly stronger than the true rev-on-F.)
- OPEN: the split problem on F (no construction; no impossibility;
  depth <= 2 excluded over the enriched library); the converse of
  the 12.3 reduction (13.5); the two-b battlefield — rev on
  {a^i b a^j b a^k} and {a^i b a^j c a^k} (round 14); the
  run-vector invariant induction for multi-b values under passes AND
  concatenations; whether any rev-computable family can have two
  separators (the construction's engine — symmetric merge + single
  anchor + complement — provably dies there, but other engines are
  not excluded).
  [ROUND 14, in the ledger's spirit of updating in place: the split
  problem CLOSED NEGATIVELY (14.5.2 Corollary 1, via the total
  sum-type calculus — with the Lemma S formalization gap named
  there and under adversarial scrutiny by the parallel lanes); the
  12.3 converse's failure explained at its root (its extraction
  step needs Corollary-1-forbidden values); the two-separator
  question CLOSED POSITIVELY with the varying-interior qualifier:
  fixed-middle families at EVERY separator count are rev-computable
  with c = 0 (14.2); the two-b battlefield remains open, now owned
  by the parallel construction/invariant lanes; the run-vector
  induction's first tier (totals) is done, the run-level tier
  (residues) is the open part.]
  [ROUND 15: the two-separator question CLOSED POSITIVELY — distinct
  letters at two separators (T1, 15.2) and at EVERY separator count
  (15B, 15.4), all-varying included; the mixed-letter disjunct of the
  surviving content question REFUTED (15.1); the two-b battlefield is
  now exactly the same-letter family {a^i b a^j b a^k}, reduced to
  the constructibility of V_h (15.5) — the live front, lane D.  The
  split's negative status upgraded: Lemma S repaired and confirmed
  under lane B's adversarial scrutiny (15.7), Schema P owned (14.5.2),
  so Corollary 1 is proved on the non-explosive stratum and
  proved-conditional-on-Schema-P in general.]

### 13.10 Files

- `verify_round13.py` / `round13_verify.log` — parts A/B/C, 4.7 s.
- `round13_sweep.c` / `./round13_sweep` / `round13_sweep.log` — the
  depth-<=2 falsification sweeps (one-b enriched library + two-b
  frontier), 0.5 s.

---

## 14. Round 14: fixed middles, the calculus fact, and the reduction

### 14.0 Charter and scope

The round-14 charter (coordinator, after their line-by-line verification
of round 13): (1) the general fixed-middle theorem; (2) the calculus
fact (no constant shaved off a b-free run by b-free means); (3) refine
13.7's program statement; (4) main event, the all-varying two-b family
W2 = {a^i b a^j b a^k}: (a) the REDUCTION question (does rev on W2
imply the split?), (b) invariant induction or construction; (5) an
enriched sweep including C-shaped scrutinees and shave-type values.

Mid-round SCOPE CHANGE (coordinator): the campaign went parallel.  I
retain 1-3 and 4(a); the invariant-induction and construction lanes
(4b, 5) were assigned to parallel agents (constructions, run-vector
invariant, split head-on, unbounded-alphabet DB).  The reduction
analysis (14.5) nevertheless derived the total sum-type calculus, which
bears directly on the split lanes; it was relayed immediately, the
coordinator ran an independent signature check (below), and lanes B/C/D
received it with attack points.  This section integrates what landed in
my lane; the parallel lanes' findings arrive separately.

Hard rules unchanged: theory problem, no brute force; every run <= 60 s;
C/C++ for anything CPU-bound; the machine only falsifies or discovers
cheaply — never proves.  (One process slip this round, corrected: the
first tdiag check ran 62.6 s; it was rewritten to 2.1 s.  The cap is
what keeps the machine subordinate to the analysis.)

### 14.1 The self-anchoring lemma

Throughout, a is the flank letter; "non-flank letter" means any letter
!= a.  For a string M let M^R be its reversal.

**Lemma 14.1 (self-anchoring).** Let M in Sigma^+ contain at least one
non-flank letter.  Then:
(i) for all i, k >= 0, M occurs exactly once in a^i M a^k (at offset i);
(ii) for all i, k, L >= 0 with L >= max(i,k), the string a^i M a^k
occurs exactly once in a^L M a^L (at offset L - i).

*Proof.*  (i) Let s_1 < ... < s_d be the offsets of M's non-flank
letters (d >= 1).  If M occurs at offset p, then for each r the text
letter at p + s_r equals M[s_r] != a, so p + s_r is a non-flank
position of the text.  The text's non-flank positions are exactly
i + s_1 < ... < i + s_d — d of them, since the flanking a^i, a^k
contribute none.  So {p + s_r} is contained in {i + s_r}, and both
sets have d elements, hence are equal; comparing their increasing
enumerations gives p + s_r = i + s_r for all r, so p = i.  The
occurrence at p = i is M itself.  (ii) The pattern a^i M a^k has the
same d non-flank letters, at pattern-offsets i + s_r; an occurrence at
offset p in a^L M a^L forces {p + i + s_r} = {L + s_r} by the same
counting, hence p = L - i; the window then fits and matches exactly
when L >= i (leading a^i lands inside the left a^L) and L >= k
(trailing a^k inside the right a^L), both of which hold.  Uniqueness
follows since every occurrence must sit at L - i.  ∎

Letter-blind: only the flank letter matters; 'b', 'c', mixed alphabets
are the same proof.  Machine: part C, 20,000 random trials, no
violation.  The lemma is the reason a fixed M can serve as its own
anchor: no spurious occurrences exist to derail the greedy scan, at
any flank lengths, including the boundaries i = 0 and k = 0.

### 14.2 The fixed-middle theorem, optimal form

**Theorem 14.2 (fixed middles, c = 0).** Let M in Sigma^+ contain at
least one non-flank letter.  Then

    E_M = [M^R / X] . C( [eps/M]X ,  M ,  [eps/M]X )

computes rev on the FULL family {a^i M a^k : i, k >= 0}.  In
particular the boundary constant is c(M) = 0 for every admissible M.

*Proof.*  Let w = a^i M a^k.  The shave [eps/M]X: by 14.1(i), M occurs
exactly once in w, at offset i, and the greedy leftmost scan deletes
exactly that window (positions before offset i are a's only, and M has
a non-flank letter, so no occurrence starts there); the output a^{i+k}
contains no M.  The scrutinee is C(a^{i+k}, M, a^{i+k}) = a^L M a^L
with L = i + k.  The pattern is X = w = a^i M a^k, which by 14.1(ii)
occurs exactly once in the scrutinee, at offset L - i = k; the window
consumes the last i a's of the left run (available: L >= i), M
exactly, and the first k a's of the right run (available: L >= k), so
the match always fires, for all i, k >= 0 — no boundary restriction.
The pass deletes the window and inserts the replacement M^R, and the
scan never rescans inserted text, so it terminates; the output is
    a^{L-i} . M^R . a^{L-k} = a^k M^R a^i = rev(w).  ∎

Remarks.
(a) Optimality: the coordinator's junction-shave stratum (14.3)
achieves the same families with boundary constants c in {1,2}; the
direct shave [eps/M] needs none.  c_min(M) = 0 for every admissible M.
(b) Unification: M = 'b' gives E_b = [b/X].C([eps/b]X, b, [eps/b]X) —
exactly round 13's E_swap (content-identical on the grid; machine part
B).  Round 13's one-b construction is the M = 'b' point of a family
that now covers every separator count and every interior structure.
(c) Degenerate M = a^d (pure filler): the family {a^i a^d a^k} = a^*
carries rev = identity, trivially computable; but the ENGINE fails —
[eps/a^d] fires at every offset of every a-run, so the shave is not
the merge.  The theorem's hypothesis (a non-flank letter in M) is
exactly what makes 14.1 apply.  When M = a^d ... with a non-flank
letter inside, the family is a fixed-middle family and the theorem
applies with c = 0.
(d) prov: prov(E_M, w) is an ascending subsequence of the labels minus
M's labels — injective, |prov| = i + k < n, so never DB (DB needs all
n labels); machine-verified (part B).  Laundering: L_a.L_b.E_M
computes rev with prov == () (verified for M = 'bab', part E) — the
round-13 laundering composes unchanged.
(e) Consistency with 14.5: E_M's scrutinee total is (2,2)-diagonal in
(i,k); nothing here contradicts the total sum-type calculus.

Machine: part B — 28 middles (all five seed M, M = 'b', and 23 more
including multi-letter, alternating, and near-periodic M), full family
{i,k >= 0} grids + 400 random per M: ALL VERIFIED; prov checks pass.

### 14.3 The junction-shave stratum (the coordinator's seed)

The coordinator's construction (their machine-verified instances; part
A re-verifies all five): E_M = [a^c M^R a^c / w].C(shave_M, M,
shave_M) on {a^i M a^k : i, k >= c}, where shave_M is a composition of
one-b junction-anchored deletions [eps/(a^x sigma a^y)].  The general
tiling behavior:

**Proposition 14.3 (single-pass junction shave).** Let M =
a^{mu_0} b a^{mu_1} b ... b a^{mu_m} (m >= 1 junction b's; the
mixed-letter case composes one pattern per junction letter).  For the
one-b pass [eps/(a^x b a^y)], on the firing region
    i + mu_0 >= x,   mu_t >= x + y  (1 <= t <= m-1),   mu_m + k >= y,
every junction window fires (greedily left to right, each window's
flanks eating into the runs diminished by the previous window), and the
output is a^{i+k-c} with
    c = (x - mu_0) + sum_{t=1}^{m-1} (x + y - mu_t) + (y - mu_m).
c can be negative (interior remnants survive).  The coordinator's
instances are the rigid case x + y = mu_t for all internal t (interior
exactly consumed): 'bab' (x,y) = (1,0), c = 1; 'baab' (2,0), c = 2;
'babab' (1,0), c = 1; 'bb' (0,1) or (1,0), c = 2; 'baac' composes the
b-window (2,0) and the c-window (2,0), c = 2.

*Proof.*  Counting: the first window eats x from the merged left run
(i + mu_0), each internal window eats y (trailing of its predecessor's
junction) + x (its own leading) from the internal run mu_t, the last
eats y from mu_m + k.  Every b dies, the survivors merge; the output
length is (i + mu_0 - x) + sum(mu_t - x - y) + (mu_m + k - y) =
i + k - c with c as claimed.  (Machine part B3: 2,045 in-region random
trials, exact match.)  ∎

Two lessons recorded.  (1) The coordinator's 'bb' cautionary note
(hand-derivation slip caught by the machine, c = 2 not 1) is a
manifestation of the proposition: derive c from the firing structure,
never by eyeball.  (2) The stratum is non-optimal: [eps/M] gives c = 0
on the full family (14.2) — e.g. 'bb' via [eps/bb], junction letters
not even needed as anchors.  What the stratum isolates is the MECHANISM
by which constants can be shaved at all: the junction letters let a
window reach INTO the flanks from inside M.  That mechanism is the
subject of the calculus fact, and it is why the fixed-middle engine is
essentially junction-mediated.

### 14.4 The calculus fact (charter item 2)

**Lemma (psi; 13.2(i) restated).**  [a^r/a^p] maps each a-run a^u to
psi(u) = r*floor(u/p) + (u mod p): greedy tiling from the left, the
leftover at the right end of the run.  (Machine D1, string level.)

**Theorem 14.4 (no constant shave).**  Let F be a composition of
b-free/b-free passes [a^{r_s}/a^{p_s}], s = 1..n.  If F's induced run
map equals u -> u - c for all sufficiently large u, then c = 0.

*Proof.*  Let Pi = prod_s p_s and Lambda = prod_s (r_s/p_s).  Claim:
for every t >= 0, F(Pi*t) = Lambda*Pi*t EXACTLY.  Induction through
the passes: before pass s the current length is
u_{s-1} = (Pi/(p_1...p_{s-1}))*(r_1...r_{s-1})*t, and Pi/(p_1...p_{s-1})
still contains every later p_j (j >= s) as a factor, so u_{s-1} = 0
mod p_s: the pass fires exactly u_{s-1}/p_s windows with zero
remainder, mapping it to (r_s/p_s)*u_{s-1} exactly.  So F(Pi*t) =
Lambda*Pi*t with no additive constant.  If F(u) = u - c for all
u >= U, then for all large t, Lambda*Pi*t = Pi*t - c, i.e.
(1 - Lambda)*Pi*t = c for arbitrarily large t; hence Lambda = 1 and
c = 0.  ∎

**Corollary.**  A nonzero constant can never be shaved off a b-free
run by b-free means.  The junction shaves of 14.3 work only because
their windows are anchored at M's junction letters, eating into the
flanks from inside M.  This strengthens 13.2(i): there the affine form
of the run map was established; now the constant case is pinned —
slope-1-and-shift is impossible, the shift must be 0.  (Machine D2:
all 15,625 compositions of depth 3 over p, r in [1..5]; the only tail
translations u - c have c = 0.)

### 14.5 The reduction question (charter item 4a)

The SPLIT on W2 = {a^i b a^j b a^k : i,j,k >= 1} is an expression
computing w2 |-> a^j (equivalently w2 |-> b a^j b: the two forms are
interdefinable via [eps/b] and C(K(b), ., K(b))).

#### 14.5.1 The forward direction: SPLIT implies REV-ON-W2

**Theorem 14.5a.**  If some E_mid computes w2 |-> a^j, then

    MID  = C(K(b), E_mid, K(b)),
    E_rev = [MID/X] . C( [eps/MID]X , MID, [eps/MID]X )

computes rev on W2.

*Proof.*  MID = b a^j b is a PALINDROME: MID^R = MID, so the
replacement needs no extra machinery — the computed value serves as its
own reverse.  w2 = a^i MID a^k, so the engine of 14.2 applies verbatim
with computed middle: [eps/MID]X = a^{i+k} (14.1(i), MID has non-flank
letters); the scrutinee is a^{i+k} MID a^{i+k}; the pattern X = w2
occurs exactly once in it (14.1(ii) with L = i+k); the window fires;
the output is a^k MID a^i = a^k b a^j b a^i = rev(w2).  ∎

Machine (part E): E_mid instantiated by constants K(a^j), j = 1..6 —
the engine verified on every fixed-j slice (9x9 grids + 300 random
each).  This validates the engine (the W6 pattern); the hypothesis —
a NON-constant E_mid — is the split.  As proved next, that hypothesis
is false, so:

**the forward reduction is TRUE but VACUOUS.**

#### 14.5.2 The total sum-type calculus

This subsection is the analysis instrument.  It corrects itself twice
in the telling — the honest record includes both corrections.

For a string s let |s|_a, |s|_b be its a- and b-counts, and for an
expression E let N_E, M_E be the a-/b-counts of its value at the input
w2 = a^i b a^j b a^k.  Write S = i + j + k.

**Lemma 14.5b (exact per-pass accounting — THE reason).**  For a pass
[R/P]F, with c_w the number of greedy windows,

    N_out = N_F + c_w*(N_R - N_P),      M_out = M_F + c_w*(M_R - M_P),

exactly, at every input.  THE REASON this is exact: the greedy scan
never rescans inserted text — every window is an occurrence of the
pattern in the ORIGINAL text, windows are disjoint in original
coordinates, and no window can consume replacement atoms within the
same pass.  So each window removes exactly the pattern value (a-count
N_P) and inserts exactly the replacement value (a-count N_R), and the
order of the greedy selection is irrelevant to the total.

*Proof.*  Immediate from the semantics: the output is the original text
with the c_w disjoint windows replaced by c_w copies of R; a-counts and
b-counts add over disjoint pieces.  ∎

**Lemma S (structure — repaired form, R1–R5 folded in this round).**
For every expression E over {V(0)} and constants there is a LOCALLY
FINITE partition of the parameter space [1,infinity)^3 into CELLS —
finite on every bounded region {S <= S_0} (R1) — such that on each
cell, every window count of every pass in E is a function of S = i+j+k
alone, and so are the totals N_E, M_E.  Read precisely: the totals are
S-functions ON EACH CELL (the cells carry residue classes of (i,j,k)
mod constant moduli), equivalently f(S) + O(1) per residue family —
NOT necessarily functions of S on all of [1,infinity)^3 (see scope
note (3), ST2).  The cells are obtained by an ORDERED refinement (R3):
first (c) SLAB levels {m*g <= f < (m+1)*g} pinning the tile counts of
computed moduli (g a pinned-polynomial modulus function, f a LONG-RUN
length of the value — see the profile in Schema P below; only the
boundedly many long runs need slabs, so the levels are locally
finite); then (b) RESIDUE classes of (i,j,k) modulo constants (making
run lengths and block residues honest pinned polynomials); and only
then (a) COINCIDENCE cutting, whose conditions are pinned-POLYNOMIAL
(in)equalities — not affine: post-explosion, firing conditions are
curved (quadrics).  A nonzero polynomial cannot vanish on an open set,
so the coincidence argument survives; cells are full-dimensional
pieces of a locally finite arrangement of algebraic hypersurfaces cut
by residue slabs.

*Proof (by induction on E, jointly for all sub-expressions;
reorganized per lane B's R2 skeleton — the count analysis never needs
run-level S-functionality, only the value PROFILE of Schema P, stated
with its status immediately after the scope notes below).*  V(0):
N = S, M = 2;
one cell.  K(s): constants; N, M constant — functions of S.  C:
totals add; the common refinement of the parts' cells.  S(R,P,F): the
cells are the ordered common refinement of F's, P's, R's cells (IH)
plus this pass's conditions.  The window count c_w decomposes by
pattern type:
  (i) TILING patterns, CONSTANT modulus p (b-free patterns of
  constant length; adjacent-letter patterns such as 'bb'): the
  windows tile runs of one letter, and summing over ALL runs of that
  letter (runs shorter than p contribute floor = 0, so the sum is
  unrestricted),
      c_w = sum_t floor(f_t/p) = (N_F - R_tilde)/p,
  where N_F, the letter-total, is an S-function by IH, and R_tilde =
  sum_t (f_t mod p) decomposes by the value's profile: each LONG run
  (boundedly many, pinned-polynomial lengths — Schema P) contributes a
  residue PINNED by the cell's residue classes; each periodic block
  (template U repeated m_g times) contributes sigma_U * m_g + O(1),
  where sigma_U = the residue sum of U's runs over one period is
  pinned by the residue classes.  By the Template Sum Lemma (Schema P
  below), the multiplicities m_g of all blocks sharing a template U
  sum to the creating pass's window count — an S-function by IH.  So
  R_tilde = sum_U sigma_U * (S-function) + pinned, an S-function up to
  pinned constants, and c_w is an S-function on the cell.
  (ii) COMPUTED-modulus patterns (b-free, g = N_P = Lambda_P*S + nu_P
  with Lambda_P > 0; if Lambda_P = 0 the modulus is piecewise-constant
  on cells and case (i) applies): windows can live only in the value's
  LONG runs — periodic blocks have constant-period run lengths, below
  g for all large S (a pinned comparison) — and there are only
  boundedly many long runs (Schema P).  On each, the tile count
  floor(f_t/g) is slab-pinned; with g = Omega(S) and f_t
  pinned-polynomial, the slab levels range over O(S) values on
  explosive strata — locally finite, finite on every {S <= S_0} (R1) —
  and c_w, the sum of the pinned slab levels, is a pinned function of
  S on each cell.  [This replaces the earlier "every run is O_E(S)"
  step, which is FALSE on the explosive stratum: [merge/'bb'].[b/a]X
  has a Theta(S^2) run while g is Theta(S), and the tile count there
  is Theta(S), not bounded.  The conclusion survives by this
  reorganization — long-runs-only — not by boundedness of the counts.]
  (iii) ANCHORED and adjacent patterns — every pattern bearing a
  non-flank letter, INCLUDING the case R4 showed was missing from the
  original writeup: single-b patterns with ZERO interior runs ('ab',
  'ba', 'aab', 'abb'-type), which are neither tiling (no single-run
  tiling) nor anchored-with-positive-interior.  Every firing site is a
  position of the value's b-skeleton; the firing condition is a
  conjunction of pinned-polynomial (in)equalities (flank fits;
  interior coincidences — Match Anchoring 13.1 makes interiors exact,
  and the coincidence conditions are pinned-polynomial by R3's
  ordering).  The sites split into boundedly many BOUNDARY sites
  (O(1) per singular region, each firing pinned on the cell) and the
  interiors of periodic blocks, where all sites are locally
  indistinguishable — the pattern sees the same bounded context at
  each — so the count is uniform per template: (per-site fires or
  not, pinned) x (total multiplicity of the template, an S-function
  by the Template Sum Lemma), plus the boundary corrections.  c_w is
  an S-function on the cell.
  In all three cases, by 14.5b, N_out = N_F + c_w(N_R - N_P) and
  M_out = M_F + c_w(M_R - M_P) with every factor an S-function on the
  cell (products of S-functions are S-functions) — hence S-functions.
  Local finiteness of the refinement: each pass adds, relative to the
  locally finitely many cells of its sub-expressions, slab levels over
  boundedly many long runs (locally finite), residue classes modulo
  constants, and coincidence cuts by nonzero pinned polynomials (each
  removes a nowhere-dense set); a finite expression yields a locally
  finite partition, finite on every bounded region.  ∎

Honest scope notes on Lemma S, post-repair (R1–R5 + ST2 folded in;
lane B's adversarial round CONFIRMED the lemma with these five
repairs, none fatal to the corollary).  (1) R1/R3: "finite partition"
was FALSE as stated — slab pieces are indexed by pinned tile count m,
and on explosive strata runs are Theta(S^2) while computed moduli g
are Theta(S), so m ranges over Theta(S) values; the correct statement
is LOCALLY FINITE (finite on each bounded region), which is all the
corollary uses.  Likewise the original applied "two affine functions
equal on a full-dimensional piece" inside case (ii) while conceding
run-level affinity fails; the repaired proof pins slabs first, then
residues, and only then cuts by coincidence, where conditions are
pinned-POLYNOMIAL — the ordering matters, and lane B's dissected box
flag (idx 455: a mod-3 sawtooth, a-content = S + jitter in {0,2,4}) is
a live demonstration that a slope test without prior residue pinning
produces false violations.  (2) R2: the original case-(ii)
boundedness claim ("every run is O_E(S)") is false on the explosive
stratum — repaired above by the long-runs-only reorganization.  The
proof now rests on ONE auxiliary, the value PROFILE of Schema P
(boundedly many long runs + periodic blocks with template-group
multiplicities), stated and largely proved immediately after
Corollary 2; until its transformer table is complete, Lemma S is
PROVED unconditionally on the non-explosive stratum (the profile is
trivial there: boundedly many runs, no periodic blocks) and
VERIFIED-ON-STATED-DOMAINS beyond it (lane B: ~45,000 random + 39
adversarial expressions to depth 5, every flag dissected to a
residue-class artifact; the idx 3372 periodic step function — support
fluctuating non-monotonically with period-4 residues on slice S=27 —
is a confirmation specimen of multi-piece residue x slab structure).
(3) ST2 and the correct reading of the conclusion: the S-exact
(residue-less) reading is DEAD — the halver [a/aa]X (replacement
first) has total ceil(i/2)+ceil(j/2)+ceil(k/2), not a function of S
(S=5: (2,2,1)->3 vs (3,1,1)->4) — but on each mod-2 cell of (i,j,k)
the total is exactly (S+#odd)/2, an S-function per cell
(machine-verified by the coordinator, verify_round15.py part G).  The
totals must be read as S-functions ON CELLS, or globally as f(S) +
O(1); ST2 kills only the residue-less reading.  Lane C's ST1 (the
quadratic [merge/'bb'].[b/a]X) likewise killed the AFFINE reading
only.  (4) RUN-level affinity FAILS in general: residue runs f mod g
with computed g are not piecewise affine (the i mod j phenomenon).
The totals survive; the run-level tier (lane D's assignment) must
handle residues.  (5) My first version of this lemma claimed piecewise
AFFINE-DIAGONAL totals; that is FALSE in general and the machine
refuted me before I wrote it down: the expression [merge/"bb"].[b/a]X
(b-free pattern with b-bearing replacement explodes w2 to b^{S+2};
the adjacent-b pattern "bb" then tiles it with merge = a^S) has
a-count S*floor((S+2)/2) — QUADRATIC in S (machine-verified exactly at
four points).  The correct general invariant is "function of S alone";
the affine-diagonal form holds on the non-explosive stratum — all of
rounds 13-14's constructions and the entire sweep stratum — where it
was machine-checked (below).  (6) Methodological caveat relayed by
lane B: under locally-finite Lemma S, slice support may legitimately
grow ~S on explosive strata, so the anti-diagonal support signature is
a valid falsifier only on the non-explosive stratum; per-piece claims
on explosive strata need the path/step test (w2path.c) — this affects
the interpretation of the 3,368-E line battery, which is
non-explosive-valid.

**Schema P (the pinned-polynomial profile — R2's induction, OWNED
this round: precise statement, the analytic core PROVED, the residual
table specified exactly).**  This is the auxiliary that the repaired
Lemma S rests on.  Fix E and the input w2 = a^i b a^j b a^k.

*Definition (profile).*  A value V has a PROFILE on a cell C if it is
a concatenation of O_E(1) SEGMENTS, each of one of two kinds:
(S) a SINGULAR run — a maximal same-letter run whose length is a
    pinned polynomial in (i,j,k) with rational coefficients (pinned =
    the polynomial is fixed on C; two adjacent segments ending and
    starting with the same letter merge into one singular run, the
    sum of pinned polynomials being pinned);
(B) a UNIFORM BLOCK — a template U repeated m times, where the
    template U is itself a fixed profile of bounded size (constant
    word, or bounded concatenation of runs whose lengths are
    S-FUNCTIONS on C — the inserted replacements' runs), and the
    MULTIPLICITY m of an individual block is a PINNED POLYNOMIAL on
    C (a tile count of pinned runs; slab-pinned bounded when the
    modulus is computed).  [ROUND 17 REPAIR, site 1 of 3: the
    round-16 text read "...pinned-polynomial runs), and the
    MULTIPLICITY m is an S-function on C" — conflating the
    template-length and multiplicity directions.  The correct
    directions (Lane B round 2, from CH2's autopsy, 17.2):
    individual block multiplicities are pinned polynomials, and
    only the template-GROUP total is an S-function (P1 below).
    A merged singular run that absorbs a PARTIAL group sum has
    length (S-function) x (pinned polynomial) — the product
    direction P4' admits and the old form forbade.]
Blocks created by ONE pass all share ONE template; the block inventory
is a finite map template -> total multiplicity (the multiplicities of
all blocks sharing U, summed).  The b-count of V is an S-function on
C (it is a sub-total of 14.5b's accounting).

*Lemma P0 (leaves and concatenation — PROVED).*  X = w2 has profile
3 singular runs (i, j, k) and two singleton b's; constants have one
constant segment; a concatenation's profile is the junction merge of
the parts' profiles (bounded segments add).  ∎

*Lemma P1 (Template Sum — PROVED; the load-bearing closure).*  For
every template U in the inventory of a value on cell C, the TOTAL
multiplicity Sigma_g m_g over all blocks with that template is an
S-function on C — namely the window count of the pass that created
those blocks (or a fixed sum/difference of such counts, under later
partial deletions, each deletion count being itself case-(iii)-type).
*Proof.*  Blocks with template U are created by one pass [R/P]F whose
replacement value R has profile U up to bounded junction corrections:
every firing inserts one copy of R, so the number of U-blocks created
is bounded by that pass's window count c_w, an S-function on C by the
Lemma S induction (the count analysis (i)-(iii) above).  A later pass
deletes or rewrites block interiors only uniformly (P2 below), in
whole periods, changing each block's multiplicity by a deletion count
that is uniform per template — the total multiplicity moves by
(per-block delta) x (number of blocks) + boundary corrections, both
S-functions (case (iii) again, via P2's site-uniformity).  ∎

*Lemma P2 (Local indistinguishability — PROVED; the bootstrap that
blocks cannot be region-differentiated).*  Within the interior of a
uniform block, every site presents the same bounded context to any
pattern of the pass; consequently no pass can fire at SOME interior
sites of a block and not others of the same template, and no pass can
insert different templates at different interior sites of the same
block.  Region-differentiation of unbounded blocks therefore requires
the regions to carry DIFFERENT templates already — and since a single
pass inserts one template everywhere it fires, and the leaves carry
no blocks (P0), the only region-differentiators available are passes
whose patterns are themselves unbounded (computed values) or anchored
at singular structure.  Computed patterns have pinned counts
(coincidence + slabs, cases (ii)/(iii)); anchored patterns fire at
b-skeleton sites, whose multiplicity per structural role is an
S-function.  Induction on depth: every unbounded block inventory is
created by tiling-periodic insertions with template-group totals =
window counts (P1).  ∎  This is the mechanism-level reason the
asymmetric-multiplicity counterexamples one keeps trying to build
(different sigma_U per region) cannot close: multiplicities enter all
later accounting only through template-GROUP sums, and those are
window counts.

*Lemma P3 (transformer cases — PROVED for the four main classes).*
Each class maps profiles to profiles, preserving the inventory's
S-functionality:
  (T1) b-free constant pattern (length p): tiles every run of the
  letter; singular runs produce leftover chunks (bounded, < p) plus a
  repetition of (R-profile + chunk) — a uniform block whose template
  is R's profile (inductively a profile) and whose multiplicity is
  the run's tile count; the template-group total is c_w (P1).  Junction
  merges are covered by (S).  Product-form singular lengths (f - mg
  with m pinned, sums, and products of pinned polynomials) stay
  pinned polynomials — closure under leftovers, insertions, and
  junction sums.
  (T2) adjacent-letter constant patterns (zero interior runs, R4's
  case): fire at b-skeleton junctions; bounded per singular gap
  (O(1) insertions between singular runs), uniform within blocks
  (P2) — profile preserved with multiplicity shifts that are window
  counts.
  (T3) anchored patterns with constant interiors (Match Anchoring):
  fire at b-skeleton sites with pinned coincidence conditions; O(1)
  firings per singular region; uniform in block interiors (P2).
  (T4) b-free computed patterns (modulus g = Omega(S)): fire only in
  long runs (block periods are constant and fall below g for large S,
  a pinned comparison), at slab-pinned counts — the profile changes
  only at the boundedly many long runs; blocks persist untouched.
  ∎ (Each case: direct from the greedy semantics + P2.)

*Lemma P4 (FINITE partition — added in round 16 as "degree
separation"; the round-16 FORM is REFUTED AS STATED and REPAIRED as
P4' in round 17; the CONCLUSION — finiteness — is kept, its proof
replaced).*  [ROUND 17 CORRECTION OF RECORD: the round-16 statement
— every run length decomposes as A(i,j,k) + P(S), with products
arising only within the S-typed kind or against pinned constants —
is REFUTED by CH2 = [merge/'bb'].[bb/aa]X (Lane B round 2;
machine-verified closed form, coordinator-reproduced, 17.2): on
the all-odd cell the output contains the singular run
a^{S(i+j-2)/2+1} — the product of the S-function S with the pinned
polynomial (i+j-2)/2 — whose k-slope on a fixed-S plane is -S/2,
unbounded, hence not of the form A(i,j,k) + P(S).  Root cause:
merged singular runs absorb PARTIAL template-group sums —
individual block multiplicities are pinned polynomials and only
P1's GROUP sums are S-functions, a distinction the round-16
writeup conflated at three sites (profile (B), P4's
parenthetical, T5's parenthetical — all repaired this round).]
REPAIRED FORM (P4'): in every profile, run lengths live in the
CLOSURE of the two atom kinds — {affine junction parts (pinned
polynomials in (i,j,k), from anchored remnants of the input's
runs); S-function template lengths (the inserted replacements'
runs)} — under sums, products (S-function) x (pinned polynomial),
and exact division (subtract the pinned residue, divide by the
pinned modulus); affine x affine never arises.  CONCLUSION (kept):
on the schema hypothesis the partition of [1,infinity)^3 is
FINITE — not merely locally finite.  *Proof (replaced; SKELETON
level, Lane B round 2 — the Telescope Lemma, 17.2):* finiteness
via exact polynomial division + provenance recursion — over the
S-typed and product directions, exact division of the closure's
polynomials by the computed moduli (deg r < deg g leaves quotient
plus bounded jitter; slab levels pinned); over the multiplicity
direction, the provenance recursion: multiplicities enter the
accounting only through P1's template-group sums, every per-run
count telescopes to a letter total, a prior window count, or a
pinned constant, and each product's factors trace to strictly
smaller depth — boundedly many distinct pinned forms, hence
boundedly many slab levels, residue classes, and coincidence cuts.
∎ (Status: the mechanism is proved and machine-checked at the
formula level; the write-out — the provenance recursion and the
quasi-polynomial closure in full — is the remaining task,
currently unowned.  The round-16 proof's error was not the
enumeration of the refinement conditions but the degree claim it
rested on: the exhibit a^{S(i+j-2)/2+1} is legal under P4' and
illegal under the old form, which is exactly why CH2 was missed.)

*What remains (specified exactly; the residual table's entries, now
THREE after the round-16 patch).*
  (i) computed-value replacements (R itself unbounded) inserted at
  anchored/coincidence sites;
  (ii) nested computed patterns on periodic regions (U^g
  interleavings with g pinned-constant);
  (iii) **T5, EXPLOSIVE TILINGS (added round 16 — the class the
  residual list omitted until the coordinator's patch): b-bearing
  CONSTANT patterns (e.g. 'bb') tiling uniform b-BLOCKS with computed
  (b-bearing) replacements — the stratum of [merge/'bb'].[b/a]X, the
  round-14 quadratic exhibit, and exactly the stratum Lane D's V1
  finding is about.**  T5 is literally T1 for the b-letter on block
  interiors: matches occur at stride |P| throughout the block
  interior (P2 — every interior site presents the same bounded
  context), each firing inserts one copy of R's profile (a profile by
  IH), so the block maps to a uniform block with template = R's
  profile and multiplicity = the tile count (an S-function WHEN the
  tiled run is a merged GROUP — the b-runs sum to M_F, an
  S-function by IH, residues pinned by the cell's classes; a
  PINNED POLYNOMIAL when the tiled run is an individual run —
  CH2's (i-1)/2, j/2, (k-1)/2 — only the group total being an
  S-function), the template-group total is
  the window count (P1), and same-letter junctions merge into
  products (S-function) x (pinned polynomial) — [ROUND 17 REPAIR,
  site 3 of 3: the round-16 text read "multiplicity = the tile
  count (an S-function: ...)" flatly, and called the junction
  merges "pinned PRODUCTS of pinned polynomials", conflating the
  template-length and multiplicity directions — CH2's
  a^{S(i+j-2)/2+1} is the (S-function) x (affine) instance (a
  merged singular run absorbing a PARTIAL group sum: the tiles of
  the first two b-runs but not the third), and the round-14
  exhibit a^{S*floor((S+2)/2)} is the (S-function) x (pinned
  polynomial in S) instance, residue-refined — both legal under
  P4', both impossible under the round-16 form].  The single-pass
  mechanism is thus proved exactly as T1's, with the letter swapped
  and the product closure appended; what is NOT written is its
  interaction through arbitrary nestings — explosive-on-explosive
  (T5 feeding T5, T5 feeding anchored passes on the merged products)
  — with the quadratic exhibit as its known, machine-verified
  instance (exact at four points, round 14).
  All three entries are finite case analyses in the style of T1–T4,
  each reducing to P1 + P2 + P4 + pinned arithmetic.  Machine status:
  lane B's corpus (depth <= 5, ~45,000 random + 39 adversarial, cap
  2^16, all-points semantics) found ZERO profile violations, with the
  two dissected flags (idx 455, idx 3372) confirming the residue x
  slab cell structure the schema predicts; my round-14 battery and
  the coordinator's 3,368-E line battery agree on the non-explosive
  stratum; Lane D's chain-biased sweeps (rev-wall/, 4550/2661) extend
  the coverage into the construction-danger zone with zero violations.
  [ROUND 17 UPDATE — the table is CLOSED AT SKELETON LEVEL: Lane B's
  round 2 (17.2) closes all three entries via the TELESCOPE LEMMA —
  every window count is an S-function on cells of a finitely
  parameterized arrangement, multiplicities enter only through
  template-group sums (P1), and per-run counts telescope to letter
  totals, prior window counts, or pinned constants; (iii) with
  c_w = (T_c − Lambda)/p exactly (CH3: T5^3 = a^{S+2S^3} exact),
  (i) with c_w = Sum kappa_U n_U + O(#segments), (ii) with
  Sum floor(m/g) = (n_U − Lambda_g)/g; the b-free-length closure via
  the totals-IH at smaller depth.]  Status after that round:
  **Lemma S is PROVED on the
  non-explosive stratum (P3 covers it: no unbounded blocks arise
  without explosive b-bearing replacements), and beyond it REDUCED
  TO A SKELETON-LEVEL PROOF — Schema P with P4' (the repaired
  degree statement) plus the Telescope mechanism; the write-out
  (provenance recursion, quasi-polynomial closure) is the remaining
  task, currently unowned, and it is what would deliver the
  FINITE-partition form in general; the split toll (Corollary 1,
  with its round-16 counting repair) inherits exactly this status —
  and is now positioned OFF the main line (17.5: the construction
  never needs the b-free splits).**  The precise statement another
  agent could attack: write out the
  transformer table for (i) computed replacements at anchored sites,
  (ii) nested computed patterns on periodic regions, and (iii) T5's
  explosive nestings — i.e., show that for [R/P]F in each of the
  three classes, the output value's segment inventory remains O_E(1)
  with template multiplicities entering only through group sums and
  run lengths in the P4' closure — every mechanism
  needed (P1 group sums, P2 site-uniformity, the Telescope
  telescoping, pinned arithmetic) is specified above; what is
  missing is the write-out, not the idea.

**Consistency check (Schema P against the 15B values).**  On the
distinct-separator families, every value in the D_m engine is
O(1)-segment singular (no blocks at all) — Schema P is trivially
satisfied; on E_mix the same holds (mrg, Lb, Lc, the boxes, T: all
bounded-run-count values).  The quadratic exhibit's b^{S+2} is one
singular run of pinned-polynomial length S+2, and the post-merge
value a^{S*floor((S+2)/2)} is one singular run with a
residue-refined pinned-polynomial (product) length — the schema's
product closure is exactly what ST1 exercises, and this is T5's
known instance (the round-16 patch made the explosive-tiling class
an explicit residual entry).  The ST2 halver's
ceil-halved runs are pinned polynomials per mod-2 cell — the residue
refinement in action.

**Corollary 1 (the split toll — charter item 2 of the asks; repaired
in round 16; repositioned round 17).**  No expression computes a^j on W2.  Likewise a^i, a^k,
a^{i+k}, a^{i+j}, a^{j+k} — no value whose length is not a function of
S alone.  STATUS: conditional on Lemma S in its FINITE-partition
form — which holds unconditionally on the non-explosive stratum and,
in general, is delivered by Schema P at its current SKELETON level
(P4' + the Telescope Lemma, 17.2; the round-16 derivation through
"degree separation" was refuted as stated and repaired — the
bracketed note in P4 above).
(The proof's counting step is round 16's repair of an invalid
covering step; see the bracketed note.)
[ROUND 17 REPOSITIONING: the toll is now a SELF-CONTAINED STRUCTURAL
THEOREM, OFF the main line — it excludes the b-free splits (a^j,
a^{i+j}, ...) which the final construction NEVER NEEDS: every
intermediate of E_rev and of the general engine carries a separator
or is a merge (17.1).  The main question (rev on all of Sigma*) does
not pass through it; see 17.5.]

*Proof (round-16 repair: the coordinator's level pigeonhole + Lane D's
diagonal counting; replaces the segment/trace step, which was
INVALID — bracketed note below).*  Suppose E computes a^j on W2, i.e.
N_E = j pointwise.  Invoke Lemma S in finite-partition form: cells
Q_1..Q_N with N_E = h_r(S) on Q_r.  Choose S_0 beyond every constant
of E with S_0 > N + 2.  On the plane {S = S_0} — a triangle of
(S_0−1)(S_0−2)/2 lattice points arranged in S_0−2 nonempty j-levels
(the lines {j = c}, c = 1..S_0−2) — a cell on which N_E = h_r(S)
meets a j-level {j = c} only with h_r(S_0) = c: every output there
has length c and a-count h_r(S_0).  So each cell meets at most one
j-level; N cells meet at most N of the S_0−2 > N levels; some level
is uncovered — but its points are covered.  Contradiction.
Equivalently and directly: if some cell meets two j-levels, its two
same-S_0 points have a-count h_r(S_0) both times while the outputs
a^{j_1} and a^{j_2} have different lengths.  The other five targets
via the corresponding coordinate's levels: a^i and a^{j+k} via the
i-levels (on the plane, j+k = S_0−i), a^k and a^{i+j} via the
k-levels, a^{i+k} via the j-levels (i+k = S_0−j).  Lane D's
diagonal-counting general version (any target length L, affine in
(i,j,k), not a function of S): each cell's trace on the plane lies
in the diagonal {L = h_r(S_0)}, a line meeting the triangle in at
most S_0−2 points, so N cells cover at most N(S_0−2) <
(S_0−1)(S_0−2)/2 points once S_0 >= 2N+3 — the level pigeonhole and
the diagonal count are the same repair, the first phrased for the
coordinate targets, the second for all affine ones.
[CORRECTION OF RECORD, round 16: the covering step as written through
round 15 — including this consolidation round's own R5b formulation
('every <= 1-dimensional cell meets the triangle in a finite set, so
some 2-dimensional cell's trace contains a segment') — is INVALID on
the integer lattice: finitely many thin lattice sets, the j-levels
{j = c} themselves, cover the triangle, so the segment inference does
not follow and the Baire/measure intuition behind it does not
transfer to the discrete parameter space (kind-(b) pieces have empty
interior in R^3 while their union covers the lattice).  Found by Lane
D (V3); the level-pigeonhole repair is the coordinator's, the
diagonal-counting repair Lane D's, both hand-verified by the
coordinator.  FINITENESS IS LOAD-BEARING (Lane D): the pieces {j = c}
form a countable j-pinning cover of every plane, so the toll does not
survive a merely countable — or merely locally finite — partition;
hence the invocation of the finite-partition form above, and the
round-16 addition of P4 (degree separation ⟹ finite partition) to
Schema P.  R5a (S_0 beyond the constants of E) survives unchanged;
R5b is RETIRED.]  ∎

Degenerate parameter reductions (asked for explicitly): the argument
needs two of the three runs to vary independently.  On 1-parameter
subfamilies the toll vanishes — and rightly so: on the i = k = 1
slice, w2 = a b a^j b a is a palindrome and [eps/ab] computes a^j there
(machine-verified; on the slice, j is a function of S = j + 2, so
Lemma S forbids nothing — the corollary is SHARP).  On 2-parameter
subfamilies the toll applies to values not expressible in the
sub-family's S: on the fixed-middle family {a^i M a^k} (S = i + k),
a^{i+k} IS a function of S and is constructible (14.2's shave), while
a^i is not a function of S and is impossible — a new small corollary:
the fixed-middle family cannot split its own flanks; 14.2's engine
computes rev but no sub-expression extracts a flank alone.  On the
one-b family {a^i b a^j} (S = i + j) the split a^j is impossible —
round 13's open split problem closes NEGATIVELY, and 12.3's failed
reduction (rev-on-F implies split) is now explained at its root: its
extraction step needs precisely the non-constructible values that
Corollary 1 forbids.  Consistency: E_swap's output a^j b a^i has total
S (a function of S) — no contradiction; the laundered variants
likewise.

**Corollary 2 (the extraction toll).**  No expression built over
X = w2 computes a pure-typed b-free value; consequently the patterns
needed to delete flanks around a middle (a^k, a^i, a^k b, b a^i as
VALUES) are non-constructible, and every deletion route that could
isolate an interior run either needs them, or is b-anchored (merging
across the deleted b's, preserving the S-function property), or needs a
2-b pattern whose interior is exactly a^j — a (0,1,0)-typed b-free
value, again non-constructible.

Machine (this subsection): tdiag_check.py (2.1 s) — 811 region-stable
affine groups over the enriched S1 stratum, ZERO genuine
T-diagonality violations; one flagged group ([onbA/onbB]onbA) resolved
by hand in the log as a b-count grouping artifact (three sub-regions
glued, each diagonal in its own varying space); zero globally-b-free
combos with non-diagonal totals.  The coordinator's independent check
(relayed): on the line i + j = S, a piecewise-diagonal a-count takes
at most C(E) distinct values independent of S while a split-like
value takes ~S; 3,368 random E's (S-depth <= 3), ZERO growth cases,
catalogue sanity exact.  The affine-diagonal form of the totals was
thus validated on two independent batteries; the general
function-of-S form carries the corollary.  Post-repair additions: the
coordinator's verify_round15.py part G (ST2 on cells: halver total =
(S+#odd)/2 per mod-2 cell of (i,j,k), per-run ceil-halving on a 7^3
grid) and lane B's stress corpus (rev-split/lemma_stress.c + w2support.c
+ growth.c + w2dissect*.c + w2path.c + dump455.c, all runs < 6 s:
~45,000 random + 39 adversarial expressions to depth 5 on F and W2,
zero split hits, zero growth beyond the dissected periodic-step
specimens; box alpha=beta on residue-clean pieces, both flags mod-3
artifacts) — the corpus is the machine evidence behind Schema P's
status in scope note (2).

#### 14.5.3 The reduction answer, with the route enumeration (ask 3)

(a) SPLIT implies REV-ON-W2: TRUE (Theorem 14.5a) — and VACUOUS: the
split is impossible (Corollary 1).

(b) REV-ON-W2 implies SPLIT: the enumeration of converse routes, each
with its status:

  Route 1 — evaluate then extract (compose E_rev with deletions):
   1a. b-free computed deletion patterns (a^k, a^i, a^k b, b a^i):
       BLOCKED — the patterns are pure-typed b-free values,
       non-constructible (Corollary 1).
   1b. b-anchored one-b deletions ([eps/(a^x b a^y)] at the two b's):
       BLOCKED — each window merges its two sides; killing both b's
       yields an S-function total, which cannot equal j (Corollary 1's
       slice argument); killing one b leaves a one-b text whose
       remaining runs are not the middle alone.
   1c. 2-b interior deletion (a pattern spanning both b's with
       interior a^j): BLOCKED — its interior run must be a
       (0,1,0)-typed b-free value, non-constructible (Corollary 1).
   1d. collapse ([eps/w2]-style on C(rev(w2), Z)): CIRCULAR — the
       collapse returns whole co-factors; a^j as a co-factor requires
       a^j as a sub-expression, i.e. the split.
  Route 2 — boundary-slice method (the 12.3 technique): on the slice
   i = k = 1 the inputs are palindromes and [eps/ab] extracts a^j —
   but only ON the slice (on full W2, [eps/ab] is the junction shave
   a^{S-2}).  The slice is a 1-parameter family where the pure value
   IS the S-function, so nothing extends to W2: BLOCKED as a route to
   the full split (and the full split is impossible outright).
  Route 3 — C-decomposition (make a^j a co-factor of a constructible
   concatenation): CIRCULAR, as 1d.
  Route 4 — prov-level extraction: BLOCKED trivially — any prov-level
   construction's content is a content-level construction.
  Route 5 — the meta-route, any extraction expression G whatsoever
   over X = w2 with G(w2) = a^j: BLOCKED — this is exactly Corollary
   1.  The extraction is refuted outright, not merely the natural
   routes.

Conclusion.  The implication REV-ON-W2 => SPLIT can hold only vacuously
(its consequent is refuted; if rev-on-W2 holds, the implication is
false, and if rev-on-W2 fails, it is vacuous) — it is not a usable
reduction in either direction.  The equivalence is broken at the split
end: THE TWO-B QUESTION STANDS ALONE.  It lives entirely at the run
level: rev's own target output has total S (an S-function — consistent
with Lemma S), so the total sum-type calculus is silent about rev on
W2; excluding it (or constructing it) requires run-level invariants
(the residue-riddled tier — lane D's assignment) or new construction
ideas (lane C).  For lane B: Corollary 1 makes the split-construction
program futile UNLESS Lemma S's proof breaks at one of the named
attack points — the productive stance is adversarial scrutiny of
Lemma S, which is exactly what the coordinator relayed.

### 14.6 The enriched sweep (ran before the scope change; retained as
evidence for 14.5.1 and lane C)

round14_sweep.c (1.3 s, 12,787,938 sims; grid [1..5]^3 = 125 points):
S1 = [R/P]F over the 16-value library (input w2, merge, two junction
shaves, a both-fire shave, two one-b window values, affine scalings,
C-shaped scrutinees w2.w2 and w2.js1, bigsym form, b-merge-b, the
symmetric (S,S,S) text, the merge-sandwich, a junction duplicator) x
24-pool; S2 = [R2/P2][R1/P1]w2 over the 18-value short pool (6
first-pass results over length 200 skipped — documented completeness
cut; cap-safe by length, expected outputs <= 20 chars).

Verdicts.  rev: 0 full-grid hits; best partial 25/125 — EXACTLY the
i = k diagonal, achieved only by identity-type combos (w2 is a
palindrome exactly there) — nothing in the stratum even approaches the
swap.  flank-progress (x1,x3) = (k,i) with arbitrary middle: 0
full-grid hits — the sharpest negative: no depth-<= 2 combo over the
enriched library crosses the flanks AT ALL.  splits and sums (a^i,
a^j, a^k, a^{i+k}, a^{i+j}, a^{j+k}): 0 full hits; best partials
36-44/125, all region artifacts (one-b window firing cones, e.g.
[eps/aab][a/onbA]w2 at 44/125 for aj) — precisely the cone behaviors
that Lemma S's piece structure predicts and Corollary 1 excludes.
middle-exact outputs (x2 = j, output != w2): ABUNDANT — every junction
shave preserves the middle exactly (e.g. [ba/ab]w2, [w2/b]big2, and
~300 S2 chains).  Reading: the middle is the CHEAP direction — every
transformation that respects the b-skeleton keeps it; everything hard
is the flanks.  This is the falsification backdrop for 14.5.1 (the
forward engine) and the starting evidence for lane C's search.

### 14.7 Machine verdicts (round 14)

- **verify_round14.py** (23.5 s, round14_verify.log): A the
  coordinator's five junction-shave instances re-verified with their
  c's; B the c = 0 theorem on 28 middles, full family {i,k >= 0},
  grids + 400 random each, prov injective and never DB, M = 'b'
  reproduces E_swap; B3 the c-formula of Proposition 14.3 on 2,045
  in-region random trials; C self-anchoring (i)/(ii)/(iii) on 20,000
  random trials; D1 psi; D2 all 15,625 depth-3 b-free compositions;
  E the reduction engine on fixed-j slices j = 1..6 and the laundered
  L_a.L_b.E_bab (rev with prov == ()).  ALL VERIFIED.
- **tdiag_check.py** (2.1 s, round14_tdiag.log): 811 affine
  region-stable groups, 0 genuine T-diagonality violations, the one
  flagged group resolved by hand in the log; 0 globally-b-free
  non-diagonal totals.  Plus the coordinator's independent line
  battery (relayed): 3,368 random E's, zero growth cases.
- **round14_sweep.c** (1.3 s, round14_sweep.log): as in 14.6.
- The quadratic exhibit [merge/"bb"].[b/a]X (14.5.2): a-count =
  S*floor((S+2)/2), machine-verified exactly.
- Run times: 23.5 + 2.1 + 1.3 s — all under the 60 s cap.

### 14.8 Honest ledger for Round 14

- PROVED: Lemma 14.1 (self-anchoring); Theorem 14.2 (fixed middles,
  c = 0, full family, boundaries included) with the M = 'b'
  unification and the laundering composition; Proposition 14.3
  (junction-shave tiling and c-formula); Theorem 14.4 (no constant
  shave) with the Pi-progression proof; Theorem 14.5a (SPLIT implies
  REV-ON-W2, palindrome-middle engine); Lemma 14.5b (exact per-pass
  accounting — the never-rescan reason); Lemma S (structure:
  piecewise S-function totals ON CELLS, repaired form with R1-R5
  folded in — locally finite cells, ordered slabs-then-residues-then-
  pinned-polynomial-coincidence, the R4 case added, the false
  explosive-boundedness step replaced by the long-runs-only
  reorganization; unconditional on the non-explosive stratum,
  conditional on Schema P beyond it); Schema P (P0, P1 Template Sum,
  P2 Local Indistinguishability, P3 transformer classes T1-T4, P4
  degree separation ⟹ finite partition — the analytic core of R2's
  induction, owned and proved in the consolidation round; the residual
  table's THREE entries — computed anchored replacements, nested
  computed patterns, T5 explosive tilings — specified exactly);
  Corollary 1 (the split toll, sharp
  against 1-parameter subfamilies, final step the round-16 counting
  repair — level pigeonhole + diagonal counting, replacing the
  invalid segment/trace covering step) — closing round 13's open split
  problem NEGATIVELY on W2 and on the one-b family, explaining 12.3's
  failure at its root, and yielding the new flank-split impossibility
  on fixed-middle families; Corollary 2 (extraction toll).
- CORRECTED DURING THE ROUND (recorded): my initial T-diagonality
  lemma claimed affine-diagonal totals in general; the machine
  exhibited the quadratic counterexample before the writeup landed;
  the correct general form (piecewise S-functions) now carries the
  corollary, with affine-diagonal retained on the non-explosive
  stratum and validated on two independent batteries.
- VERIFIED ON STATED DOMAINS: 14.7 in full.
- CONSISTENCY (no contradiction anywhere): E_swap, E_M, junction
  shaves, laundered variants — all totals are S-functions; the
  fixed-middle exemption is coherent (in (i,k)-space, a^{i+k} IS the
  S-function and is constructed by 14.2).
- OPEN (handed off per the scope change): rev on W2 itself — Lemma S
  is silent about it (rev's output total is S); the run-level tier
  (residues, run placement) — lane D; constructions against the wall —
  lane C; the split head-on — lane B (now adversarial scrutiny of
  Lemma S, the productive stance given Corollary 1); the
  unbounded-alphabet DB program — lane E.  The sweep's completeness
  cuts: depth <= 2, the 18-value short pool, first-pass results
  <= 200 chars — documented above.
- NOT DONE (scope): the invariant-induction beyond the total tier and
  any construction attempt on W2 — removed from my lane by the
  mid-round scope change; nothing was spent there beyond what the
  reduction analysis required.

### 14.9 Files

- `verify_round14.py` / `round14_verify.log` — parts A/B/B3/C/D/E,
  23.5 s, ALL VERIFIED.
- `tdiag_check.py` / `round14_tdiag.log` — the total-type spot check
  (811 groups) plus the artifact resolution and the slice-extraction
  note, 2.1 s.
- `round14_sweep.c` / `./round14_sweep` / `round14_sweep.log` — the
  enriched all-varying two-b sweep, 1.3 s.
- `seed_round14_fixed_middle.py` — the coordinator's seed, re-verified
  (part A).

## 15. Rounds 15 + 15B (consolidation): the fixed-alphabet frontier

### 15.0 Charter and sources

Consolidation round.  The parallel lanes landed; this section
integrates their verified results into the arc's record, applies the
coordinator's verification corrections, and reorganizes the frontier.
Sources, all independently re-verified by the coordinator (hand
derivations re-derived, not just script re-runs):

- LANE C (round 15, constructions): `../rev-try/REPORT.md` — the
  coordinator's transcription of C's blocked write, topped by the
  verification verdict and the round-15B addendum.  Battery:
  `verify_round15.py` (parts A-G, ALL VERIFIED) + `round15_verify.log`.
- ROUNDS 15B + the batteries: the coordinator's own constructions and
  runs (`verify_round15b.py`, `round15b_verify.log`).
- LANE B (adversarial scrutiny of Lemma S): `../rev-split/REPORT.md`
  — verdict LEMMA S STANDS with repairs R1-R5, all scripts in
  rev-split/ reproducing; folded into 14.5.2 above.
- LANE E (unbounded alphabets): `../rev-db/REPORT.md` and the
  paper-voice fragment `../rev-db/separable_rigidity.tex`.

Provenance caveat, recorded per the coordinator's note: in rev-try/,
`t1_mixed.log` and `t2_corr.log` reproduce byte-identically on
re-run; `t3star.log` and `t4_reductions.log` are NARRATIVE
CONCATENATIONS of earlier script versions (they contain a stale "ST1
REFUTED" from a check-formula bug and an early superseded "REFUTED"),
and the final scripts dropped four checks that exist only in those
logs (the slack calculus, the size counts, A7-convergence, the
(0,0,c)-closure) — all four are re-established by the coordinator's
battery (parts C, F, E, D).  Trust rev-try/REPORT.md's verification
note, not those two logs.

### 15.1 The correction of record

**13.7's "distinct rare letters — same wall" clause is REFUTED.**
The claim (two places in 13.7, corrected in situ above with bracketed
notes) was that {a^i b a^j c a^k} presents the same interior-exactness
wall as w2, because interior exactness is letter-blind.  The letter-
blindness of Match Anchoring is true — but the inference was wrong:
distinct letters are an ADVANTAGE, not a neutral fact, because they
make one-letter PROJECTIONS unique ([eps/c]X and [eps/b]X each fire
once), and the projections feed the complement boxes.  T1 (15.2)
computes rev on the full mixed-letter all-varying family.  The error's
mechanism, for the record: 13.7(c) correctly killed the two-b
COMPLEMENT route (interior exactness pins the middle) but then
overgeneralized to "every branch of the complement route requires
middle-run isolation" — the evasion is a ONE-b final pattern with an
OVERSUPPLIED middle (the merge-flavored shave), which never isolates
anything.  The wall survives only where the separators COLLIDE (the
same-letter family) — 15.4's consequence and 15.5's reduction make
that exact.

### 15.2 T1 — the mixed-letter all-varying family falls

**Theorem (T1, PROVED; machine-verified).**  Over Sigma = {a,b,c},
the expression

    E_mix = [b / mrg.b] . (Cc . Bb)

computes rev on the FULL family {a^i b a^j c a^k : i,j,k >= 0} — all
three runs varying, the first two-separator all-varying family to
fall — where

    mrg = [eps/c][eps/b]X = a^{i+j+k} = a^S
    Lb  = [eps/c]X = a^i b a^{j+k}        (one-b projection)
    Lc  = [eps/b]X = a^{i+j} c a^k        (one-c projection)
    Cc  = [c/Lc](mrg.c.mrg) = a^k c a^{i+j}     (c-anchored box)
    Bb  = [b/Lb](mrg.b.mrg) = a^{j+k} b a^i     (b-anchored box)
    T   = Cc.Bb = a^k c a^{i+2j+k} b a^i

15 S-nodes, S-depth 4, size 58 (tree counts confirmed by the
coordinator: 58 nodes, 15 S-nodes, S-depth 4, AST depth 7 edges).

*Proof.*  Each of b, c is unique in X = a^i b a^j c a^k, so each
projection pass fires exactly once — this is what b != c buys.  Each
box is the round-14 complement engine with M = c (resp. M = b): the
pattern Lc has one c and aligns at the scrutinee's (a^S c a^S)
unique c, forced start s = S - (i+j) = k, flanks fit since S >= i+j
and S >= k (j, k >= 0), so it fires once and outputs the complements
(S - (i+j), S - k) = (k, i+j); Bb mirrorwise gives (j+k, i).  T = Cc.Bb
is already in rev's separator order — c before b — with exact
extreme flanks (k from Cc, i from Bb) and the middle OVERSUPPLIED by
S.  The final pass [b/(mrg.b)]: the pattern mrg.b = a^S b is one-b;
T has a single b; the window must end at that b, its leading run S
fits in T's middle run i+2j+k iff j >= 0; exactly one firing shaves
exactly S, leaving j.  Output a^k c a^j b a^i = rev(X).  Boundaries
(i=j=k=0, j=0, i=0, k=0) hand-check and are in the verified grids.
NO middle-run isolation ever happens — the middle is an oversupplied
merge and the shave pattern is merge-flavored; that is exactly how it
evades 13.7(c).  ∎

Corollaries (verified): L_a.L_b.L_c.E_mix computes rev with prov ==
() — the laundering composition; prov(E_mix) is never DB and is
injective on the family; Gamma(E_mix) = {a,b,c} = Sigma, so
|Sigma \ Gamma(E_mix)| = 0 — consistent with lane E's Corollary 4
(15.6).  Program impact: no fixed-alphabet content obstruction can
live at 2 separators with distinct letters, at any level.

### 15.3 T3* — the rational symmetric correlation spectrum falls

**Theorem (T3*, PROVED; machine-verified).**  For every coprime pair
c >= 0, d >= 1,

    E_{c,d} = [b.M.b / X] . (F . b . M . b . F)

computes rev on {a^i b a^{c(i+k)/d} b a^k} (integrality of j forces
d | (i+k); write i+k = dt, j = ct, S = (c+d)t), where

    F = [a^d / a^{c+d}].[eps/b]X = a^{i+k}      M = [a^c / a^{c+d}].[eps/b]X = a^j

9 S-nodes, S-depth 3, size 40.  Instances verified: (0,1) =
{a^i bb a^k} (the M = 'bb' fixed-middle point with c(M) = 0 — the
engines MEET at this family), (m-1,1) for m = 2,3,4, and (1,2), (3,2),
(2,3), (5,2), (4,3), (1,3).

*Proof.*  [eps/b]X = a^S with S = (c+d)t an exact multiple of c+d
on-family; the b-free passes [a^d/a^{c+d}] and [a^c/a^{c+d}] act by
the round-13 run map psi(u) = r*floor(u/p) + u mod p with u = S, p =
c+d: floor-division of an exact multiple is exact, so F = a^{dt} =
a^{i+k} and M = a^{ct} = a^j with NO leftover.  The pattern X (two
b's, interior j) fires once at T' = F.b.M.b.F = a^{i+k} b a^j b
a^{i+k}: interior exact by Match Anchoring; flanks i+k dominate i
and k separately.  One firing: remnants (k, i), R = b.M.b resupplies
the middle.  Output a^k b a^j b a^i.  ∎

Boundary (conditional on the total-content invariant): the
direct-swap scrutinee a^{i+k} b a^j b a^{i+k} has total 2(i+k)+j; on
{j = alpha*i + beta*k} this is a function of S iff alpha = beta (x ->
(2+x)/(1+x) injective), and irrational alpha is empty — so the
direct-swap engine lives exactly on the rational symmetric
correlations, all of which T3* constructs.  Consistency (no Lemma S
contradiction): on every T3* family a^j = a^{cS/(c+d)} is a function
of S — the families are S-legal, as they must be.  Lane B's A7
convergence verified: [eps/(b.M.b)]X = a^{i+k} fires on F_{c,d}
(interior supplied).  E_{1,1}'s off-family near-miss (fires on
j = i+k+1, outputs flanks inflated by 1) is the halver's O(1) jitter
leaking — the mechanism ST2 isolates (14.5.2, scope note 3).

### 15.4 Round 15B — the general distinct-separator theorem

**Theorem (distinct separators at any number, PROVED;
machine-verified k <= 4).**  For every k >= 1, distinct separators
s_1..s_k over any alphabet containing a, and runs r_0..r_k >= 0, rev
is computable on the all-varying family

    { a^{r_0} s_1 a^{r_1} s_2 ... s_k a^{r_k} }

by the following engine.  With S = r_0+...+r_k, mrg = [delete all
s_m]X = a^S, and L_m = [keep only s_m]X = a^{r_0+..+r_{m-1}} s_m
a^{r_m+..+r_k} (each projection fires once — s_m unique in X):

    D_m = [s_m / L_m](mrg . s_m . mrg) = a^{r_m+..+r_k} s_m a^{r_0+..+r_{m-1}}

(the round-14 complement engine on the m-th projection).  The
concatenation D_k...D_1 has inter-separator run exactly S + r_m, so
the k-1 shaves [s_m / mrg.s_m], applied s_{k-1} FIRST down to s_1,
remove exactly S and leave r_m; the leading run r_k and the trailing
r_0 are exact with no shave.  Output

    a^{r_k} s_k a^{r_{k-1}} ... s_1 a^{r_0} = rev(X).

*Proof.*  Each D_m: the pattern L_m has one s_m and aligns at the
scrutinee's unique s_m; the leading run r_0+..+r_{m-1} <= S and the
trailing r_m+..+r_k <= S, so exactly one firing outputs the complements
(S - (r_0+..+r_{m-1}), S - (r_m+..+r_k)) = (r_m+..+r_k, r_0+..+r_{m-1}).
Concatenation: between s_m and s_{m-1} the run is (r_0+..+r_{m-1}) +
(r_{m-1}+..+r_k) = S + r_{m-1}; the extremes are r_k (leading, from
D_k) and r_0 (trailing, from D_1).  Each shave [s_m/(mrg.s_m)]: the
pattern a^S s_m has its s_m at the unique s_m of the current text
(the separators are distinct and no earlier shave touches s_m's
neighborhood), its leading run S fits in S + r_m, and exactly one
firing leaves r_m before s_m.  All sub-expressions evaluate at the
original input, so mrg = a^S is stable across the shaves.  ∎

Sizes (verified by tree counts): E_1: 14 nodes, 3 S-nodes, S-depth
2; E_2: 58/15/4 (= E_mix exactly — T1 IS the k=2 instance; the
coordinator's independently built E_2 reproduces T1's counts); E_3:
126/35/6; E_4: 218/63/8.  In general 4k^2-1 S-nodes, S-depth 2k
(O(k^2) nodes).  Special cases: k=1 unifies with the round-14
complement engine (and with E_swap / Theorem 14.2 at M = 'b');
k=2 IS E_mix.

**Consequence.**  Every distinct-separator all-varying family falls,
at any number of separators.  A fixed-alphabet obstruction for rev
can live ONLY where separators collide — the same-letter question —
which 15.5 reduces to V_h.  Gamma(E_k) = Sigma_k throughout,
consistent with lane E's Corollary 4.
[ROUND 17 SUPERSESSION OF RECORD: the "ONLY where separators
collide" clause is REFUTED — round 15C's E_rev computes rev on the
same-letter family W2 itself (17.1), and the general engine
computes rev on EVERY fixed separator structure, repeats
included.  This theorem survives as a COROLLARY of the general
engine (distinct letters make each L_m a chain of one-letter
passes — the deletion engine of 17.1 degenerates to it), and its
bounds are superseded: the general engine's systematic encoding
has k^2+k+1 S-nodes (DAG) against 4k^2−1 here (tree), with
S-depth 2k+1 against 2k — repeats included at strictly smaller
size, one more level of depth; see 17.1's size table for both
conventions.  No claim of this section is false; its scoping
claim is.]

### 15.5 The V_h reduction — the LIVE FRONT

**[STATUS — RESOLVED, round 15C (17.1): the equivalence below is
PROVED and now WITNESSED at h = 0: E_rev's value IS V_0 =
a^k b a^j b a^i, so the "if" direction is instantiated and rev on
W2 is COMPUTABLE.  Every universal V_h-unconstructibility or
projection-exclusion claim is thereby REFUTED.  What follows is
PROVED unless marked, and is retained as the analysis that located
the target the construction then hit.]**

**Theorem (V_h-equivalence, PROVED; machine-verified round trip
through E_2).**  rev is computable on the same-letter all-varying
family W2 = {a^i b a^j b a^k} IFF the value

    V_h = a^k b a^{j+h} b a^{i+h}

is constructible for some constant h >= 0.

*Proof.*  (⇐) E = [b / b.a^h].V_h: the constant pattern b.a^h fires
at both b's (the following runs j+h and i+h dominate h), replacing
b.a^h by b; output a^k b a^j b a^i = rev.  (⇒) [b.a^h / b].E, where E
computes rev: the pattern b fires at both b's of a^k b a^j b a^i,
replacing each by b.a^h: output a^k b a^{j+h} b a^{i+h} = V_h.  ∎

**Rev-slack calculus (corrected forms; the sign slip in C's written
report is fixed here per the coordinator's machine verification).**
Call a^{k+d1} b a^{j+c} b a^{i+d2} a SLACK VALUE of class (d1, c, d2).
Every slack value with d1 + d2 = h computes rev by ONE constant pass:

    STRIP  [a^{r0-d1} b a^{r1-d2} / a^{r0} b a^{r1}]   (slack -> rev)
    PAD    [a^{r0+d1} b a^{r1+d2} / a^{r0} b a^{r1}]   (rev -> slack)

with constant bounds r0 >= d1, r1 >= d2, k >= r0, j >= r1+r0, i >=
r1 (the c(M) phenomenon — 14.2's toll is exactly the boundary here).
[The form as written in C's report — [a^{d1+r0} b a^{r1+h-d1} /
a^{r0} b a^{r1}] applied to slack — is a sign slip: it yields
a^{k+2d1} b a^{j+2h} b a^{i+2d2}.]  STRIP hand-check: the pattern
a^{r0} b a^{r1} fires at the first b (leading run k+d1 >= r0,
following j+c >= r1 by the bounds), replacing a^{r0} b a^{r1} by
a^{r0-d1} b a^{r1-d2}; the leading run becomes (k+d1-r0) +
(r0-d1) = k, the following (r1-d2) + (j+c-r1) = j+c-d2; the pass
resumes and fires at the second b likewise, leaving j+c-d2-d2 = j and
i.  Machine-verified, 400 cases (coordinator part C).

**Slack-class closure (PROVED; verified 300 cases, part D).**  The
full slack class {a^{k+d1} b a^{j+c} b a^{i+d2}} is closed under
one-b constant passes, with affine action

    (d1, c, d2)  ->  (d1 - r0 + x,  c + x + y - r1 - r0,  d2 + y - r1)

for pattern a^{r0} b a^{r1} and replacement a^{x} b a^{y},
independent of i, j, k.  This subsumes the (0,0,c) closure in the
original log.

**Wall analysis (final-pass form, hand-derived by lane C,
hand-verified by the coordinator).**  Any two-b-pattern final pass
computing rev (T two-b, one firing, b-free remnants) forces R's
middle run = j EXACTLY: the output's middle is enclosed by R's two
b's, so no remnant enters it.  The constructible j-middle suppliers
are exactly three: (i) X-family flanks (i+O(1), k+O(1)) — then T
becomes rev-slack on a k >= i dominance cell, i.e. the V_h route;
(ii) merge-powers — exactly the T3* families; (iii) the split
b.a^j.b — total j+2, not an S-function — DEAD by round 14 Corollary
1.  T with >= 3 b's reduces to rev-slack by the same arithmetic.
Every final-pass route reduces to V_h, a T3* correlation, or the
dead split.

**Transplant lemma (PROVED; hand-verified).**  If the one-b
projections P1 = a^i b a^{j+k} and P2 = a^{i+j} b a^k were
constructible on W2, the E_mix skeleton (letter-blind) computes rev
on the same-letter family: the boxes [b/P2](mrg.b.mrg) = a^k b a^{i+j}
and [b/P1](mrg.b.mrg) = a^{j+k} b a^i give T = a^k b a^{i+2j+k} b
a^i, and the final [b/(mrg.b)] aligns at the second b (the first
b's leading run k < S on all-varying inputs), shaving S from
i+2j+k and leaving j.  T1's verification is this lemma's machine
check.  Hence P1 ∧ P2 ⇒ rev, and with the equivalence, P1 ∧ P2 ⇒
V_h; P1, P2 are S-legal (total S) and unconstructed.  [The
coordinator's verification record lists the full converse P1∧P2 ⇔
V_h; the ⇐ half (V_h yielding P1, P2) is relayed-verified but not
re-derived here — the direct routes we checked (deleting a b or a
flank from rev or from V_h) need a^j- or a^i-typed patterns, which
Corollary 1 forbids, so the route must be indirect.]
[ROUND 15C RESOLUTION: P1 and P2 ARE constructible —
P1 = [eps/(b.mrg.a)](X.mrg.a) and P2 = [eps/(a.mrg.b)](a.mrg.X),
the MERGE-CATALYZED SELECTIVE DELETIONS of 17.1 (the merge-padded
concatenated scrutinees are exactly the escape the round-15 "no
direct route" analysis lacked: the deletion consumes the merge, not
a flank, so no a^j- or a^i-typed pattern is ever needed).  The
transplant closes with them, E_rev is the resulting witness, and
the two OPEN questions below are ANSWERED: V_0 is constructible
(it is E_rev's value), and V_h ⇒ P1 ∧ P2 holds outright at h = 0.
The wall analysis above survives as the analysis of its CLASS —
two-b patterns, one firing, b-free remnants, R's middle forced to
j — and E_rev's final pass sits outside that class: a ONE-b,
merge-flavored pattern (a^{S+1}.b) shaving an oversupplied middle
(S+1+j) and leaving j as REMNANT, the same evasion mechanism Lane
C identified for E_mix ("no middle-run isolation; the middle is an
oversupplied merge and the shave pattern is merge-flavored"),
realized here on the same-letter family.  The closing sentence
"every final-pass route reduces to V_h, a T3* correlation, or the
dead split" is thereby SUPERSEDED: the fourth route — merge-flavored
remnant shave — exists and is the one that computes rev.]

### 15.6 Lane E — separable rigidity: the unbounded-alphabet question closes

**Theorem (Separable Rigidity, PROVED).**  For every expression E
(any S-depth, any shape) and every input w = x_0...x_{n-1} whose
letters are pairwise distinct and disjoint from Gamma(E) (SEPARABLE
for E), n >= 1: whenever [E](w) is defined it is in COPY FORM — v_0 W
v_1 ... W v_M, where each W is a contiguous block of n atoms
spelling w with labels (0,...,n-1) in order and each v_j in
Gamma(E)^* — and prov(E,w) = (0,1,...,n-1)^M.

*Proof architecture (full paper-voice proof in
`../rev-db/separable_rigidity.tex`, integrated into the paper this
round — 15.11/task D).*  (1) Copy-alignment lemma: in a copy-form
value, every occurrence of a copy-form pattern either lies inside a
single constant run or covers whole consecutive instances with the
pattern's gaps matching the interior constant runs exactly — no
match window starts or ends strictly inside an instance (x_0 occurs
only at instance starts; any n consecutive letters spelling w are
one instance; the gap-matching induction).  (2) Preservation: the
greedy pass selects disjoint windows each of which is a union of
whole instances plus constant-run pieces, so the output interleaves
the uncovered instances (whole, in order) with one copy of y's
instances per site — copy form again.  (3) Induction on E: constants
are M=0, the variable is W, concatenation merges at the junction,
the pass node applies (2).  ∎

**Corollaries (all PROVED).**  (a) No descending provenance at any
depth: for n >= 2 and w separable, prov(E,w) is empty or contains
the adjacent ascending pair (0,1) — E realizes no descending
bijection at any S-depth; the budget conjecture holds on separable
inputs with budget 1, for every E.  (b) Reversal fails on every
separable input: the output is a Gamma-word or contains w FORWARDS
contiguously, which rev(w) — same length — contains only if
w = rev(w), impossible for pairwise distinct letters at n >= 2.  (c)
**Reversal is not computable in L over unbounded alphabets, at any
depth**: for every E there are separable inputs of every length
>= 2, and E differs from reversal on every one.  (d) **Corollary 4
(fixed-Sigma witness shape): any fixed-Sigma witness for rev has
|Sigma \ Gamma(E)| <= 1** — a witness's constants must cover all but
one letter of the alphabet.  By round 12's laundering theorem this
is a constraint, not an obstruction (the prov level can be laundered
away); the fixed-alphabet question itself remains open, now entirely
at V_h.

Machine (lane E's, all runs < 60 s, rev-db/): instrumented
atom-level copy-alignment on 2,500 random evaluations (1,170
windows, 0 instance cuts, exact agreement with the independent
evaluator); 9,300 random expressions to S-depth 8 (0 violations);
exhaustive-in-shape falsification at S-depth <= 4 over a 24-form
pass-free library on canonical separable inputs — 122,935,396
defined pipelines, 0 violations; 1,874 cross samples re-evaluated
with the independent evaluator, exact agreement.

Relation to the depth-2 theorems (rounds 10-11, descending_bijection.tex):
those bound the DB-realizing inputs of depth-<=2 expressions for ALL
inputs — stronger in the input dimension, weaker in depth;
separable rigidity is all-depths but separable-only.  For the reversal
application, which by round 12's forcing lemma constrains only
separable inputs, it suffices alone.

### 15.7 Lane B's verdict on Lemma S (pointer)

Lemma S STANDS under adversarial scrutiny, with the five repairs
R1-R5 folded into 14.5.2 this round (locally finite partition; the
explosive-stratum reorganization with the pinned-polynomial schema —
now OWNED as Schema P with P0-P3 proved and the residual table
specified; the ordered slabs-then-residues-then-coincidence
refinement with pinned-POLYNOMIAL conditions; the R4 single-b
zero-interior-run case; the R5 slice-step caveats — of which R5a
survives and R5b was found INVALID in round 16 (Lane D's V3,
16.2) and retired in favor of the counting repair) plus the ST2
constraint (totals are S-functions on CELLS, or f(S)+O(1); ST2 =
[a/aa]X — the halver, replacement first — kills only the residue-less
reading, and the per-cell form (S+#odd)/2 survives, coordinator part
G).  Lane B's closing record also contributes: the independent
derivation of the flank-antisymmetry obstruction from the two-b
deletion engine (priority for the general form: this arc's round
14); the F-version corollary written out (no split on F = {a^i b
a^j}, conditional on Schema P's completion); the near-miss catalogue
A1-A10; the support-growth methodological caveat (folded into
14.5.2's scope note 6).  The split toll's status is therefore: PROVED
on the non-explosive stratum, VERIFIED-ON-STATED-DOMAINS beyond it,
PROVED-CONDITIONAL-ON-SCHEMA-P in general.

### 15.8 Machine verdicts (rounds 15 + 15B)

- **verify_round15.py** (coordinator's battery, ~10 s, parts A-G,
  ALL VERIFIED; log `round15_verify.log`): A E_mix fresh encoding,
  13^3 grid + 500 random; B E_{c,d} fresh encoding, 12 pairs (incl.
  7/3, 5/6); C rev-slack PAD/STRIP with corrected signs, 400 cases;
  D slack-class closure, affine action on (d1,c,d2), 300 cases; E
  A7-convergence [eps/(b.M.b)]w2 = a^{i+k}, 4 families x 200; F size
  counts (E_mix 58/15/4; E_{c,d} 40/9/3); G ST2 cells — halver total
  (S+#odd)/2 per mod-2 cell, per-run ceil-halving on 7^3.
- **verify_round15b.py** (25 s, ALL VERIFIED; log
  `round15b_verify.log`): k=1 (13x13 grid), k=2 (10^3), k=3 {a^i b
  a^j c a^k d a^l} (9^4 grid + 400 random), k=4 (7^5 grid + 300
  random); tree counts E_1..E_4 as in 15.4.
- Lane C's own runs (rev-try/): 15.9 s total, PASS (t1/t2
  byte-identical on re-run; t3star/t4 logs carry the provenance
  caveat of 15.0).
- Lane B's runs (rev-split/): all < 6 s, contents in 15.7 and
  14.5.2's machine paragraph.
- Lane E's runs: 15.6.

### 15.9 Honest ledger for Rounds 15 + 15B

- PROVED: T1 (E_mix on {a^i b a^j c a^k}, all varying); T3* (all
  coprime c,d); the distinct-separator theorem at every k (15B); the
  V_h-equivalence (both directions); the rev-slack calculus (PAD and
  STRIP, corrected signs); the slack-class closure with its affine
  action; the wall analysis (two-b one-firing final passes force
  R's middle = j; three suppliers); the transplant lemma (P1∧P2 ⇒
  rev); separable rigidity with Corollaries a-d (lane E); Schema
  P0-P3 (the analytic core of R2's induction).
- CORRECTED (this round, all recorded in situ): 13.7's
  distinct-rare-letters clause (REFUTED by T1 — the arc's third
  relocated wall, now final: only same-letter survives); C's
  rev-slack sign slip (PAD/STRIP forms); ST2's expression label
  ([a/aa]X, the halver); the t3star/t4 log provenance; Lemma S's
  five repairs R1-R5 + ST2's per-cell reading.
- VERIFIED ON STATED DOMAINS: 15.8 in full.
- CONSISTENCY (no contradiction anywhere): Gamma(E_mix) = Sigma;
  T3* families are S-legal (a^j = a^{cS/(c+d)}); E_2's off-family
  jitter is ST2's O(1); every 15B value is O(1)-segment singular
  (Schema P trivial); V_h's total is S+2h, so Lemma S is silent on
  V_h — the reduction is coherent with the total tier.
- OPEN (the live front, in order): V_h constructibility (⇔ rev on
  same-letter all-varying W2; ⇔ the last fixed-alphabet content
  question — Lane D running, outcome slots into 15.5); whether
  V_h ⇒ P1 ∧ P2; nonlinear {j = mu(S)} families; the residual
  Schema P transformer table (computed anchored replacements —
  14.5.2); the fixed-alphabet prov level beyond laundering.
- NOT DONE (scope): no new machine falsification campaigns were run
  by this lane this round — consolidation only; the batteries cited
  are the coordinator's and the lanes', re-verified per 15.0.

### 15.10 Files

- `verify_round15.py` / `round15_verify.log` — the coordinator's
  round-15 battery (parts A-G, ALL VERIFIED).
- `verify_round15b.py` / `round15b_verify.log` — the 15B battery
  (k <= 4, ALL VERIFIED).
- `../rev-try/` — lane C's scripts and logs (t1/t2 reproduce; t3star/
  t4 carry the 15.0 provenance caveat).
- `../rev-split/` — lane B's scripts and logs (verify_grid.py,
  lemma_stress.c, w2support.c, growth.c, w2dissect*.c, w2path.c,
  dump455.c + logs; all reproduce).
- `../rev-db/` — lane E's scripts, logs, and the paper-voice fragment
  `separable_rigidity.tex` (integrated into the paper this round).
- `../rev/descending_bijection.tex` — the rounds 10-13 record (the
  DB program's position in the paper draws on it; round-13 addendum
  further corrected this round — see below).
- This file's 14.5.2 (Lemma S repaired + Schema P) and 13.7 (the
  bracketed round-15 corrections) are the other writes of this round.

### 15.11 The paper integration (task D, executed)

The verified halves are integrated into `../../../main.tex` this
round: the exclusion half (separable rigidity with its corollaries —
reusing rev-db/separable_rigidity.tex — and the middle-run toll with
its Schema-P-conditional status) and the positive half (the
one-separator engine E_swap; the fixed-middle theorem; the general
distinct-separator theorem; the rational correlations; the V_h
reduction as the frontier statement), in a new subsection of the
Alphabet Invariance section.  The descending_bijection.tex addendum
(the round-13 "varying interior runs" correction) was updated to the
round-15 boundary: the obstruction lives only where separators
collide.  Details and placement: see the subsection itself
(\subsection{The Reversal Frontier}, ssec:frontier, in the Alphabet
Invariance section of main.tex).

## 16. Round 16 (follow-up): the run-level tier — E_asym, the toll's counting repair, PREFIX-DOMINANCE, and the convergence

### 16.0 Charter and sources

Follow-up round, chartered by the coordinator after their verification
of the consolidation (three patches + this integration).  Source: Lane
D's round (the run-level invariant lane), `../rev-wall/REPORT.md`
(481 lines), verified in full by the coordinator — every machine
number reproduced exactly, and three hand verifications performed
(E_asym, every firing in all three regimes; V3's counting repair; the
prefix-dominance selectivity matrix), recorded in
`../../OVERVIEW.md` ("Lane D verification").  Lane D's charter: the
run-level invariant for W2 after lane E closed the unbounded-alphabet
program and lane C fell the mixed-letter family — with the precise
target lane C's reduction: a run-level invariant must exclude exactly
V_h.  Secondary items, both delivered: adversarial scrutiny of Lemma
S's INDUCTION (lane B holds the boundary/arrangement angle), and the
sign-gate primitive E_asym.

This round's writes: the three patches (main.tex prop:toll's proof —
the level pigeonhole; main.tex thm:separators' node counts; Schema
P's residual — T5 — plus P4 in 14.5.2 and lem:structure's status), the
Corollary 1 repair in 14.5.2, and this section.  Lane D's independent
rederivations (the firing-count lemma and the exact count identities =
14.5b, rederived before reading ours, with an endorsement of the
never-rescan emphasis) are recorded in their report and not
duplicated here.

### 16.1 The sign-gate E_asym (PROVED; machine-verified 1025/0)

**Theorem (sign-gate, Lane D).**  On F1 = {a^i b a^j : i,j >= 1},

    merge  = [eps/b]X                (= a^{i+j})
    dbl    = [aa/a]X                 (= a^{2i} b a^{2j} on F1)
    diff   = [eps/merge]dbl
    T      = C(X, diff)
    Q      = C(K(b), merge)          (= b a^{i+j})
    E_asym = [eps/b]([eps/Q]T)

computes a^f with f = i+j for i <= j and f = 2(i+j) for i > j.

*Proof (Lane D's, hand-verified by the coordinator and re-derived at
integration).*  merge = a^{i+j}; dbl = a^{2i} b a^{2j} (the DOUBLER
[aa/a]X — replacement first; its twin [a/aa]X is the ST2 halver, the
round-15 correction — the two are not to be conflated).  diff: the
pattern a^{i+j} is b-free, so it tiles each run of a^{2i} b a^{2j}
separately, window count floor(2i/(i+j)) + floor(2j/(i+j)): i<j gives
0+1 -> a^{2i} b a^{j-i}; i=j gives 1+1 -> b; i>j gives 1+0 ->
a^{i-j} b a^{2j}.  T = X.diff: i<j: a^i b a^{j+2i} b a^{j-i}; i=j:
a^i b a^i b; i>j: a^i b a^i b a^{2j}.  The pass [eps/Q] scans for
b a^{i+j}: i<j — fires once at the first b (i+j <= j+2i always),
leaving a^{2i} b a^{j-i}, the second b starved (needs i+j <= j-i);
i=j — no occurrence (only i a's after either b, needs 2i); i>j — no
occurrence (i < i+j and 2j < i+j).  Then [eps/b] removes the b's:
i<=j: a^{i+j}; i>j: a^{2(i+j)}.  ∎  Machine: wall_verify.py part A,
625 grid + 400 random, 0 mismatches (coordinator-reproduced).

*Significance.*  (1) A b-free value whose length is a PIECEWISE
function of s = i+j with the piece selected by the SIGN of j-i: the
"piecewise" clause of Lemma S is essential — no pure function of s
(and by transfer no pure function of S on W2).  (2) The sign of the
run difference is EXTRACTABLE as a GATE — a two-valued behavioral fork
keyed on sign(j-i) — but not as a length: the two pieces are s and
2s, both s-functions on their pieces.  (3) It kills, by explicit
witness, three cheap invariant candidates: "b-free lengths are
S-functions" (false without pieces), "bounded asymmetry of b-free
lengths" (ratio 2), "exact symmetry".  Any run-level invariant must
be INEQUALITY-shaped (dominance), not function-shaped — this is what
motivated 16.3's invariant.

### 16.2 V1/V2/V3 — the toll's counting repair (CORRECTION OF RECORD)

Lane D's scrutiny of Lemma S's induction, three findings:

**V1 — case (i)'s "every run is O_E(S)" sub-claim is FALSE** (an
invalid inference — a bound on the SUM of run lengths does not bound
each run — and false in fact: [merge/'bb'].[b/a]X has a single
Theta(S^2) run while computed moduli are Theta(S), so the tile count
is Theta(S), unbounded; the "finitely many slab levels" step fails).
Found independently by Lane D; already repaired in round 15's fold-in
(14.5.2's long-runs-only reorganization, with the falsity flagged in
situ).  The bounded-tile-count route is dead on the explosive
stratum; the repair route is the schema — now including round 16's
T5, which makes the explosive stratum an explicit part of the
residual table.

**V2 — the salvage analysis.**  The dangerous configuration needs
BOTH (alpha) a scrutinee with SEVERAL runs whose individual lengths
are not S-functions (e.g. X itself: runs i, j, k) AND (beta) either a
sublinear-unbounded computed b-free modulus g(S), or a non-affine
computed interior run in an anchored pattern.  Why the explosives do
not immediately break the lemma: explosive values of the
[merge/'bb'] type COLLAPSE to a single run, and single-run
S-functional scrutinees re-S-functionalize the arithmetic.  Machine
evidence (Lane D): on the one-b family, m1 = a^s, p2 = [a/aa]m1 =
a^{ceil(s/2)}, p3 = [eps/p2]m1 = eps (s even) or a^{(s-1)/2} (s odd),
q4 = [a/aa]p3 — 729 + 365 checks, 0 mismatches: the attempted
non-affine modulus s mod ceil(s/2) COLLAPSES to affine-on-parity
classes (2 pieces), and one more nesting stays affine-per-class.
Standing conjecture (unowned, cheap to state): CONSTRUCTIBLE b-free
moduli are piecewise-affine with finitely many pieces — nothing
strictly between Theta(1) and Theta(S), no Sturmian-like modulus.
This is a special case of Schema P — P4's degree separation is its
run-length counterpart.

**V3 — Corollary 1's covering step was INVALID on the integer
lattice; replaced this round (the headline correction).**  As written
through round 15 — including this arc's own consolidation-round R5b
formulation — the step "the triangle is covered by the finitely many
pieces' traces, so some piece's trace is 2-dimensional / contains a
segment" is FALSE: the triangle IS coverable by finitely many thin
lattice sets — the j-levels {j = c}, c = 1..S_0-2, each a line — and
likewise by finitely many congruence classes.  The
continuous-simplex intuition (Baire/measure/dimension) does not
transfer to the discrete parameter space, and kind-(b) pieces have
empty interior in R^3 while their union covers the lattice.  Found by
Lane D; repaired TWO ways, both hand-verified by the coordinator:
  - the LEVEL PIGEONHOLE (the coordinator's, simplest): N cells each
    confined to a single j-level cover at most N of the plane's S_0-2
    j-levels, so for S_0 > N+2 some cell meets two levels — and two
    same-cell, same-S_0 points with different j ALREADY contradict
    (the a-count is h_r(S_0), fixed, while the output lengths
    differ).  All six toll targets work via the corresponding
    coordinate's levels (a^i, a^{j+k}: i-levels; a^k, a^{i+j}:
    k-levels; a^{i+k}: j-levels — on the plane, i+k = S_0 - j).
  - the DIAGONAL COUNTING (Lane D's, the general-target version): for
    any target length L affine in (i,j,k) and not a function of S,
    each cell's trace on the plane lies in the diagonal
    {L = h_r(S_0)}, a line meeting the triangle in at most S_0-2
    points, so N cells cover at most N(S_0-2) < (S_0-1)(S_0-2)/2
    points once S_0 >= 2N+3.
Both are now in 14.5.2's Corollary 1 and main.tex's prop:toll (with
the invalid step's history bracketed in place).  FINITENESS IS
LOAD-BEARING (Lane D): the pieces {j = c} themselves form a COUNTABLE
j-pinning cover of every plane, so the toll does not survive a
merely countable — or merely locally finite — partition.  This is why
round 16 adds P4 to Schema P: the degree separation delivers the
FINITE-partition form (every slab index bounded: affine runs are at
most C_E*S, and over S-typed parts polynomial division leaves bounded
jitter), and the toll invokes exactly that form.  The toll's status
is now exactly as main.tex states it: conditional on the structure
lemma in finite-partition form — unconditional on the non-explosive
stratum (runs affine there, partition finite), Schema-P-conditional
beyond.  Lane B's F-version corollary (no split on F = {a^i b a^j})
inherits the same repair verbatim.

### 16.3 PREFIX-DOMINANCE — the run-level tier (CONJECTURED, the invariant)

**Statement (Lane D's candidate invariant).**  For every expression E
over X = w2 and every piece of the (Schema-P-strengthened) partition:
every prefix a-count of E's value, taken at a RUN BOUNDARY, is
i-DOMINANT (type (alpha,beta,gamma) with alpha >= beta and alpha >=
gamma); dually every suffix a-count is k-dominant.  Notation: D1/D2
(lead/tail runs), P1/P2 (all prefix/suffix sums).  Run types: a run's
a-count as a function of (i,j,k) has TYPE (alpha,beta,gamma), its
slopes along i, j, k.

*Why inequality-shaped:* the sign-gate (16.1) shows function-shaped
statements ("lengths are S-functions") need piece structure the run
level does not have; dominance is a CONVEX CONE — closed under
addition — which is what makes concatenation close (below).

**Selectivity — the invariant excludes exactly V_h (the coordinator's
sharp target; matrix hand-verified by the coordinator):**

    V_h = a^k b a^{j+h} b a^{i+h}:  lead run k-typed (0,0,1):
                                   0 >= 1 FALSE — EXCLUDED by D1.
    rev(w2) = a^k b a^j b a^i:      lead (0,0,1) — EXCLUDED (same check).
    P1 = a^i b a^{j+k}:            prefixes (1,0,0), (1,1,1);
                                   suffix from the tail (0,1,1):
                                   k-dominant — LEGAL.
    P2 = a^{i+j} b a^k:            lead (1,1,0): i-dominant — LEGAL;
                                   tail (0,0,1) — LEGAL.

The exact selectivity the reduction demands: compatible with both
building blocks of lane C's transplant lemma, incompatible with its
target.  If the invariant is proved, V_h is unconstructible for every
h, and by the reduction (15.5) rev-on-W2 is impossible.

**The conditional theorem (the implication PROVED, one line).**  If
prefix-dominance holds for all constructible values on W2, then rev is
not computable on W2: rev(w2)'s lead run has type (0,0,1) and
i-dominance demands 0 >= 1.  ∎

**The C-split classification (PROVED, with a status marking).**  Every
C-decomposition rev(w2) = A.B with B non-constant has a factor
violating prefix-dominance; hence any witness has a PASS at the root,
and the conditional theorem needs only the pass case.  *Proof (Lane
D):* A is a proper prefix of a^k b a^j b a^i.  If A contains the
first b, A's lead run IS a^k exactly (the factorization is pointwise),
type (0,0,1) — violation, UNCONDITIONALLY.  If A is b-free, A = a^{k'}
with k' <= k, and the branch needs k' to TRACK k — i.e. the
piecewise-affine/partition structure — to conclude the type
(0,0,alpha), alpha > 0, violating i-dominance.  [COORDINATOR'S
MARKING (verification note a), folded in: the b-free branch SILENTLY
ASSUMES the prefix length tracks k — the partition/affine structure —
so that branch INHERITS the Schema-P conditionality like its
neighbors; the b-bearing branch is the unconditional one.]  Degenerate
splits (B = eps) recurse at smaller size; X itself is not rev.  ∎

**The complement-text obstruction (PROVED modulo Lemma S, hence
conditional on Schema P).**  The symmetric value a^{i+k} b a^j b
a^{i+k} is unconstructible: its a-total is 2(i+k)+j = 2S - j, not a
function of S.  This kills at the total level the naive strategy
"cut both flanks to a common length and swap" — the symmetric
scaffold is not a constructible intermediate at any depth.  ∎

**Induction status (Lane D's closure analysis).**  K: constants —
prefix sums (0,0,0), dominant.  V: X's prefix sums have types (1,0,0),
(1,1,0), (1,1,1) — i-dominant; suffixes dually k-dominant.  C: prefix
sums of A.B are (prefix sums of A) plus (total(A) + prefix sums of B),
total(A) a prefix sum by IH, and dominance is a cone — closed under
addition.  All three close (given the common refinement of the parts'
pieces — the schema again).  S (the pass): the output's run-boundary
prefixes are sums of text pieces between window cuts and copies of R;
the text pieces are NOT prefixes of F's value in general — a window
cut truncates a run from its left end by the pattern's lead.  Depth-1
passes survive by ABSORPTION (a cut prefix ending mid-run merges with
the inserted replacement or the run's remainder; the invariant
controls run-BOUNDARY prefixes — the b-structure carries the burden).
The case that escapes absorption: a window anchored at the text's
SECOND b whose pattern-lead x satisfies d_i(x) < d_j(x) strictly,
with |x| large enough to eat the middle run — the surviving cut
prefix i + (j - x) is non-i-dominant and IS a run boundary when R is
b-bearing at the seam.  THE L-FAMILY WINDOW CUT: the patterns with
the required lead magnitude and (j+k)-tail type are exactly lane C's
L-family (b-free a^{j+k}-typed leads, or one-b a^x b a^{j+k-x}).
Circularity analysis: a C-decomposition of an L-value has a proper
prefix that is b-free — non-constructible by the split toll
(conditional on Schema P, 16.2) — or degenerate: the C-case is
circular-closed.  The pass-case circularity is PARTIAL: the needed
pattern lead lies in (i, S) with (j+k)-tail, forcing L-family or
D2-violating pattern shape, but the exclusion of the D2-violating
branch at arbitrary depth is NOT done.  OPEN.  STATUS:
prefix-dominance is CONJECTURED — the induction closes at K, V, C and
at depth-1 passes by absorption; the remaining gap is exactly the
L-family window cut, and closing it appears to require the split toll
— making the invariant, like the toll, ultimately conditional on
Schema P.

**[ROUND 17 ADDENDUM — PREFIX-DOMINANCE REFUTED AS A UNIVERSAL
INVARIANT (status block).]**  Round 15C (17.1) constructs V_0 =
a^k b a^j b a^i outright — it IS E_rev's value — and V_1 =
[b.a/b]E_rev = a^k b a^{j+1} b a^{i+1}; both lead runs are
k-typed (0,0,1), excluded by D1, yet constructible.  The
conditional theorem above stands as an implication; its hypothesis
is FALSE.  The induction's two escape mechanisms, now located: (a)
MERGE-PADDED CONCATENATED SCRUTINEES — P1 = [eps/(b.mrg.a)](X.mrg.a)
and P2 = [eps/(a.mrg.s)](a.mrg.X) put windows at the first/last
separator with the merge absorbing the deletion (no cut prefix
survives: the deleted a's are the merge's, not the flank's); (b)
COMPLEMENT BOXES [s_m/L_m](mrg.s_m.mrg) whose output leads are
S-TYPED (S minus the pattern's trail), not flank-typed.  Invariant
programs closing over X-structured texts see neither step.  The
invariant's surviving scope: the NON-MERGE-PADDED, CONSTANT-PATTERN
stratum only.  The L-family window cut — the one gap this section
left open — is where the refutation enters: the large pattern lead
it demands is supplied by the merge (escape (a)), and the cut the
window makes deletes merge text, not flank ("it eats exactly the
merge, gluing E's natural tail" — 17.1).  Lane D's round-1 sweep
data stands as recorded; the refuting expressions live in the
merge-padded shapes this section's analysis did not name.

### 16.4 The convergence and the endgame chain

The wall (prefix-dominance) and the toll have converged on the same
load-bearing stone: **proving the invariant, proving the toll, and
completing Schema P have become the same program.**  The endgame
chain, every arrow owned except the schema's residual table — which
this round's T5 patch leaves COMPLETELY SPECIFIED:

    Schema P complete (residual entries (i) computed anchored
    replacements, (ii) nested computed patterns, (iii) T5 explosive
    nestings)
      ⟹ Lemma S in finite-partition form (P4's degree separation)
      ⟹ the split toll (the level pigeonhole + diagonal counting,
         16.2)
      ⟹ the L-family window cut closed (the circularity resolves)
      ⟹ prefix-dominance (the pass case closes)
      ⟹ V_h unconstructible for every h (the selectivity matrix)
      ⟹ rev impossible on W2 (the V_h-equivalence, 15.5)
      ⟹ with rounds 10-15B + separable rigidity (15.6) and the
        paper's reversal uniformity: rev not L-reachable over any
        fixed alphabet with >= 2 letters.

Arrow owners: the schema residual — this lane (the attackable
formulation closes 14.5.2; P0-P4 and the T1-T5 mechanisms proved; the
table's three nestings unowned); the toll's counting — Lane D + the
coordinator (DONE, this round); the L-family cut — Lane D's
localization + the toll; the prefix-dominance induction — Lane D
(K/V/C + absorption done, the pass case open); V_h-equivalence —
round 15; separable rigidity — lane E; reversal uniformity — the
paper (thm:rev-uniform).

**[ROUND 17 RE-ROUTE OF RECORD: the chain's last four arrows are
DEAD.**  Round 15C (17.1) constructs E_rev, which computes rev on W2
outright: "V_h unconstructible for every h" is false at h = 0 (V_0
IS E_rev's value), so "rev impossible on W2" is false, and with it
the fixed-alphabet collapse at the chain's end (the paper's
frontier claim "an obstruction can only live at the colliding-
separator family" — rewritten this round).  Prefix-dominance, the
chain's next-to-last stone, is refuted as a universal invariant
(16.3's addendum); the L-family cut is where the construction came
through, not a gap to close.  What survives is the chain's FIRST
HALF, now a self-contained program: Schema P (P4' + Telescope, at
skeleton level) ⟹ Lemma S in finite-partition form ⟹ the split
toll — a STRUCTURAL theorem about the b-free splits, off the main
line, since the construction never needs them (17.5's repositioning).
The main question — rev on all of Sigma*, i.e. VARYING separator
count — no longer passes through the toll at all.**]

### 16.5 Machine verdicts (Lane D's battery; coordinator-reproduced exactly; every run < 60 s)

- **wall_verify.py part A**: E_asym — 625 grid + 400 random = 1025
  checks, 0 mismatches.  Part B: the W2 catalogue sanity (ww = C(X,X),
  big2, E_aug = [R_diag/b]w2 with R_diag the lead-augmented w2,
  [b/ba]w2, E_M(bab)) — passes.
- **part C (sweep 1)**: 1500 tried / 884 clean, with 9 FLAG INSTANCES
  on 6 DISTINCT EXPRESSIONS — CORRECTED COUNT (Lane D's report says
  "9 flagged expressions"; per the coordinator's verification it is 9
  instances on 6 expressions, each carrying multiple tags).  All 6
  autopsied by dissect.py: cell crossings and residue sawtooths
  (e.g. runs oscillating 4-7 with no linear trend; a probe line
  straddling a firing threshold with the value collapsing to
  [1,1,1,1,0] on one side and [8,5,12,5,4] on the other).  Superseded
  by sweep2.py's cell-local method (the artifact fix).
- **sweep2.py** (cell-local slope measurement: each axis probed at 13
  points from 8 bases; a slope accepted only when the half-line
  slopes agree within 0.30; a violation flagged only when the
  accepted slope in one axis beats the dominant axis by more than 0.45
  in BOTH halves — bounded residue sawtooths contribute < 0.25):
  depth-3 uniform, seeds 424242 (1200/670), 111 (800/443), 333
  (800/463), 555 (700/402); depth-4, seed 444 (250/56 — low clean
  rate, depth-4 values blow past CAP or vary b-count); chain-biased
  (pure S-chains of depth 1-3 over a 19-value library of computed
  patterns/replacements — the construction-danger zone), seed 999
  (800/627).  TOTAL 4550 tried / 2661 clean, ZERO violations of
  D1/D2/P1/P2/VH/P1f/P2f/D1k-oneb.
- **controls.py**: E_swap on F1 flagged 5/5 at all bases (the
  positive control — the checker is not blind); E_asym clean; the
  catalogue passes.
- **p3/q4 modulus collapse**: 729 + 365 = 1094 checks, 0 mismatches.
- **seed 222**: pathological expression hit twice, timed out (exit
  124 at 55 s, unbounded blowup — coordinator-reproduced; a
  construction-budget datum, not evidence of anything else).
- Honest scope (Lane D's, endorsed): "clean" requires a fixed b-count
  across all 312 probe evaluations (bias toward tame values); the
  checker sees slope-level dominance only (a violation with slope gap
  < 0.45, or confined to a thin cell, is invisible); the machine
  falsifies only — these numbers are the ABSENCE of counterexamples.

### 16.6 Honest ledger for Round 16

- PROVED (hand): E_asym (the sign-gate, all three regimes); the
  counting repair (the level pigeonhole for the six coordinate
  targets; the diagonal counting for all affine targets — given
  finite partitions); the conditional theorem (prefix-dominance ⟹
  rev impossible on W2); the C-split classification (any witness has
  a pass at the root) — the b-bearing branch unconditional, the
  b-free branch Schema-P-conditional (coordinator's marking);
  the complement-text obstruction (modulo Lemma S); P4 (degree
  separation ⟹ finite partition, as an implication — 14.5.2); Lane
  D's V1 finding (independently of round 15's repair).
  [Round 17, two entries retired in place: P4's degree form is
  REFUTED as stated and repaired as P4' (14.5.2, 17.2); the
  conditional theorem's hypothesis is FALSE — prefix-dominance
  refuted as a universal invariant (16.3 addendum, 17.1).  This
  ledger records the round-16 state.]
- CORRECTED (this round, all recorded in situ): Corollary 1's
  covering step — INVALID on the integer lattice through round 15,
  replaced by the level pigeonhole + diagonal counting (the round's
  headline correction; 14.5.2 and main.tex); the 9-flag-instances /
  6-distinct-expressions count; R5b retired (R5a survives); main.tex
  thm:separators' node counts (pass nodes 3/15/35/63, not the tree
  sizes 14/58/126/218 — relabeled with both).
- CONJECTURED: PREFIX-DOMINANCE (K/V/C and depth-1 absorption closed;
  the L-family window cut open, itself circular on the toll);
  constructible b-free moduli piecewise-affine with finitely many
  pieces, nothing strictly between Theta(1) and Theta(S) (V2).
- OPEN: the L-family window cut (the invariant's pass case; the
  D2-violating-pattern branch at arbitrary depth unexcluded); Schema
  P's residual table (three entries, the statement now complete in
  scope); sublinear-unbounded b-free moduli (nonexistence unowned);
  depth >= 2 flank crossings in constructions (still no witness
  anywhere in the campaign — 2661 more clean expressions here).
- NOT DONE (scope): no new machine runs by this lane this round —
  integration and patches only; all numbers cited are Lane D's and
  the coordinator's, reproduced per 16.0/16.5.

### 16.7 Files

- `../rev-wall/` — Lane D's round: REPORT.md, wall_verify.py (parts
  A/B/C), sweep2.py, controls.py, dissect.py, prov.py, lcore.py,
  s1.log..s6.log.
- `../../OVERVIEW.md` — the coordinator's verification section ("Lane
  D verification", with the two artifact notes folded into 16.3/16.5
  above).
- This round's other writes: 14.5.2 (Corollary 1's counting repair
  with the bracketed correction of record; Schema P's P4 and the
  three-entry residual with T5); main.tex (prop:toll's proof and
  statement; thm:separators' parenthetical; lem:structure's status
  block); 15.7's R5 note; this section.

## 17. Rounds 15C + B-2 (integration): THE SAME-LETTER WALL FALLS —
## E_rev, the general engine, the Telescope skeleton, P4', and the
## frontier relocated to varying separator count

### 17.0 Charter and sources

Charter: `CHARTER_integration.md` (coordinator, 2026-09-22), round 4
for this lane.  Rule: every claim integrated must trace to the
coordinator's OVERVIEW.md entries ("Lane C round 15C + Lane B round 2
verification", "Correction + exact engine sizes") or to the listed
artifacts; "skeleton-level" and "refuted as stated" must be said
exactly; no new math.

Sources, with one provenance note: the charter relayed Lane C's 15C
report as "verbatim at /home/cc/.claude/jobs/54aca51d/tmp/
laneC_report.md — 8 KB"; the file at that path contains the ROUND 15
report (already integrated as 15.1-15.5).  The 15C content is taken
from the construction docstrings of `../rev-try/verify_t5_rev.py` and
`../rev-try/verify_t6_general.py` (Lane C's stated convention: the
hand proofs are fully re-derivable from the scripts' docstrings), the
logs' narrative addenda (`t5_rev.log`, `t6_general.log`), the
coordinator's OVERVIEW entry, and the charter — cited claim by claim
below.  Lane B's round 2 has no report file; it is reconstructed from
the OVERVIEW entry plus `../rev-split/` artifacts (`schema_p.c`,
`schema_p`, `schema_p.log`, `verify_lc_rev.py`), per the charter.
Before writing this section I re-derived by hand: E_rev's every
firing (P1, P2, Cc, Bb, T2, the final shave, all boundary cases),
the general engine's inter-separator arithmetic (S+1+r_{m-1}) and the
per-letter shave's exclusion of the last separator, and CH2's closed
form on the all-odd cell — all agree with the machine batteries.

### 17.1 Round 15C (Lane C, rev-try/): E_rev and the general engine

**THEOREM (E_rev — PROVED; three independent machine batteries).**
rev is computable in L on W2 = {a^i b a^j b a^k : i,j,k >= 0} over
Sigma = {a,b} — the same-letter all-varying family, the last fixed-
structure family — by

    E_rev = [b/(a.mrg.b)](Cc . a . Bb),   mrg = [eps/b]X = a^S,

via MERGE-CATALYZED SELECTIVE DELETION (the round's mechanism):
concatenating the merge next to the input gives ONE separator an
unbounded adjacent run, so a merge-flavored pattern fires there
UNCONDITIONALLY and at the other separator NEVER; the deletion
consumes exactly the merge, and the natural glue is what remains.

    P1 = [eps/(b.mrg.a)](X.mrg.a)  = a^i b a^{j+k}
      scrutinee a^i b a^j b a^{k+S+1}: the pattern b.a^{S+1} fires
      only at b#2 (b#2's following run k+S+1 >= S+1; b#1's j <= S
      < S+1); the window eats b#2 plus S+1 a's — exactly the merge
      plus the pad — leaving a^i b a^{j+k}.
    P2 = [eps/(a.mrg.b)](a.mrg.X)  = a^{i+j} b a^k
      scrutinee a^{S+1+i} b a^j b a^k: the pattern a^{S+1}.b fires
      only at b#1 (b#1's preceding run S+1+i >= S+1; b#2's j <= S
      < S+1), leaving a^{i+j} b a^k.
    Cc  = [b/P2](mrg.b.mrg) = a^k b a^{i+j}
    Bb  = [b/P1](mrg.b.mrg) = a^{j+k} b a^i
    T2  = Cc . a . Bb = a^k b a^{S+1+j} b a^i
    E_rev = [b/(a.mrg.b)] T2: the pattern a^{S+1}.b fires only at
      T2's second b (the first b's preceding run k <= S < S+1; the
      middle run S+1+j >= S+1 iff j >= 0), shaving exactly S+1 and
      leaving j.  Output a^k b a^j b a^i = rev(X).

The K('a') pad between Cc and Bb and the +1 in the final pattern are
PAIRED EDGE-GUARDS: at j = 0 the middle run is exactly S+1 (the pad
keeps the window alive), and at i = j = 0 the first b's preceding run
k must stay < S+1 (the +1 guarantees it even when k = S — without it
the first b would fire and eat the tail).  NO middle-run isolation
ever happens — the middle is an oversupplied merge and the final
pattern is merge-flavored: 13.7's wall is BYPASSED, not broken.  P1
and P2 are exactly the "unconstructible" one-b projections of the
round-15 transplant lemma (15.5): they are constructible, the
transplant closes with them, and E_rev is the witness.

**THE GENERAL ENGINE (any separator word, REPEATS ALLOWED — PROVED;
machine-verified on 11 words).**  For every k >= 1, every separator
word s_1..s_k whose letters are distinct from the filler a (repeats
allowed), and all varying runs, rev is computable on
{a^{r_0} s_1 a^{r_1} ... s_k a^{r_k}} by:

    mrg       = chained [eps/s] over the DISTINCT letters = a^S.
    del_last(E,s)  = [eps/(s.mrg.a)](E.mrg.a)     delete the LAST s:
       the concatenation boosts the last s's following run to
       rho+S+1; the pattern s.a^{S+1} fires there unconditionally
       (every other s-gap of E is a contiguous sum of original runs,
       <= S < S+1) and nowhere else; the window eats exactly the
       merge plus the pad, gluing E's natural tail (the surviving
       count is rho in every case).
    del_first(E,s) = [eps/(a.mrg.s)](a.mrg.E)     delete the FIRST s
       (mirror: the first s's preceding run is boosted).
    L_m = del_first^(m-1) del_last^(k-m) X
        = a^{r_0+..+r_{m-1}} s_m a^{r_m+..+r_k}
       (delete s_1..s_{m-1} in order, then s_k..s_{m+1} from the
       right; for a same-letter word this is exactly "keep the m-th
       occurrence" — repeats need no separate treatment).
    D_m = [s_m/L_m](mrg.s_m.mrg) = a^{r_m+..+r_k} s_m a^{r_0+..+r_{m-1}}
       (the complement box; the scrutinee mrg.s_m.mrg has a SINGLE
       s_m, so anchoring is unaffected by repeats in X).
    T'  = D_k . a . D_{k-1} . a . ... . a . D_1
       inter-separator runs exactly S+1+r_{m-1}; leading run r_k and
       trailing r_0 exact.
    final: ONE pass per DISTINCT letter, [s/(s.mrg.a)]: fires at
       every s-separator whose following run is >= S+1 — exactly all
       separators except the LAST (the rightmost, whose following
       run is r_0 <= S) — eating exactly S+1 and leaving r_{m-1}.
       Output a^{r_k} s_k a^{r_{k-1}} ... s_1 a^{r_0} = rev(X).

The 'a' pads and the +1 are the same paired edge-guards: without them
the last separator fires when r_0 = S (all other runs 0) and eats
the tail.  The engine unifies the round-14 complement engine (k=1),
15B's distinct-separator engine, E_mix, and E_rev (= the hand-built
k=2 same-letter instance).  K-ADAPTIVITY FACT (the base of Lane C's
unification round, now in flight): the per-letter pass is
count-adaptive — it fires at every separator except the last
REGARDLESS of k; only the positional middle projections L_m are
k-dependent.

**SIZES (two conventions, both machine counts; the coordinator's
correction of record applied).**
- The coordinator's gen_engine encoding (same-letter words, k=1..5):
  DAG nodes 9k^2+2k+4 (15/44/91/156/239), S-nodes k^2+k+1
  (3/7/13/21/31), S-DEPTH 2k+1 (3/5/7/9/11) — the del_first/
  del_last chains stack.  Mixed-letter words are within O(k) of
  these: cbb (k=3) 97/14/8; cbccb (k=5) 245/32/12; cbccbcc (k=7)
  465/58/16.
- Lane C's own encoding (verify_t6_general.py's counts(), TREE):
  k=2 (= E_rev) 75 nodes / S-depth 4 / AST depth 8; k=3: 160/5/12;
  k=4: 279/6/16.
- E_rev itself is the HAND-OPTIMIZED k=2 case: tree 75 nodes / 14
  S-nodes / S-depth 4; DAG 41 / 6.  gen_engine('bb') (44/7/5) is a
  SECOND, systematic encoding that AGREES WITH E_rev's function on
  W2 — it is not the hand-built E_rev (the wording fix from the
  coordinator's correction entry).
- DEPTH IS Theta(k), NOT CONSTANT: the coordinator caught their own
  relay prose generalizing E_rev's S-depth 4 (the hand-optimized
  k=2 case) to "S-depth 4 for every k" — FALSE; charters for lanes
  C/D/B were corrected before dispatch, no false claim reached an
  agent.  Do not write "S-depth 4 for all k" anywhere.
- Bottom line for the paper: for every fixed k, rev on the
  k-separator family is computable with S-depth 2k+O(1) and size
  Theta(k^2).  This SUPERSEDES 15B's distinct-separator bounds
  (4k^2-1 S-nodes, S-depth 2k, tree): repeats included, strictly
  smaller S-node counts (k^2+k+1 vs 4k^2-1), one more depth level
  (2k+1 vs 2k); 15B's theorem becomes a COROLLARY (see 15.4's
  supersession note).  Paper convention: syntactic size = TREE;
  DAG counts parenthetical.

**Consequences (all verified).**
1. The V_h-equivalence (15.5) survives with witness h = 0: V_0 =
   a^k b a^j b a^i IS E_rev's value; V_1 = [b.a/b]E_rev =
   a^k b a^{j+1} b a^{i+1}.  Every universal V_h-unconstructibility
   or projection-exclusion claim is refuted.
2. PREFIX-DOMINANCE (16.3) is REFUTED as a universal invariant
   (V_0's lead run is k-typed (0,0,1)); the escapes: (a)
   merge-padded CONCATENATED scrutinees (X.mrg.a, a.mrg.X) —
   enabling windows at the first/last separator, the merge absorbing
   the deletion; (b) complement boxes [s/L_m](mrg.s_m.mrg) whose
   output leads are S-typed (S minus the pattern's trail).
   Invariant programs closing over X-structured texts see neither
   step; the invariant survives only on the non-merge-padded,
   constant-pattern stratum (16.3's addendum).
3. Lemma S / Schema P UNTOUCHED: all intermediates S-total (mrg, P1,
   P2, Cc, Bb at S; T2 at 2S+1; the final pattern's total S+2), and
   Lane B's rebuild checked exactly this (every intermediate's
   a-content a function of S alone; the final pass entry-(ii)
   class: computed adjacent-letter pattern a^{S+1}b, O(1) firings
   under pinned comparisons).  The engine is a positive specimen of
   the residual table's entry-(i) classes (computed replacements at
   anchored sites — the boxes' replacements are the computed
   projections).
4. Lane E consistent: Gamma(E_rev) = {a,b} = Sigma — Corollary 4's
   constraint met with equality 0 (every letter a constant; no
   obstruction can be read off the unused-letter count).
5. The b-free splits (a^i, a^{i+j}, a^{j+k}) remain toll-excluded —
   and are never needed.

### 17.2 Lane B round 2 (rev-split/): the Telescope skeleton, and
### P4 refuted-and-repaired

**THE TELESCOPE LEMMA (closes Schema P's residual table at
PROOF-SKELETON level).**  Every window count is an S-function on
cells of a finitely parameterized arrangement, because
multiplicities enter only through template-group sums (P1) and every
per-run count telescopes to a letter total, a prior window count, or
a pinned constant.  The three residual entries close:
  (iii) T5 explosive tilings + nestings: c_w = (T_c − Lambda)/p
        exactly; CH3: T5^3 = a^{S+2S^3} exact (the triple nesting's
        closed form, machine-verified against the hand rule);
  (i) computed replacements at anchored sites: site types O(1)
        singular + per-template kappa_U; c_w = Sum kappa_U n_U +
        O(#segments);
  (ii) nested computed patterns on periodic regions:
        Sum floor(m/g) = (n_U − Lambda_g)/g.
The b-free-length closure uses the totals-IH at smaller depth (the
coordinator's addendum's point — load-bearing, non-circular).
STATUS: the mechanism is sound (coordinator-scrutinized at skeleton
level); the write-out — the provenance recursion and the
quasi-polynomial closure — is the remaining writing task, currently
unowned.  Lemma S's full proof (finite partition + S-functional
totals) is one write-out away; the toll inherits that status.

**P4 REFUTED AS STATED; REPAIRED AS P4'.**  CH2 = [merge/'bb'].
[bb/aa]X (merge = [eps/b]X): on the all-odd cell the output is
    a^{S(i+j-2)/2+1} b a^{S(k-1)/2+1} b a
(machine-verified closed form, coordinator-reproduced; re-derived
by hand at integration: [bb/aa]X tiles each a-run a^n to
(bb)^{floor(n/2)} a^{n%2}, giving b^{i-1} a b^j a b^{k-1} a on
all-odd; [merge/'bb'] then tiles each b-run of length L to
(a^S)^{floor(L/2)} b^{L%2}, and the a-leftovers merge across — the
first segment is S*(i-1)/2 + 1 + S*(j-1)/2 = S(i+j-2)/2+1).  The
first run is INDECOMPOSABLE as A(i,j,k)+P(S): its k-slope on a
fixed-S plane is -S/2, unbounded.  Root cause: the run absorbed a
PARTIAL group sum — individual block multiplicities are pinned
polynomials ((i-1)/2, floor(j/2), (k-1)/2), only P1's GROUP sums are
S-functions; the round-16 writeup conflated the two directions at
THREE sites (profile (B), P4's parenthetical, T5's parenthetical —
all repaired in place this round; P4's PROOF replaced, its
CONCLUSION kept).  REPAIR (P4'): run lengths live in the closure of
{affine junction parts; S-function template lengths} under sums,
products (S-function) x (pinned polynomial), and exact division —
affine x affine never arises; finiteness via exact polynomial
division + provenance recursion (+ cones + finite arrangements).
The TOLL SURVIVES the repair (only its derivation route changed).
Lemma S untouched: the totals still telescope — on the all-odd cell
the output's a-count is S(S-3)/2+3, an exact function of S
[the coordinator's OVERVIEW entry writes S(S-4)/2+3; the
machine-verified closed form gives S(S-3)/2+3 — a transcription
slip in the entry, corrected here; hand-checked at (1,1,1) -> 3
and (3,1,1) -> 8].  Also in the battery: CH9 = [a/merge].CH2 (the
degree collapse under computed-modulus division) and CH10 = the
modulus-(S+1) jitter-pinning case on S*m+1 runs.

**Battery (schema_p.c, C, caps 2^16).**  Rebuilt from source by the
coordinator: mode t5 (crafted chains vs hand-derived forms; chains
CH1 = [merge/bb].[b/a]X quadratic exhibit + wrong-formula control,
CH2 rule + P4 specimen, CH3 = T5^3, CH4-CH8 anchored/U^g count
formulas, CH9, CH10) reproduces BYTE-IDENTICALLY: 4,192 checks, 0
failures, the control FLAGGED (the harness works).  Mode cells
(random chains, within-(S,residue) equality; the cut-explained
violations are the known m=2 cut cells): run 1 = the default
invocation (seed 777111/1000) byte-identical — 765 exprs, 293,507
cells tested, unexplained 0; runs 2-3 (seeds unrecorded — Lane B's
bookkeeping slip, recorded as such): 604 exprs / 231,930 cells and
695 / 266,872, unexplained 0 both; 20+ fresh seed probes by the
coordinator all return unexplained 0 — the claim is
over-reproduced.

### 17.3 The coordinator's round-17 battery, and the size correction

**verify_round17.py (33 s, ALL VERIFIED — every encoding fresh from
the coordinator's own hand derivations, which preceded reading
either lane's scripts):**
- A  E_rev: 12^3 grid (boundaries incl.) + 500 random to 300 + 300
  adversarial scales (one run tiny 0-4, another huge 50-200, mixed
  orderings) — rev exact.
- A2 intermediates mrg/P1/P2/Cc/Bb/T2, 8^3 grid — exact.
- A3 prov never DB + injective (300 random).
- A4 laundered L_a.L_b.E_rev = rev with prov == () (7^3 + 100).
- B  V_0 = E_rev and V_1 = [b.a/b]E_rev (200 random to 60):
  V_0 -> w2(k,j,i), V_1 -> w2(k,j+1,i+1) — prefix-dominance
  concretely refuted.
- C  the general engine on 11 separator words, 800 cases each
  (600 random to 5 + 200 random to 40 per word): b (k=1 cross-check
  = the round-14 engine), bb (k=2 — agrees with E_rev), bbb, bbbb
  (k=3/4 same-letter), cbb, bcb, bcc, cbc (k=3 mixed with repeats),
  cb, bc (k=2 — E_mix cross-checks), cbccb (k=5, mixed with
  repeats).  Separator letters must be distinct from the filler —
  the engine's hypothesis; words containing 'a' as a separator are
  out of scope.
- D  CH2's all-odd closed form (grid 1..8 odd + 300 random
  residue-rule checks) — the indecomposable run confirmed.
- E  E_rev sizes: DAG 41 nodes / 6 S-nodes; TREE 75 / 14; S-depth 4.
Lane C's own scripts re-run by the coordinator: all VERIFIED
(verify_t5_rev 13.2 s + verify_t6_general 18.3 s; the logs carry
appended narrative blocks beyond script output, as in round 15).
Lane B's independent rebuild rev-split/verify_lc_rev.py re-run:
VERIFIED, 13.5 s.

**The size correction (coordinator, in OVERVIEW as "Correction +
exact engine sizes").**  While producing size counts for the paper,
the coordinator caught an error in their own relay prose: E_rev's
S-depth 4 (the hand-optimized k=2 case) had been generalized to
"S-depth 4 for every k" — FALSE (the machine counts are 2k+1 for
the systematic encoding, k+2 for Lane C's own).  Charters for lanes
C/D/B were corrected before dispatch; no false claim reached an
agent.  The canonical counts for the paper are the coordinator's
(17.1's size block), tree convention primary.

### 17.4 Corrections of record applied in place this round

- 13.7: the bracketed round-15 correction extended with the FINAL
  resolution — the same-separator wall is bypassed (E_rev; no
  middle-run isolation; clause (c) never invoked by the winner);
  no surviving content question at fixed separator count.
- 14.5.2 (Schema P): the three conflation sites repaired (profile
  (B); P4's parenthetical and proof — refutation bracketed, P4'
  installed, conclusion kept, skeleton status marked; T5's
  parenthetical); the residual table's closing status updated to
  CLOSED AT SKELETON LEVEL (Telescope); Corollary 1's status
  updated (P4' route) and the toll REPOSITIONED off the main line.
- 15.4: supersession note — 15B's theorem becomes a corollary of
  the general engine; its scoping claim ("an obstruction can live
  ONLY where separators collide") refuted; counts reconciled in
  both conventions.
- 15.5: status block resolved (h = 0 witnessed); the transplant
  lemma's OPEN questions answered (P1, P2 constructed; V_0 = E_rev's
  value; the wall analysis's class scope and its superseded
  completeness sentence marked).
- 16.3: the addendum (prefix-dominance refuted as a universal
  invariant; escapes (a)/(b); surviving scope; the L-family cut is
  where the refutation enters).
- 16.4: the endgame chain re-routed (last four arrows dead; the
  surviving half is a self-contained structural program).
- 16.6: two ledger entries retired in place with a bracketed note.

### 17.5 Program status after these rounds — the frontier relocated

rev is computable on EVERY fixed separator-structure family over
any finite alphabet (the general engine).  The unbounded-alphabet
negative (Lane E, separable rigidity) stands.  The fixed-alphabet
question now lives EXACTLY at VARYING SEPARATOR COUNT: one
expression computing rev on ALL of Sigma* (Union_k W_k) — or an
obstruction there.  The toll is no longer on the path to the main
question (it constrains the b-free splits, which are not needed);
it is a self-contained structural theorem.  In flight, not waited
on (their results arrive as later rounds): Lane C — the
unification construction (varying k; the k-adaptivity fact of
17.1 is its base); Lane D — the varying-k obstruction hunt; Lane B
— the Telescope at varying k.

### 17.6 Machine verdicts (all runs < 60 s)

- rev-try/verify_t5_rev.py (13.2 s): REV grid 11^3 + 600 random to
  250 + intermediates 8^3 + prov (300) + laundering (7^3 + 100) —
  ALL VERIFIED; the adversarial addendum (360 cases, one run tiny /
  one huge) — VERIFIED (the first 4500-case attempt was killed by
  its own 55 s timeout — case count too high — superseded by the
  slim run; recorded).
- rev-try/verify_t6_general.py (18.3 s): k=1..4 same-letter (grids
  9^2/8^3/5^4/4^5 + randoms), mixed b,b,c / b,c,b / c,b (grids +
  randoms + intermediates), k=2..4 size counts, k=3 prov +
  laundering — ALL VERIFIED.
- rev/verify_round17.py (33 s): parts A/A2/A3/A4/B/C/D/E — ALL
  VERIFIED (17.3's list).
- rev-split/verify_lc_rev.py (13.5 s): the independent rebuild —
  E_rev == rev (11^3 incl. zero boundaries + 600 random), Lemma S
  consistency (all intermediates' a-content functions of S), final
  pass entry-(ii) class — VERIFIED.
- rev-split/schema_p (+ .c, .log): mode t5 4,192 checks / 0
  failures (control FLAGGED); mode cells 765 exprs / 293,507 cells /
  unexplained 0 (run 1 byte-identical; runs 2-3 and 20+ fresh
  seeds agree).

### 17.7 Honest ledger for this round (integration; no new machine
### runs by this lane — all numbers are the lanes' and the
### coordinator's, re-verified per 17.3/17.6)

- PROVED (hand, machine-verified three ways): E_rev computes rev on
  W2; the general engine computes rev on every fixed separator
  structure (repeats allowed); V_0 and V_1 constructible; the CH2
  closed form; the engine's k-adaptivity fact.
- CLOSED AT SKELETON LEVEL (mechanism + formulas machine-checked;
  write-out unowned): the Telescope Lemma and with it Schema P's
  residual table, hence Lemma S in finite-partition form, hence
  the toll's condition.
- REFUTED: P4 as stated (CH2); PREFIX-DOMINANCE as a universal
  invariant; the scoping claim "a fixed-alphabet obstruction can
  only live at the colliding-separator family"; the wall analysis's
  completeness sentence ("every final-pass route reduces to V_h, a
  T3* correlation, or the dead split" — the fourth route, the
  merge-flavored remnant shave, is the one that computes rev).
- CORRECTED (this round, all bracketed in situ): the three
  conflation sites; the relay "S-depth 4 for every k"; the
  OVERVIEW's S(S-4)/2 transcription (the closed form gives
  S(S-3)/2); this section's report-file provenance note (17.0).
- OPEN: rev on all of Sigma* (varying separator count — the new
  frontier); the Schema P write-out (provenance recursion,
  quasi-polynomial closure); the unification construction; varying-
  k invariants.  Whether an obstruction exists at varying k is
  open in both directions.

### 17.8 Files

- `../rev-try/` — Lane C round 15C: verify_t5_rev.py + t5_rev.log,
  _edge_t5.py, verify_t6_general.py + t6_general.log (REPORT.md
  there is the round-15 report, integrated as 15.1-15.5);
  CHARTER_unification.md (the next round, in flight).
- `../rev-split/` — Lane B round 2: schema_p.c + schema_p +
  schema_p.log, verify_lc_rev.py (the E_rev rebuild).
- `./verify_round17.py` + `round17_verify.log` — the coordinator's
  battery (this round's own directory).
- `../../OVERVIEW.md` — the coordinator's entries "Lane C round 15C
  + Lane B round 2 verification" and "Correction + exact engine
  sizes".
- `CHARTER_integration.md` — this round's charter.
- This round's other writes: the in-place corrections of 17.4;
  main.tex (the frontier subsection rewritten — 17.9).

### 17.9 The paper integration (charter Part 2, executed)

- ssec:frontier REWRITTEN: the positive general theorem (fixed
  separator structure, repeats allowed, with the engine's proof
  sketch and both size conventions), E_rev's mechanism paragraph
  (merge-catalyzed selective deletion, paired edge-guards), the
  V_h paragraph resolved at h = 0, thm:correlations marked
  subsumed, and the NEW open problem — varying separator count
  (one expression for all of Sigma*).
- lem:structure: P4's refutation + P4' + the Telescope at skeleton
  level; the finiteness-is-load-bearing note kept.
- prop:toll: repositioned off the main line (self-contained
  structural theorem; the b-free splits the construction never
  needs); the closing paragraph rewritten to the new frontier.
- thm:separators: generalized (repeats allowed) with the engine;
  Patch 2's counts superseded by the round-17 size table.
- Wire-ins (the landscape's open problem, the alphabet section's
  intro, the conclusion) updated to the new story: fixed structure
  always computable, unbounded alphabets never, varying k open.
- Build: clean (0 errors, 0 undefined references, 0 overfull);
  page count reported to the coordinator.  Nothing committed to
  git (the user commits).

## 18. The endgame rounds (integration): THE UNIFICATION IS
## ARCHITECTURALLY IMPOSSIBLE — the conditional dichotomy

### 18.0 Charter and sources

Charter: `CHARTER_integration5.md` (coordinator, 2026-09-22, round 5
for this lane).  Rounds 15C/B-2 integration verified end-to-end by the
coordinator (build reproduced 87pp/0/0; §17 checked claim by claim; my
CH2 correction S(S-3)/2+3 accepted and machine-verified, the
coordinator's OVERVIEW entry fixed; the 293,307 cells slip corrected
to 293,507 there and in 17.2/17.6 above).  The coordinator's own patch
to main.tex — prop:toll's tail scoped to AFFINE targets, with the
parenthetical that the diagonal count does not reach
residue-dependent lengths — is preserved verbatim this round and must
survive every future pass of this lane.

Sources, all verified by the coordinator (OVERVIEW entries "Lane D
round 2, Lane A round 4, Lane C round 16 verification" and "Lane B
round 3 verification"):
- D2: `../rev-wall/REPORT.md` sections R2.1-R2.2.8 (its own writes)
  + `varyingk_check.py`/`varyingk.log` + the coordinator's
  `verify_r2_wall.py` (the direct SNF decomposition check, 765/765).
- C16: `../rev-try/ROUND16_REPORT.md` (transcribed by the coordinator
  with scrutiny notes) + `verify_r16.py`/`r16.log` (including the
  think-pass narrative recorded BEFORE machine work, per the charter)
  + `verify_r16_coord.py`/`r16_coord_verify.log` (the coordinator's
  fresh-encoding battery, ALL VERIFIED).
- B3: `../rev-split/ROUND3_REPORT.md` (transcribed by the coordinator;
  reproduction caveats noted below) + `varying_k.c`/`varying_k`/
  `varying_k.log`.
Before writing I re-derived by hand: SNF's three-line proof; the
diagonal-census constructions E_abk and E_ab (including why E_abk
fails at k = 0); E_block and E_alt (including the output identity
a.(ab)^k.a = aa.(ba)^k); E_poll's mechanism; and the halver census
law ceil((k+1)/2) against the log's k = 1..7 rows (1,2,2,3,3,4,4) —
all agree with the machine batteries.

### 18.1 Lane D round 2 (rev-wall/): the refutation recorded, and the
### varying-separator-count hunt opens

**R2.1 — prefix-dominance: chapter closed.**  The lane records the
refutation (16.3's addendum is the integration of record) with the
autopsy, at four heads:
  (a) MERGE-PADDED CONCATENATED SCRUTINEES: the working patterns fire
      on X.mrg.a and a.mrg.X — the input concatenated with a computed
      merge text; the lane's sweeps scrutineed X and library chains
      only.  The pad puts an unbounded run next to a separator, so a
      computed pattern fires there unconditionally and never at the
      other separator.
  (b) COMPUTED PATTERNS: P1/P2's patterns CONTAIN the merge
      subexpression (b.mrg.a, a.mrg.b); the sweep library used
      constant patterns plus a few fixed computed ones, never computed
      b-bearing patterns at this nesting.
  (c) COMPLEMENT BOXES: [b/P](mrg.b.mrg)'s output lead = S minus the
      pattern's lead — an S-TYPED computation whose RESULT is k-typed
      by subtraction inside the pad run; dominance tests look for
      k-typed construction, complementation is invisible to them.
  (d) WHERE THE INDUCTION ACTUALLY BROKE: the round-1 pass-case
      analysis assumed the text pieces between windows behave like
      prefixes of F's value (left cuts); a window whose lead consumes
      from the LEFT edge of a pad run leaves a SUFFIX-REMAINDER as the
      new head — the head can be (pad run) − (computed lead), a
      difference, not a prefix.  The "absorption" argument never
      considered right-remainders.
Verdict: the invariant survives only on the non-merge-padded,
constant-pattern stratum — exactly the stratum the 4550-expression
sweep sampled; the checker was sound for what it saw (E_swap flagged,
the catalogue passed), the sample space omitted the winning stratum.
Future sweeps' construction-danger zone must include C(X, computed)
scrutinees and computed b-bearing patterns.  Surviving round-1 content
(unchanged): the count identities + the 14.5b endorsement, the Lemma S
scrutiny findings V1-V3, E_asym, the complement-text obstruction, the
C-split classification (now vacuous), the sweeps (real
non-violations, wrong stratum).

**R2.2.1 — the Sweep Normal Form (SNF), PROVED.**  For E = S(R,P,F)
and any input where defined, with R = R(w), P = P(w), F = F(w): the
greedy leftmost scan partitions F into disjoint windows; the output is
    E(w) = q_0 R q_1 R ... R q_t
with q_0..q_t the surviving chunks of F IN ORDER (t >= 0 fire sites;
R the SAME string at every firing; t = 0 gives E(w) = F(w)).
*Proof.*  Greedy leftmost, never rescans inserted text: each window is
an occurrence of P in the original text, windows disjoint, scan
proceeds left to right; survivors appear in order.  (3 lines from the
semantics.)  ∎  Machine: the lane's independent greedy evaluator vs
the campaign evaluator, 990/990; the coordinator's addition — the
decomposition verified DIRECTLY against the campaign evaluator
(765/765).  CONSEQUENCES (the uniform interleave): in any single
sweep R is evaluated ONCE — every firing emits the SAME text;
deletions are occurrences of one fixed value; site-specific output
comes only from distinct S-nodes or from remnants, which appear in
input order.  Stacks to depth d: sweep d+1's scrutinee = sweep d's
output.  The only REORDERING power in the whole language: the C-tree
(fixed arity, fixed order) and R-copies (identical, repeated).

**R2.2.2 — the diagonal census (hand-derived, machine-confirmed).**
  - b^k |-> b^k: identity (X).  NOT obstructive.
  - a.b^k |-> b^k.a: COMPUTABLE UNIFORMLY IN K:
    E_abk = [R/X](X.a) with R = [eps/a]X.  On w = a.b^k (k >= 1):
    R(w) = b^k; the scrutinee a.b^k.a contains X = a.b^k exactly at
    position 0 (the only a-block is the prefix); the single firing
    outputs b^k.a = rev(w).  Fails only at k = 0 (the pattern 'a'
    fires twice).  40/40 + the coordinator's fresh encodings (60
    k-values + boundary + off-family honesty): VERIFIED.
  - (ab)^k |-> (ba)^k: COMPUTABLE UNIFORMLY IN K, ONE CONSTANT PASS:
    E_ab = [ba/ab]X fires at positions 0,2,..,2k-2; output (ba)^k =
    rev((ab)^k).  40/40 + fresh encodings: VERIFIED.
  - a^i b a^i b a^i and every palindrome-profile family: rev =
    identity there; X computes it.  NOT obstructive.
LESSON: period-k diagonals and single-run-varying diagonals fall to
constant/uniform tricks; the obstruction, if any, lives on ASYMMETRIC
profiles with all runs DISTINCT — the increasing power diagonal
D(k;B) = a^{B^0} b a^{B^1} ... b a^{B^k} (B >= 3: subset sums unique,
2B^m != B^{m'}, residues recognizable).

**R2.2.3 — how k = 2 fell, and the resource it consumed.**  The k=2
engine's three mechanisms (all confirmed in E_rev): (1) PADS
(X.mrg.a / a.mrg.X / mrg.b.mrg put unbounded computed runs next to
chosen separators, making them the ONLY firing sites of computed
patterns — the S+1 trick); (2) COMPLEMENT BOXES (the surviving head is
the pad run MINUS the pattern's lead: S − (i+j) = k, a k-typed lead
from an S-typed pad); (3) PER-POSITION KNOWLEDGE (each pattern encodes
"first"/"second" via its pad; the engine spends Theta(k) patterns for
k separators).  The uniform-k analogue of (3) fails: finitely many
S-nodes = finitely many patterns, so the pigeonhole must be about
STRUCTURE.  Selectivity landscape (hand analysis, increasing
diagonals): unpadded junction patterns a^x b a^y fire at junction m
iff r_{m-1} >= x and r_m >= y — a THRESHOLD SET {m >= m_0},
position-blind within the qualifying set (a uniform edit); double
thresholds select one junction j — but x, y must be computed values,
and a computed value of size ~ lambda.B^k selects a junction at FIXED
OFFSET log_B(1/lambda) from the TOP (or a fixed position from the
bottom, for constants): finitely many patterns cover finitely many
fixed-offset positions + finitely many pad-marked positions + uniform
threshold classes.  The reversal needs Omega(k) junction-specific
edits.  [To be made a theorem — conjecture V3 below.]

**R2.2.4 — the arithmetic fixed point (the wedge).**  For the output's
HEAD to be r_k on the diagonal, the assembly must cut the merged pad
at exactly S − r_k = sum_{i<k} r_i ("sum minus max").  Each route is
circular: (i) cut the pad a^S with a pattern a^y.b — needs y =
sum_{i<k} r_i as a constructible b-free length; (ii) delete the last
run (pattern b.a^{r_k}) — needs r_k; (iii) threshold-exclude the max —
whole-run deletion needs the run's length (Match Anchoring: interior
consumed exactly = the pattern KNOWS the length), partial cuts leave
impure residues r_m − y.  DUALITY: r_k and S − r_k are
inter-constructible (complement boxes convert either into the other);
NEITHER is reachable without the other.  At k = 2 the circle is
broken from outside: sum_{i<2} r_i = r_0 + r_1 is an ADJACENT MERGE —
constructible by a pad-anchored junction deletion without knowing r_2
(E_rev's P2 lead).  At k >= 3 the sum spans k runs: a single window
spanning k−1 separators must contain them as INTERIOR runs (Match
Anchoring: exact) — its value is "w minus its last run"-shaped — the
same extraction problem one level down.  [The k=2-vs-k=3 boundary is
where the fixed point bites — confirmed by the R2.2.6 sample.]
  - CONJECTURE V1 (LAST-RUN EXTRACTION): no expression computes
    w |-> a^{r_k} on the increasing diagonals, for all k.
  - CONJECTURE V2 (ARITHMETIC SPLIT / SUM-MINUS-MAX): no constructible
    b-free value has length sum_{i<k} r_i on the increasing diagonals,
    for all k.  (The varying-k analogue of the split toll — but on a
    1-parameter family Lemma S is VACUOUS (round 13's lesson), so this
    needs run-level structure, not total-content counting.)
  - CONJECTURE V3 (SELECTIVITY COVERING): fixed expressions reach only
    pad-marked junctions, fixed-offset-from-an-end junctions, and
    uniform threshold classes — insufficient for reversal.
  - TARGET THEOREM (conditional, next rounds): V2 (with the
    head-propagation lemma) implies no E computes rev on the increasing
    diagonals, hence none on all of {a,b}*.  The airtight version needs
    the run-level schema induction on the k-axis.

**R2.2.5 — dec-capacity probe (machine; falsification direction).**
dec(V) := longest strictly-decreasing subsequence (by length) of V's
maximal-run sequence.  dec(X) = 1; dec(rev(D(k;B))) = k+1.  325 random
depth-3 expressions on D(k;3), k = 1..5: max dec = 3 at EVERY k — dec
does NOT grow with k on the sample.  COORDINATOR'S CAVEAT (folded in
as the round's correction): the probe's len <= 600 cap silently
excluded the EXPLOSIVE STRATUM, where the naive dec claim is FALSE —
[X/a]X has dec(output) = 2,3,5,6 growing with k (sizes 21,197,1723,
15129); Lane C INDEPENDENTLY found the same class from the
construction side ([X/'b']X, LDS ~ k at S-depth 2).  Convergent
discovery, recorded: any dec/LDS-type invariant must carry
VALUE-STRATIFICATION (disjoint value ranges across copies), not
subsequence counts alone.  (Cosmetic: D's part-C label prints "B=4"
while the code uses B=3; the report says B=3 correctly.)

**R2.2.6 — extraction hunt (machine; falsification direction for
V1/V2).**  700 random depth-3 expressions on D(k;3), k = 1..5, tested
for: value = a^{r_k}; value = a^{S-r_k}; head run = r_k; value = w
minus last run.  Hits only at k <= 2, and the k=2 "sum-minus-max" hit
dissected to a CONSTANT coincidence (a^4 on all of k = 1..6 — the
coordinator's replay confirms).  ZERO genuine extraction hits; none at
k >= 3 in the sample.  At k = 2, sum-minus-max = r_0 + r_1 = the
adjacent merge — constructible, exactly as the k=2 engine requires.

### 18.2 Lane C round 16 (rev-try/): the unification is architecturally
### impossible

**VERDICT: IMPOSSIBLE — no fixed expression E computes rev on all of
{a,b}*.**  Delivered as an ARCHITECTURAL proof: one core lemma fully
proved by hand, the descent formulated precisely with both escape
routes identified and killed on analysis, and exactly TWO
formalization lemmas remaining (both in Lane B's program; statements
below).  Per the charter the pure-think pass came FIRST — the
obstruction was written down before any machine work (r16.log's
appended think-pass narrative; the coordinator's battery confirms the
log's script output byte-identical, so the think-pass is genuine).

**The reformulation that organizes everything.**  rev on {a,b}* is not
"swap letters" — it is the MIRROR-PLANT: reflect the b-positions about
the center of the a-material, i.e., reverse the gap/run sequence
(i_0, i_1, ..., i_k) -> (i_k, ..., i_1, i_0); equivalently, write the
merge a^S (S = total a's) and plant each b at depth equal to its
right-a-count in w.  Every mechanism ever found for reversing (E_rev,
the engine, block-swap, phase-swap) is a way of buying that plant.
The question is whether a FIXED DAG can buy unboundedly many plants.

**Lemma FP (the Final-Pass Lemma — PROVED by hand; coordinator-scrutinized
line by line).**  Suppose E = [R/P]F and E(w) = rev(w) for all w in the
super-increasing family w^(k) = a^{2^0} b a^{2^1} ... b a^{2^k} (k
varying).  Then for each large k:
  1. R is single-b or pure: if R's value had an interior a-run, that
     run's text is emitted at EVERY firing, so the output's run list
     repeats a value; rev(w^(k))'s run values are the distinct powers
     2^k...2^0, each exactly once — so any nonempty interior forces
     t = 1, and a t = 1 final pass changes nothing structural (single
     splice; the reversal must then already live in F up to that
     splice — the descent applies directly).  [The b^m (m >= 2)
     exclusion: consecutive b's — rev(w^(k))'s runs are positive, so
     adjacent b's cannot appear.]
  2. Hence the output's run list is EXACTLY the remnant stretches of F
     concatenated in F-order, separated by single b's, each remnant run
     tweaked by at most the two boundary bites of the adjacent
     windows — bites that are the SAME (p0, p1) at every site (one
     pattern, one greedy).
  3. Consequently rev(w^(k))'s run list is an IN-ORDER EXTRACTION from
     F's run list (delete window material), with per-element tweaks
     from a fixed finite set of uniform subtractions.
COORDINATOR'S WRITEUP PRECISION (folded in): the tweak set includes
ADDITIVE contributions from R's flanks (a^{m1} b a^{m2} merges its
flanks into adjacent remnant runs), so the finite tweak set is
{−p0, −p1, +m1, +m2}; q_0 and q_t have only one bite each.

**The descent, and why both escapes die (ANALYSIS-GRADE, per the
ledger).**  FP(3) says F's run list contains the reversal as an
in-order subsequence with uniform tweaks.  Recurse into F =
[R'/P']F': those reversal-runs come from F'-remnants (F'-order) or
from the INTERIORS of the t' copies of R', as contiguous kept pieces.
  - ESCAPE A (stratified picks across many copies): copies of one R'
    with many distinct interior values could donate one element each,
    values stratified across copies.  This is a REAL phenomenon — it
    refuted the lane's first invariant ("LDS(out) <= 2^{S-depth(E)}":
    [X/'b']X has LDS ~ k at S-depth 2) — but it cannot build the
    reversal: the kept pieces from different copies must occupy
    pairwise DISJOINT VALUE RANGES (they sit at strictly decreasing
    positions of the output), so R'-interior must contain that many
    distinct deep values at disjoint positions AS CONTIGUOUS
    DECREASING STRETCHES; distinct deep values are distinct input
    runs, so R' itself must already contain a deep-rich decreasing
    structure — the descent recurses into R' unchanged.
  - ESCAPE B (phase carving): let the copies be of an X-like
    (increasing) R', and let the FINAL pass's windows carve a
    different run out of each copy, the carve depth controlled by the
    greedy phase, i.e., by the F-side remnant lengths between
    firings.  The kill is a DELETION-RATE/TUNING ARGUMENT: to carve
    run 2^j out of a copy, the windows must consume the adjacent runs
    1,...,2^{j-1} and the material after; a pattern bites at most
    (p0+p1) from any single run per adjacent firing, and pattern
    flanks are pinned values (~ alpha.S + beta, the schema): only the
    top-O(depth) run-sizes 2^j (j >= k+1-m for alpha = 2^{-m}) are
    bitable by big-flank patterns, while deep runs are only bitable by
    constant or tweak-flanked flanks — and each distinct deep
    run-size needs a flank tuned to that size.  A fixed pattern has
    finitely many runs; tuning to ~k distinct depths needs ~k
    patterns, i.e., Omega(k) S-NODES: the size lower bound,
    consistent with the engine's Theta(k) depth and Theta(k^2) size.
    (The descent also self-identifies: the phase sequence needed to
    walk the carve from 2^k down to 2^0 is the power sequence itself —
    the reversal — so the deeper level must encode the reversal as
    remnant lengths, and the recursion terminates at X, which is
    increasing.)

**The quantitative conclusion (CONJECTURE-GRADE until the two lemmas
land):** any E reversing the k+1 super-increasing runs has
#S-nodes >= Omega(k) — the mirror-plant needs ~k plants and each
S-node supplies O(1) of them once the pinned schema fixes what a
computed flank/tweak can be.  A fixed E has fixed #S-nodes, so it
fails for k beyond its bound.  Contradiction: no fixed E reverses all
of {a,b}*.  With E's own constants the failure is EFFECTIVE at
k > f(|E|).

**The two remaining lemmas (exact statements; both in Lane B's
program).**
  1. PINNED-SCHEMA AT VARYING K, SHARP FORM (load-bearing): for a
     fixed expression V, on w^(k) with S = 2^{k+1}−1: every a-run of
     V(w^(k)) is either an EXTRACTION TWEAK (within a V-fixed constant
     of some input run 2^j) or a PINNED AFFINE VALUE from a finite
     V-fixed set {alpha.S + beta}, and each pinned function sits at
     top-O(depth) run-sizes only — formally: the set of j-depths hit
     infinitely often by pinned values is finite.  (The L3 battery
     machine-illustrates this for a 6-value battery, k <= 6,
     tweak-or-affine, tolerance 8; e.g. del_last's glued run
     2^{k-1}+2^k = (3/4)(S+1) exactly — pinned.  The SHARP form —
     exact equality, no tolerance — is what closes Escape B.)
  2. THE TUNING/DELETION-RATE LEMMA: each distinct deep run-size needs
     a flank tuned to that size; ~k depths need Omega(k) S-nodes.
     [B3's finding, folded in: this lemma must be MERGE-SENSITIVE —
     see 18.3's separation budget and pollution witness.]
COORDINATOR'S BRIDGE NOTE (load-bearing for lemma 1): B3's halver
degeneration (18.3, MT(b): totals are NOT functions of (S_a, k) in
general) does NOT kill lemma 1 on w^(k), whose residues the family
pins ITSELF (one odd run, distinct powers) — the lemma must EXPLOIT
the family's residue structure rather than assert a general
(S_a,k)-granularity.

**Positive byproducts (machine-verified; the coordinator's fresh
encodings agree).**
  - P1 E_block: rev on {a^i b^k} by SKELETON SEPARATION — B = [eps/a]X
    = b^k (pure-b skeleton, total, k-adaptive), mrg = [eps/b]X =
    a^i, E_block = [B/(X.b)]((X.b).mrg): the scrutinee literally
    begins with the pattern value X.b (its only occurrence), single
    firing swaps cluster for material.  Grid 13^2 incl. all boundaries
    + 400 randoms to 200 + intermediates: VERIFIED (the coordinator's
    battery: 15^2 + 500 random, all boundaries).
  - P2 E_alt: rev on {(ab)^k aa, k >= 1} by PHASE SWAP — R =
    [eps/'aa']X = (ab)^k, P = [eps/'aa']([ba/'ab']X) = (ba)^k; (ba)^k
    occurs in w_k only at position 1; single firing; output
    a.(ab)^k.a = aa.(ba)^k = rev(w_k).  k = 1..44 + intermediates
    k = 1..14: VERIFIED (the coordinator's battery: k = 1..69 +
    pattern uniqueness).  (k = 0 is the empty-pattern edge; the claim
    is k >= 1.)
  - L1/L2 collapse facts: [R/P](P.G) = R.G when P not in G;
    [R/V](mrg.V.mrg) = mrg.R.mrg for one-b V — 7^3 W2 grid (the
    coordinator's battery: 8^3): VERIFIED.
  - L3 schema illustration: on w^(k), k <= 6, a battery of computed
    values (mrg, skeleton, halver, doubler, del_last, del_first) has
    every run a tweak of some 2^m or affine in S: VERIFIED.

**Three letters do not help.**  The argument runs verbatim on any
finite alphabet with >= 2 letters: on Sigma = {a,b,c} apply the whole
analysis to the a-runs with separators b,c (the mixed-letter engine
already handles every FIXED structure over any finite alphabet); FP,
the copy-stratification kill, and the tuning kill are all statements
about run values and greedy mechanics, independent of alphabet size.
Conversely the a-free subfamily {b,c}* reversal is Lane E's
unbounded-alphabet case in miniature, excluded for the same reason.
Scratch-letter encodings of run values cannot escape: any encoding's
runs are themselves run values subject to the same pinned/tweak
dichotomy and the same order-preservation channels.  The dichotomy is
by STRUCTURE (fixed vs varying separator count), not by alphabet size
(beyond |Sigma| >= 2).

**The proposed dichotomy theorem (the paper's statement — integrated
as ssec:frontier's closing, 18.8).**  (i) fixed structure positive
(round 15C engine); (ii) no single E for all of Sigma* — indeed none
for the a-run/b-separator strings with unboundedly many b's —
CONDITIONAL on the pinned-schema (lemma 1) and the tuning lemma
(lemma 2), with the effective bound k > f(|E|) on the super-increasing
family; (iii) unbounded alphabets negative (Lane E).

### 18.3 Lane B round 3 (rev-split/): the Telescope at varying k

Full battery: 1,755,621 checks, 0 failures, 0.8 s (five modes: SD,
OPS, CEN, FP, SB).  [Coordinator's reproduction: OPS/CEN/FP exact at
the default and probed seeds; SD/SB case counts seed-dependent (the
default tr=400 gives 203/197/400/214; tr=4000 at 5 fresh seeds gives
the exact total 1,755,621/0); the lane's log seed was unrecorded —
bookkeeping slip #3, same class as round 2's cells runs 2-3 — and the
lane is told to log the full invocation in the log header from now
on.  VERIFIED with the invocation-unrecorded caveat; the 0-failure
claim is over-reproduced.]

**Theorem MT (the multivariate telescope).**  (a) The per-pass
accounting N_out = N_F + c_w(N_R − N_P), M_out = M_F + c_w(M_R − M_P)
is k-FREE (exact, any k), and all three count mechanisms — tiling
c_w = (T_c − Lambda)/p with Lambda now a sum over k+1 runs; computed
moduli via slabs; anchored/adjacent via site conditions.  For each
FIXED k the same ordered refinement (slabs -> residue classes of the
run-vector -> pinned-polynomial coincidence cuts) is locally finite
in the (k+1)-dimensional run-vector space: counts and totals are
functions of (S_a, k) on cells.  (b) THE CANNOT (the round-2 charter's
guess is FALSE as stated): totals are NOT functions of (S_a, k).
Witness: the ceiling-halver [a/aa]X has N = Sum ceil(r_t/2) =
(S_a + nu)/2 with nu = #odd runs; at fixed (S_a, k), nu takes every
value of the right parity in [0, k+1], so N takes ceil((k+1)/2)
DISTINCT VALUES — Theta(k) spread (machine-verified exactly, k = 1..7,
every composition: the census law 1,2,2,3,3,4,4).  Site-local data is
not uniform because each site contributes an independent residue: any
statistic determining Lambda = Sum(r_t mod p) must read Theta(k)
bits.  The correct surviving pinning is the RESIDUE-VECTOR: finite per
k with #cells = M^{k+1}.(slabs).(coincidences) — NO k-UNIFORMLY-
BOUNDED FINITE PARTITION EXISTS, and no quasi-polynomial-in-
(r_0..r_k, k) family at the (S_a, k) granularity.  This is exactly the
degeneration of the fixed-k "S-function per cell".

**Lemma SD (site distinctness — PROVED).**  If a scrutinee's positive
runs are pairwise distinct and the pattern has >= 2 b's with at least
one positive interior run, the pass fires AT MOST ONCE.  *Proof.*  Two
windows would put equal interior run-sequences at two distinct
skeleton positions; positive-run distinctness forces the same
position, contradicting disjointness.  Exception class: b^q-type
patterns (all interiors zero) — the T5 tilers.  Sharp both ways
machine-verified: 2007 qualifying cases, 0 multi-firings; 1036/1993
controls (q <= 1 or 'bb'-type) fired multiply.

**Theorem FP (the final-pass constraint — PROVED; INDEPENDENT of Lane
C's hand proof: the convergence, 18.4).**  If E(w) = rev(w) with w's
runs positive and pairwise distinct, and the top S-node fires t >= 2
times, then R(w) has AT MOST ONE b.  *Proof.*  The t disjoint copies
of R(w) sit verbatim in rev(w); each copy's consecutive b's are
consecutive skeleton b's of rev(w), so each copy's interior run
profile equals rev's local profile; two copies with >= 2 b's and a
positive interior force the same skeleton interval (distinctness),
contradicting disjointness; the all-zero-interior case contains 'bb',
excluded by positive runs.  Machine: 4000 forced multi-b multi-fire
cases — every output != rev with the repeated profile; Lane C's
E_rev: 343/343 correct reversals with the top pass exactly t = 1
(consistent: its top R = 'b').

**Theorem SB (the Separation Budget — PROVED; the no-progress lemma,
merge-free regime).**  Label each a-character by its input run.  Call
a derivation MERGE-FREE if every maximal a-run of every value carries
material from <= 1 input run.  Let Phi'(V) = # of distinct
input-adjacent pairs (t, t+1) appearing as a REVERSED SEPARATION in
V(w) (a b with run t+1's material immediately left, run t's
immediately right).  Then (i) Phi'(rev(w)) = k for every w in W_k —
no genericity needed; (ii) merge-free derivations satisfy
Phi'(S(R,P,F)) <= Phi'(F) + Phi'(R) + 4 and Phi'(C(A,B)) <=
Phi'(A) + Phi'(B) + 2 — the multi-firing junction pairs collapse
because each new pair is PINNED BY ONE OF R's four boundary-adjacent
run labels, so t firings contribute <= 4 DISTINCT pairs regardless of
t; hence Phi'(E) <= 4.#S(E) + 2.#C(E), A FIXED BUDGET; (iii) NO
MERGE-FREE E COMPUTES rev ON W_k FOR k BEYOND ITS SIZE — in
particular no merge-free unifier exists, and ANY unifier must merge
input-run material into common a-runs on every input with
k > 4#S + 2#C.  Machine: 2112/2112 random merge-free derivations
respect even the tighter 2#S + 2#C (the tight constant is open; the
hand proof gives 4/2).  [Coordinator-scrutinized: the
pinned-by-boundary-labels argument is sound.]

**The pollution witness (merge-freeness is load-bearing).**  E_poll =
[(merge.b)/'aa']merge: one pass whose every junction separation sits
between merged runs carrying ALL labels — Phi' = k with budget 8
(verified at k = 9, 10).  So MERGING IS THE UNBOUNDED FLIP-CREATING
RESOURCE; flip-counting alone can NEVER prove the no-go.  The
obstruction, if it exists, must live in RUN-LENGTH EXACTNESS.

**Lemma DECOMP (PROVED).**  C-nodes split the problem: if E(w) =
A(w).B(w) = rev(w) then A(w) = rev(suffix), B(w) = rev(prefix), and
inductively the fixed C-tree's leaves reverse a partition of w into
consecutive intervals in reverse order; by pigeonhole some leaf's
subtree reverses an interval with unboundedly many separators, and
its top must be an S-node (X only reverses separator-free intervals,
where rev = identity).  This REDUCES the unification question to
S-topped trees reversing unbounded-separator intervals — exactly
where SD, FP, and SB apply.

**The toll at varying k: the exclusions STRENGTHEN, nothing becomes
vacuous.**  At each fixed k the same machinery runs in the
(k+1)-dimensional vector space; the level-pigeonhole needs S_a beyond
N(k) = #cells meeting the slice (finite per k, growing with k:
M^{k+1}.poly).  Since an E computing a b-free split on the union U_k
W_k would compute it on each W_k, the per-k exclusion (S_a > N(k))
kills the union statement outright — the k-dependence enters only
through the per-k threshold, never the conclusion.  CAVEAT at the
round-2 honesty bar: conditional on the general-k profile write-out
(Schema P was proved at k = 2; the mechanisms are k-free per MT(a),
so the skeleton carries over — same status as round 2's Lemma S:
CLOSED AT SKELETON LEVEL).  No new obstructions appear at varying k,
and none are needed.  (D_last's a-total is S_a — Lemma S concerns
totals and counts, not run lengths; its run profile (r_0,
r_{k-1}+r_k) is pinned-polynomial, as Schema P claims.)

**Task 4 — the k-adaptive mechanisms classified (Lane C's ops on all
349,524 run-vectors, k = 1..8).**  D_last = [eps/(b.mrg.a)](X.mrg.a)
and D_first are q = 1, zero-interior patterns whose S-domination flank
(S_a+1) pins a single firing at the last/first separator WHATEVER k
is — verified in closed form on all 349,524 run-vectors for k = 1..8
including zero runs (the OPS mode: 16+64+...+262144), along with the
skeleton-preserving shave [b/ab], the merge-shave [eps/ab] (fires at
junctions with r_t >= 1, b's survive exactly at zero-run junctions),
and the halver.  Concatenated scrutinees are covered by P0
(concatenation = junction merge of profiles); the counts of
multi-site k-adaptive ops are census statistics — (S_a, k,
residue-vector)-functional per MT, exactly as Lemma S requires at
fixed k.  The only write-up action: make explicit that F may be a
concatenation node and that profile operations apply verbatim.

**The open core (now precise).**  Can merging + q <= 1 patterns (the
k-adaptive class: SD and FP push all bulk work there) reverse
unbounded k at fixed size/depth?  The budget theorem shows any
impossibility proof must fire in the MERGEY REGIME; E_poll shows
order-inversion alone is cheap there — the obstruction, if it exists,
must live in RUN-LENGTH EXACTNESS (final singleton runs with the exact
reversed lengths).  For Lane D: any invariant candidate that holds
merge-free is already budgeted and cannot obstruct; it must be
merge-sensitive.  For Lane C: every multi-firing final replacement is
confined to <= 1 b, and multi-b positive-interior patterns are
single-firing on distinct-run texts — the constructive channel is
narrow and precisely mapped.  Next-round candidates: (a) a
merge-sensitive budget (charge pollution to the merging passes and
bound total creation-then-deletion under length exactness); (b) the
tight SB constant; (c) the general-k profile write-out to make the
toll lift unconditional.

### 18.4 The convergence (the three lanes' endgame findings)

- **FP PROVED TWICE.**  Lane C's hand proof (18.2: on the
  super-increasing family, multi-fire forces R single-b-or-pure; the
  reversal pre-exists in the scrutinee as an in-order extraction with
  uniform tweaks) and Lane B's independent proof (18.3: on any
  distinct-positive-run input, multi-fire forces R at most one b) —
  from the construction side and the counting side respectively; the
  machines agree (4000 forced cases; E_rev 343/343 with top pass
  t = 1, R = 'b' — the live instance).
- **THE COUNTEREXAMPLE CLASS FOUND TWICE.**  [X/'b']X (Lane C, from
  the construction side) and [X/a]X (the coordinator, from the
  falsification side) both have dec/LDS growing with k at S-depth 2 —
  the stratified-picks phenomenon is real, and any dec/LDS-type
  invariant must carry VALUE-STRATIFICATION (disjoint value ranges
  across copies), not subsequence counts alone.  Lane C's first
  invariant died on it; the corrected descent carries the
  stratification.
- **THE MERGEY-REGIME LOCATION SHARED.**  Lane B's SB proves no
  merge-free no-go (Phi' budget 4#S + 2#C against Phi'(rev) = k);
  E_poll proves order-inversion is CHEAP under merging (Phi' = k with
  budget 8).  E_rev itself lives in the mergey regime (its pads and
  boxes merge input material) — so the no-go must work THERE, which is
  why SB alone cannot finish it.  All three lanes converge on: the
  obstruction lives in the mergey regime, in RUN-LENGTH EXACTNESS.
- **PROGRAM STATUS.**  PROVED: FP (two independent proofs + machines),
  SD, SB (merge-free no-go), DECOMP, MT(a), SNF, the toll's
  strengthening at varying k (per-k thresholds; skeleton-level
  condition), the positive byproducts (E_block, E_alt, the diagonal
  census), and the fixed-structure dichotomy positive half.  ANALYSIS-
  GRADE: the descent's two escape kills (value-range disjointness;
  deletion-rate/tuning).  CONJECTURED: the full unification
  impossibility — conditional on L1 (the pinned-schema at varying k,
  sharp form, on w^(k), exploiting the family's residue structure)
  and L2 (the tuning lemma, merge-sensitive per B3).  SKELETON-LEVEL:
  the general-k profile write-out (the toll's lift).  In flight, not
  waited on: Lane B — the merge-sensitive budget; Lane D — the tuning
  lemma from the selectivity side; Lane C — the FP/descent LaTeX
  fragment (rev-try/dichotomy.tex).

### 18.5 Machine verdicts (all runs < 60 s)

- rev-wall/varyingk_check.py (via varyingk.log, byte-identical on the
  coordinator's re-run): A semantics cross-check 990/990; B the
  diagonal constructions (40/40 each + the coordinator's fresh
  encodings: 60 k-values + boundary + off-family honesty); C the dec
  probe (325 depth-3, k = 1..5); D the extraction hunt (700 depth-3,
  zero genuine hits at k >= 3).  The coordinator's verify_r2_wall.py
  part 4: the SNF decomposition directly against the campaign
  evaluator, 765/765.
- rev-try/verify_r16.py (~7 s): P1 E_block grid 13^2 + 400 random +
  intermediates 10^2; P2 E_alt k = 1..44 + intermediates k = 1..14;
  L1/L2 on 7^3 W2 grid; L3 k = 1..6 — ALL VERIFIED; the think-pass
  narrative appended to r16.log BEFORE machine work (genuine).
- rev-try/verify_r16_coord.py: E_block 15^2 + 500 random (all
  boundaries); E_alt k = 1..69 + uniqueness; L1/L2 8^3; the
  counterexamples [X/b]X and [X/a]X dec >= k at S-depth 2 (k = 1..6);
  the FP uniform-bite spot-check [bab/aa]X — ALL VERIFIED.
- rev-split/varying_k (0.8 s): SD 2007 qualifying, 0 violations
  (controls 1036/1993 multi-fire); OPS 1,747,600 closed-form checks
  over k = 1..8 (all 349,524 run-vectors); CEN the halver census law
  exact k = 1..7; FP 4000 + E_rev 343/343 (t = 1); SB 2112/2112 +
  E_poll k = 9, 10.  TOTAL 1,755,621 checks, 0 failures (reproduced
  by the coordinator at 5 fresh seeds; the lane's own seed
  unrecorded — the caveat of 18.3).

### 18.6 Honest ledger for this round (integration; no new machine
### runs by this lane — all numbers are the lanes' and the
### coordinator's, re-verified per 18.0/18.5)

- PROVED (hand, machine-confirmed): SNF; the Final-Pass Lemma (Lane
  C's hand proof on w^(k)); Theorem FP (Lane B's independent proof);
  Lemma SD; Theorem SB (merge-free no-go); Lemma DECOMP; Theorem
  MT(a) (k-free accounting); the diagonal census (E_abk, E_ab,
  identity cases); the positive byproducts E_block and E_alt; the
  L1/L2 collapse facts; the counterexample class ([X/'b']X, [X/a]X —
  dec/LDS >= k at S-depth 2).
- ANALYSIS-GRADE (hand arguments, not formalized): the descent's two
  escape kills (value-range disjointness across copies; the
  deletion-rate/tuning argument); the arithmetic fixed point (the
  wedge); the selectivity landscape.
- CONJECTURED: the full unification impossibility (no fixed E
  computes rev on all of {a,b}*) — conditional on L1 (pinned-schema at
  varying k, sharp form, on w^(k)) and L2 (the tuning lemma,
  merge-sensitive); V1 (last-run extraction), V2 (sum-minus-max), V3
  (selectivity covering), the target theorem; the tight SB constant.
- SKELETON-LEVEL: the general-k profile write-out (the toll's lift to
  unconditional); MT(b)'s residue-vector pinning as the surviving
  form of the fixed-k cells.
- VERIFIED-ON-STATED-DOMAIN (machine, falsification only): dec
  bounded on the NON-EXPLOSIVE sample (with the coordinator's cap
  caveat — the explosive stratum refutes the naive dec program);
  zero extraction hits at k >= 3 (700 depth-3 expressions); the L3
  tweak-or-affine illustration (k <= 6, tolerance 8).
- REFUTED: the naive dec/LDS bound (dec <= C independent of k) —
  FALSE on the explosive stratum; the round-2 charter's guess (totals
  as functions of (S_a, k)) — FALSE by the halver witness; the
  round-1 invariant family (superseded; the autopsy at 18.1).
- CORRECTED (this round, all bracketed in situ): the 293,307 ->
  293,507 cells transcription (17.2, 17.6 — Lane B caught it, the
  coordinator fixed the OVERVIEW entry); the dec-probe's cap caveat
  folded in; B3's unrecorded-seed caveat recorded.
- OPEN: the two lemmas (L1 sharp form, L2 merge-sensitive tuning);
  the merge-sensitive budget; the head-propagation lemma on the
  k-axis; V1/V2/V3.

### 18.7 Files

- `../rev-wall/` — Lane D round 2: REPORT.md (R2.1-R2.2.8),
  varyingk_check.py, varyingk.log, CHARTER_varying_k.md; the
  coordinator's verify_r2_wall.py.
- `../rev-try/` — Lane C round 16: ROUND16_REPORT.md (coordinator-
  transcribed with scrutiny notes), verify_r16.py + r16.log (with the
  think-pass narrative), verify_r16_coord.py +
  r16_coord_verify.log, CHARTER_unification.md; dichotomy.tex (the
  standalone fragment, round in flight — NOT integrated yet).
- `../rev-split/` — Lane B round 3: ROUND3_REPORT.md (coordinator-
  transcribed), varying_k.c + varying_k + varying_k.log.
- `../../OVERVIEW.md` — the coordinator's entries "Lane D round 2,
  Lane A round 4, Lane C round 16 verification" and "Lane B round 3
  verification".
- `CHARTER_integration5.md` — this round's charter.
- This round's other writes: 17.2/17.6 (the 293,507 correction);
  main.tex (ssec:frontier's closing sharpened to the conditional
  dichotomy — 18.8; the wire-ins; the dichotomy.tex integration
  hook).

### 18.8 The paper integration (charter Part B, executed)

- ssec:frontier's closing sharpened: the varying-separator-count
  question is now answered IN ARCHITECTURE — the dichotomy presented
  as a theorem schema, parts (i) and (iii) proved, part (ii) stated as
  a conditional theorem naming exactly the two remaining lemmas (the
  pinned-schema at varying separator count in its sharp form; the
  tuning lemma, necessarily merge-sensitive); the architecture
  summarized (FP proved twice; SNF; the separation budget closing the
  merge-free regime; the pollution witness locating the obstruction
  in run-length exactness; the effective bound on the super-increasing
  family).  The three rounds cited.
- Wire-ins (the landscape's open problem, the alphabet section's
  intro, the conclusion) updated: not "open at varying k" but
  "architecturally closed — no unified expression exists, pending two
  named structure lemmas".
- The prop:toll affine-scoping patch (the coordinator's) preserved
  verbatim.
- Integration hook left at the dichotomy theorem's insertion point
  for Lane C's in-flight fragment rev-try/dichotomy.tex (a LaTeX
  comment; not referenced until the coordinator relays it).
- Build: clean (0 errors, 0 undefined references, 0 overfull); page
  count reported to the coordinator.  Nothing committed to git (the
  user commits).

Execution specifics: the theorem is `thm:dichotomy` ("The Reversal
Dichotomy", Theorem 6.9, p. 74 of the built PDF), stated with
\begin{enumerate}[(i)] per the paper's convention, with a short proof
environment (parts (i)/(iii) by citation; part (ii)'s conditional
status part of the statement; a machine-backdrop parenthetical with
the round-exact counts: SNF 990/990 + 765/765, FP 4,000 forced cases +
engine 343/343, SB 2,112 + E_poll at k=9,10, OPS 1,747,600 checks over
the 349,524 run-vectors k<=8).  The closing paragraph's first half
(the toll companion + repositioning) kept; its second half replaced by
the architecture paragraph (SNF -> FP -> descent kills -> separation
budget -> pollution witness -> obstruction located), the theorem, and
the final paragraph naming the two lemmas with the bridge note (the
family's own residue structure vs the residue-vector degeneration).
Four edits total in main.tex: the closing block (line ~2611 region),
the ssec:frontier intro (2421), and the three wire-ins (landscape
open problem 2196, alphabet intro 2251, conclusion ~3004) — all now
"architecturally closed — no unified expression, conditional on two
named structure lemmas".  Build: 89 pages (up from 87), 0 errors,
0 overfull, 0 reference/citation warnings; the only log warnings are
the 10 pre-existing font-shape lines.


## 19. THE FINAL INTEGRATION — the dichotomy's part (ii) PROVED
## (the residue: NONE, the record's honest one-liners below)

Lane A, 2026-09-22, under CHARTER_integration_final_DRAFT.md (the
coordinator's FINAL INTEGRATION dispatch; every dependency verified
by the coordinator same day: OVERVIEW entries B8, B9, C19–C21b,
D4–D8).  Status: EXECUTED IN FULL.  Build after integration: 104
pages (up from 89), 0 errors, 0 overfull, 0 undefined references,
0 multiply-defined labels; the only log warnings remain the
pre-existing font-shape lines.

### 19.1 What entered the paper (all traced to the verified record)

- thm:dichotomy (ii) FLIPPED TO PROVED, unconditional: "each E fails
  on the strongly super-increasing inputs D(k;3) (any fixed base
  B >= 3 works; base 2 is the degenerate boundary, Proposition
  dich:prop:boundary) beyond separator count k > c_E #S(E) + c'_E —
  linear in the pass count".  The family overclaim fixed per the
  charter (base 2 IS super-increasing and is the boundary; the
  committed family is the strongly super-increasing D(k;3)).
  Conclusion unchanged (D(k;3) is a subfamily of {a,b}*).  The
  tightness remark kept (engine Theta(k) depth, Theta(k^2) size).
  (i) and (iii) untouched.
- The proof of thm:dichotomy rewritten as the unconditional
  Order/Budget/Supply/Demand/Count assembly, citing the mounted
  apparatus; the round-5 machine-backdrop line kept verbatim per the
  charter.
- The DESCENT LEMMAS mounted from rev-try/dichotomy.tex (round 18,
  coordinator-verified): sweep normal form (dich:lem:sweep), the
  Final-Pass Lemma (dich:lem:FP), site distinctness (dich:lem:SD),
  the flank cap (dich:lem:flankcap), the separation budget
  (dich:lem:SB), the payment theorem (dich:lem:PAYMENT), decomposition
  (dich:lem:DECOMP), the descent paragraph, Escape A
  (dich:escapeA), Escape B (dich:escapeB) — with the reference
  rewiring the charter prescribes: Assumption L1'' -> the Truncation
  Ledger (Theorem thm:TL); the demand assumption -> "the demand side
  below"; "the named assumptions below" -> "the lemmas below".
- THE TRUNCATION LEDGER (thm:TL + rem:TLprof) mounted VERBATIM from
  rev-split/ROUND9_REPORT.md section 1 (NOT round 7's section 5):
  the two-color profile clause, the replication-corrected expansion
  exponent Delta_V (C-R9-1), clause (i)'s ambient-index anchoring
  (C-R9-2), the two-tier directive count N_V <= 3^d(2|V|+1) for 1-D
  fired sets / 2^{|V|^2} general (C-R9-3), masks as Boolean
  combinations of residue tests (mod2 ord_4(3)=2 and mod7
  ord_7(3)=6 both exhibited), T_V's spelled-out domain, Merge
  uniformly over both colors.  Wiring deviations (disclosed):
  the remark's first sentence (the [R/P]F definition) dropped, the
  paper's Section 2 defining the pass; "(Remark~\ref{rem:TLprof})"
  rewired to "(the remark below)" because the paper's remark
  environment is renewed unnumbered (a \ref would resolve to the
  wrong counter); the em-dashes normalized to the paper's "--";
  the T_V display broken across two align lines (the single line
  overfull by 94.7pt in llncs's text block — the content unchanged).
- The B5 CORRECTIONS paragraph mounted after the ledger, per the
  charter's items (b)-(f): the k-affine junk stratum (the halver
  [e/b][a/aa]X = a^{(S+k+1)/2} on D(k;3), the +k/2 irreducible);
  rational slopes with V-fixed denominators (the tripler
  [a/aaa]X runs (2^j+2)/3 [even], (2^j+4)/3 [odd] at base 2,
  non-dyadic) and the strengthened supply/demand mismatch (non-dyadic
  supply never equals dyadic demand, s nmid 3^Delta 2^d); the honest
  constants (8#S+O_V(1) run-level AND (d+2)M_V per form, kept
  separate, NOT unified); the count-times-S product class (E_prod's
  last run 1 + floor(3^k/2)*S, interior S(3^j-1)/2+1); the site
  terms 3^t reading with E_leak's runs (S+3^0,...,3^k).
- The SUPPLY SIDE: dich:lem:L2.1 (slope-pinning) and dich:lem:L2.2
  (per-node supply), mounted with proofs.
- THE DEMAND SIDE, restructured to the channel analysis with NO
  remaining conditionality: the channel intro (c = rho_j - p0,
  drift Delta = M_R - p0 - p1); Lemma M (dich:lem:M, the two-sided
  match with the double-bite bookkeeping and locality); Lemma FIT
  (dich:lem:FIT); Lemma K2 (dich:lem:K2, real-channel rigidity —
  consecutive merges only, the repunit-digit kernel proof, the
  cross-pair kill at the real firing, the census as CORROBORATION
  ONLY: 2,025 constant families, k = 7, 8, zero census-passing
  two-hit non-ladders, 11 ladders); Lemma S (dich:lem:S, the mirror
  forcing, exclusive, with the exact window and the drift two-case);
  Theorem D (dich:thm:D, D1 drift-robust mirror forcing with
  (t+1)Delta >= (3^k+1)/2, D2 the window/debt dichotomy, D3
  multi-service pricing, MR mass routing with the Payment interface);
  Lemma INH (dich:lem:INH, the survivor supply bound (3^k+1)/2, the
  origin trace, the mod-3 separation); Lemma FSL (dich:lem:FSL, the
  fired-set recursion theorem c_{sigma+1} = R_{sigma+1} -
  j*[fire], SKIP-AFTER-BITE, COR-A/B/B1, the class-escape); Lemma
  trace (dich:lem:trace, D1 order preservation, D1''-WEAK + the
  mod-3 T1-trace — the strong form NOT entered as proved — and the
  round-4 corollary "value > 3^lambda implies T2/T3" recorded as
  WITHDRAWN); the engine autopsy as machine facts (k = 2..5); the
  ATOM OBLIGATION LAW at full altitude (dich:thm:ATOM: depth >=
  (min(v,k-u) - 1 - floor(log_3 M))/2, M <= Q(8#S + O_V(1)) +
  (v-u+1) + O(log k), the collected form Sum_d mu_d 3^d = 0 with
  the machine's gamma convention per the coordinator's D8 flag —
  gamma names the value of the collected low-scale material inside
  mu, |gamma| = O(k) entering only the gap bound 3^{g-1} <= DM above
  log_3(2D|gamma|); the mass form with the n=7 transition and the
  witness 7 I(0,1)+8 = I(2,3), M = 20; the C=2 closing); the
  trichotomy (a) per-pattern scale slots / (b) deep tuned
  intermediates / (c) mergey pollution; the DISJUNCTIVE COUNTING
  COROLLARY (dich:cor:counting, both branches linear).
- Census numbers cited as corroboration only, never load-bearing:
  29/80/361/651 surviving records at k=5/6/8/9 (the two-sided
  corrected counts), 23/57/218/365 distinct channels, <= 4 real hits
  per drifting channel, the bottom-ladder the only unbounded family.
- The staging family, the mirror plant, and the UPDATED boundary
  proposition (dich:prop:boundary with the round-19 offset-cost
  ceiling: at B=2 every VALUE cheap (the five tools) but the ORDER
  priced, Theta(k) from both free ends; uniform rev on the B=2
  family REMAINS OPEN, census-backed obstructed; the dichotomy's
  linear f(|E|) survives the boundary intact) — mounted before the
  theorem; the architecture paragraph keeps the FP base-2
  construction-side proof (proved) with the B=2 degeneracy
  parenthetical as the recorded reason the staging family is base 3.
- All 14 status-flip wire-ins (abstract, intro x2, landscape open
  problem, alphabet intro, conj:union evidence, frontier lead-in,
  rem:price, toll closing, hook comment -> integration record,
  conclusion) now state the proved status; the conclusion's "two
  hinges" sentence updated to the one remaining hinge (the
  once-primitive).

### 19.2 The honest residue (in the record, NOT in the theorem)

One line each, per the charter:
1. The (beta)-level plant interface (plants at perturbed, non-D(k;3)
   scrutinees) is STATED, NOT PROVED in the paper — carried by the
   supply branch (Lane C round 21 section 5; the paper's corollary
   marks it "stated, not proved here").
2. S4.3-general's swept domains (the strata families F1-F3, 3
   pieces, |bite| <= 18, u,v <= 6; the interval catalogs 21833 +
   52959/7871/4299; the coordinator's 139895 superset) extend to the
   general anchored families by the EPT-licensed finiteness (the
   landing equations eventually periodic in k), not by exhaustive
   sweep.
3. The -O(log k) additive slack (the mass form + the EPT range) and
   the tight constant C in [2,4] (C = 2 by the induction's
   arithmetic; the witnessed routes in [2,4]) are open refinement
   questions, not gaps.

Also standing (from the round-19 side quest, NEGATIVE =
architectural): the B=2 offset-cost ceiling; uniform rev on the
B=2 family open, census-backed obstructed; the dichotomy's linear
f(|E|) survives the boundary intact.

### 19.3 The endgame rounds this integrates (the residue map)

rev-wall rounds 4-8 (D1; D1''-weak + the mod-3 T1-trace; the
fired-set fix FSL' + S4.1-S4.6; S4.3-general + the obligation lemma
+ the tripler/merges; G1+G2+C=2 + the atom obligation law at full
altitude); rev-try rounds 18-21b (the verified fragment; the B=2
side quest; OL-1's Lemma M/FIT/K/K2/S with the corrected forms; the
trichotomy; Theorem D + INH + the disjunctive counting corollary +
the two-sided census); rev-split rounds 5-9 (TL conditional; PO
closed, TL unconditional; the measure/INV3 coordination; the two
corrections C-R9-1/2/3 + the final two-color TL LaTeX); rounds 15C
and the earlier endgame rounds in section 18.  Every demand-side
path by which a separator of rev(D(k;3)) reaches its mirror depth is
priced: the plant window (exact top-scale pattern value — a scale
slot at full consumption or an exact deficit), the mass debt
((3^k+1)/2 top-scale, MR/Payment), or the survivor supply (INH +
the atom law).  The verdict: reversal is not L-reachable over any
finite alphabet |Sigma| >= 2, uniform by the coding invariance; the
once-primitive and r in L (the union criterion) remain open.

### 19.4 Artifacts

- main.tex — the integrated paper (104 pages, 0/0/0 build; the
  apparatus sits between the proof of thm:dichotomy and the
  "Unary Edge" subsection: the descent lemmas, the descent, the
  truncation ledger + its remark + the corrections paragraph, the
  supply side, the demand side, the trichotomy + the counting
  corollary, the closing map paragraph, the machine-backdrop
  remark).
- The lanes' reports and artifacts, all frozen as cited in
  sections 18 and 19.3; nothing committed (the user commits
  externally).
- CHARTER_integration_final_DRAFT.md — this round's charter (the
  coordinator's dispatch).

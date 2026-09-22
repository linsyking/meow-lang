# rev-wall — Round 1 report: the run-level invariant lane (the impossibility wall)

Lane charter (coordinator): the run-level invariant for the all-varying
same-letter two-b family W2 = {a^i b a^j b a^k : i,j,k >= 1} on the fixed
alphabet {a,b} — after Lane E closed the unbounded-alphabet program and
Lane C fell the mixed-letter family, this lane is the only remaining
route to a fixed-alphabet impossibility theorem (or the remaining
freedom, for constructions).  Precise target (Lane C's reduction): rev
is computable on W2 IFF V_h = a^k b a^{j+h} b a^{i+h} is constructible
for some constant h; so a run-level invariant must exclude exactly V_h.

Secondary charter items, both delivered: (S) adversarial scrutiny of
Lemma S's INDUCTION (my assigned angle: the induction itself, not the
boundary/arrangement pathologies Lane B holds); (G) the sign-gate
primitive E_asym.

Method and discipline: hand proofs for every claimed result; the
machine only falsifies; every machine run <= 60 s (batches smaller than
that, logs below); nothing committed; own directory rev-wall/; the
evaluators prov.py / lcore.py are independent copies of the campaign's
(lcore's C is 2-ary — nest for triples).

Conventions.  S(R,P,F): R = replacement, P = pattern, F = scrutinee;
greedy leftmost-first scan, never rescans inserted text; empty pattern
undefined; all S-children evaluate at the ORIGINAL input; chains
compose right-to-left.  For an expression E over X = V(0) with input
w2, run types: a run's a-count as a function of (i,j,k) (affine on a
piece) has TYPE (alpha,beta,gamma), its slopes along i, j, k.
i-DOMINANT: alpha >= beta and alpha >= gamma.  k-dominant dually.

--------------------------------------------------------------------------
## 1. The exact count identities (independent rederivation)

**Firing-count lemma.**  For a fixed pattern P and text T, the greedy
leftmost scan fires mu(T) windows, and mu(T) equals the maximum number
of pairwise disjoint occurrences of P in T.  *Proof.*  All occurrences
of a fixed pattern have equal length; greedy leftmost selection over
intervals of equal length is the classic optimal interval-scheduling
(exchange argument: the leftmost-ending available occurrence is always
safe).  ∎

**Exact count identities (= Lane A's 14.5b; rederived independently
before reading theirs).**  For E = S(R,P,F) and any input where
defined, with mu = mu(F(w)):

    A(E,w) = A(F,w) + mu * (A(R,w) - A(P,w)),
    B(E,w) = B(F,w) + mu * (B(R,w) - B(P,w)),

exactly.  *Proof.*  The greedy scan never rescans inserted text, so
every window is an occurrence in the ORIGINAL text and the windows are
disjoint in original coordinates; the output is the original text with
the mu disjoint windows replaced by mu copies of R(w); a- and b-counts
add over the pieces.  ∎

ENDORSEMENT: 14.5b's proof ("Immediate from the semantics") is correct
and its emphasis is right — never-rescan exactness is THE reason the
total-content calculus closes.  Everything below is run-level precisely
because the totals are exactly accounted and still say nothing about
rev (rev's own output has total S, an S-function).

Coordinate caution (coordinator's, CONFIRMED and sharpened): [a/aa]X
acts per run by psi(u) = r*floor(u/p) + (u mod p) — the REMAINDER
SURVIVES (I initially mis-derived floor(u/2) for [a/aa]; the machine
corrected me: it is ceil(u/2)).  So [a/aa]X on w2 has runs
(ceil(i/2), ceil(j/2), ceil(k/2)) and total
ceil(i/2)+ceil(j/2)+ceil(k/2) — NOT a function of S = i+j+k until the
partition refines by the parities of (i,j,k): kind-(b) residue pieces
are first-class, not a convenience.

--------------------------------------------------------------------------
## 2. The sign-gate E_asym (PROVED hand, machine-verified)

**Theorem (sign-gate).**  On F1 = {a^i b a^j : i,j >= 1},

    merge = [eps/b]X                       (= a^{i+j})
    dbl   = [aa/a]X                        (= a^{2i} b a^{2j} on F1)
    diff  = [eps/merge]dbl
    T     = C(X, diff)
    Q     = C(K(b), merge)                 (= b a^{i+j})
    E_asym = [eps/b] ([eps/Q] T)

computes a^f with f = i+j for i <= j and f = 2(i+j) for i > j.

*Hand proof.*  merge(w) = a^{i+j}; dbl(w) = a^{2i} b a^{2j} (psi with
p=1 doubles every atom).  diff(w): pattern a^{i+j} is b-free, so it
tiles each run of a^{2i} b a^{2j} separately: window count
floor(2i/(i+j)) + floor(2j/(i+j)).
  - i < j: 0 + 1 windows -> a^{2i} b a^{2j-(i+j)} = a^{2i} b a^{j-i}.
  - i = j: 1 + 1 -> b.
  - i > j: 1 + 0 -> a^{2i-(i+j)} b a^{2j} = a^{i-j} b a^{2j}.
T(w) = w . diff(w):
  - i < j: a^i b a^{j+2i} b a^{j-i};
  - i = j: a^i b a^i b;
  - i > j: a^i b a^i b a^{2j}.
Q(w) = b a^{i+j}.  The pass [eps/Q]T scans for b a^{i+j}:
  - i < j: fires at the first b (i+j <= j+2i always), eating the b and
    i+j a's, leaving a^i . a^i b a^{j-i} = a^{2i} b a^{j-i}; the second
    b cannot fire (needs i+j <= j-i, i.e. 2i <= 0).
  - i = j: after either b there are only i a's before the next b/end;
    needs 2i: no occurrence; text unchanged.
  - i > j: after the first b only i a's (needs i+j), after the second
    only 2j (needs i+j <= 2j, i.e. i <= j): no occurrence; unchanged.
Finally [eps/b] removes the b's:
  - i < j: a^{2i+j-i} = a^{i+j};
  - i = j: a^{2i} = a^{i+j};
  - i > j: a^{i+i+2j} = a^{2(i+j)}.  ∎

Machine (wall_verify.py part A): 625 grid + 400 random checks,
0 mismatches — VERIFIED.

**Significance.**  (1) A b-free value whose length is a piecewise
function of s = i+j with the piece selected by the SIGN of j-i: the
"piecewise" clause of Lemma S is essential — no pure function of s
(and by transfer, no pure function of S on W2).  (2) The sign of the
run difference is EXTRACTABLE as a gate (a two-valued behavioral fork
keyed on sign(j-i)); it is not extractable as a length (the two pieces
are s and 2s, both s-functions on their pieces).  (3) It kills, by
explicit witness, three cheap invariant candidates: "b-free lengths are
S-functions" (false without pieces), "bounded asymmetry of b-free
lengths" (ratio 2), and "exact symmetry" (the [eps/b]half example).
Any run-level invariant must be inequality-shaped (dominance), not
function-shaped — this motivated the invariant of section 4.

--------------------------------------------------------------------------
## 3. Scrutiny of Lemma S's induction (assigned angle)

Target (rev/REPORT.md, Lemma S, round 14): finite partition of
[1,inf)^3 into pieces (kinds (a) affine, (b) residue classes mod
constants, (c) slab levels for computed moduli) on each of which every
window count of every pass is pinned and N_E, M_E are functions of S.

### 3.1 Finding V1 — the case (i) sub-claim "every run is O_E(S)" is FALSE

The proof of case (i) (tiling patterns) says: "if Lambda_P > 0 then
g = Omega(S), every run is O_E(S) (their sum N_F is), so the tile
counts floor(f_t/g) are bounded, take finitely many values".  Two
defects, independently fatal:

(1) INVALID INFERENCE: a bound on the SUM of run lengths does not
bound each run.  (2) FALSE IN FACT: their own honest scope note (3)
exhibits a depth-2 value with a single run ~ S^2/2 —
[merge/"bb"].[b/a]X explodes w2 to b^{S+2} and re-tiles it with
merge = a^S, giving a^{S*floor((S+2)/2)}.  Feed that to a later pass
with a computed b-free pattern of length g = Theta(S): the tile count
floor(f/g) is Theta(S) — UNBOUNDED — so the "finitely many slab
levels" step fails: the level index m is not a constant, and the slab
boundary m*g(S) with varying m is not an affine condition.  The
bounded-tile-count route to case (i) is dead on the explosive stratum.

### 3.2 Finding V2 — what actually survives (salvage analysis)

The dangerous configuration needs BOTH:
  (alpha) a scrutinee with SEVERAL runs whose individual lengths are
  not S-functions (e.g. X itself: runs i, j, k), AND
  (beta) either a sublinear-unbounded computed b-free modulus g(S),
  or a non-affine computed interior run in an anchored pattern.

Why the explosives do not immediately break the lemma: explosive values
of the [merge/"bb"] type COLLAPSE to a single run, and single-run
S-functional scrutinees re-S-functionalize the arithmetic — dividing
piecewise-affine-in-S by piecewise-affine-in-S yields a
piecewise-affine quotient with O(1) jitter and a remainder that is
again piecewise-affine in S with finitely many pieces (the main term
cancels; the floor jitter is periodic).  Machine evidence (this round):

    m1 = [eps/b]X                = a^S
    p2 = [a/aa]m1                 = a^{ceil(S/2)}      (psi keeps u mod p)
    p3 = [eps/p2]m1               = a^{S mod ceil(S/2)} = 0 (S even) or (S-1)/2 (S odd)
    q4 = [a/aa]p3                 = a^{ceil(h/2)}      on top of h = |p3|

729 + 365 checks, 0 mismatches: the attempted "non-affine modulus"
S mod ceil(S/2) COLLAPSES to affine-on-parity-classes (2 pieces), and
one more nesting level stays affine-per-class.  Every attempt of mine
to build a sublinear-unbounded or non-piecewise-affine computed modulus
collapsed the same way or died by pattern-emptiness ([eps/empty] is
undefined, so even-S moduli that vanish kill the pass).

Standing conjecture from this (unowned, cheap to state, hard to prove):
CONSTRUCTIBLE b-free moduli are piecewise-affine with finitely many
pieces — nothing strictly between Theta(1) and Theta(S) is
constructible, and no Sturmian-like modulus arises.  This is a special
case of Lane B's R2 (pinned-polynomial run lengths) — to which the
whole repair now points.

CONCLUSION of V1+V2: Lemma S's case (i) cannot be repaired by the
bounded-tile-count route; it CAN be repaired by the R2 route (piecewise
pinned-polynomial run lengths through arbitrary nestings), because the
only unpinned behavior (non-S-functional scrutinee runs meeting
patterns) is then governed by affine firing conditions
({run = pattern-run} with pattern runs pinned-polynomial).

### 3.3 Finding V3 — Corollary 1's covering step is invalid as written; counting repair (mine)

Corollary 1's proof says: the plane {S = S_0} triangle "is covered by
the finitely many pieces' traces, so some piece's trace is
2-dimensional (a finite union of <= 1-dimensional sets cannot cover
it)".  On the INTEGER lattice this is false as stated: the triangle IS
coverable by finitely many thin sets — the j-levels {j = c},
c = 1..S_0-2 (each a line, no 2x2 grid), and likewise finitely many
congruence classes {i = r mod p} cover everything with each piece
grid-free.  The continuous-simplex intuition (Baire/measure) does not
transfer to the discrete parameter space, and kind-(b) pieces have
empty interior in R^3 while their union covers the lattice.

REPAIR (hand, 3 lines, replaces the dimension step).  Assume the
finite-partition form of Lemma S: pieces Q_1..Q_N, N_E = h_r(S) on
Q_r.  Suppose E computes a^j, i.e. N_E = j.  Then on each Q_r,
j = h_r(i+j+k), so Q_r's trace on the plane S = S_0 lies in the
DIAGONAL {j = h_r(S_0)} — at most S_0 lattice points.  The N traces
cover at most N*S_0 points; the plane has (S_0-1)(S_0-2)/2 points;
for S_0 > 2N + 3 the traces do not cover the plane — contradicting
that the pieces partition the space.  ∎  (The same argument with any
non-S-functional length in place of j gives the other five toll
targets of Corollary 1.)

So Corollary 1 = {Lemma S in finite-partition form} + this counting
step.  It does NOT survive a merely countable partition: the pieces
{j = c} themselves form a countable j-pinning cover of every plane.
FINITENESS IS LOAD-BEARING — and finiteness is exactly what V1/V2 show
is unproven without R2.

### 3.4 Verdict (the lane's headline scrutiny finding)

- 14.5b (exact count identities): PROVED, endorsed (section 1).
- Lemma S's case (ii) (anchored patterns, Match Anchoring): the
  mechanism is sound; "two affine functions equal on a full-dimensional
  piece are equal" is fine; the multi-pass b-skeleton bookkeeping
  ("each role's multiplicity is a window count or copy count of a
  previous pass, inductively an S-function") is the schema induction —
  R2 again, not a gap I can close from outside.
- Lemma S's case (i): GAP (V1), not repairable by bounded tile counts;
  repairable by R2 (V2).
- Corollary 1's covering step: GAP as written (V3), repaired by my
  counting argument GIVEN finite partitions.

THEREFORE: **the split toll (Corollary 1) is currently CONDITIONAL on
Lane B's R2 (pinned-polynomial run lengths, the unowned auxiliary).**
If R2 fails — a counterexample to pinned-polynomial run lengths through
arbitrary nestings — Lemma S's finiteness fails with it and the split
RE-OPENS, reopening extraction routes 1a-1c of 14.5.3 with it.  The
coordinator should regard the split toll as CONJECTURED-until-R2, not
banked.  (Everything else equal: my sweeps and Lane A's found no
counterexample to the S-function property of totals on any stratum
tested; the conditional is not under suspicion, it is unowned.)

--------------------------------------------------------------------------
## 4. The run-level tier: PREFIX-DOMINANCE

### 4.1 Statement

CANDIDATE INVARIANT.  For every expression E over X = w2 and every
piece of the (R2-strengthened) partition: every prefix a-count of
E's value, taken at a run boundary, is i-dominant (type
(alpha,beta,gamma) with alpha >= beta and alpha >= gamma); dually
every suffix a-count is k-dominant.  Notation: D1/D2 (lead/tail runs),
P1/P2 (all prefix/suffix sums).

Why inequality-shaped: the sign-gate (section 2) shows function-shaped
statements ("lengths are S-functions") need piece structure that the
run level does not have; dominance is a convex cone — closed under
addition — which is what makes concatenation close (below).

### 4.2 Selectivity — the invariant excludes exactly V_h (the coordinator's sharp target)

- V_h = a^k b a^{j+h} b a^{i+h}: lead run k-typed (0,0,1): 0 >= 1
  FALSE — EXCLUDED by D1.
- rev(w2) = a^k b a^j b a^i: lead (0,0,1) — EXCLUDED (same check).
- P1 = a^i b a^{j+k}: prefixes (1,0,0), (1,1,1); suffixes from the
  tail (0,1,1): k-dominant (1 >= 0) — LEGAL.
- P2 = a^{i+j} b a^k: lead (1,1,0): i-dominant (1 >= 1, 1 >= 0) —
  LEGAL; tail (0,0,1) — LEGAL.

So the invariant is compatible with both building blocks of Lane C's
transplant lemma and incompatible with its target — the required
selectivity.  (If the invariant is proved, V_h is unconstructible for
every h, and by the reduction rev-on-W2 is impossible.)

### 4.3 The conditional theorem

**Theorem (conditional; the implication is PROVED).**  If
prefix-dominance holds for all constructible values on W2, then rev is
not computable on W2.

*Proof.*  rev(w2) = a^k b a^j b a^i; its lead run's a-count has type
(0,0,1); i-dominance demands 0 >= 1.  Contradiction.  ∎

**Lemma (C-split classification; PROVED).**  Every C-decomposition
rev(w2) = A . B with B non-constant has a factor violating
prefix-dominance.  *Proof.*  A is a proper prefix of a^k b a^j b a^i.
If A is b-free, A = a^k' with k' <= k tracking k: its single prefix sum
has type (0,0,alpha) with alpha > 0, violating i-dominance (0 >= alpha
false).  If A contains the first b, A's first prefix sum (its lead
run) is the same k-typed value — violation.  Degenerate splits
(B = eps) recurse to the same value at smaller expression size; X
itself is not rev.  So any witness has a PASS at the root, and the
conditional theorem needs only the pass case of the invariant.  ∎

**Lemma (complement-text obstruction; PROVED modulo Lemma S, hence
conditional on R2).**  The symmetric value a^{i+k} b a^j b a^{i+k} is
unconstructible: its a-total is 2(i+k) + j = 2S - j, not a function of
S.  This kills at the total level the naive strategy "cut both flanks
to a common length and swap" — the symmetric scaffold is not a
constructible intermediate at any depth.  ∎

### 4.4 Induction status: K, V, C close; the pass case hits the L-family crux

- K: constant run vectors; prefix sums (0,0,0) — dominant (equalities).
- V: X's prefix sums have types (1,0,0), (1,1,0), (1,1,1) —
  i-dominant; suffixes dually k-dominant.  HOLDS.
- C: prefix sums of A.B are (prefix sums of A) plus (total(A) + prefix
  sums of B); the total of A is a prefix sum of A (IH); dominance is a
  cone, closed under addition.  HOLDS (given the common refinement of
  the parts' pieces — R2 again).
- S (the pass): the output's run-boundary prefixes are sums of
  (i) text pieces BETWEEN window cuts and (ii) copies of R.  The
  text pieces are NOT prefixes of F's value in general — a window cut
  truncates a run from its left end by the pattern's lead.  Depth-1
  passes survive by ABSORPTION: a cut prefix ending mid-run merges
  with the inserted replacement (or the run's remainder), and the
  invariant only controls run-BOUNDARY prefixes — the b-structure,
  not every cut position, carries the proof burden.  The case that
  escapes absorption: a window anchored at the text's SECOND b whose
  pattern-lead x satisfies d_i(x) < d_j(x) strictly with |x| large
  enough to eat the middle run — the surviving cut prefix
  i + (j - x) is then non-i-dominant and IS a run boundary when R is
  b-bearing at the seam.  THE L-FAMILY WINDOW CUT: the patterns with
  the required lead magnitude and (j+k)-tail type are exactly
  Lane C's L-family (b-free a^{j+k}-typed leads, or one-b
  a^x b a^{j+k-x}).
- Circularity analysis of the L-family: a C-decomposition of an
  L-value has a proper prefix that is b-free — non-constructible by
  the split toll (conditional on R2, section 3.4) — or degenerate:
  C-case PROVED circular.  The pass-case circularity (the L-family
  pattern is itself only constructible via L-family values, or via
  D2-violating patterns) is PARTIAL: I can show the needed pattern
  lead lies in (i, S) with (j+k)-tail, forcing L-family or
  D2-violating pattern shape, but the exclusion of the D2-violating
  branch at arbitrary depth is not done.  OPEN.

STATUS: prefix-dominance is CONJECTURED.  All evidence is consistent
(section 5); the induction closes at K, V, C and at depth-1 passes by
absorption; the remaining gap is exactly the L-family window cut, and
closing it appears to require the split toll — making the invariant,
like the toll itself, ultimately conditional on R2.  The wall and the
toll have converged on the same load-bearing stone.

--------------------------------------------------------------------------
## 5. Machine battery (falsification only; every run < 60 s)

### 5.1 Method

Cell-local slope measurement (sweep2.py): for each expression, probe
each axis at 13 points (step 2, range 24) from 8 base points; a slope
is ACCEPTED only when the two half-line slopes agree within 0.30 (the
line stayed inside one piece of the structure); a violation is flagged
only when the accepted slope in one axis beats the dominant axis by
more than 0.45 in BOTH halves.  Bounded residue sawtooths contribute
< 0.25 noise — below the 0.45 margin.  This design is the fix for
sweep 1's artifacts (two flags dissected to residue sawtooths and cell
crossings; dissect.py retains the autopsies: e.g. runs oscillating
4-7 with no linear trend; one probe line straddling a firing threshold
with the value collapsing to [1,1,1,1,0] on one side and [8,5,12,5,4]
on the other).

Checks: D1k/D1j (lead), D2i/D2j (tail), P1k/P1j/P2i/P2j@u (prefix and
suffix sums at every run boundary), VH (two-b output with run-0
k-typed and run-2 i-typed — Lane C's V_h, h folded into tolerance),
P1f/P2f (L-family a^i b a^{j+k} and mirror a^{i+j} b a^k), D1k-oneb.

### 5.2 Controls (controls.py; the checker is not blind)

- POSITIVE: E_swap = [b/X]bigsym on F1 outputs (j, i) — a j-dominant
  lead; the F1-analogue of the dominance check flags it at 5/5 bases.
- E_asym on F1: no flag (its length is s-dominant per cell).
- W2 catalogue through the full checker: ww = C(X,X), big2,
  E_aug = [R_diag/b]w2 with R_diag = C(C(halfm,b),halfm) (the
  lead-augmented w2), [b/ba]w2 (junction shave), E_M(bab) (the
  fixed-middle engine) — all pass, no flags.

### 5.3 Results

Depth-3 uniform generator (sweep2.py rand_expr, S/C/K/V mix):
  seed 424242: 1200 tried,  670 clean, 0 violations
  seed 111:     800 tried,  443 clean, 0 violations
  seed 333:     800 tried,  463 clean, 0 violations
  seed 555:     700 tried,  402 clean, 0 violations
Depth-4 (seed 444): 250 tried, 56 clean, 0 violations (low clean rate —
depth-4 values often blow up past CAP or vary b-count across probes).
Chain-biased generator (chain_main: pure S-chains of depth 1-3 over a
19-value library of computed patterns/replacements — merge2, big2, ww,
halfm, dbl2, diff2, b.merge, merge.b, the [b/X]big2 swap-analogue, and
11 constants; the construction-danger zone): seed 999: 800 tried, 627
clean, 0 violations.

TOTAL: 4550 expressions tried, 2661 cleanly evaluated, ZERO violations
of D1/D2/P1/P2/VH/P1f/P2f/D1k-oneb.

Honest scope of the sweeps: (1) "clean" requires a fixed b-count
across all 312 probe evaluations — many expressions (especially
depth-4) are excluded, so the sample is biased toward tame values;
(2) the checker sees slope-level dominance only — a violation with
slope gap < 0.45, or confined to a thin cell, is invisible; (3) seed
222 hit a pathological expression twice and timed out (55 s,
unbounded blowup — not autopsied; noted as a construction-budget datum,
not evidence of anything else); (4) the machine falsifies only — these
numbers are the ABSENCE of counterexamples, not support for a proof.

Other machine results this round: E_asym 1025 checks, 0 mismatches
(wall_verify.py part A); W2 catalogue sanity (part B); p3/q4
modulus-collapse checks 729 + 365, 0 mismatches; sweep-1 autopsies
(dissect.py, 9 flagged expressions all resolved as artifacts).

### 5.4 Files (all in rev-wall/)

  REPORT.md        this report
  wall_verify.py   part A (E_asym), part B (catalogue), part C (sweep 1,
                   artifact-prone, superseded by sweep2.py)
  sweep2.py        the cell-local checker + main()/chain_main()
                   (seeds via argv: NTRY DEPTH SEED)
  controls.py      the three controls
  dissect.py       sweep-1 autopsies
  prov.py, lcore.py  evaluator copies (lcore imports ../rec/lazy_pass)
  s1.log ... s6.log  the batch logs (each under 60 s)

--------------------------------------------------------------------------
## 6. Honest ledger

PROVED (hand):
  - Firing-count lemma and the exact count identities (section 1;
    = 14.5b, independently rederived; endorsement of their proof).
  - E_asym sign-gate theorem (section 2) — machine-verified 1025/0.
  - Corollary 1's counting repair (section 3.3) — given finite
    partitions.
  - The conditional theorem (section 4.3): prefix-dominance => rev
    impossible on W2 (one-line proof).
  - C-split classification (4.3): any rev-on-W2 witness has a pass at
    the root.
  - Complement-text obstruction (4.3): a^{i+k} b a^j b a^{i+k}
    unconstructible — via Lemma S, hence conditional on R2.
  - Scrutiny finding V1: Lemma S case (i)'s "every run is O_E(S)"
    sub-claim is false (their own exhibit refutes it).

VERIFIED-ON-STATED-DOMAIN (machine, falsification only):
  - E_asym: 1025 checks.
  - Sweeps: 4550 expressions (S-depth <= 4 + chain-biased), 2661
    clean, zero violations of the dominance/V_h/L-family checks.
  - p3/q4 modulus collapse: 1094 checks.
  - Sweep-1 flags: 9 autopsies, all artifacts.

CONJECTURED:
  - PREFIX-DOMINANCE (section 4): the run-level invariant.  Closes at
    K/V/C and depth-1 passes (absorption); open at the L-family
    window cut; if it holds, rev-on-W2 is impossible (4.3).
  - Constructible b-free moduli are piecewise-affine finitely-many-
    pieces; nothing strictly between Theta(1) and Theta(S) (V2).

OPEN / RELAYED:
  - THE SPLIT TOLL IS CONDITIONAL ON R2 (headline, section 3.4): both
    Lemma S's finiteness and Corollary 1's covering step have gaps;
    both repair via Lane B's R2 + my counting step.  Until R2 is owned
    and proved, the campaign should book Corollary 1 as
    conjectured-strongly-supported, not proved.  This also means my
    L-family circularity (which invokes the toll) and the
    complement-text obstruction inherit the same condition.
  - The L-family window cut (the invariant's pass case) — the precise
    location of the wall; the D2-violating-pattern branch at arbitrary
    depth is unexcluded.
  - Sublinear-unbounded b-free moduli: nonexistence unowned.
  - Depth >= 2 flank crossings in constructions: still no witness
    anywhere in the campaign (the "flank slack" scarcity the
    coordinator flagged); the sweeps here add 2661 clean expressions
    with none.

Bottom line for the coordinator: the run-level lane's invariant
(prefix-dominance) has the exact selectivity the reduction demands
(excludes V_h, admits P1/P2), closes three of four induction cases,
and its one open case has been localized to the L-family window cut;
meanwhile the scrutiny lane found that the split toll everyone is
building on is conditional on Lane B's R2 — the two results meet:
proving the invariant (or the toll) and proving R2 have become the
same program.

--------------------------------------------------------------------------
# ROUND 2 — REFUTATION RECORD + THE VARYING-SEPARATOR-COUNT HUNT

Charter: CHARTER_varying_k.md (coordinator, 2026-09-22).  Round 1's
machine numbers were verified by the coordinator; this round (1) records
the refutation of prefix-dominance, (2) opens the varying-k program.

## R2.1  REFUTATION OF PREFIX-DOMINANCE (chapter closed)

PREFIX-DOMINANCE IS REFUTED as a universal invariant.  Lane C
constructed (coordinator-verified: 12^3 grid + 500 random + 300
adversarial scales + boundary hand-traces; Lane B independently
reproduced) an expression computing rev on ALL of W2:

    mrg = [e/b]X = a^S
    P1  = [e/(b.mrg.a)](X.mrg.a) = a^i b a^{j+k}   (fires only at b#2:
          its following run k+S+1 >= S+1; b#1's is j <= S < S+1)
    P2  = [e/(a.mrg.b)](a.mrg.X)  = a^{i+j} b a^k   (fires only at b#1)
    Cc  = [b/P2](mrg.b.mrg) = a^k b a^{i+j}
    Bb  = [b/P1](mrg.b.mrg) = a^{j+k} b a^i
    T2  = Cc.a.Bb = a^k b a^{S+1+j} b a^i
    E_rev = [b/(a.mrg.b)](T2)      (pattern a^{S+1}.b fires only at
                                    T2's second b, shaving exactly S+1)
    = rev on ALL of W2.  75 nodes / 14 S-nodes, S-depth 4 (DAG 41/6).

In particular V_0 = a^k b a^j b a^i and V_1 = a^k b a^{j+1} b a^{i+1}
are BOTH constructible — the exact values my D1 check excludes.  My
round-1 conditional theorem (4.3) is thereby VACUOUS (hypothesis false).

What survives round 1 (unchanged by this): the exact count identities
and the endorsement of 14.5b; the Lemma S scrutiny findings V1-V3 (the
gaps are in Lemma S's PROOF; E_rev's totals are S-functions — fully
consistent with Lemma S's statement, as round 1's 4.2 anticipated);
E_asym; the complement-text obstruction (a^{i+k} b a^j b a^{i+k} has
total 2S-j, still not an S-function); the C-split classification
(vacuous); the sweeps (real non-violations, wrong stratum — below).

### R2.1.1  The autopsy: why the sweep missed it (recorded precisely)

(a) MERGE-PADDED CONCATENATED SCRUTINEES.  The working deletion
    patterns fire on X.mrg.a and a.mrg.X — the input CONCATENATED with
    a computed merge text; and the complement boxes fire on
    mrg.b.mrg.  My sweeps scrutineed X and library chains only —
    never X composed with computed subexpressions.  The pad puts an
    unbounded run next to a separator, so a computed pattern fires
    there unconditionally and never at the other separator.
(b) COMPUTED PATTERNS.  P1/P2's patterns CONTAIN the merge
    subexpression (b.mrg.a, a.mrg.b, a.mrg.b).  My library used
    constant patterns plus a few fixed computed ones (X, merge2,
    dbl2, ...), never computed b-bearing patterns at this nesting.
(c) COMPLEMENT BOXES.  [b/P](mrg.b.mrg)'s output lead = S minus the
    pattern's lead — an S-TYPED computation whose RESULT is k-typed by
    subtraction inside the pad run.  My dominance tests look for
    k-typed construction; complementation is invisible to them.
    Where the induction actually broke: my pass-case analysis assumed
    the text pieces between windows behave like prefixes of F's value
    (left cuts).  A window whose lead consumes from the left edge of a
    pad run leaves a SUFFIX-REMAINDER as the new head — the head can
    be (pad run) - (computed lead), a difference, not a prefix.  My
    "absorption" argument (4.4) never considered right-remainders.

VERDICT: the invariant survives only on the non-merge-padded,
constant-pattern stratum — exactly the stratum my 4550-expression sweep
sampled.  The checker was sound for what it saw (E_swap flagged; the
catalogue passed); the sample space omitted the winning stratum.  The
construction-danger zone for future sweeps must include C(X, computed)
scrutinees and computed b-bearing patterns.

## R2.2  The varying-separator-count program (the last fixed-alphabet refuge)

Every FIXED separator structure falls (the general engine: any letters,
repeats, any k — S-depth 2k+O(1), size Theta(k^2)).  The open question:
does ONE expression E compute rev on ALL of U_k W_k (varying k)?

### R2.2.1  The Sweep Normal Form (SNF) — PROVED

**Lemma (SNF).**  For E = S(R,P,F) and any input where defined, with
R = R(w), P = P(w), F = F(w): the greedy leftmost scan partitions F
into disjoint windows; the output is

    E(w) = q_0 R q_1 R ... R q_t

where q_0..q_t are the surviving chunks of F IN ORDER (t >= 0 fire
sites; R is the SAME string at every firing; t = 0 gives E(w) = F(w)).
*Proof.*  Greedy leftmost, never rescans inserted text: each window is
an occurrence of P in the original text, windows disjoint, scan
proceeds left to right; survivors appear in order.  (3 lines from the
semantics.)  ∎  Machine: my independent greedy evaluator vs the
campaign's prov.py — 990 random expression/input pairs, ZERO
disagreements (varyingk_check.py part A).

Consequences (the coordinator's "uniform interleave"): in any single
sweep, R is evaluated ONCE — every firing emits the SAME text;
deletions are occurrences of one fixed value; site-specific output
comes only from distinct S-nodes or from remnants, which appear in
input order.  Stacks to depth d: sweep d+1's scrutinee = sweep d's
output.  The only REORDERING power in the whole language: the C-tree
(fixed arity, fixed order) and R-copies (identical, repeated).

### R2.2.2  The diagonal census (hand-derived, machine-confirmed)

- b^k |-> b^k: identity (X).  NOT obstructive.
- a.b^k |-> b^k.a: **COMPUTABLE uniformly in k.**
      E_abk = [R/X](X.a)  with R = [eps/a]X.
  *Proof.*  On w = a b^k (k >= 1): R(w) = b^k (the single a deleted);
  scrutinee F(w) = a b^k a; the pattern P = X = a b^k occurs in F(w)
  exactly at position 0 (the only k-run of b's); greedy fires there;
  output = R . (F minus window) = b^k . a = rev(w).  Fails only at
  k = 0 (pattern 'a' fires twice).  ∎  Machine: 40/40 checks.
- (ab)^k |-> (ba)^k: **COMPUTABLE uniformly in k — one constant pass.**
      E_ab = [ba/ab]X.
  *Proof.*  Greedy leftmost fires at positions 0,2,...,2k-2: k windows
  'ab' -> 'ba'; output (ba)^k = rev((ab)^k).  ∎  Machine: 40/40.
- a^i b a^i b a^i and every palindrome-profile family: rev = identity
  there; X computes it.  NOT obstructive.
  (Machine-confirmed, varyingk_check.py part B.)

LESSON: period-k diagonals and single-run-varying diagonals fall to
constant/uniform tricks.  The obstruction, if any, lives on ASYMMETRIC
profiles with all runs DISTINCT — the increasing power diagonal
D(k;B) = a^{B^0} b a^{B^1} b ... b a^{B^k} (B >= 3: subset sums unique,
2B^m != B^{m'}, residues recognizable).

### R2.2.3  How k=2 fell — and the resource it consumed

The k=2 engine's three mechanisms, all confirmed in Lane C's E_rev:
1. PADS: X.mrg.a / a.mrg.X / mrg.b.mrg put unbounded computed runs
   next to chosen separators, making them the ONLY firing sites of
   computed patterns (the S+1 trick: a junction pattern a^x b a^y with
   y = S+1 fires only where the following run >= S+1 — i.e. only at a
   padded junction).
2. COMPLEMENT BOXES: [b/P](mrg.b.mrg) — the surviving head is the pad
   run MINUS the pattern's lead: a difference; S - (i+j) = k gives a
   k-typed lead from an S-typed pad.
3. PER-POSITION KNOWLEDGE: each pattern encodes "first"/"second" via
   its pad; the engine spends Theta(k) patterns for k separators.

The uniform-k analogue of (3) fails: finitely many S-nodes = finitely
many patterns; a pattern VALUE can be huge/computed, so the pigeonhole
must be about STRUCTURE:

**Selectivity landscape (hand analysis, increasing diagonals).**
Unpadded junction patterns a^x b a^y fire at junction m iff
r_{m-1} >= x and r_m >= y — a THRESHOLD SET {m >= m_0}: position-blind
within the qualifying set (a uniform edit).  Double thresholds select
one junction j (x in (r_{j-2}, r_{j-1}], y in (r_{j-1}, r_j]) — but x, y
must be computed values, and a computed value of size ~ lambda.B^k
selects a junction at FIXED OFFSET log_B(1/lambda) from the TOP (or a
fixed position from the bottom, for constants): finitely many patterns
cover finitely many fixed-offset positions + finitely many pad-marked
positions + uniform threshold classes.  The reversal needs Omega(k)
junction-specific edits.  [To be made a theorem — see V3.]

### R2.2.4  The arithmetic fixed point (the wedge)

For the output's HEAD to be r_k on the diagonal, the assembly must cut
the merged pad at exactly S - r_k = sum_{i<k} r_i ("sum minus max").
Routes, each circular:
  (i) cut the pad a^S with a pattern a^y . b: needs y = sum_{i<k} r_i
      as a constructible b-free LENGTH;
  (ii) delete the last run (pattern b . a^{r_k}): needs r_k;
  (iii) threshold-exclude the max: whole-run deletion needs the run's
      length (Match Anchoring: interior consumed exactly = the pattern
      KNOWS the length); partial cuts leave impure residues r_m - y.
DUALITY: r_k and S - r_k are inter-constructible (complement boxes
convert either into the other); NEITHER is reachable without the
other.  At k = 2 the circle is broken from outside:
sum_{i<2} r_i = r_0 + r_1 is an ADJACENT MERGE — constructible by a
pad-anchored junction deletion without knowing r_2 (E_rev's P2 lead).
At k >= 3 the sum spans k runs: a single window spanning k-1
separators must contain them as INTERIOR runs (Match Anchoring: exact)
— its value is "w minus its last run"-shaped — the same extraction
problem one level down.

**Conjecture V1 (LAST-RUN EXTRACTION).**  No expression computes
w |-> a^{r_k} (the last run) on the increasing diagonals, for all k.

**Conjecture V2 (ARITHMETIC SPLIT / SUM-MINUS-MAX).**  No constructible
b-free value has length sum_{i<k} r_i on the increasing diagonals, for
all k.  (The varying-k analogue of round 1's split toll — but NOTE: on
a 1-parameter family Lemma S is VACUOUS (round 13's lesson), so this
needs run-level structure, not total-content counting.)

**Target theorem (conditional, next rounds).**  V2 (with the
head-propagation lemma) implies no E computes rev on the increasing
diagonals, hence none on all of {a,b}*.  Sketch: rev's output head is
r_k; the head of any value is (head-propagation): r_0-material or
constant, minus computed cuts, plus merges — reaching r_k forces a
cut value sum_{i<k} r_i + O(1) (the O(1) slack is the V_h-analogue of
Lane C's fixed-k reduction).  The airtight version needs the run-level
schema induction (R2-flavored) on the k-axis.

### R2.2.5  dec-capacity probe (machine; falsification direction for the program)

dec(V) := longest strictly-decreasing subsequence (by length) of V's
maximal-run sequence.  dec(X) = 1; dec(rev(D(k;B))) = k+1.  If some
small expression had dec growing with k, the dec-capacity program
(which aims to prove dec <= C(E) independent of k) would die.
Machine (varyingk_check.py part C, B=3, k=1..5): library values dec =
1 (X.X = 2); 325 random depth-3 expressions evaluated on all k: max dec
= 3 at EVERY k — dec does NOT grow with k on the sample; dec(rev) does
(2,3,4,5,6).  Consistent with the program.

### R2.2.6  Extraction hunt (machine; falsification direction for V1/V2)

700 random depth-3 expressions on D(k;3), k=1..5, tested for: value =
a^{r_k} (last run); value = a^{S-r_k} (sum-minus-max); head run =
r_k; value = w minus last run.  Hits: only at k <= 2, and the k=2
"sum-minus-max" hit dissected to a CONSTANT coincidence (a^4 on all
of k=2,3,4 — not extraction).  ZERO genuine extraction hits; none at
k >= 3 in the sample.  (At k=2, sum-minus-max = r_0 + r_1 = adjacent
merge — constructible, exactly as the k=2 engine requires.  The
k=2-vs-k=3 boundary is where the fixed point bites: sample evidence.)

### R2.2.7  Files (round 2)

  CHARTER_varying_k.md   the charter
  varyingk_check.py      parts A (semantics cross-check), B (diagonal
                         constructions), C (dec probe), D (extraction hunt)
  varyingk.log           the run log (< 60 s)

### R2.2.8  Honest ledger (round 2)

PROVED (hand + machine-confirmed):
  - SNF (uniform interleave), with the greedy semantics cross-checked
    990/990 against the campaign evaluator.
  - a.b^k |-> b^k.a computable uniformly in k (k >= 1).
  - (ab)^k |-> (ba)^k computable uniformly in k, one constant pass.
  - b^k and palindrome-profile families: identity computes rev.

VERIFIED-ON-STATED-DOMAIN (machine, falsification only):
  - dec-capacity bounded (<= 3) on 325 random depth-3 expressions at
    k=1..5 while dec(rev) = k+1.
  - No extraction (last run / sum-minus-max / head = r_k / w-minus-
    last-run) at k >= 3 in a 700-expression sample; k=2 hits are
    constant coincidences or the adjacent merge.

CONJECTURED:
  - V1 (last-run extraction impossible uniformly in k).
  - V2 (no b-free sum-minus-max length, uniformly in k).
  - V3 (selectivity covering: fixed expressions reach only
    pad-marked junctions, fixed-offset-from-an-end junctions, and
    uniform threshold classes — insufficient for reversal).
  - Target theorem: V2 (or V1) => no uniform rev on {a,b}*.

OPEN / NEXT:
  - Make the head-propagation lemma airtight (schema induction on the
    k-axis; the round-1 scrutiny tools — exact count identities,
    firing counts, threshold selectivity — transplant to the k-axis).
  - Make V3 precise: formalize "uniform edits commute with reversal"
    (a uniform junction edit applied to all qualifying junctions
    cannot invert a distinct-run sequence; the dec-capacity measure is
    the leading candidate for the induction).
  - Relay to Lane B (count/telescope side): the arithmetic fixed point
    (r_k <=> S - r_k) and the threshold/offset selectivity landscape
    are the run-level counterpart of their R2 schema induction.

--------------------------------------------------------------------------
# ROUND 3 — THE TUNING LEMMA (L2) + the B=2 degeneracy finding

Charter: CHARTER_tuning.md.  Round 2 verified by the coordinator
(verify_r2_wall.py ALL VERIFIED, incl. the constant-a^4 dissection at
every k and direct SNF checks 765/765).  Recorded verification notes:
(1) the part-C print label said "B=4" while the code used B=3 — fixed
in varyingk_check.py (cosmetic; varyingk.log, verified
byte-identically, predates the fix).  (2) The naive dec-capacity
claim is FALSE on the explosive stratum — my probe's len <= 600 cap
silently excluded the class.  My own re-measurement (tuning.log part
B): [X/a]X has dec = 2,3,5,6,7,8 (|out| = 13,65,273,1089,4289,16897)
and [X/'b']X has dec = 1,2,3,4,5,6, both growing with k at S-depth 1.
TRIPLE-CONFIRMED: any dec/LDS-type invariant must carry
VALUE-STRATIFICATION (disjoint value ranges across copies), not
subsequence counts alone.

## R3.1  THE B=2 DEGENERACY (new finding; machine-verified; must be relayed)

Lane C's impossibility architecture is staged on the super-increasing
family w^(k) = a^{2^0} b ... b a^{2^k} — the BOUNDARY case of
super-increase (2^j = Sum_{i<j} 2^i + 1).  The boundary telescopes: the
per-run ceiling-halver satisfies Sum_i ceil(2^i/2) = 2^k EXACTLY.
Consequently (all VERIFIED, tuning_fixA.log, 65 checks, 0 failures):

    E_last = [e/b][a/aa]X            = a^{2^k}        the LAST RUN, b-free
    E_cbox = [b/(E_last.b)](mrg.b.mrg) = a^{2^k-1} b a^S   (sum-minus-max as HEAD)
    E_smm  = [e/(b.mrg)]E_cbox       = a^{2^k-1}      B-FREE SUM-MINUS-MAX
    E_h2   = [a/aa]E_smm             = a^{2^{k-1}}    2nd-from-top run, b-free
    [e/b][aa/a]X                      = a^{2^{k+2}-2}  (tweak at depth k+2)
    del_last (Lane B/C's)             = runs 0..k-2, then glued 2^{k-1}+2^k

Consequences:
(a) My round-2 conjectures V1 (last-run extraction) and V2 (no b-free
    sum-minus-max) are REFUTED on B=2 — they were stated for B >= 3
    and STAND there (verified: on D(k;3) the corresponding values sit
    in the gaps — E_last = Sum ceil(3^i/2) has relative power-distance
    growing to ~1/4; E_smm/E_h2 similar; small-k coincidences at
    k <= 4 recorded honestly in the table).
(b) The round-2 "arithmetic fixed point" wedge (r_k and S-r_k
    inter-constructible, neither reachable) is FALSE on B=2: BOTH are
    reachable, in O(1) S-depth, by the telescoping.
(c) LANE C'S FAMILY CAUTION: the pinned schema (their ask 1) survives
    in form — E_last hits each FIXED depth j only once (at k = j), so
    "finitely many j-depths hit infinitely often" still holds — but
    every extraction-impossibility argument of V1/V2 type is
    unavailable on w^(k).  The architecture's remaining lemmas must
    not lean on non-extractability there; alternatively migrate the
    staging family to strongly-super-increasing (B >= 3), where the
    supply/demand separation below is clean.  The per-node supply
    bound (R3.2) is family-independent and holds on B=2 as well.
(d) Uniform rev on w^(k): NOT found.  Four structured attempts (head
    assembly h.b.tail, complement box, E_poll-style pollution, block
    swap) all fail at k = 2,3,4 (tuning.log part D).  The recursion
    rev(w^k) = a^{2^k} b rev(w^{k-1}) still needs k unfoldings; the
    halving chain reaches only fixed offsets from the top.

## R3.2  The Tuning Lemma (L2), proved parts + conditional composition

Setting: strongly-super-increasing families D(k;B), B >= 3 (every run
more than doubles the sum of all smaller runs — powers B^j with
B >= 3 satisfy this; B = 2 is exactly the degenerate boundary).

**L2.1 (cut amounts are slope-pinned; hand, exact arithmetic).**
Separating depth-j material from depth-(j+1) material inside a merged
run (the only reordering channel that is not a C-permutation or an
R-copy) requires a window boundary at the interface: the amount the
window's flank removes, measured from either end of the merged run,
is a consecutive interval sum Sum_{[u..v]} B^i + O(c(E)) (the tweak
budget).  Arithmetic of interval sums:
    Sum_{[u..v]} B^i = (B^{v+1} - B^u)/(B - 1) = alpha*S + err,
    alpha = B^{v-k},  |err| <= (B^u - 1)/(B - 1).
So an exactness cut at interface (u, v) is realized only by a
computed value whose S-slope is the DYADIC alpha = B^{v-k}, up to the
bounded error (which the tweak channel can absorb only when u, or
k - v, is O(1)).  Moreover single interval sums are pairwise distinct
and never within O(1) of a power except when u = v (the run itself:
the tweak channel).  Hence:
  EXACT CUTS AT OFFSET d = k - v FROM THE TOP REQUIRE A VALUE WITH
  DYADIC SLOPE B^{-d}, AND THE TWEAK CHANNEL ONLY COVERS O(1)
  OFFSETS FROM AN END.
[On B = 2 the first clause survives; the tweak channel degenerates
(Sum_{[0..k-1]} 2^i = 2^k - 1 is within 1 of the power), which is
exactly the R3.1 telescoping.]

**L2.2 (per-node supply is O(1); hand; unconditional).**  Every
firing of an S-node cuts ONLY at its window's two ends, with the SAME
amounts at every firing (the pattern's lead and tail runs), and adds
at most the two boundary flanks of R (m_1, m_2).  Interior pattern
runs do not cut — they match text runs exactly (Match Anchoring),
i.e. they are DEMANDS on the pattern's own value, not supplies of
cuts.  So one S-node supplies at most 4 distinct cut amounts (two
subtractive, two additive), regardless of its firing count and
regardless of how many runs its pattern has.  The pinned schema
(Lane B's lemma 1) then pins those amounts to the slope/tweak
classes; the SLOPE SET of an expression is finite (each S-node
contributes finitely many ratio-products), so the offsets reachable
by a fixed E form a finite set D(E) with |D(E)| = O(#S).

**L2.3 (demand and composition — interface, not duplicated).**  The
descent (Lane C round 16 sec 3, with the Escape A kill) forces the
k+1 final singleton exact runs to be produced by remnant-in-order
assemblies plus R-copy insertions; SB (Lane B) forces merging (the
order-inversion budget Phi' <= 4#S+2#C < k); every merge that
co-locates depth <= j with depth > j material must later be
re-separated at their interface; by L2.1 each re-separation at
offset d needs a dyadic-slope-B^{-d} value; distinct offsets need
distinct slopes (and the copy/refutation class [X/a]X only supplies
the VALUES, not the deletions — the final exactness forces the
deletion work, which is where the demand lives; E_poll shows the
flip-creating half is cheap, the exact-deletion half is not).
Conclusion (CONDITIONAL on the pinned schema's sharp form + the
descent's formalization, i.e. exactly the two lemmas the round-16
architecture already names): #S(E) = Omega(k) — no fixed E reverses
the k+1 runs for unbounded k.  Lane B is building the
merge-sensitive budget from the same composition; the interface
between our rounds is: TUNED CUTS ARE THE DELETION BUDGET THAT PAYS
FOR THE POLLUTION.

## R3.3  Machine battery (step 4; tuning.log + tuning_fixA.log)

- Part A (corrected): the six B=2 degeneracy constructions above,
  65 checks, 0 failures.  [The first version of part A had three
  wrong hand-derivations — [a/aa]X alone is NOT b-free (psi keeps the
  b-structure; the [e/b] merge must be composed), my del_last
  expected-form had an extra run, and my complement-box pattern used
  the b-bearing halver — the machine falsified all three before I
  wrote them down anywhere permanent.  Recorded as a process note:
  exactly what the machine is for.]
- Part A7: B=3 contrast table (a-counts, distances to nearest power):
  the supply values stay in the gaps (relative distance bounded away,
  ~1/4 asymptotically for the halver, ~0.11 for E_h2), with honest
  small-k coincidences (k <= 4: E_h2 = 9 = 3^2 at k=3 etc.).
- Part B: the dec-refutation class re-measured by me (numbers above).
- Part C: tuned-bite dichotomy on D(k;3), 168 random depth-<=3
  expressions instrumented (my greedy cross-checked against the
  campaign evaluator): 56 exactness events (survivor within 8 of a
  power), ALL classified as tweak-class bites; ZERO middle-interval
  bites; zero evaluator mismatches.
- Part D: four structured uniform-rev-on-B=2 attempts, all fail.

## R3.4  Files (round 3)

  tuning_check.py / tuning.log          the battery (parts A-D; part A
                                        corrected by tuning_fixA.py)
  tuning_fixA.py / tuning_fixA.log       the corrected part A + A7
  CHARTER_tuning.md                     the charter

## R3.5  Honest ledger (round 3)

PROVED (hand + machine-confirmed):
  - The six B=2 degeneracy constructions (R3.1) — V1/V2 REFUTED on
    B=2 as values/lengths.
  - L2.2 (per-node cut supply = 4 amounts, all firings, any pattern
    arity) — unconditional.
  - L2.1's arithmetic (interval sums are dyadic-slope-pinned with
    bounded error; pairwise distinct; power-separated on B >= 3).
  - Round-2 verification notes recorded (label fix; dec-refutation
    class confirmed by independent measurement).

VERIFIED-ON-STATED-DOMAIN (machine, falsification only):
  - B=3 gap separation for the three supply families (k <= 8, with
    small-k coincidences honestly listed).
  - Tuned-bite dichotomy: 168 expressions, 56 exactness events, zero
    middle-interval bites.
  - Four structured uniform-rev attempts fail at k = 2,3,4.

CONJECTURED / CONDITIONAL:
  - L2.3's composition: #S = Omega(k) on strongly-super-increasing
    families — conditional on the pinned schema's sharp form and the
    descent formalization (the same two lemmas as round 16; the
    family should be B >= 3, or B = 2 handled with the telescoping
    caveat).

RELAYED (for the coordinator):
  1. The B=2 degeneracy (R3.1) — Lane C's staging family is the
     boundary case; extraction-impossibility arguments do not survive
     there; recommend migrating to B >= 3 or re-deriving the descent
     without V1/V2-style support.
  2. The corrected supply-side core for L2: cuts are slope-pinned
     (dyadic B^{-d}); per-node supply is 4 amounts unconditionally;
     the demand is in the DELETIONS (the [X/a]X class supplies values
     cheaply but not exact deletions) — the merge-sensitive budget
     should charge tuned cuts, matching Lane B's composition.

--------------------------------------------------------------------------
# ROUND 4 — THE DEMAND LEMMA (L3): the demand-side composition on B >= 3

Charter: CHARTER_demand.md.  Round 3 verified end-to-end by the
coordinator (all six B=2 constructions re-verified with fresh encodings
k=0..11; the B=3 gap confirmed k=5..14; fixA byte-identical).  The
degeneracy finding ADOPTED: staging family = D(k;3).  Round-3 label fix
recorded.  This round: L2.3 upgraded from interface toward lemma —
what is now PROVED, what the composition needs, and the two precisely
named open lemmas the gap reduces to.  Battery: demand_check.py /
demand.log (parts A-D, all runs ~2 s; the tagged evaluator cross-checked
against the campaign evaluator at every node: 0 mismatches in 202
clean top-level evaluations + 1594 node-checks + the engine; all 98
part-A skips are empty-pattern undefineds, none evaluator divergence).

## R4.1  D1 — F-channel order preservation (PROVED + machine)

For a subexpression nu = [R/P](F) and the fixed input w, call an atom of
value(nu) REMNANT-CHANNEL if it descends from value(F) without passing
through a copy of R (formally: its routing history has no nu-step).
Reading the remnant-channel atoms of value(nu) left to right, their
provenance input-positions form the same relative order as in
value(F).  PROOF: the FU position flow — the sweep's output is
q_0 R q_1 R ... R q_t with remnants q_i in F-order; C concatenates;
X is the identity; K is fresh.  Induction over the expression tree.
This is the atom-granularity formalization of "X maps to identity".
Machine (part A): 300 random depth-<=3 expressions on D(3;3), every
S-node checked (remnant atoms' position sequence a subsequence of F's):
1594 node-checks, 0 violations.

## R4.2  D1'' — the corrected F-side bound (PROVED + machine)

All output runs that are F-pure (never routed at any S-node) AND
single-label share ONE common input label lambda, and appear as
left-to-right slices of input run lambda in input order.  PROOF: two
such runs at distinct labels a < b would place a's atoms before b's
atoms (D1), while the decreasing output places the b-run first.
COROLLARY: every output run with value > 3^lambda is T2/T3-supplied.
HONEST NOTE: my round-3-era informal statement "at most one F-pure
clean run" is FALSE, and the machine caught it before it was written
anywhere permanent: the engine exhibits k such runs, all slicing the
TOP input run (part B: T1 labels = [k] at every k=2..5).

## R4.3  The engine autopsy — the demand picture made concrete (machine)

On D(k;3), k = 2..5, Lane C's T6 engine (re-implemented with
attribution; rev VERIFIED, tagged evaluation identical):
- The engine's reversal is NOT a permutation of runs.  Output run 0
  (length 3^k) is a MERGED BLOB (T3, labels 0..k) whose exact length
  is arithmetic: S - (prefix-sum of L_{k-1}) = 3^k.  The remaining k
  output runs are SLICES OF THE TOP INPUT RUN (T1, label k; T2 = 0).
- All k output b's are ROUTED plants (routing depth 1: box splices),
  at the exact top-anchored sums — verified [81, 108, 117, 120] at
  k=4 — while the input b's sit at bottom-anchored masses: the mirror
  plant, carried entirely by routed b's.
- The k junction differentiations are paid by k box patterns, each
  carrying exactly 2 anchored-offset values (L_m's prefix at
  bottom-offset m and suffix at top-offset k-m-1): part-B-tight, and
  0 L2.2 violations (no pattern with > 4 distinct deep amounts).
- The del-chain walks: k-1 del nodes per junction (3(k-1) S-nodes
  counting the inline mrg copies), Theta(k^2) total — the interior
  anchored sums are reached only by END-WALKS.  The round-2 supply
  class finding (middle sums not directly constructible) is visible
  here as the engine's cost structure; the Omega(k) floor is the k
  DISTINCT anchored offsets (part C: k of k realized).

## R4.4  The Demand Lemma (L3) — statement and channel analysis

TARGET (charter): if the DECOMP-reduced S-topped leaf reverses
intervals w_I with m+1 runs (m -> infinity), the derivation contains
scale-local exactness events at Omega(m) distinct junction scales;
with supply <= 4 cut amounts per node (L2.2) and <= 2 deep
fully-consumed scales per pattern (Lane C part B), #S = Omega(m).

The output's exactness objects: m+1 run lengths + m plant positions,
at m+1 distinct scales.  Supply channels:

(T1) F-pure pass-through: by D1'' all share one label lambda (the
     engine: slices of the top run).  The runs are free; their
     boundary PLANTS are not — the b's between the slices are routed
     or displaced, and each plant sits at an exact top-anchored mass.
(T2) copy-routed: the refutation-class channel ([X/'b']X supplies the
     VALUES cheaply).  Identical copies are treated identically by
     any downstream pass up to the remnant material between them; a
     window that differentiates copy c from copy c' must span the
     boundary and carry the differentiating remnant's scale in its
     pattern — <= 2 deep scales per pattern (part B).
(T3) merge-assembled: Lane B's Payment theorem (hand-proved):
     surviving mergey flips are stripped by downstream exact deep
     cuts; the cuts are slope-pinned (L2.1) and <= 4 amounts per node
     (L2.2).  The engine's top blob is exactly this channel, paid by
     the box patterns' anchored values.

Counting: the m plants at m distinct top-anchored offsets each require
somewhere in the derivation a value realizing the anchored/interval
sum at the plant's offset — via (a) a pattern flank/interior at the
plant's scale (match-exactness; <= 2 scales/pattern), or (b) recursion
into a strictly smaller subexpression (the R/P channels — the
plant-capacity descent: a value with many correct plants is itself
partially reversed, and X has zero correct plants since BotSum(t) <>
TopSum(t) for all t on D(k;3)), or (c) a composition of off-scale
events (the "lucky-sum" channel).  (a) and (b) are Omega(m)-charged
under the per-node budgets; (c) is the remaining gap.

## R4.5  The two named open lemmas (the precise residue)

(OL-1) MATCH-EXACTNESS: a window boundary creating an exact deep
  boundary at scale 3^s requires the pattern's value to contain a run
  within c(E) of a scale-s-adjacent amount, UNLESS the exactness is
  composed from off-scale events.  The loophole's boundary is now
  mapped: by strong super-increase, TopSum(t) has a unique 0/1
  site-term representation (the consecutive-complete support
  {3^s : s > t}); the alternative S - BotSum(t) uses {S} + low terms;
  BOTH are ledger-cheap (the consecutive-complete collapse) — so the
  TERM LEDGER ALONE DOES NOT OBSTRUCT anchored plants.  The
  obstruction must live in the SCALE-COUNT (part B) plus the WALKS
  (OL-2).  Machine: the engine pays real nodes for every plant, 0
  part-B violations.
(OL-2) INTERIOR-ANCHOR SUPPLY: on D(k;3), anchored-sum values at
  interior offsets are not constructible at O(1) S-depth — the
  end-walk bound Omega(dist-to-end).  Evidence: the engine's Theta(k)
  chains; the round-2 arithmetic fixed point; round-3's A7 gaps (the
  extractor candidates land in gaps on B=3); the B=2 counterexample
  boundary (where it is FALSE — the telescoping).  This is the
  supply-side companion of L2.1 and where the B=2 vs B >= 3
  distinction enters the demand side.

## R4.6  The composition (interface, not duplicated)

SB (proved) closes the merge-free regime; Payment (B, proved)
converts mergey flips into deep-cut demands; L2.1/L2.2 (proved) pin
the cuts; part B (machine) caps per-pattern deep scales; D1/D1''
(this round, proved) close the F-pure channel's reordering power;
OL-1/OL-2 are the residue.  CONDITIONAL THEOREM (form unchanged from
round 16, gaps now named precisely): #S = Omega(m) on D(k;3), hence
no fixed E computes rev on {a,b}* — failure effective at
k > f(|E|).  NOTE FOR LANE B: the term ledger's consecutive-complete
collapse means the demand does NOT close through the ledger for
anchored sums — the interface is the deep-cut count (Payment) plus
the per-pattern scale cap (part B), with OL-2 the supply-side gap.

## R4.7  Machine battery (all < 2 s; demand_check.py / demand.log)

- A: D1 per-node remnant-order: 300 exprs, 1594 node-checks,
  0 violations; tagged evaluator = campaign evaluator (0 mismatches).
- B: engine on D(k;3) k=2..5: rev VERIFIED; trichotomy census
  (T1=k slices of run k, T2=0, T3=1 merged top blob; D1'' holds);
  all output b's routed plants.
- C: ledger k=4,5: 0 L2.2 violations (<= 4 deep amounts per
  pattern); k of k distinct anchored offsets realized; del-chain
  walks [9,9,9,9]/[12,12,12,12,12] (Theta(k^2) total, Theta(k) per
  junction).
- D: plant census k=4: output b masses == top-anchored sums exactly;
  routing depths all 1.

## R4.8  Honest ledger (round 4)

PROVED (hand + machine-confirmed):
  - D1 (F-channel order preservation, atom granularity).
  - D1'' (one shared label for F-pure single-label runs; the slice
    structure).
  - The engine autopsy facts (B=2..5): not-a-permutation, top blob
    arithmetic, slices-of-top-run, routed plants at exact
    top-anchored sums, part-B-tight box patterns.
VERIFIED-ON-STATED-DOMAIN (machine, k=2..5):
  - the trichotomy census; the anchored-offset realization count;
    the del-chain walk structure; the evaluator cross-checks.
CONJECTURED / CONDITIONAL:
  - L3 (the demand lemma) conditional on OL-1 (match-exactness) and
    OL-2 (interior-anchor supply) + B's L1'' write-out and Payment
    as already proved/hand-proved inputs.
OPEN (named):
  - OL-1 MATCH-EXACTNESS (the lucky-sum loophole, mapped to the
    consecutive-complete collapse).
  - OL-2 INTERIOR-ANCHOR SUPPLY (end-walk bound; FALSE on B=2).
REFUTED-BY-MACHINE-BEFORE-WRITTEN (process note, as in round 3):
  - my "at most one F-pure clean output run" — false; corrected to
    D1''.

## R4.9  Files (round 4)

  demand_check.py / demand.log      the battery (parts A-D)
  CHARTER_demand.md                 the charter

--------------------------------------------------------------------------
# ROUND 5 — D1'' RESOLVED (weak + trace) + OL-2 (the interior-anchor supply)

Charter: CHARTER_ol2.md.  Round 4 verified end-to-end (the coordinator's
fresh route-list tagged evaluator replays part A exactly, 1594/0); the
D1'' correction ACCEPTED (my round-4 two-line proof was incomplete —
it conflated a run's LABEL with its VALUE; multi-label assignments are
consistent with non-decreasing labels + the slice bound + per-label
exhaustion).  Discipline note adopted: full invocation in the first
line of every log (ol2.log complies).

## R5.1  D1'' — the weak form is the proved form; the T1-trace is proved

**D1''-weak (PROVED, from D1).**  The F-pure single-label output runs,
in output order, have non-decreasing labels, each label lambda
satisfies 3^lambda >= the run's value, and the total F-pure length at
one label is <= 3^lambda (per-label exhaustion).  [Round-4 proof,
correctly stated.]

**The T1-trace (PROVED — what the composition actually needs).**
(i) MOD-3 LEMMA: on D(k;3), the t-th output plant sits at a-mass
TopSum(t) = Sum_{s=k-t..k} 3^s, which is congruent to 0 mod 3 for
every t <= k-1; every input b sits at BotSum(sigma) =
Sum_{s<=sigma} 3^s, congruent to 1 mod 3.  Hence NO input b can
survive at a correct plant position with zero displacement: every
output b is either ROUTED (an S-node inserted it: a plant event) or
DISPLACED by a nonzero mass change Delta = TopSum - BotSum ~= 0
(realized by the exact mass events — window inserts/deletes — to its
left).  Machine (part D): the TopSum/BotSum tables at k=4 with
residues [0,0,0,0] vs [1,1,1,1], intersection EMPTY.
(ii) The inter-plant gaps are the output runs, exact at k+1 distinct
scales; the plants and gaps carry the T1-channel's demand through the
same OL-1 channel as T2/T3 — INDEPENDENTLY of the F-pure label
structure.  The round-4 corollary "every run with value > 3^lambda is
T2/T3-supplied" is WITHDRAWN (it needed the strong form); nothing
else in the round-4 composition used the strong form: the R4.6 list
reduces to D1 (order preservation) + the plants/gaps trace, both
proved.  The composition survives D1''-weak.

**D1''-strong (one shared label): OPEN, with the wall mapped.**  My
directed constructions at k=2 all fail on the same selectivity wall
(machine part E): E1 = [a^9 b a^3 b / a b a^3 b a^8]X computes
rev(D(2;3)) in one splice but yields exactly ONE F-pure run (the top
run's last atom); E2 = [a^9 b / a b]X double-fires (the second firing
eats a run-1 atom and glues: runs (9, 11, 9)); E3: every short
selector a^i b fires at a SUFFIX of the junction set — the first b
cannot be selected alone without eating run 1.  The coordinator's
consistency example (k=4: full run 3 + slices of run 4) remains
unrealized; the wall suggests the strong form may be true, but the
only proof route I found runs through the isolation cost (OL-2's
selectivity), so I record it as OPEN rather than claim it.

## R5.2  OL-2 — the interior-anchor supply bound (the round's core)

**STATEMENT.**  There are universal constants c, c' and a V-fixed
finite offset set J(V) such that: for every k and every a-run of
every value in V's derivation on D(k;3) whose length is exactly an
anchored sum Sum_{[0..m]} or Sum_{[m+1..k]}: either
min(m+1, k-m) <= c * Sdepth(V) + c'   or   m in J(V).
I.e. anchored sums at interior offsets are not constructible at
O(1) S-depth: the END-WALK BOUND Omega(dist-to-end).  (FALSE on B=2:
the telescoping boundary — round 3.)

**The proof architecture (five steps, with grades).**

STEP 1 (normal-form dichotomy; uses TL at altitude-minus-one, i.e.
conditional on PO).  By TL, a run's value is in the closure C =
Sum q_i 3^{e_i} + (Ak+B) + beta with V-fixed anchored exponent
families.  The anchored sum Sum_{[0..m]} = (3^{m+1}-1)/2 has an
essentially unique such representation (super-increase), so its
exponent m+1 comes from {k-c, k+1-c} (top-anchored: m >= k-O(1)),
or {j-c'} (SITE-anchored: the run's site j = m+O(1), i.e. the run
carries input-run-m material), or {c''} (fixed: m in J(V)).

STEP 2 (site-anchored means material).  In TL's measure form, a
site-anchored run of value Sum_{[0..m]} carries the interval measure
[0..m] (count-scale 1): the input runs 0..m are MERGED in V's
subtree, i.e. the separators b_0..b_{m-1} were deleted there.

STEP 3 (THE FIRED-SET LEMMA — PROVED this round, hand + machine).
On D(k;3) (and any X-descended distinct-run value):
 (i) a single-b pattern fires at a set of junctions that is a
     SUFFIX of the junction order (monotonicity: the local runs only
     grow, so a pattern fitting at an earlier junction fits at every
     later one);
 (ii) a multi-b pattern with positive interior fires at most once
     (SD on distinct-run texts), its ONE window spanning a contiguous
     junction block whose interior runs match the pattern's interior
     runs EXACTLY (Match Anchoring) — the fired block is pinned by
     the pattern's interior values: FIXED offsets if they are
     powers, no firing otherwise;
 (iii) 'bb'-type interiors do not fire.
Machine (part A): 82 single-b checks 0 non-suffix; 1400 multi-b
checks 0 violations (160 firings, all single-window, interior-exact;
the j = 0 'bb' interiors fire never — D(k;3) has no 'bb').

STEP 4 (the walk accounting — proved modulo bookkeeping).  The
head-merge [0..m] needs the junction-prefix {b_0..b_{m-1}} deleted.
By Step 3, no single pass deletes a strict-interior block (machine
part B1: 0 hits over all single-b selectors and all interior blocks)
and no single-b pass deletes a prefix (suffixes only).  The two
channels: (a) the BOOST-WALK — the S+1-threshold pattern fires at
exactly the one boosted junction (the pad-created one), so each pass
deletes ONE head-b at O(1) cost: Omega(m) passes; (b) the BLOB
channel — the full merge a^S (pattern 'b', one pass) destroys all
junctions, and recovering an interior anchored run from the blob
requires a two-sided box whose PATTERN carries anchored sums at the
same offsets (Step 5).  The tail-merge [m+1..k] is one pass for a
scrutinee whose threshold leading-run has value 3^{m+1} (a^{3^{m+1}} b
fires at exactly b_{m+1}..b_{k-1}) — but that threshold is not free:
V is one expression for ALL k, so the leading run is either a V-fixed
constant (fixed scale: m+1 in J(V)) or a COMPUTED value at scale
3^{m+1} with its own supply cost: the site-channel (isolation: the
head-merge again) or the psi-descent — the [a/aaa]-chain multiplies
by ~1/3 per node (machine part C: the scale-distance from the top
power descends ~1 per node: -0.37, 0.63, 1.60, 2.60, 3.37, 4.37 at
depths 0..5; no chain value is an exact power — the gap phenomenon),
and every psi-ratio is a quotient of two VALUES whose own
scale-distance is subject to the same accounting, the only free
scales being the input's runs — usable as values only through
interior isolation, which is Step 3's selectivity again.  Both
channels give Omega(min(m, k-m)).

STEP 5 (the box-chain termination — proved sketch).  The blob-channel
recursion preserves the offset while the depth strictly decreases;
the leaves (X, K) realize only the EXTREME anchored sums (m = 0 and
m = k-1 are the input's own runs) and the fixed constants (J(V)).
Hence any realization of an interior anchored sum contains, somewhere
in its subtree, a walk-segment of length Omega(min(m, k-m)); the walk
passes are nested (each del's scrutinee contains the previous), so
the S-depth pays it.

**Status: OL-2 is PROVED at analysis grade conditional on TL (= PO),
with two write-out pieces precisely located: the walk-accounting
bookkeeping (Step 4) and the box-chain termination (Step 5).
The ENDS of the range are free (part F): [e/b][aa/aaa]X = a^{3^k}
exactly, at S-depth 2 — the psi-map run u -> r*floor(u/p) + (u mod p)
with (r,p) = (2,3) sends run j >= 1 to 2*3^{j-1} and leaves run 0, so
the merge sums 1 + Sum 2*3^{j-1} = 3^k (the top input run itself:
the B=3 analog of the B=2 E_last; k = 1..6 machine-exact).  This is
consistent with the bound (min(m+1, k-m) = 1 at m = k-1) and is the
contrast that makes OL-2 interior-only.  The engine is the tightness
witness: L_m realizes the anchored sums at offsets m and k-m-1 with
k-1 del nodes each (machine part B3: runs (1,120),(4,117),(13,108),
(40,81) at S-depth 4); the Omega(k) floor is the k distinct
offsets.**

## R5.3  Machine battery (ol2_check.py / ol2.log; ~0.1 s)

A: fired-set lemma: 82 + 1400 checks, 0 violations (j = 0 'bb'
   interiors included: they never fire — D(k;3) has no 'bb').
B: no one-pass interior block (0 hits); the staged suffix-deletion
   EATS its threshold-sized preceding run at every step (the runs
   (1,3,9,81) -> (1,3,81) trace); the box patterns' runs and depths.
C: the psi-chain scale walk (one scale-distance per node; no exact
   powers — the gap).
D: the mod-3 lemma tables.
E: the D1''-strong directed attempts (E1 one-splice rev with one
   F-pure run; E2 the double-firing damage; E3 the selector wall).
F: the end-anchored contrast — [e/b][aa/aaa]X = a^{3^k}, k = 1..6
   exact (inner runs {1} u {2*3^{j-1}}).
[Process note: two of my own check implementations were WRONG first
 (window-relative b positions; block enumeration including v = k-1,
 i.e. suffixes) — the machine caught both before anything was
 recorded, and the corrected checks are what the lemma actually
 says.  The A2 'violations' in the first run were single windows
 spanning multiple junctions — the box mechanism itself.  Two
 print-text nits in the first saved log (E2's junction label, E3
 printing positions under an 'indices' header) were fixed and the
 battery re-run before reporting; every number in this section is
 from the final log.]

## R5.4  Honest ledger (round 5)

PROVED (hand + machine-confirmed):
  - The FIRED-SET LEMMA (Step 3) — the round-2 selectivity landscape,
    now sharp on D(k;3).
  - The MOD-3 LEMMA + the T1-trace (R5.1): the composition's
    T1-channel survives D1''-weak; the plants/gaps carry Omega(k)
    through the OL-1 channel regardless of labels.
  - D1''-weak (restated, from D1).
VERIFIED-ON-STATED-DOMAIN (machine):
  - all Step-3/4 checks above at k=2..5; the psi-walk at k=5.
  - the end-anchored contrast [e/b][aa/aaa]X = a^{3^k} (k = 1..6,
    exact): the ENDS of OL-2's range are free at depth 2; the floor
    is interior-only.  (A supply-side bonus for B's ledger: a
    1-anchored-term boundary value at depth 2, consistent with
    TL(iii).)
PROVED AT ANALYSIS GRADE (conditional on TL/PO; write-out pieces
located): OL-2 (Steps 1-5).
OPEN:
  - D1''-strong (one shared label): the wall is mapped (the
    selectivity/isolation cost); the coordinator's k=4 consistency
    example is unrealized by my directed attempts.
  - The tight constant of OL-2 (the engine pays k-1 per junction;
    the bound says Omega(min(m, k-m))).

## R5.5  Files (round 5)

  ol2_check.py / ol2.log      the battery (invocation first line)
  CHARTER_ol2.md               the charter

--------------------------------------------------------------------------
# ROUND 6 — THE FIRED-SET FIX (FSL') + THE OL-2 WRITE-OUTS

Charter: CHARTER_writeouts.md.  Round 5 verified and accepted with one
correction: FSL (i) was FALSE AS STATED — my A1 battery covered only
ONE-FLANK patterns (a^i b, b a^i); TWO-FLANK patterns (a^i b a^j) fire
at SKIP-AFTER-BITE sets (the coordinator's [eps/a^3 b a^9]X fires
{1,3}).  The correction is ACCEPTED and is the first item below.  The
Step-4 use (no clean proper-prefix deletion) SURVIVES and is now
PROVED in the relativized form.

## R6.0  The corrected fired-set lemma (FSL') — PROVED

**THE RECURSION THEOREM (the exact closed form).**  On any text with
runs R_0..R_k (lengths >= 0) and single-b pattern P = a^i b a^j
(i, j >= 0), the greedy fired set is given by:
    c_0 = R_0;  fire_sigma  <=>  c_sigma >= i  and  R_{sigma+1} >= j;
    c_{sigma+1} = R_{sigma+1} - j*[fire_sigma].
Proof: scan mechanics.  The window at b_sigma consumes the last i
atoms of run sigma's remnant (the remaining c_sigma - i stay as
remnant), b_sigma, and the first j atoms of run sigma+1 (Match
Anchoring at one-b granularity); the contiguous a's before
b_sigma are exactly the run-sigma tail left by the previous window
(the bite j) or the full run; the leftmost occurrence is at the first
fitting junction.  Induction on sigma.  Machine (part A): 3211 checks
EXACT over D(k;3), SUFFIX-MERGED, PSI-MAPPED and BITTEN texts (empty
runs), k = 2..6, i, j <= 12.

**(i-a) ONE-FLANK (i = 0 or j = 0): suffix.**  With j = 0 the bite is
zero, so c_sigma = R_sigma always: fired = {sigma : R_sigma >= i}; with
i = 0 the leading is vacuous: fired = {sigma : R_{sigma+1} >= j}.  On
strictly increasing-run texts both are SUFFIXES of the junction order.
Machine: 0 non-suffix over k = 2..6, i <= 60, both orientations.

**(i-b) TWO-FLANK: SKIP-AFTER-BITE.**  Let F = {sigma : R_sigma >= i,
R_{sigma+1} >= j} be the fitting region — a suffix, since runs strictly
increase.  sigma* = min F fires (c_{sigma*} = R_{sigma*}).  Every
skipped sigma in [sigma*, k-1] satisfies: sigma-1 FIRED and the skip is
the bite, c_sigma = R_sigma - j < i.  RESUMPTION: after a skip,
c_{sigma+1} = R_{sigma+1} (the full run), so sigma+1 fires if it fits:
no two consecutive skips in F, and the fired set is F minus isolated
holes, each hole immediately after a firing.  [The coordinator's
counterexamples are the densest case: [eps/a^3 b a^9]X on D(4;3) =
{1,3}: the junction-1 window consumes ALL of run 2 (j = 9 = R_2), so
c_2 = 0 < 3.]

**COR-A (prefix exclusion).**  No single-b pass fires EXACTLY the
proper prefix {b_0..b_{m-1}} (1 <= m <= k-1) on texts with >= 3
junctions whose runs are D-coarsenings (interval sums of D(k;3)).
Proof: (1) b_m fits on intact material (i <= R_{m-1} < R_m,
j <= R_m < R_{m+1}).  (2) So its skip is a bite: R_m - j < i.
(3) If m <= k-2, the resumption fires b_{m+1} (full run R_{m+1} >= i,
R_{m+2} >= j): contradiction.  (4) m = k-1: the b_0 firing gives
i <= R_0 and j <= R_1, so R_{k-1} < i + j <= R_0 + R_1 < 3^k <=
R_{k-1}: contradiction.  On coarsenings the same inequality: the last
coarsened run >= 3^k while any two earlier coarsened runs sum < 3^k.
EDGE: at k = 2 the exception is REAL — [eps/a.b.a^3]X fires {b_0}
(machine part C1) — exactly where OL-2's bound min(m+1, k-m) = O(1)
anyway.  Machine (part B): 0 violations, k = 3..6, all single-b
patterns i, j <= 12, on D, suffix-merged, psi-mapped texts.

**COR-B (interior-block exclusion, size >= 2, ALL single-b).**  No
single-b pass fires exactly {b_u..b_v} with 1 <= u < v <= k-2.
Proof: if v <= k-3 the resumption at b_{v+2} fires — contradiction;
v = k-2: R_{k-1} < i + j <= R_u + R_{u+1} < 3^k <= R_{k-1} —
contradiction.  [This EXTENDS round-5's B1, which tested one-flank
selectors only — a battery gap the coordinator's correction exposed;
now proved for all single-b and machine-checked.]

**COR-B1 (the size-1 exception, sharp).**  A single-b pass CAN fire
exactly {b_u} (u interior) ONLY at u = k-2 (the second-to-last
junction), and then the trailing flank obeys j > R_{k-1} - R_u >=
2*3^{k-2}: the window eats more than 2/3 of run k-1 (the
second-from-top run).  Machine (part C2): [eps/a.b.a^9]X on D(3;3)
fires {b_1}, run 2 eaten entirely (j = 9 = R_2); j = 7, 8 leave
leading 2, 1 >= i = 1 so b_2 fires ({1,2}).

**(ii) multi-b and (iii) 'bb': unchanged from round 5** (SD: at most
one firing on distinct-run texts, the window interior-exact; 'bb'
never fires on D(k;3)).

**THE CLASS-ESCAPE LEMMA (the mechanism behind the corollaries).**
All of FSL' and COR-A/B/B1 live on STRICTLY INCREASING-run texts.  The
engine's BOOST is exactly the controlled escape: the pad a^{S+1}
PREPENDED to the text makes run 0 the maximum (the increase is
broken), so the one-flank threshold set {sigma : R_sigma >= S+1}
becomes the PREFIX {0} — the fired set COR-A forbids on the class.
The window consumes the pad's tail, all of run 0, and b_0; the
leftover pad (r_0 atoms) merges with run 1: the output value is the
CLEAN head-merge Sigma_{[0..1]} (machine-verified semantics: the
leftover = r_0 = the run-0 length, by the window arithmetic), and the
increase is RESTORED (Sigma_{[0..t]} < 3^{t+1} <= next run).  So each
escape deletes exactly ONE head junction and returns to the class.
This is the proof-altitude account of the boost-walk: the class can
only be escaped with material exceeding the text's total mass (the
pad), each escape is O(1) junctions, and the pad is top-scale material
(free: [eps/b]X-derivatives, depth 2) — but it must be REAPPLIED per
junction.

## R6.1  THE STEP-4 WRITE-OUT (proof altitude)

**S4.0 (the obligation).**  Fix V; there are C, c' and a finite J(V)
such that for all k: if a run of any value in V's derivation on
D(k;3) has length exactly Sum_{[0..m]} = (3^{m+1}-1)/2 with
D <= m <= k-D, then min(m, k-m) <= C*Sdepth(V) + c' or m in J(V).

**S4.1 (the text class).**  The derivation's intermediate values are
handled in two regimes.  CLEAN: texts whose runs are interval sums of
D(k;3) (coarsenings — strictly increasing, since Sum_{[u..v]} <
3^{v+1} <= Sum_{[v+1..w]}); FSL' and COR-A/B/B1 hold on them
(relativized, machine part B).  CORRECTION: texts with bites, empty
runs, or inserted copies — the fired-set structure is still EXACT
(the recursion theorem holds on ALL texts: machine part A includes
the bitten texts), but the exclusions need the value bookkeeping,
which is S4.3.  [Honest boundary: the exclusions are proved on
increasing-run texts; the correction regime is routed through S4.3,
whose general case is the named conditional below.]

**S4.2 (the head channel: the boost-walk, Omega(m)).**  The head-merge
[0..m] requires {b_0..b_{m-1}} deleted inside the subtree, with the
boundary b_m present.  Consider the clean routes: by COR-A no pass
fires a proper prefix of the current text; by the class-escape lemma
the only clean first-junction deletion is the boost (one junction per
escape, the pad at top scale, the increase restored after each);
multi-b windows are SD-single with interior-exact matches, so a
multi-b head-eat needs the pattern to BE the D-fragment text
(S4.5's circular supply); the non-clean routes (skips with bites,
fused prefix+later firings like {0,2}, the full merge) corrupt the
value and enter S4.3/S4.4.  Hence m clean head-deletions = m nested
passes: Sdepth >= m - O(1).  The engine's del_first chains are the
tightness witness (Theta(m)).

**S4.3 (the exactness arithmetic: compensation-at-scale).**  In the
GLUE decomposition v(r) = span - bites + c*rho, exactness of the
repunit Sum_{[0..m]} (base-3 digits all 1 on scales 0..m, 0 above)
forces PER-SCALE matching: a bite at scale s creates a digit defect
that cannot cancel against terms at separated scales (super-increase:
a defect at scale s exceeds the sum of all lower-scale terms), so it
must be compensated by R-material at scale s + O(1) — a synthetic
value at an interior scale, whose supply is S4.5's recursion.
PROVED CASES (round-2 fixed-point style, machine part E5): the
psi-map never lands on the repunit — [a/aa]a^{3^{m+1}} =
a^{Sum_{[0..m]}+1} (the +1 is exactly the scale-0 digit defect); the
 ONLY exact synthetic landing is the MOD-DELETION (S4.4), which pays
the threshold.  GENERAL CASE: stated as the named conditional
(S4.3-general: unbounded term counts) — the remaining write-out
piece of the whole theorem.

**S4.4 (the blob route: the exact mod-landing, Omega(k-m)).**
[eps/b]X = a^S (one pass).  Then the DELETION map (not the psi-map)
lands exactly: S = 3^{m+1}*((3^{k-m}-1)/2) + Sum_{[0..m]}, so
    [eps/a^{3^{m+1}}].[eps/b].X = a^{Sum_{[0..m]}}  EXACTLY
(machine part E4, all m < k <= 6).  Round-5's "gap phenomenon" was an
artifact of restricting to psi-maps: U -> r*floor(U/p) + U mod p
never produces the repunit from a power, but U -> U mod p does, at
the price of the threshold pattern.  The cost is S4.5.

**S4.5 (the threshold-supply recursion: one scale per node).**  The
only O(1)-depth single-run powers are the TOP ([aa/aaa][eps/b]X =
a^{3^k}: depth 2 — round-5 part F) and V-fixed constants (s in J(V)).
An interior power a^{3^{t+1}} is supplied by: (a) the psi-descent
from the top — each node's ratio is a quotient of two VALUES; a
constant-pattern node descends only V-fixed many scales (the pattern
is a fixed string), and a computed-ratio node's pattern must itself
be supplied at the higher scale (the recursion), so the descent from
3^k to 3^{t+1} costs Omega(k-t-1) nodes (machine E1: one
scale-distance per [a/aaa] node); or (b) the SITE-isolation of run
t+1 — the head mass (runs 0..t) must be deleted, which LEMMA MASS
(machine part D) forbids for b-free patterns: [eps/a^p] kills exactly
the run-suffix {s : p | 3^s} (p a power of 3) or nothing, never a
small run with a larger surviving; the fixed box eats only fixed many
runs (machine E6: [eps/a.b.aaa.b]X eats runs 0..1: the t = O(1)
absorption); the computed box IS the prefix text — circular, paying
the theorem at t; multi-b windows eat one run each.  All routes pay
Omega(min(t+1, k-t-1)) or land in J(V).

**S4.6 (the C-seam closure).**  The concatenation seam splits the
repunit as e1-last ++ e2-first = Sum_{[0..t]} ++ Sum_{[t+1..m]}.  The
first piece pays S4.2/S4.5 at t; the second piece's HEAD MASS (runs
0..t) deletion is MASS-forbidden for b-free patterns, the fixed box
eats only fixed t, the computed box is the prefix at t (circular), and
multi-b windows eat one run each (Omega(t)); the scale shift
([a/aa][a^2/a^3]X: runs (1, 1, 3, ..., 3^{k-1}) — machine E7)
preserves both distances to the interval ends.  The seam therefore
pays max(Omega(t), Omega(m-t, k-m)) — never below the bound.

**THE STEP-4 THEOREM.**  Assembling S4.1-S4.6: every route to an
interior Sum_{[0..m]} pays Omega(min(m, k-m)) or lands in J(V):
the boost-walk pays m; the blob and box routes pay the threshold
descent k-m; the compensations recurse into the same supplies; the
splits re-apply the obligations.  Grade: PROVED conditional on TL (=
PO, for the strata decomposition) and S4.3-general (the digit-matching
lemma in the unbounded-term case).

## R6.2  THE STEP-5 WRITE-OUT (box-chain termination)

Updated by S4.4: the BLOB channel pays DIRECTLY (the mod-landing at
the threshold's cost) — no recursion needed there.  The BOX channel:
a multi-b pattern's window interior must match the text's interior
runs EXACTLY (round-5 A2 + Match Anchoring), so a box realizing
anchored sums at interior offsets has a pattern that IS a D-fragment
text: its supply is the prefix isolation (S4.5: the threshold
descent, Omega(k-t)) or a smaller box (recursion on strictly smaller
subtrees).  The recursion terminates: the leaves X and K supply only
the full text and V-fixed constants — no interior fragments — and the
del-scrutinee nesting (each del's scrutinee contains the previous)
means the walk's passes are paid in S-depth, not width.  Hence every
realization of an interior anchored sum contains a walk-segment of
length Omega(min(m, k-m)) in its subtree.

**OL-2 assembled:** with R6.0-R6.2, OL-2 stands at PROVED CONDITIONAL
ON TL (= PO) + S4.3-general, with S4.3-general the single remaining
write-out piece (it is exactly the lucky-sum/compensation channel the
round-5 report named as optional).

## R6.3  Machine battery (fsl6_check.py / fsl6.log; 0.1 s)

A: the recursion theorem: 3211 checks EXACT (D, suffix-merged,
   psi-mapped, bitten texts; k = 2..6, i, j <= 12).
B: 0 violations of COR-A / COR-B / COR-B1 / skip-after-bite /
   one-flank suffix, on the clean texts.
C: the edge witnesses: k=2 prefix exception ([eps/a.b.a^3]X = {b_0});
   the size-1 interior exception at u = n-2 with the run-(n-1)
   destruction ([eps/a.b.a^9]X at k=3: {b_1}, run 2 = 9 eaten).
D: LEMMA MASS: [eps/a^p]X on D(6;3), p = 1..40: the killed set is a
   suffix {s >= c} iff p is a power of 3, else empty; never a small
   run dead with a larger alive.
E: the fixed points: E1 one scale per node (the power chain); E2 the
   prefix isolation [eps/a^{3^{t+1}}]X = D(t;3).b^{k-t}; E3 the
   b-tail cleanup [eps/bb]; E4 the BLOB LANDING
   [eps/a^{3^{m+1}}][eps/b]X = a^{Sum_{[0..m]}} EXACTLY; E5 the
   halver gap ([a/aa]a^{3^{m+1}} = Sum + 1); E6 the fixed-box
   head-eat; E7 the clean scale shift.
F: the S-depth witnesses (the two routes pay k-m and m).
[Process note: one battery bug (an index-list treated as an array in
 part D) crashed the first run before any result was recorded; fixed
 and re-run.  The round-5 B1 gap (one-flank only) is disclosed above
 and closed by COR-B.]

## R6.4  Honest ledger (round 6)

PROVED (hand + machine-confirmed):
  - FSL' complete: the RECURSION THEOREM (exact closed form on all
    texts), (i-a) one-flank suffixes, (i-b) skip-after-bite +
    resumption, COR-A, COR-B, COR-B1 with the two sharp edge
    witnesses, the CLASS-ESCAPE lemma (the boost as the controlled
    increase-break).
  - LEMMA MASS (b-free monotonicity: kill a run-suffix or nothing).
  - The PREFIX-ISOLATION and BLOB-LANDING fixed points (E2, E4) and
    the halver gap (E5).
  - S4.2 (the head channel, Omega(m)), S4.4 (the blob route,
    Omega(k-m)), S4.5 (the threshold recursion, one scale per node),
    S4.6 (the C-seam closure), R6.2 (Step 5) — at proof altitude in
    the clean regime.
PROVED CONDITIONAL (the assembled OL-2): on TL (= PO) for the strata
  decomposition and S4.3-general (the digit-matching lemma,
  unbounded-term case) for the correction regime.
OPEN: S4.3-general (the compensation channel = the lucky-sum
  question); the OL-2 tight constant; D1''-strong (untouched this
  round, per the charter's priority).

## R6.5  Files (round 6)

  fsl6_check.py / fsl6.log    the battery (invocation first line)
  CHARTER_writeouts.md        the charter

---

# ROUND 7 — S4.3-GENERAL: THE COMPENSATION CHANNEL (the digit-matching
# lemma, unbounded terms)

Charter: CHARTER_s43.md.  The last piece of OL-2: the exactness
arithmetic in the CORRECTION regime.  Battery: s43_check.py /
s43.log (0 FAILS, 1.2 s).  Nothing committed.

## R7.0  The refutation record (the machine falsifying my own claims
## before they were written anywhere permanent)

Three intermediate claims died in the battery this round; the final
statements below are the corrected forms.  This is the honest process
working as designed.

1.  "The psi-maps never land a non-singleton interval" (the round-5
    E5 view, generalized from the halver): REFUTED.  The general
    (r,p) sweep finds 428 replacing-map landings and 15 mod-deletion
    landings; the tripler [a^3/a^2] maps 3^s to (3U-1)/2 = I(0,s), a
    DEEP-WIDE landing.  Round 5 had only tested r = 1, p = 2 (the
    halver: (3^s+1)/2: never lands — that part stands, with a cleaner
    proof: (3^{m+1}+1)/2 = 2 mod 3 while I(a,b) in {0,1} mod 3).
    Corrected form: Lemma 7.5 (the landing classification with the
    top-scale bound).
2.  "The obligation set is the end-anchored intervals as run VALUES"
    (the rounds-5/6 reading): REFUTED.  The tripler produces a run of
    value I(0,sigma) at EVERY position at S-depth 1 with V-fixed
    atoms; the junction-eating merge [a^3/abaa]X = a^{I(0,k)} produces
    the FULL prefix as one block at depth 1; the pair-merge with a
    stopping flank produces I(sigma,sigma+1) merged runs at depth 1.
    Corrected form: the obligations are ATOM-LEVEL (R7.3): the
    standalone a-blocks demanded in R/P positions; the embedded
    values are cheap and this cheapness is REAL STRUCTURE (three
    families), but every route from an embedded value to an ATOM pays
    the isolation/stopping walk.
3.  The part-C property took three refinements (big-piece/tile: 1066
    violations; spanning-piece either sign: 318; scale-covering: 1205
    — each refutation exposed the count and carry channels) before
    the correct induction-ready form (the OBLIGATION LEMMA: 0
    violations on all 21833 solutions).  The degenerate solutions
    with bite = the target were excluded by the natural filter
    |bite| < 3^u (the piece at scale u IS the target's bottom digit;
    a bite >= 3^u is material, not junk).

## R7.1  The formal core

Setup (rounds 5-6): D1 order preservation gives the SPAN REDUCTION —
an output run's material is one contiguous input interval [a..b]; the
glue decomposition v = I(a,b) - bites + Sum_c c*rho (the span, the
eaten flanks, the inserted copies with multiplicities).  S4.3 is the
exactness arithmetic of this equation when the demanded value is an
interval sum.

LEMMA 7.1 (3-adic valuation).  v_3(I(u,v)) = u; I(u,v)/3^u =
(3^{v-u+1}-1)/2 = 1 mod 3.  Proof: factor out 3^u; the trailing
geometric factor is a 3-adic unit.  [A: 120 checks.]

LEMMA 7.2 (count classification).  c*I(u,v) = I(U,V), c >= 1, iff
(a) SHIFT: c = 3^j, (U,V) = (u+j, v+j) (Lane C K(c)); or
(b) LENGTH-DIVISIBILITY: c = 3^{U-u}(3^{L'}-1)/(3^L-1) with
    L = v-u+1 | L' = V-U+1, U >= u.
Proof: v_3 both sides gives v_3(c) = U-u; the unit part c' =
(3^{L'}-1)/(3^L-1) is the geometric sum 1 + 3^L + ... iff L | L'.
[B: 191/191 solutions classified.]

LEMMA 7.3 (pure multi-fire impossibility).  No single-b pattern
a^i b a^j whose fires are exactly the consecutive junctions [u..v]
merges runs [u..v+1] into one run of value exactly I(u,v).  Proof:
the merged value is I(u,v+1) - c(i+j) + c|R| with c = v-u+1, so
exactness needs |R| = i+j - 3^{v+1}/c; but the fire at u forces
i <= 3^u and j <= 3^{u+1}, so i+j <= 4*3^u; and
3^{v+1}/(v-u+1) >= 3^{u+2}/(v-u+1) > 4*3^u (at v = u+1: 9/2 > 4,
increasing in v); hence |R| < 0.  So the count channel enters ONLY
inside correction equations (with span material), never alone.
[Hand; consistent with C.]

LEMMA 7.4 (THE OBLIGATION LEMMA — the round-7 core).  Any solution of
    Sum_{i<=n} s_i I(c_i,d_i) + t = I(u,v)
    (n <= 3 signed pieces after +/- cancellation, |t| < 3^u, 1 <= u < v)
satisfies: for every k > v there is a piece with
    min(d_i, k-c_i) >= m*(k) - 1,
    m*(k) = max_{sigma in [u..v]} min(sigma, k-sigma)   (worst scale).
[C: all 21833 catalog solutions, all k in (v,16].]  The three
structural cases (the machine's solutions all reduce to these):
  (a) SPANNING: a piece covers the worst scale sigma* (c <= sigma* <=
      d): then min(d, k-c) >= min(sigma*, k-sigma*) = m* exactly.
  (b) COUNT/SHIFT: the pieces are copies of a lower interval with
      c*I(u',v') = I(u,v) (Lemma 7.2): the copy count <= n <= 3 gives
      the shift j <= log_3 n <= 1: the copies' obligations reach
      m* - log_3 n.  (For general n the slack is log_3 n — see G2.)
  (c) CARRY: the digit at sigma* is carried from scales <= sigma*-1
      (three units below): the carriers' tops d <= sigma*-1 and their
      obligations min(sigma*-1, k-c) >= m*-1 in both regimes
      (sigma* <= k/2: direct; sigma* > k/2: sigma*-1 >= k-sigma*).

THE INDUCTION (S4.3's engine, closing the charter's step 1): structural
induction on the tree.  P(T): every interval-value ATOM demanded in T
sits at depth >= its obligation/C from the demand point.  At the
producing S-node, the glue equation's pieces are the demanded values
in the R/P children (strictly smaller trees); by Lemma 7.4 some piece
carries min(d, k-c) >= m*-1; by the IH that piece's supply sits at
depth >= (m*-1)/C; the demand point pays 1 + (m*-1)/C >= m*/C, which
closes EXACTLY at C = 2 (2 + m* - 1 >= m*).  Base: the powers
(S4.5: one scale per node) and the V-fixed constants (J(V): their
obligation is O(1)).

## R7.2  The channel classification

LEMMA 7.5 (psi-landing classification).  [a^r/a^p] on an isolated
run a^{3^s}: w = r*floor(3^s/p) + (3^s mod p).  The landings w=I(a,b):
(i) ASCENTS (r/p a power of 3 dividing into 3^s): the singletons
    I(s+j,s+j): J(V)-cheap;
(ii) MOD-DELETIONS (r=0): 15 in the sweep: priced by the pattern
    supply at scale ~p (S4.4, round 6);
(iii) REPLACING (r>=1, a<b): 428 in the sweep (r,p <= 40, s <= 7):
    the TRIPLER (3,2): I(0,s); (1,7,5): I(1,3); (1,6,2): I(0,1); ...
    ALL satisfy the TOP-SCALE BOUND b - s <= floor(log_3 r_max) = 3
    on the swept range; the general law b <= s + ceil(log_3(r/p))+O(1)
    (the amplification paid by the R-atom a^r at scale log_3 r:
    V-fixed: O(1); growing: its own walk).  [D: 0 violations.]
CHANNEL COST: [isolate run s; amplify] pays the head-mass walk: every
run 0..s-1 must be FULLY eaten, and a single-b pattern with fixed
flanks (i,j) zeroes at most 2 runs (3^sigma in {i, j, i+j}: at most
two powers, since 3^a + 3^b = 3^c has no solution: a<b gives
3^a(1+3^{b-a}) = 3^c with 1+3^{b-a} = 1 mod 3, contradiction; a=b
gives 2*3^a).  So the eating pattern carries an atom matching
essentially every run scale (the D(s-1;3) box or the descending
staircase): the max atom supply at the middle sigma ~ s/2:
Omega(min(s, k-s)).  This covers the bound min(b, k-a) <=
min(s+O(1), k) up to C ~ 2.

LEMMA 7.6 (the junk obstructions).  (a) The halver (3^{m+1}+1)/2 = 2
mod 3 while I(a,b) in {0,1} mod 3: never lands [E3; the round-5
mod-3 lemma again].  (b) The E-channel (I(0,t)+t+1)/2: only the
singleton landings t in {0,1}: the k-affine junk blocks every merged
landing [E2].  (c) The tripler merge [e/b][a^3/a^2]X =
a^{(3^{k+2}-2k-5)/4}: never an interval sum (k=2..8; the -2k-5 junk;
EPT-licensed for general k) [H2].

## R7.3  THE TRIPLER AND THE MERGES: the atom-level obligation set
## (the round-7 correction to rounds 5-6)

THE DISCOVERIES (all machine-confirmed, hand-derived first):
  - TRIPLER: [a^3/a^2]X = a^{I(0,0)}.b.a^{I(0,1)}.b...b.a^{I(0,k)}:
    EVERY run lands its prefix interval at S-depth 1, V-fixed atoms
    [H1].  Hand: floor(3^sigma/2) windows aa -> aaa:
    3(3^sigma-1)/2 + 1 = (3^{sigma+1}-1)/2.
  - FULL MERGE: [a^3/abaa]X = a^{I(0,k)}: the WHOLE TEXT as one
    block at depth 1, V-fixed atoms [H3a].  Hand: every junction fires
    (net 0 per fire: |R| = i+j = 3), the fires never stop.
  - PAIR-MERGE: [a^{i+j}/a^i b a^j] — the fired set is the round-6
    RECURSION THEOREM's (fire_sigma iff c_sigma >= i and R_{sigma+1}
    >= j; c_{sigma+1} = R_{sigma+1} - j*[fire_sigma]).  The width-1
    atom I(u,u+1) arises when i <= 3^u and the window
    max(3^u, 3^{u+1}-i) < j <= 3^{u+1}: j > 3^u blocks every
    sigma <= u-1 (right flank), j > 3^{u+1}-i blocks u+1 (the
    shrunken remnant c_{u+1} = 3^{u+1}-j < i), j <= 3^{u+1} allows
    fire_u; the fires above u+1 CHAIN to the top
    (c_{sigma+1} = 3^{sigma+1}-j >= i), merging the tail into one
    run; the atom is bounded by the surviving junctions b_{u-1},
    b_{u+1}.  [H3b: a.b.a^3.b.a^36.b.a^324 on D(5;3).]
    [ERRATUM, coordinator round-7 verdict, machine probes
    coord_d7_check.py §5: the round-7 sentence "the fires exactly at
    the junctions sigma with 3^{sigma+1} >= j" is FALSE in general —
    (1,27) at k=7 fires {2,4,5,6} (junction 3 blocked by the
    remnant 0 < i; 5,6 chain after 4; the k=5 witness works because
    k cuts the chain), and the old window's interior (1,20) fires
    {2,3,4}, chaining runs 2..5 into ONE run — no width-1 atom.  The
    existence claim and the stopping-flank pricing stand; the
    corrected window and fired set are as stated above, machine-
    verified in R8.0.]

THE CORRECTION: the obligation set is NOT "the end-anchored intervals
as run values".  Three families of interval values are CHEAP EMBEDDED
(the tripler prefixes, the width-1 pair-merges, the full merge).  The
obligations are ATOM-LEVEL: the standalone a-blocks demanded in R/P
positions (the pattern thresholds, the R-material).  The pricing of
every atom route:
  - the width-1 atom a^{I(u,u+1)}: the stopping flank a^j at scale
    u+1 (2*3^u < j <= 3^{u+1}) pays Omega(min(u+1, k-u-1)) — the
    interval bound minus 1;
  - the partial-prefix atom a^{I(0,m)}, m < k: the merge-stop needs
    i+j > 3^m with i <= 3^0 = 1 at the first junction, forcing the
    staircase/blocking at scale m: the blob route
    [e/bb][e/a^{3^{m+1}}]X pays Omega(k-m) (round 6) and the
    tripler+extraction route pays the isolation walk
    Omega(min(m, k-m)): the routes agree at min(m, k-m) up to the
    constant;
  - the interior atom I(u,v), width >= 2: the box R = a^{I(u,v)}
    (the R-obligation: the IH), or the span-route (the pattern atoms
    at the scales of [u..v]: the worst-scale atom pays Omega(m*)), or
    the psi-routes (Lemma 7.5: the isolation walk): all >= m*/C;
  - the FREE BOUNDARIES: the full merge I(0,k) (no stopping needed),
    the top-anchored values (v ~ k: Omega(k-v) = the same formula),
    the V-fixed constants (J(V)).
And the composition collapse: the box [R / tripler-text] applied to
the tripler text collapses to R (the whole-text match: one window):
the demand reappears at the R-atom — the embedded cheapness does not
compose into atom cheapness.

## R7.4  S4.3-GENERAL assembled

THE STATEMENT (the atom obligation law).  Let T be an lcore tree on
the input D(k;3) (all S-children at the original input).  Any
standalone a-block of value I(u,v) (u >= 1 interior, or u = 0 with
v < k) demanded in an R/P position of T sits at depth
>= min(v, k-u)/C from the demand point, for an absolute constant C
(the analysis closes at C = 2; the witnessed routes are consistent
with C ~ 2-4).

PROOF ASSEMBLY: the span reduction (D1) + the glue decomposition at
the producing node; the pieces by Lemma 7.4 (some piece carries
m*-1); the structural induction with the step 1 + (m*-1)/2 >= m*/2;
the base by S4.5 (powers) and J(V); the channels by Lemma 7.5
(psi-routes pay the isolation walk), Lemmas 7.2+7.3 (the count
channel only inside correction equations; the pure multi-fire
impossible), Lemma 7.6 (the junk never lands), the C-seam closure
(round 6: TL(iii) boundary runs: no middle-depth strata), EPT (Lane
B: the k-finiteness of the landing equations).

GRADE AND THE LOCATED GAPS (this is the honest residue):
  G1 (the main one): Lemma 7.4 is machine-exhaustive for INTERVAL
     pieces (n <= 3, |bite| < 3^u, u,v <= 6: 21833 solutions) plus
     the three hand cases; the true correction-equation pieces are
     TL-STRATA values (Sum q_i 3^{e_i} + (Ak+B) + beta), not
     intervals.  The extension is the charter's step-1 downward
     induction (the top defect scale's compensation must come from
     an anchored term AT that scale; the super-increase + the
     boundary-run structure TL(iii)), with EPT as the finiteness
     engine — analysis-grade, located, not yet at exhaustive
     altitude.
  G2: the piece-count generalization (the slack log_3 n in case (b)
     of 7.4; the induction over n with the carry algebra).
  G3: the constant C (2 by the induction's arithmetic; the witnessed
     routes give 2-4; not tightened).
With G1+G2, S4.3-general reaches the altitude of round-6's S4.1-S4.6,
and OL-2's assembly reads: PROVED on TL (unconditional, Lane B) +
S4.3-general at the catalog altitude, with G1/G2 as the precisely
located remaining write-out.  The lucky-sum question (the charter's
step 3) resolves into: the count channel is classified (7.2) and
cannot close alone (7.3); the composed corrections route through the
obligation lemma (7.4); the dyadic-demand mismatch is Lemma 7.6(a)
(the halver's mod-3 obstruction) and the second-difference route
(evenly-spaced hits) reduces to the pair-merge analysis (R7.3) —
the evenly-spaced fires produce width-1 merged runs, and their atom
extraction pays the stopping flank.

## R7.5  The battery (s43_check.py / s43.log, 0 FAILS, 1.2 s)

  A   v_3(I(u,v)) = u: 120 checks.
  B   count classification: 191 solutions = 136 shifts + 55
      length-divisibility: ALL CLASSIFIED.
  C   correction-equation catalog: 21833 solutions; the obligation
      lemma min(d, k-c) >= m*(k)-1 for some piece, all k in (v,16]:
      0 violations.
  D   psi-landing sweep (r,p <= 40, s <= 7): 5323 singletons; 15
      mod-deletions; 428 replacing landings, ALL within the top-scale
      bound b-s <= 3: 0 violations.
  E   E1 the prefix-halver identity (t=0..4); E2 (I(0,t)+t+1)/2
      lands only singletons; E3 the halver never lands (the +1 gap).
  F   the fixed-box interior merge I(1,2)=12 at S-depth 1; F2 the
      prefix-isolation depth (the threshold walk).
  G   the middle merge I(2,3)=36 at S-depth 1.
  H   H1 the tripler (every run I(0,sigma), depth 1); H2 the tripler
      b-kill merge (3^{k+2}-2k-5)/4 never lands; H3a the full merge
      a^{I(0,k)} at depth 1; H3b the pair-merge with the stopping
      flank (I(2,3), I(4,5) merged runs).

## R7.6  Honest ledger (round 7)

PROVED (hand + machine-confirmed):
  - Lemmas 7.1, 7.2, 7.3, 7.6 (the valuation, the count
    classification, the multi-fire impossibility, the junk
    obstructions).
  - Lemma 7.4 on the interval-piece catalog (machine-exhaustive,
    21833 solutions, all k in (v,16]) + the three hand cases.
  - The psi-landing classification on the swept domain (7.5) with the
    top-scale bound.
  - The three embedded-cheapness families (H1, H3a, H3b) and the
    atom-level pricing of their extraction routes (the stopping
    flank, the isolation walk, the blob walk).
  - THE ATOM OBLIGATION LAW at catalog altitude (R7.4).
ANALYSIS-GRADE (located, engine identified, not exhaustive):
  - G1: the strata-piece extension of Lemma 7.4 (the downward
    induction on the top defect scale; EPT the engine).
  - G2: the piece-count generalization (slack log_3 n).
  - G3: the constant C.
REFUTED-BY-MACHINE-BEFORE-WRITTEN (R7.0): the all-intervals
  value-level obligation; the psi-maps-never-land claim; the
  big-piece/tile and spanning-piece forms of the C property.
OPEN (unchanged): D1''-strong; the OL-2 tight constant.

## R7.7  Files (round 7)

  s43_check.py / s43.log    the battery (invocation first line)
  CHARTER_s43.md            the charter

---

# ROUND 8 — G1+G2: THE STRATA-PIECE CLOSURE (S4.3-general to full
# altitude)

Charter: CHARTER_g1g2.md.  Battery: g1g2_check.py / g1g2.log (0
FAILS, 2.8 s).  Nothing committed.

## R8.0  The H3b erratum (the coordinator's round-7 correction)

The round-7 sentence "the fires exactly at the junctions sigma with
3^{sigma+1} >= j" is FALSE in general, as the coordinator's probes
showed.  The corrected statement (now in R7.3 and in s43_check.py's
H3b, both re-run clean):

  The pair-merge fired set IS the round-6 RECURSION THEOREM's:
  fire_sigma iff c_sigma >= i and R_{sigma+1} >= j, with
  c_{sigma+1} = R_{sigma+1} - j*[fire_sigma].  The width-1 atom
  I(u,u+1) arises exactly when i <= 3^u and the window
      max(3^u, 3^{u+1}-i) < j <= 3^{u+1}:
  j > 3^u blocks every sigma <= u-1 (the right flank does not fit
  run u); j > 3^{u+1}-i blocks u+1 (the shrunken remnant
  c_{u+1} = 3^{u+1}-j < i); j <= 3^{u+1} allows fire_u; and the
  fires above u+1 CHAIN to the top (c_{sigma+1} = 3^{sigma+1}-j >= i),
  merging the tail [u+2..k] into one run.  The atom is bounded by the
  surviving junctions b_{u-1}, b_{u+1}.

Machine (battery part 0): the evaluator confirms the atom runs for
u=1..3 at j = 3^{u+1}; the negative witnesses confirmed ((1,27) at
k=7 fires {2,4,5,6}; (1,20) at k=5 fires {2,3,4}: runs 2..5 chain
into ONE run); and the window sweep (i <= 3, j <= 3^{u+1}, u=1..3:
351 cases) is an EXACT MATCH to the fired-set condition
fire_u and not fire_{u-1} and not fire_{u+1}.  The existence claim
and the stopping-flank pricing Omega(min(u+1, k-u-1)) STAND.

## R8.1  G1 — the digit-defect lemma, line by line (the strata-piece
## extension of the obligation lemma)

Setting.  The correction equation at the producing S-node (rounds
5-7: the span reduction D1 + the glue decomposition):
    Sum_p s_p v_p + t = I(u,v),
the pieces the TL-strata values — TL now UNCONDITIONAL at full
altitude (Lane B round 7, coordinator-verified):
    v_p = Sum_{i <= M_p} q_{p,i} 3^{e_{p,i}} + (A_p k + B_p) + beta_p,
M_p <= 8#S + O_V(1) terms, the q_{p,i} rationals with V-fixed
denominators, |beta_p| = O(k), the e_{p,i} anchored exponents
(families {k-c, k+1-c} U {j-c'} U {c''} U products).

8.1  THE COLLECTED FORM.  Sum_d mu_d 3^d = 0, where mu_d collects,
at every scale d, the strata coefficients (Sum_{e_{p,i}=d} s_p
q_{p,i}), the target's repunit digits (-[u <= d <= v]), and the raw
ternary digits of the COLLECTED LOW-SCALE MATERIAL
    gamma = Sum_p s_p (A_p k + B_p + beta_p) + t
(the affine, junk, and bite ALL TOGETHER: |gamma| = O(k); its digit
mass is O(log k), absorbed into M; gamma is NOT a separate equation
term — it names the value of the low-scale material already inside
mu).  The identity is exact — this is the machine's convention
(g1g2_check.py rawmu: the bite's digits enter mu; there is no
separate gamma term).  [Erratum, the coordinator's round-8
verification: the first draft of this section wrote
"Sum_d mu_d 3^d + gamma = 0 ... gamma = ... + t" while ALSO
putting the bite's digits in mu_d — the bite double-counted as
written; fixed here to match the machine, which is the convention
G2's M = 20 and 8.3's EPT boundary both use.]

8.2  THE COEFFICIENT DISCIPLINE (TL).  The mu_d are rationals with
a common V-fixed denominator D; mu_d != 0 implies |mu_d| >= 1/D.
The raw mass M = Sum_d |mu_d| <= Q N + (v-u+1) + O(log k) with
N = Sum_p M_p <= 8#S + O_V(1) and Q the max |q|.

8.3  THE DIGIT-DEFECT LEMMA and THE GAP BOUND.  Let d* be the top
defect scale (the largest d with mu_d != 0).  Then
    |mu_{d*}| 3^{d*} <= Sum_{d < d*} |mu_d| 3^d
(the charter's core inequality, CLEANLY: the identity
mu_{d*} 3^{d*} = -Sum_{d<d*} mu_d 3^d holds with everything —
strata, target, bite, affine, junk — collected in mu; the
low-scale material's VALUE |gamma| = O(k) enters only through its
digits, which sit below the scale log_3(2|gamma|)).  GAP BOUND: if
no stratum sits at any scale in [d*-g, d*], then the lower mass
Sum_{d<d*} |mu_d| 3^d <= M 3^{d*-g} + |gamma| (the second term the
collected low-scale material's value), so (1/D) 3^{d*} <=
M 3^{d*-g} + |gamma|; for d* >= log_3(2D|gamma|) — above the
affine-absorbable range, the EPT range boundary, since
|gamma| = O(k) — this gives
    3^{g-1} <= D M,  i.e.  g <= 1 + log_3 M + O_V(1).
THE TOP DEFECT'S COMPENSATION SITS AT THE TOP DEFECT SCALE MINUS
1 - log_3(DM): the super-increase forces the top of the defect
tower to be matched by an anchored exponent AT that scale (within
the log-of-mass gap), and the induction continues DOWNWARD on d*.

8.4  THE STRATA OBLIGATION LEMMA (the downward induction, at the
worst scale).  Let sigma* in [u..v] achieve m* = min(sigma*, k-sigma*)
and consider how its digit 1 is supplied:
  (a) SPANNING: a piece has a stratum at sigma* (or within the gap
      bound below it): its exponent e in
      [sigma*-1-log_3(DM), sigma*], and its supply obligation
      (8.5) min(e_top, k-e_bottom) >= m* - 1 - log_3(DM);
  (b) CARRY: the digit is carried up from the origin scale
      sigma*-g: the chain of length g requires >= 3^g raw units
      concentrated at the origin (each carry step divides the mass
      by 3 while the intermediate demands subtract 1 each):
      3^g <= the origin mass <= M: the origin piece's obligation
      >= m* - floor(log_3(DM));
  (c) COUNT: the multiplicities — c (lower strata) = the higher
      digits — are classified by 7.2 (the shift c = 3^j: the copies
      at sigma*-j; the length-divisibility: the geometric sums):
      the copies' obligations reach m* - floor(log_3 c) >=
      m* - floor(log_3(DM)).
CONCLUSION: some piece has an anchored exponent whose supply
obligation is >= m* - 1 - floor(log_3(DM)).  [Machine A: the strata
catalog — pieces q*3^e (q in {1,2,4}), I(a,b), and the geometric
sums G(r,T,m); 3 pieces; |bite| <= 18 (the collected affine+junk);
targets 3 <= u < v <= 6: 8937 solutions; the top-defect inequality
holds identically; the deficit bound m*(k) - max Omega(p) <= 1 +
floor(log_3 M): 0 violations; max deficit 1.]

8.5  THE SUPPLY SIDE (the anchored families' pricing = S4.5,
round 6).  The anchored exponent e: {k-c}: the top descent, one
scale per node: Omega = c = k-e; {j-c'}: the construction's own
scale: Omega = min(j-c', k-j+c'); {c''}: V-fixed: J(V), O(1);
the products: the scale-sum walk.  In every family the supply
obligation of a stratum at scale e is min(e, k-e) up to a V-fixed
constant.

8.6  THE INV3 COORDINATION (Lane B round 8, section 3).  Their
measure form: the measures of profiles are anchored exponentials +
affine + residue-periodic, and a periodic fired set enters as a
parity split of geometric sums collapsing to SERIES IN 3^T.  That
is exactly the F3 family here: G(r,T,m) = Sum_{i<r} 3^{m-iT}; and
these coefficients land exactly in the count channel's
classification (7.2: the geometric sums (3^{L'}-1)/(3^L-1)): the
strata obligation lemma applies verbatim to the INV3 measure
pieces.  [The battery's F3 pieces: 0 violations.]

8.7  THE EPT USE (the affine range).  The k-affine parts (Ak+B):
the landing equations are eventually periodic in k (EPT, Lane B
round 6); the affine material sits at the scales <= log_3 k + O(1)
[Machine A2: the top ternary scale of |Ak+B| <= 3 for A <= 2,
k <= 16]: inert for the targets with u >= log_3(2 C_V k)+1 — the
same obstruction as E2/H2 (the k-affine junk never lands), and the
final law's -O(log k) slack absorbs the EPT range boundary.

## R8.2  G2 — the mass form (the piece-count generalization, with
## the coordinator's data)

THE COORDINATOR'S QUESTION: is m*-1 valid for all n (their n=4
probe: 210075 four-piece solutions, ZERO violations at m*-1), or
does the slack grow (my round-7 expectation: log_3 n)?

THE ANSWER: the slack is governed by the RAW DIGIT MASS M =
Sum_d |mu_d| of the collected equation, NOT by the piece count
alone — the bite's digit mass joins the pieces' mass:

  THE MASS FORM.  max_p Omega(p) >= m*(k) - 1 - floor(log_3 M).
  PROOF: the deficit is the carry-chain length g into the worst
  scale; a chain of length g requires >= 3^g raw units
  concentrated at the origin scale (each carry step divides the
  mass by 3, the intermediate demands subtract 1); so 3^g <= M,
  with the +1 absorbing the value-level rounding in the upper
  regime (3^{g-1} <= 2M).

  THE TRANSITION: the smallest n violating m*-1 is n = 7:
      7 I(0,1) + 8 = I(2,3),  deficit 2, M = 20:
  the raw mass 9 at scale 0 and 9 at scale 1 (the seven copies'
  digits + the bite 8 = 22_3's two units): the DOUBLE 2-SCALE
  CARRY (9 at scale 0 -> 1 at scale 2; 9 at scale 1 -> 1 at scale
  3: the target 1100_3).  At n = 6 the maximum concentration is
  6 + 2 = 8 < 9 = 3^2: IMPOSSIBLE — so n <= 6 (with |bite| < 9)
  never violates.  [Machine B(i): the exhaustive catalog (a,b<=3,
  u<v<=3, |t|<3^u, multiplicity <= 7): 52959 solutions; the m*-1
  violations by n: {(7,1)} — exactly this exhibit; the mass form:
  0 violations.]

  THE COORDINATOR'S n=4 DATUM EXPLAINED: their 210075 ordered
  4-tuples = my 7871 multisets x the ordering factor 4! = 24 (and
  the +-canonicalization), 0 violations [machine B(iii)]: at
  n <= 4 with |t| <= 2 the concentrated mass <= 4 + 2 = 6 < 9:
  the deficit <= 1.  The transition is the MASS 9 = 3^2, reached
  at n = 7 (7 pieces + the bite's 2 units = 9 concentrated).

  THE COUNT-CHANNEL ABSORPTION: my round-7 log_3 n expectation is
  subsumed: the shift c = 3^j needs the multiplicity 3^j <= n <= M
  (the count channel's copies at sigma*-j: j <= log_3 M) — the
  mass form's slack covers both channels.  The tight margin: on
  every observed solution the deficit <= floor(log_3 M) exactly
  [B(iv): max(deficit - floor(log_3 M)) = 0 over 4299 random
  solutions; the exhibits: 3 I(0,1) = I(1,2): deficit 1 =
  floor(log_3 6); 7 I(0,1)+8: deficit 2 = floor(log_3 20);
  9 I(1,3) = I(3,5): deficit 2 <= floor(log_3 28) = 3].

## R8.3  G3 — the constant C

The structural induction's step: depth >= 1 + (obligation(piece) -
1)/2 at each assembly; 1 + (m*-1)/2 >= m*/2 iff 2 + m* - 1 >= m*:
the induction closes EXACTLY at C = 2 [machine C: verified for all
m* in 2..39].  The witnessed routes (the round-7 channels: the
isolation walk, the stopping flank, the blob walk, the box atoms)
are consistent with C in [2,4].  The law is stated with C = 2 and
the additive slack 1 + floor(log_3 M); whether any family of trees
realizes a constant strictly above 2 (depth < m*/2 asymptotically
while beating m*/3) is the tight-constant question — open, one
line, not needed for the Omega.

## R8.4  S4.3-GENERAL AT FULL ALTITUDE (the final law)

THE ATOM OBLIGATION LAW (full altitude).  Let T be an lcore tree on
D(k;3) (all S-children evaluated at the original input).  Any
standalone a-block of value I(u,v) (u >= 1 interior, or u = 0 with
v < k) demanded in an R/P position of T sits at depth
    >= ( min(v, k-u) - 1 - floor(log_3 M) ) / 2
from the demand point, where M is the raw digit mass of the
correction equation at the producing node,
M <= Q (8#S + O_V(1)) + (v-u+1) + O(log k).

For #S = O(k) trees (the box-chain regime): depth >= min(v, k-u)/2
- O(log k): Omega(min(v, k-u)) SURVIVES.

PROOF (the assembly): the span reduction (D1) + the glue
decomposition at the producing node; the pieces by 8.4 (the strata
obligation lemma: some piece's anchored exponent carries
m* - 1 - log_3(DM)); the structural induction with the step
1 + (m*-1)/2 (C = 2); the base by S4.5 (the powers: one scale per
node) and J(V) (the V-fixed constants); the channels by 7.5 (the
psi-routes pay the isolation walk), 7.2 + 7.3 (the count channel
only inside the correction equations; the pure multi-fire
impossible), 7.6 + 8.7 (the junk and the k-affine never land: the
mod-3 and the k-affine obstructions, EPT-licensed), the C-seam
closure (round 6: TL(iii): no middle-depth strata), the corrected
pair-merge pricing (R8.0: the stopping flank at scale u+1), and
the atom-level extraction (the isolation walk: the fixed-flank
zeroing zeroes at most 2 runs, so the head-mass eating pattern
carries an atom at essentially every run scale).  ∎

THE OL-2 ASSEMBLY NOW READS: PROVED on TL (unconditional) +
S4.3-general AT FULL ALTITUDE.  The remaining honest caveats, all
additive-slack-level: (i) the -O(log k) term (the mass form + the
EPT range); (ii) the tight constant (C = 2 by the induction's
arithmetic; the witnesses in [2,4]); (iii) the battery's swept
domains (the strata families F1-F3 with 3 pieces, |bite| <= 18,
u,v <= 6: 8937 solutions; the interval catalogs: round 7's 21833 +
this round's 52959/7871/4299) — the extension beyond the swept
families is the EPT-licensed finiteness (for fixed V the anchored
exponent families are finite and the case structure is eventually
periodic in k and j).

## R8.5  The battery (g1g2_check.py / g1g2.log, 0 FAILS, 2.8 s)

  0   the H3b erratum: the corrected window and fired set
      (evaluator u=1..3; the negative witnesses; the 351-case window
      sweep: EXACT MATCH).
  A   the strata catalog (8937 solutions): the top-defect
      inequality (identity); the deficit bound <= 1 + floor(log_3 M):
      0 violations, max deficit 1.
  A2  the affine range: the k-affine material at the scales
      <= log_3 k + O(1) (the EPT range).
  B(i)   the exhaustive multiplicity-<=7 interval catalog (52959
      solutions): the m*-1 violations start EXACTLY at n=7 (the
      exhibit); the mass form 0 violations.
  B(ii)  the directed exhibits (the count-shift family and the
      carry exhibits: the deficit = the concentrated mass's log).
  B(iii) the coordinator's n<=4 box reproduced (7871 multisets =
      their 210075 ordered tuples / 24): 0 violations.
  B(iv)  the random n in [2,12] sweep (4299 solutions): the mass
      form 0 violations; the tight margin max(deficit -
      floor(log_3 M)) = 0.
  C   the closing arithmetic at C=2 (m* = 2..39).

## R8.6  Honest ledger (round 8)

PROVED (hand + machine-confirmed):
  - 8.1-8.3: the collected form, the coefficient discipline, the
    digit-defect lemma with the gap bound (the charter's step-1
    line-by-line).
  - 8.4: the strata obligation lemma (the downward induction; the
    three cases with the anchored exponents as the endpoints) at
    catalog altitude + the carry-chain proof.
  - 8.5-8.7: the supply side, the INV3 coordination (the series in
    3^T land in 7.2's classification), the EPT affine range.
  - G2: the MASS FORM with the transition at n = 7 and the
    coordinator's n=4 datum explained (the mass 9 = 3^2 threshold).
  - G3: the C=2 closing arithmetic.
  - R8.0: the corrected pair-merge fired set (the recursion
    theorem's own domain).
  - THE ATOM OBLIGATION LAW AT FULL ALTITUDE (R8.4).
MACHINE-CONFIRMED ON THE SWEPT DOMAINS (EPT-licensed extension):
  the strata families F1-F3 (3 pieces), the multiplicities <= 7
  exhaustive / 12 random, the bites <= 18.
OPEN: the tight constant C; the necessity of the -O(log k) slack;
D1''-strong (untouched, per the standing priority).

## R8.7  Files (round 8)

  g1g2_check.py / g1g2.log    the battery (invocation first line)
  CHARTER_g1g2.md             the charter
  s43_check.py / s43.log      re-run after the R8.0 erratum fix (0
                              FAILS, new md5 4e1873a6ff81dd1b23c2...)

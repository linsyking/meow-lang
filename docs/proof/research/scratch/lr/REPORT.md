# L+R: the mixed left/right substitution calculus — investigation report

Study directory: docs/proof/research/scratch/lr/.  System under study: the
paper's expression calculus (Def. def:exp, strict eager denotation Def.
def:den, NO recursion) with a second node kind — the R-pass [R/P]^R E of
Def. def:r2l (one right-to-left sweep, rightmost match first, all
occurrences, never rescans inserted text) — mixed freely with the L-pass.

Round 1 (§1–4): setup + seed facts + smallest witness.  Round 2 (§5):
normal forms and commutation.  Rounds 3–4 planned (§7).

## 1. Infrastructure

* lrcore.py — the evaluator.  AST: ('K',w) ('V',i) ('C',e1,e2) ('S',R,P,E)
  (L-pass) ('SR',R,P,E) (R-pass); strict eager denotation, PatternEmpty on
  an empty pattern value, both directions.  subst is the paper's greedy
  leftmost loop (as in rec/lazy_pass/core.py); substR is a fresh ITERATIVE
  rightmost-first collector, cross-checked against rev-duality (C1) — two
  independent derivations of the R-pass.  Also: allR (L -> all-R), conj
  (the rev-conjugate of thm:conjugation, extended to mixed expressions),
  pp, enumeration and tally utilities.  Reuses toolkit.py of
  rec/lazy_pass (the cross-verified §2 builder library) via sys.path.
* verify_r1.py — round-1 battery (C1–C9), all green (~40 s).
* verify_r2.py — round-2 battery (D1–D4), all green (~2 min).
* pilot_collapse.py (+pilot_mixed_only.txt) — constant-level collapse probe
  (~90 s).

## 2. Seed facts re-verified (verify_r1.py, all 0 failures)

| fact | check | domain | evals |
|---|---|---|---|
| rev-duality (impl. cross-check) substR(A,B,C)=rev(subst(revA,revB,revC)) | C1 | abs<=3,abs(B)<=3,abs(C)<=6, Σ={a,b} | 26,670 |
| prop:r2l-agree (unbordered B => equal) | C2 | same | 26,670 |
| disagreement => B bordered (contrapositive) | C2b | same | 992 disagreements, all bordered |
| every bordered B admits a disagreement | C3 | abs(B)<=4, abs(A)<=2, abs(C)<=7 | 16/16 |
| thm:r2l-toolkit: enc,dec,tail,head,cat,eq,if (toolkit ASTs, L vs allR) | C5 | inputs <=5 (eq/if scrutinees <=3) | 1,888 |
| thm:conjugation EXTENDED to mixed exprs; conj∘conj = id | C6 | 400 random mixed exprs x 6 inputs | 2,800 |
| prop:last: last / init / rotate-right, THIS evaluator | C7 | all 1023 strings <=9, Σ={a,b} | 3,069 |
| R-pass length bound abs([A/B]^R C) <= abs(C)*(1+abs(A)) | C8 | as C1 | 26,670 |
| unary corner: [A/B]^R = [A/B] always (Σ={a}) | inline | abs(A),abs(B)<=4, abs(C)<=8 | 180 |

## 3. Round-1 results

### 3.1 The smallest scan-direction witness (C4)

Proposition. [A/B]C != [A/B]^R C requires |B| >= 2 and |C| >= |B|+1.  The
unique minimal shape, up to renaming, is B = c^2, C = c^3, |A| = 1: for any
d != c, [d/c^2]c^3 = dc  vs  [d/c^2]^R c^3 = cd.  For (B,C) = (c^2,c^3)
the two values are A.c and c.A, so they disagree IFF A is not a power of
c (C4b).  Binary canonical: [b/aa]"aaa" = "ba" vs [b/aa]^R"aaa" = "ab".
Evidence: 116 disagreements (binary, |A|<=2,|B|<=3,|C|<=5), 912 (ternary),
none smaller; ternary minimal set exactly {(d,c^2,c^3) : d != c}.

### 3.2 prop:r2l-agree sharpened into a biconditional (C9)

Proposition. For B != eps over |Σ| >= 2:
    [A/B]^R = [A/B] for all A, C   <=>   B is unbordered.
(<=) is the paper's prop:r2l-agree.  (=>) contrapositive: B bordered, p =
smallest period (= |B| - longest border), C = B . B[|B|-p:] (length
|B|+p <= 2|B|-1).  Occurrences of B in C are exactly {0,p} (a q with 0<q<p
would be a smaller period; q > p does not fit).  They overlap, so the
L-scan takes 0 and the R-scan takes p:
    [a/B] C = a . B[|B|-p:]        [a/B]^R C = B[:p] . a
for ANY single character a; the two differ whenever a != B[0].  A
single-character replacement suffices; C is shorter than 2|B|.  Verified:
all 80 bordered B with |B| <= 6 over {a,b}, both choices of a (320 value
checks + 80 disagreement checks).  Over the UNARY alphabet no disagreement
exists at all (A^m c^r = c^r A^m) — the biconditional needs |Σ| >= 2.

### 3.3 The Collapse Criterion (theory)

Write rho for the 3-ary pass function
    rho(A,B,C) = [A/B]^R C    (undefined iff B = eps),
i.e. the denotation of the one-node mixed expression [X1/X2]^R X3.

THEOREM.  The following are equivalent:
  1. L+R = L;   2. R <= L (every R-expression denotes an L-function);
  3. rho ∈ L.

Proof.  (3=>1, 3=>2): let E_rho in Exp_3 with [[E_rho]] = rho.  Translate
every mixed expression F bottom-up: t fixes K, V, commutes with
concatenation and L-nodes, and
    t([R/P]^R E) = E_rho[ t(R)/X1, t(P)/X2, t(E)/X3 ].
By lem:beta and induction on F, [[t(F)]] = [[F]] as PARTIAL functions.
DEFINEDNESS: the beta-application needs lem:beta's partial-function
clause, whose hypothesis is that every X_i OCCURS in the expression being
substituted into.  Any E_rho computing rho automatically satisfies it:
rho depends on each argument ([A/a]a = A; [A/b]a = a; [A/a]aa = AA), so an
E_rho omitting some X_i would denote a function independent of that
argument.  (Alternatively, the paper's own patch at cor:closure
(main.tex:730) applies verbatim: WLOG force an unused variable with the
identity pass [X_i sigma / X_i sigma] — direction-robust, since
[W/W]^R S = S by rev-duality and the L-theorem.)  On defined values the
equation is exactly the R-node's denotation.  t(F) is an L-expression, so
L+R <= L (and R <= L); L <= L+R is trivial.  (1=>3): [X1/X2]^R X3 is a
mixed expression denoting rho.  QED.

Consequences:
* rev ∈ L => L+R = L (rho = rev o sigma o rev, sigma = [[ [X1/X2]X3 ]] ∈
  L, closure under composition).  The criterion is strictly WEAKER than
  hinge 2: L+R could collapse with rev ∉ L.
* L+R ⊋ L => rev ∉ L — a strictness witness resolves hinge 2 NEGATIVELY.
* rev ∈ L+R => (rev ∈ L or L+R ⊋ L); and rev ∈ L+R with L+R = L gives
  rev ∈ L: the R3 witness hunt is decisive no matter what R4 proves.
* With the paper's new cor:incl-symmetry (R ⊑ L iff L ⊑ R, via the mirror
  m(f) = rev o f o rev carrying the L-class onto the R-class): the
  criterion composes with the mirror into
      L+R = L  <=>  L+R = R  <=>  rho ∈ L  <=>  sigma ∈ R
  (m(sigma) = rho is rev-duality; D4 re-verifies both ingredients on the
  finite domain).  The mixed calculus collapses to L iff it collapses to
  R — ONE question, not two.

So the study funnels into: Q-rho (is rho ∈ L?) and Q-rev (is rev ∈ L+R?).

### 3.4 Structural facts (recorded; R2 verified the transfers)

* conj is an involution on mixed expressions; the conjugation identity
  extends to L+R (C6): the function class is closed under f -> rev o f o
  rev.
* Growth: the R-pass has the same disjoint-match length bound (C8), so
  def:deg / lem:length / thm:fp transfer verbatim: L+R functions are
  polynomial-time, degree bounded by the expression; X -> X^|X| is
  L+R-reachable, X -> X^{2^|X|} is not.
* Over the unary alphabet L = R = L+R (rev = id).

### 3.5 Round-1 pilot (constant level)

84 pass types (patterns <= 2 over {a,b}, replacements <= 2), 63 inputs of
length <= 5, pipelines depth <= 3: pure-L 21,232 tables = pure-R 21,232;
mixed 36,798; 4,242 need both directions; 0 tables equal rev; pure-L at
depth 4 (452,214 tables) still misses 15,265 mixed tables.  At the
CONSTANT level the mixed fragment is robustly beyond pure L — already a
theorem via thm:subsequential — but this does not lift to the full
calculi, where variable patterns (eq, if, rep_n, prop:last) live.

## 4. Round 1 next-round plan (superseded by §6)

## 5. ROUND 2: normal forms and commutation (verify_r2.py, all green)

### 5.1 Disjoint Commutation Lemma (new, D1/D1b)

LEMMA.  Passes P1 = [A/B]^{d1} and P2 = [C/D]^{d2} (B, D != eps, d1, d2
arbitrary directions) COMMUTE, P1 o P2 = P2 o P1, whenever
    alph(B) ∩ alph(D) = empty,
    A != eps with alph(A) ∩ alph(D) = empty,
    C != eps with alph(C) ∩ alph(B) = empty.

Proof sketch (full pen-and-paper proof ready for the paper):
(i) alph(B) ∩ alph(D) = empty implies no occurrence of B intersects any
occurrence of D (an intersection point is a shared character).
(ii) Applying P1: selected B-matches -> A.  Every D-occurrence of T
survives (none intersects a B-occurrence), and no new one appears: an
occurrence touching an inserted copy of A contains a character of A
(A != eps makes any crossing occurrence contain some A[·]), excluded by
disjointness.  Deletion (A = eps) would merge arbitrary neighbours — the
reason for the A != eps clause (counterexample: [eps/c] vs [d/ab] on
"acb" gives "ab" vs "d").
(iii) The correspondence preserves the order AND the overlap structure of
D-occurrences: between the starts of two overlapping D-occurrences no
B-match can start (its first character would be a D-character), so their
distance is unchanged; between two non-overlapping ones every B-match
needs room outside both occurrences, so the shrinkage is at most
(distance - |D|) - #matches, keeping the new distance > |D|.
(iv) Hence the greedy selection in either direction picks corresponding
occurrences in T and in P1(T), and both compositions equal the
SIMULTANEOUS replacement of T's B-greedy-selected matches by A and
D-greedy-selected matches by C — two position-disjoint sets.
Verified: all 1,152 quadruples (A,B,C,D) with |A|,|B|,|C|,|D| <= 2 over
{a,b,c} satisfying the conditions, x 4 direction pairs x 364 inputs =
1,677,312 checks, 0 failures.  NECESSITY of each clause (D1b):
alph(B)∩alph(D): [a/b] vs [a/bb], LL, "bb" -> "a" vs "aa";  A: [eps/a] vs
[b/bb], LL, "bab" -> "bb" vs "b";  C: [a/b] vs [b/c], LL, "c" -> "a" vs
"b".  By iteration: any family of pairwise-disjoint non-deleting rules
runs in any direction order.

This generalizes the paper's independence mechanisms (Independent
Substitution; thm:pos-hinge(ii) marking) to the mixed calculus — but it
only ever pulls APART alphabet-disjoint passes; the interesting cases
(both patterns over the same alphabet, bordered) are not covered.

### 5.2 The alternation census: one-alternation normal form FAILS at the
     constant level (D2/D2b/D2bb/D2bbb)

Census (all 84 constant pass types, 63 inputs <= 5, words of depth <= 3
in run order, minimal alternation count per table):
  * 36,798 tables total; 4,242 need >= 1 alternation; 156 need
    >= 2 alternations (no word L^aR^b or R^bL^a of depth <= 3 reaches
    them).  Example: [aa/bb], [bb/aa]^R, [aa/bb] (run order L,R,L).
  * Restricted universe (|A| <= 1, 36 pass types): 2,499 tables; exactly
    FOUR need >= 2 alternations — the four sibling pipelines
        [a/bb]   [b/aa]^R   [a/bb]      (L R L)
        [a/bb]^R [b/aa]    [a/bb]^R     (R L R)
    and the two renamings a<->b.
  * All four SURVIVE every two-block search attempted:
      - exhaustive two-block with ALL block words of depth <= 2, both
        orders (22,112 tables) — 0 hits;
      - randomized two-block, total budget <= 6, restricted universe
        (40,000 x 2 orders) — 0 hits;
      - randomized two-block, total budget <= 6, FULL universe (100,000 x
        2 orders in the battery; 400,000 x 2 in a one-off run) — 0 hits;
      - exhaustive two-block over the two halving passes {[a/bb],[b/aa]},
        blocks up to depth 4 — no form exists at all.
  * The star survivor W = [a/bb] . [b/aa]^R . [a/bb] fixes every
    alternating string: W((ab)^k) = (ab)^k; on b^n it computes a halving
    cascade (b^n -> '', 'b', 'a', 'ab', 'b', 'a', 'ab', 'aa', ...).

Structural reading (heuristic, not a proof): an L-halving [d/cc] places
the odd residue at the RIGHT end of the produced block, an R-halving
[d/cc]^R at the LEFT end; W's residue ends alternate right-left-right,
while any two-block form L^j o R^k applies all R-passes first, fixing the
residue-end pattern to left^k right^j.  A PROOF that W has no one-block
form at any depth needs an invariant separating RLR- from two-block
cascades — R4 material.

Conclusions for the paper:
  * The one-alternation normal form ("every mixed pipeline = L-block o
    R-block") is REFUTED at the constant level within the tested budgets
    (exhaustive: depth-3 mixed vs two-block depth <= 4, restricted
    universe; randomized to total depth 6, full universe; plus the
    halving-pass exhaustion).  Standing caveat: finite domain (63 inputs),
    and absence of a bounded two-block form is not a separation at
    unbounded depth.
  * The commutation lemmas (5.1 + prop:r2l-agree) do not normalize
    bordered mixed pipelines: genuinely interleaved behavior exists.
    Interleaving needs bordered patterns: mixed pipelines with only
    unbordered patterns are pure-L functions verbatim (D2c: 376 = 376
    tables at depth <= 2 — each R-pass equals its L-version).

### 5.3 thm:core transfers to L+R (D3)

For random mixed E1, E2 (2-ary, both node kinds, concatenations), the
L-expression cat of thm:cat substituted, cat[E1/X1, E2/X2], computes
E1 * E2 with matching definedness: 750/750 checks.  Together with the
pen-and-paper induction (cat is an L-expression available in the mixed
calculus; lem:beta is direction-agnostic; the WLOG forcing patch of
cor:closure applies since identity passes are direction-robust),
concatenation is eliminable in L+R: every mixed expression is a mixed
pipeline over an atomic scrutinee.

### 5.4 cor:incl-symmetry ingredients (D4)

m(sigma) = rho (rev-duality, 13,230 checks on the finite domain) and the
conj involution on mixed expressions (150 random): the mirror m is an
involution carrying the L-class onto the R-class, so R ⊑ L iff L ⊑ R and
L+R = L iff L+R = R iff rho ∈ L iff sigma ∈ R — one question.

## 6. Updated round plan

* R3 — the witness hunts (next).  (a) Q-rev: CEGIS/genetic/SAT over mixed
  pipelines seeded with the §2 toolkit (enc/enc^2, fresh anchors, prop:last
  junction tests, rep_n); any candidate re-verified on strictly larger
  domains and multiple (b,x) choices before being believed.  (b) Q-rho:
  search for rho in L constructively (variable patterns essential:
  constant-pattern L-pipelines are left-subsequential (thm:subsequential)
  and rho is not).  (c) same for sigma ∈ R (the mirror question).
* R4 — collapse vs strictness + the landscape row for L+R:
    variant     | L ⊑ V+R? | V+R ⊑ L? | toolkit | growth
    L+R (mixed) | trivially yes (both) | ONE question: rho ∈ L
                                          (⟺ sigma ∈ R, ⟺ L+R = R) |
    full (both toolkits) | polynomial (same degree calculus)
  with the rev-consequences of §3.3 and the alternation results of §5.2.
  Also: an invariant separating the survivor W from all two-block forms
  (would promote the empirical refutation of the one-alternation normal
  form to a theorem); place the 4 sibling pipelines in the paper as the
  concrete interleaving witnesses.

## 7. Re-running

    cd docs/proof/research/scratch/lr
    python3 verify_r1.py        # ~40 s, C1–C9, exits 0
    python3 verify_r2.py        # ~2 min, D1–D4, exits 0
    python3 pilot_collapse.py   # ~90 s incl. depth-4 escalation
    python3 search_r3.py        # ~7 min, S1+S2+S3 (§8)
    python3 search_r3.py ext    # ~2.5 min, S1-ext1 + S1-ext2 (§8)
    python3 verify_r4.py        # ~5 s, E0-E4 (§10); full log in r4.log

## 8. ROUND 3: the witness hunts (search_r3.py — all searches negative, machinery sanity-planted)

**Method.** All three hunts ran as table-based BFS/randomized/genetic search over
*template pipelines*: passes [R/P]^d whose pattern and replacement sources are
built from short constants and the INPUT VARIABLES (raw values, not the running
text): constants a,b,aa,ab,ba,bb; variables X_i; short concatenations (a·C, C·a,
b·C, C·b, X_i·X_j); and (S1-ext2 only) computed patterns — one-pass transforms
[ε/aa]C, [a/aa]C, [ε/ab]C, [ε/ba]C, [ε/a]C, [ε/b]C, [b/a]C, [a/b]C, [b/bb]C,
[a/ab]C of X_1 or X_2. Tables record per-point values; None (empty pattern
value) propagates as strict undefinedness. Dedup by table. Targets: the R-pass
itself on the domain.

**S1 — the minimal hard case f2(A,C) = [A/aa]^R C in L** (aa = smallest
bordered pattern; unbordered patterns collapse by the sharpened prop:r2l-agree,
so this is the essence of Q-ρ). Domain A ∈ {ε,b}, |C| ≤ 3 (30 points).
- Base: 12 pattern × 13 replacement sources = 156 L-passes, BFS depth ≤ 3:
  **592,447 distinct tables, no hit** (31s). Randomized 300K pipelines
  depth ≤ 5: no hit. (Pass count corrected: R_srcs = 1 empty + 6 constants +
  2 variables + 4 concatenations = 13, as the script prints; the earlier
  "180" in this report double-counted two concatenation sources.)
- ext1 (constant-anchored variable patterns a·C, C·a, b·C, C·b added): 240
  passes, depth 3: **1,574,748 tables, no hit** (103s). Randomized 200K
  depth ≤ 5: no hit.
- ext2 (computed pattern sources added): 540 passes, depth 2: 74,525 tables,
  no hit; randomized 200K depth ≤ 5: no hit.
- Sanity plants: the search finds [A/aa]C at depth 1
  (('V',1),(('v',0),('c','aa'),'L')) and [b/a]∘[A/aa] at depth 2 — machinery
  detects real witnesses at the right depths within the space, so the
  negatives are meaningful, not vacuous.

**S2 — full ρ(A,B,C) = [A/B]^R C in L** (3-ary). Domain A ∈ {ε,b},
B ∈ {a,aa,ab}, |C| ≤ 3 (90 points). 15 pattern × 12 replacement sources = 180
L-passes, BFS depth ≤ 3: **1,841,923 distinct tables, no hit** (114s).
Randomized 300K depth ≤ 5: no hit.

**S3 — rev ∈ L+R** (the decisive question: a yes collapses the union to L; a
no proves L+R ⊋ L, resolving hinge 2 negatively). Domain |X| ≤ 4 (31 points).
312 mixed passes (both directions), exhaustive depth ≤ 2: 11,945 tables, no
hit. Randomized 400K depth ≤ 6: no hit. Genetic (pop 400 × 400 gens, depth
≤ 11, fitness = exact per-point match count): **best 13/31** — the best
programs compute palindromes correctly at the 13 palindromic points and fail
every non-palindrome, i.e. the search plateaus exactly at the trivial
palindrome symmetry. No witness at any searched budget. The mirror question
σ = ⟦[X₁/X₂]X₃⟧ ∈ R is the conj-image of S2's space (spaces mirror-symmetric);
no separate run needed.

**Why no witness (construction analysis, hand proof-level).** The obstruction
is *residue routing*. Consider [A/aa]^R on C = b·a^ℓ·b: right-pairing of a^ℓ
leaves an a^(ℓ mod 2) residue at the FRONT of the produced block
(σ-halving = ρ-halving of residue-padded runs: right-pairing within a run is
left-pairing of a run with the residue pre-pended). An L-pass computes
per-run residues only *destructively at run ENDS* — [ε/a^k] passes
a^(ℓ mod k)·(remainder of the word) at each run end, and every L-pass's scan
frontier moves left-to-right, so information cannot be routed from a run end
back to the corresponding run front. An R-pass moves the frontier
right-to-left and does exactly this routing natively — that is what ρ *is*.
Concretely: to left-pair a^ℓ you must first test ℓ's parity, which L can only
do by deleting a right context (parity marker at run end), then *move the
marker left* to where the pairing starts. Attempts to do the move inside L:
pad-then-pair ([ε/aa] to fold, then re-anchor) dies because the pad acts
mid-run but the pairing must re-derive the run start; parity-marking in the
comma-code image ([ε/baba] — the enc² tool from thm:cat) leaves the residue at
run end; offset-1 pairing [ε/abab] does leave residue blocks at run FRONT but
corrupts every b-run/a-run junction (the offset needs the run's own letter,
which the L-pass cannot make depend on position). Each attempt is a concrete
counterexample-bearing failure, consistent with the machine negatives.

**Scope of the negatives (honest limits).** Template searches cover
*pipeline-shaped* expressions with single-pass pattern sources; they do NOT
cover DAG-shaped expressions (patterns computed by sub-pipelines, as in
prop:last's fresh-anchor enc²(X)·bb trick or thm:rep's [ε/b^k]-fan). prop:last
shows such shapes can genuinely leave the pipeline template: last/init/rotate
were found by hand with anchored junction patterns x·σ·bb, not by any pipeline
search. So S1–S3 prove: no pipeline-template witness exists at the stated
depths/domains. The remaining space for a ρ ∈ L construction is
exactly: DAG-shaped, junction-pattern expressions. Both steering facts from
the coordinator bind: (i) any ρ ∈ L witness must use variable patterns
essentially — constant-pattern L-pipelines are left-subsequential
(thm:subsequential) and [b/aa]^R is not (main.tex thm:subsequential); (ii)
short-domain artifacts are real — every number above states its domain, and
no candidate ever reached escalation stage.

**Verdict for R3 (provisional, R4 to consolidate):** no rev-witness in L+R and
no ρ-witness in L at any searched budget; combined with the Collapse
Criterion (§3) the working hypothesis flips to **L+R ⊋ L strictly** (equivalently
rev ∉ L, resolving hinge 2 negatively, and σ ∉ R). This is evidence, not
proof: the decisive facts are (a) thm:subsequential (constant fragments
incomparable) and (b) the residue-routing obstruction above; a proof needs an
L-invariant that ρ violates — R4's first task.

**Transferable machinery for the ONCE agent (hinge 1: delete-leftmost-b in
L; research/scratch/once/)** — from this round's construction analysis:
1. *Duplication by multiple variable occurrence*: a pattern source like
   X·X (same variable twice) duplicates the argument into the text, giving
   one copy to consume and one to keep — the pipeline template's cheapest
   non-destructive read. (Used in S2's P_srcs as ('cd',('v',1),('v',1)).)
2. *[ε/a^k] position-preserving residue skeleton*: [ε/a^k] deletes a's
   leftmost-first in blocks of k and leaves a^(ℓ mod k) at each a-run END,
   leaving all other positions intact — the cleanest L-native "reduce mod k
   per run" primitive. If the once-target needs length arithmetic on runs
   (it likely does: ordinal selection is length-driven), this is the
   L-fragment's only direct length reducer; note it computes at run ends
   (right side), never run fronts.
3. *Pad-then-pair reduction*: right-to-left pairing (R-halving) of a run =
   left-to-right pairing of the residue-padded run. Any construction that
   can arrange the residue of a run to sit at the run's FRONT converts an
   R-computation into an L-computation on the padded instance — conversely,
   proving some target needs residue-at-front proves it needs R. This
   reduction is what makes the L vs R boundary concrete and checkable.
4. *Offset-1 pairing* [ε/abab] (from the parity-marking attempts): pairs a
   run leftmost-first starting one position in, leaving a residue block at
   the run FRONT — but junctions between different letters corrupt (the
   offset consumes the first letter of the following run's pairing). If the
   once-target's runs are single-alphabet or separated by anchors, this may
   be directly usable: it is the only L-pass in our census that moves run
   residues from right end to left front.
In the other direction: if the once-agent finds that delete-leftmost-b
requires reading a marker at the FRONT of a run that was written at the run's
END, that is the same residue-routing obstruction as ours — the two hunts
would then share one invariant candidate.

## 9. Updated round plan (post-R3)

- R4a: attempt an L-invariant that ρ (or [b/aa]^R on the 2-block domain)
  violates — candidates: left-subsequentiality transfer to variable-pattern
  pipelines under some normalization; a "residue-side" quantity that
  L-compositions move right and R-compositions move left (sharpen the
  §5 residue-end heuristic into a real invariant, per coordinator request);
  degree/growth bounds from §4 (thm:fp) as a function-space separator.
- R4b: landscape row for L+R reflecting cor:incl-symmetry — L+R = L ⟺
  L+R = R ⟺ ρ ∈ L ⟺ σ ∈ R is ONE question; the row should present a single
  open cell (strictness conjecture), not two.
- R4c: place the 4 sibling ≥2-alternation pipelines (§5, D2b) in the paper as
  concrete interleaving witnesses (mixed pipelines not expressible as
  L^j∘R^k at the constant level).
- Final: verdict + numbers in REPORT.md and final message.

## 10. ROUND 4: collapse vs strictness, complete two-block theorem, invariant hunt (verify_r4.py, all green, ~5 s)

**E0 — W closed forms.** W = [a/bb]^L ; [b/aa]^R ; [a/bb]^L (run order) fixes
all 19 alternating strings of length ≤ 9 (no pass of W fires without an aa or
bb). W(b^n) = a^{(n div 2) mod 2 + (q+r) div 2} · b^{(q+r) mod 2} with
q = (n div 2) div 2, r = n mod 2, machine-verified for n ≤ 65 — W divides
run lengths by ~8 while routing first- and second-order parity bits to
opposite flanks.

**E1a — direction-independence of single-letter patterns.** Every constant
pass with |B| = 1 satisfies L = R (28,658 checks, all strings ≤ 10, 7
replacements): such a pass is exactly the letter-substitution homomorphism
σ ↦ A (inserted text is never rescanned), so ALL direction-sensitivity of
constant passes lives in |B| ≥ 2 patterns. (Paper-ready lemma; explains why
the 36-pass restricted universe and U2 carry all the alternation structure.)

**E1b — Orientation Lemma (the formal residue-end heuristic).** For
cross-letter letter-power passes [τ^q/σ^p], σ ≠ τ, p ≥ 2, on any σ^ℓ run,
bare or sentinel-delimited with an inert third letter: L gives
(τ^q)^{⌊ℓ/p⌋}·σ^{ℓ mod p} (produced LEFT, residue RIGHT); R gives
σ^{ℓ mod p}·(τ^q)^{⌊ℓ/p⌋} = rev of the L image (residue LEFT). Verified for
p ∈ {2,3}, q ∈ {1,2}, ℓ ≤ 12, both letters. Proof: direct greedy-scan
analysis (L consumes pairs from the run's left, R from its right; the
sentinel prevents merging). This is the single-pass core of the R3
residue-routing obstruction.

**E2 — the complete two-block impossibility theorem (R2 D2b upgraded from
budget-limited to complete).** All passes of U_min = {[a/bb], [b/aa]} × {L,R}
are length-non-increasing, so D_N = all binary strings ≤ N is closed under
the universe and every pipeline restricts to a function D_N → D_N. Tables are
byte-vectors over D_N indices; a pass is a byte translation table; closures
therefore SATURATE exactly (dedup by table) — saturation covers ALL block
lengths, not a budget. Results (N = 5, 6, 7): pure-L closure 11/13/15 tables,
pure-R 11/13/15, two-block composites (both orders) 39/53/69. At N = 7 (255
strings): **none of the 4 sibling pipelines is a two-block composite at any
block length**; the 1-alternation plants are present in both two-block
closures (sanity). Complete depth-3 census: **exactly 4 of the 64 mixed
words over U_min are not two-blocks — precisely the 4 siblings** (W_LRL,
W_RLR, and the two a↔b renamings). Paper statement: *over the pass universe
{a-run→b-run, b-run→a-run halvings, both directions}, on all binary strings
of length ≤ 7, the 3-pass alternating pipelines require ≥ 2 alternations;
no composition L^j∘R^k or R^k∘L^j (any j, k) agrees with them.* Honest
scope: U2 (all 24 length-non-increasing |B|=2 passes) and U36 closures
exceed 493,115 / 701,020 tables already at N = 5 — the two-block separation
over the larger universes remains budget-limited (R2 D2b numbers stand).

**E3 — the invariant hunt (five operationalizations of "no right-to-left
flow of unbounded information"; four falsified, one survives partially).**
Aligned with the ONCE agent's formulation ("junction-local bounded
left-context"), probed by single-run +1 extensions (a parity flip of one
run, at any position):
- v1 whole-output prefix/suffix events: FALSIFIED — even identity and
  cat(·,c) slices give suffix events when a middle run is extended (the
  input difference itself sits left of center; e.g. cat('ab','aab') =
  'ab','aab').
- v2 bounded prefix-erosion: FALSIFIED — eq(·,c) erodes the shared input
  prefix unboundedly (one output character depending on the whole input).
- v3/v4 suffix-comparable + erosion ≥ 3 (± excluding prefix-comparable
  pairs): FALSIFIED both ways — L-side deletion passes [ε/ab], [ε/ba] and
  words of the pure-L U_min closure produce them (max erosion 4 on |x| ≤ 5,
  growing with length), while the R-passes produce NONE under v4: with left
  context u, [a/bb]^R gives u·a^m vs u·b·a^m — MIXED, not suffix-comparable —
  because the R-routing is INTRA-RUN (residue at the run's front, not the
  string's front). Whole-output shape statistics cannot see it.
- v5 first-difference OFFSET (where the parity signal surfaces, rel =
  d / max|output|, 0 = far left): SEPARATES at every level short of computed
  patterns — identity 0.75-0.88, single L-passes ≥ 0.50 (mean ≥ 0.84),
  [a/bb]^R 0.14, [b/aa]^R 0.00, enc/dec/tail/init/rot 0.67-0.90, last
  absorbed, the ENTIRE §2 toolkit slice battery 0/44 with any low-rel event,
  and the mixed survivor W_LRL **0.00** (it routes parity leftward through
  its internal R). FALSIFIED only by the computed-pattern class: 1/30 random
  1-ary L-expressions (4,000 sampled in the v3 scan, 75 with v3-events)
  reaches 0.00 via deletion with an input-computed pattern — the identified
  falsifier is [ε / [bab/aba]X] applied to ([ε/aa]X)·([abb/X]X), i.e.
  deletion whose needle is computed from the same input — exactly the
  rep_n / spanning-needle escape hatch the ONCE analysis predicts.
**Conclusion (R4a):** no output-shape or event-level statistic separates L
from R; the surviving separation (v5) holds for all constant-pattern
pipelines and the entire toolkit, and is broken precisely by computed
needles. The unified separation lemma must therefore be DEPENDENCE-
STRUCTURAL (a property of how each output position depends on input
positions, closed under composition, satisfied by rep_n-style computed
needles, violated by ρ and by ONCE's takeWhile≠b) — as the coordinator's
steer anticipated. The falsification data above (which classes break which
candidate) is the input for that lemma; the ONCE agent's toolkit-composite
enumeration attacks it from their side. FLAG for the unified open problem:
both hunts share the obstruction (my residue-to-run-front routing = their
complete-run-length-at-the-junction), and the v5 toolkit result shows the
boundary passes through computed needles.

**E4 — growth transfer.** 20,000 random mixed pipelines (depth ≤ 5, strings
≤ 12): |f(x)| ≤ |x|·Π max(1, |A_i|/|B_i|) holds throughout — the L+R growth
class equals the L growth class (per-pass factors multiply identically;
thm:fp and the §4 degree machinery transfer verbatim).

## 11. The landscape row for L+R (paper-ready draft)

Row "L + R (mixed unions of both passes)" for the §5 landscape table:

- **Growth:** same class as L (E4; per-pass factor Π max(1,|A|/|B|)).
- **Toolkit:** strictly contains L's toolkit (and R's, by mirror); all §2
  constructions transfer (verified R1 C5 via allR images).
- **Constant fragments:** L and R incomparable (thm:subsequential +
  [b/aa]^R; R1 C4 smallest witness (|B|,|C|,|A|) = (2,3,1): [b/aa] vs
  [b/aa]^R on "aaa"). Single-letter patterns are direction-independent
  (E1a) — the direction-sensitivity of constant passes lives in |B| ≥ 2.
- **Inclusions / collapse:** ONE open cell. By cor:incl-symmetry composed
  with the Collapse Criterion: L+R = L ⟺ L+R = R ⟺ ρ ∈ L ⟺ σ ∈ R
  (ρ = ⟦[X₁/X₂]^R X₃⟧, σ = m(ρ) the L-pass as a 3-ary function). All four
  statements are the same question — the row states a single strictness
  conjecture, not two.
- **Strictness conjecture (evidence, not proof):** L+R ⊋ L (equivalently
  rev ∉ L, σ ∉ R). Supporting: thm:subsequential (constant fragments
  incomparable); the R3 residue-routing obstruction (three concrete failed
  constructions, each with its own counterexample); the R3/S1-S3 exhaustive
  negatives (592,447 / 1,841,923 / 11,945 tables + randomized + genetic
  13/31 palindrome plateau); and E2's complete finite-domain two-block
  separation with the E3 invariant boundary (constant pipelines + toolkit:
  no leftward parity routing; computed needles: the escape hatch).
- **Normal forms:** pure-L/pure-R blocks do not suffice — 4 concrete ≥2-
  alternation witnesses, complete over block lengths at U_min level (E2);
  Disjoint Commutation Lemma (R2 D1) as the positive commutation result;
  one-alternation normal form FALSE at the constant level (R2 D2b).

## 12. Final verdict of the L+R study

**What R adds over L: right-to-left routing of run-local summaries
(residues) — and, conjecturally, that is exactly what L cannot do.** The
Collapse Criterion reduces the union question to ρ ∈ L; the machine
evidence (all R3 searches negative at every stated budget; the residue-
routing obstruction; the complete E2 two-block separation; the v5 invariant
boundary passing through computed needles) supports strictness
L+R ⊋ L, with rev ∉ L and σ ∉ R as equivalents. Not a proof: the missing
piece is the dependence-structural invariant (R4a/E3 conclusion), shared
with the ONCE hinge. Deliverables: smallest-witness calculus (R1),
biconditional sharpening of prop:r2l-agree with the general bordered-P
construction (R1 C9), Collapse Criterion + mirror composition (R1-R2),
Disjoint Commutation Lemma (R2 D1), one-alternation refutation + 4 sibling
witnesses (R2 D2b, now complete at U_min level, E2), thm:core transfer
(R2 D3), direction-independence of single-letter patterns (E1a),
Orientation Lemma (E1b), complete two-block impossibility + census (E2),
five-way invariant falsification map (E3), growth transfer (E4).

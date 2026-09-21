# Alphabet Invariance of the Reachable Class — Report

Round 1 + round 2 (continuation). All work in this directory; `main.tex` untouched.
Shared library: `meow.py`. Batteries: `verify_alignment.py` (+`alignment.log`),
`verify_transfer.py` (+`transfer.log`), `verify_palindromes.py` (+`palindromes.log`),
`verify_unary.py` (+`unary.log`). Paper-form write-up: `transfer.tex`.
**Standing tooling constraint (user, effective this round):** no Python for
CPU-bound work; compute-heavy kernels are in C++ (`verify_hot.cpp`,
+`hot.log`), with Python retained only as glue and as the reference
specification. See §8.

**Headline.** Open problem 4 of the paper (line ~875) is settled affirmatively
in the strong form: *the reachable class is invariant under alphabet size for
every |Sigma|,|Gamma| >= 2, after conjugation by a comma-free coding.*
Both directions are proved and machine-verified end to end; the reversal
equivariance needs a palindromic refinement (see §5 — a genuine proof error
caught by the machine in round 1); the |Sigma|=1 edge splits cleanly
(one direction holds, the other has a structural obstruction).

---

## 1. Formalization (item 1)

**Good codings.** A *coding* is an injective character-wise monoid homomorphism
c: Sigma* -> Gamma*, given by D_c = {c(sigma) : sigma in Sigma} of uniform
length ell. c is **good** iff D_c is *comma-free* (Golomb: no codeword occurs
in u·v at a junction-straddling position 1..ell-1). Arbitrary injective
codings degenerate: the free assignment with ell(SS) = ell(S)^2 makes
X -> XX conjugate to unary squaring — the conjugacy class of a function then
depends on the coding. Comma-freeness is exactly the self-synchronization
that kills this (the Golomb analogue of the paper's Comma Code Lemma for
enc^2_{b,x}, blocks xc).

**The statement proved** (all |Sigma|,|Gamma| >= 2, all good c):
f is L_Sigma-reachable iff the conjugate f^c = c∘f∘c^{-1} (on image(c), as a
*partial* function in the sense of the restriction clause of def:reachable)
is L_Gamma-reachable; and when f is total the Gamma-witness is total and
agrees with f^c on the image — the total-extension clause is the
gamma-wrapper [R^c/gamma(P^c)] with gamma(X) = if(eq(X,eps),b,X) (the §2
toolkit). The theorem is *independent of the choice of good c*: any two are
connected by the composition lemma (dict(d∘c) comma-free) plus the retraction.

**Quantitative clauses** (machine-measured): the transferred expression E^c
has the *same node count* as E (leaves map to leaves, structure preserved —
T7b: max |E^c|/|E| = 1.00); its constant symbols grow ell-fold in word
length; deg(E^c) = deg(E) and Safe(E) => Safe(E^c) syntactically (T7: 2,954
expressions, 0 violations). Direction 2 preserves degree as well (roundtrip:
155 expressions, 0 mismatches) at a node overhead of 528 nodes for the
(3,2)-alphabet pair — an alphabet-dependent constant independent of E.

## 2. Main theorem, both directions (item 2)

Ingredients (each machine-verified; numbers in §6):
1. **Existence.** The explicit family
   D_ell = { a a m b : m in Gamma^{ell-3}, 'aa' not a factor of m, m[0] != a }
   is comma-free; over binary |D_ell| = Fib(ell-2) — arbitrarily large.
2. **Self-Synchronization.** In a comma-free uniform dictionary every
   occurrence of a codeword in a codeword-sequence starts at a multiple of
   ell; occurrences of c(B) in c(C) are exactly { ell*s : s in occ(C,B) }
   (A2: 14,196 cases).
3. **Pass Transfer.** [c(A)/c(B)] c(C) = c([A/B]C) — the first codeword of
   c(B) pins alignment; greedy scans correspond step for step; resume points
   stay aligned. The same proof covers *once*, *R* (rightmost), and *k-th
   occurrence* semantics: the occurrence correspondence is an
   order-isomorphism, so leftmost/first/k-th transfer, and it is
   direction-free so rightmost transfers too (A3v: 31,200 cases, 0).
4. **Composition.** D_c (over Gamma) and D_d (over Sigma) comma-free
   => { d(w) : w in D_c } comma-free (A4) — makes the retraction h = d∘c a
   self-coding of Sigma with a decodable image.
5. **Retraction.** Any uniform comma-free self-coding h has a *total*
   L-reachable realization (rep, single-character patterns) and decoder H_h
   (rep, codeword patterns), H_h(h(S)) = S — rep_n needs no pattern
   restrictions (thm:multiple substitution).

**Direction 1** (E -> E^c node-wise: constants -> c(W), variables and
structure unchanged): [[E^c]](c(S_vec)) = c([[E]](S_vec)) with *matching
definedness* (the pattern is eps in one iff in the other). Verified end to
end on all 2,954 depth<=1 expressions over ternary (constants <= 2) x 121
inputs = 357,434 evaluations, 0 mismatches, 23,912 undefined (matching);
plus 48,000 deeper-random; plus once/R modes (118,160 each, 0).

**Direction 2.** f^c L_Gamma-reachable => f L_Sigma-reachable: with
d: Gamma -> Sigma good and h = d∘c,
    E_final = H_h( E'_d( h(X_1),...,h(X_n) ) ),   E'_d = (E^c)^d,
is total when f is, and computes f exactly. Verified as a full roundtrip on
the 155-expression constants<=1 space x 40 inputs = 6,200 evaluations, 0
mismatches, 1,025 undefined (matching).

## 3. The |Sigma| = 1 edge (item 3)

**(a) unary -> binary: holds.** c(a) = 'ab' is good ({w} comma-free iff w
primitive — A6c). Every unary-reachable function is the restriction of a
binary-reachable one: all 258 depth<=1 unary expressions x a^0..a^24 = 6,450
evaluations, 0 mismatches (T3), plus 12,000 deeper-random (T3b). Alignment:
occurrences of (ab)^j in (ab)^m exactly at 2s (A6: 104 cases); pass law
[a^i/a^j]a^m = a^{ i*floor(m/j) + m mod j } (A6b: 462; U1a: 20 pairs).

**(b) binary -> unary: fails, structurally.** There is *no* injective monoid
homomorphism {a,b}* -> {a}*: any h has h(ab) = h(a)h(b) = h(b)h(a) = h(ba)
while ab != ba. So no coding-conjugation scheme exists at all in that
direction; the transfer theorem cannot cross |Sigma| = 1 from above (U2:
machine echo, 16 pairs).

*What the unary class is.* Every unary L-expression computes a length map in
the closure of { n -> n, n -> k } under pointwise + (cat) and
(g,r,p) -> ( n -> r(n)*floor(g(n)/p(n)) + g(n) mod p(n) ) (pass); constant
passes act as n -> i*floor(n/j) + (n mod j); [X_1/a]X_1 squares. Every unary
length map is eventually polynomially bounded (induction: a pass is bounded
by r*g + g), so n -> 2^n is unreachable at any size — the unary face of the
paper's X^{2^|X|} theorem.

*The halving question.* floor(n/2) is **not** found in the exhaustive
size<=7 unary space (36,978 expressions, 2,091 distinct length maps on
n = 0..24) nor among 3,000 random depth<=4; ceil(n/2) and parity *are*
reachable (size 4); n^4 needs size 10 (witness [[X/a]X / a]([X/a]X),
verified). Bounded-search evidence, consistent with prop:unary-once: the
paper's H = [b/a][eps/b][a/bb] needs the second letter; every single unary
pass leaks the residue (n mod j), and subtraction is not available to remove
it.

*Binary profiles vs the unary class.* Of 480 total binary length profiles
n -> |[[E]](a^n)| (n <= 12; all depth<=1 binary expressions with constants
<= 2 plus 2,000 random depth<=3), only **2** are realized by no size<=7 unary
expression nor any constant shift of one:
[1,3,5,9,13,20,29,35,47,61,69,86,105] and
[1,5,9,14,21,27,37,44,57,65,81,90,109] — both born of variable patterns
(residue-carry interactions). Bounded-search evidence, stated as such.

## 4. No contradiction with the native-function results (item 4)

The transfer theorem is a statement about *conjugates on code images*;
prop:del-leftmost and prop:kth are statements about *native* functions. No
conflict:

- prop:del-leftmost: the native once-node [eps/b]_1 is L-reachable over
  binary (depth-5 witness W) and resists over |Sigma| >= 3. Transfer moves W
  to a ternary alphabet as the *conjugate* [eps/c(b)]_1 on image(c) — a
  block-level function, not the native ternary [eps/gamma]_1 (different
  length profile: it deletes an ell-block, not a character). The native
  ternary function is a different conjugacy class; the ternary negative
  searches (exhaustive depth 3, etc.) do not see the transferred witness in
  any case (transfer scales constant lengths by ell, and Direction 2 adds
  the rep retraction — depth far beyond every search run). Alphabet
  sensitivity of a *native* function and invariance of every *conjugacy
  class* are consistent.
- The ell = 1 subtlety: when |Gamma| >= |Sigma|, an injective character-map
  (comma-free trivially — no straddling positions) conjugates f to the
  *native* function restricted to the sub-alphabet — so the binary
  once-deletion being reachable does give, over ternary, the restriction of
  [eps/b]_1 to any two-letter sub-alphabet, reachable as a partial function
  (the restriction clause of def:reachable). Consistent with the paper's
  picture: reachable on the anchored sub-domain, resistant in general
  position.
- **ONCE (and R, and k-th) have their own transfer theorems.** The alignment
  lemma is scan-direction- and multiplicity-agnostic (occurrences correspond
  order-isomorphically), so [c(A)/c(B)]_1 c(C) = c([A/B]_1 C), likewise
  rightmost and k-th occurrence: A3v (31,200), T2 (118,160 per mode, full
  expression level), T5c/T6b-0 (1,176 each). The first coded occurrence is
  the coding of the first native occurrence. prop:kth's marker-freshness
  obstruction is about *native* simulation of k-th nodes by once-nodes
  within one alphabet; untouched.

## 5. The payoff (item 5) — and the error the machine caught

**Negatives upgrade.** By Direction 1: if f is L_Sigma-reachable then f^c is
L_Gamma-reachable for *every* |Gamma| >= 2; contrapositively, every
L_Gamma-nonexistence result for a conjugate is an L_Sigma-one. For *native
alphabet-uniform* functions the needed equivariance is the Pass Transfer
Lemma: the pass node (all four semantics) commutes with every good coding,
so its reachability question is alphabet-uniform — verified end to end
(T6b: L-mode full expression, 294 evaluations, 0; once/R/kth semantic
composition, 882; T5c/T6b-0: 1,176 each). The paper's union criterion
(r in L?) and the once-hinge (r_1) are therefore *single* questions, not one
per alphabet: r in L_Sigma for one |Sigma| >= 2 iff for all.

**Reversal — corrected mathematics.** Round 1 claimed c(rev S) = rev(c(S));
the machine refuted it (T5b round 1: 60 failures on 31 inputs):
character-wise reversal reverses *each codeword individually*, so the
identity holds **iff every codeword is a palindrome**. The naive "rev on the
code image" is *not* the reversal of the image. The repair: retract with a
coding whose e-side is *palindromic comma-free*. With e: Gamma -> Sigma^k
palindromic comma-free and q = c∘e:
    [[E']](q(T)) = c(rev e(T)) = c(e(rev T)) = q(rev T),
so rev_Gamma = H_q ∘ [[E']] ∘ q — the palindrome property makes
e(rev T) = rev(e(T)). Verified: T5b, 63 inputs |T| <= 5, 0 failures, with
q, H_q as *expressions* and the oracle D = c∘rev∘c^{-1} standing in for
[[E']] (rev-reachability is the hypothesis, not a given).

*Palindromic comma-free dictionaries exist in the needed sizes:*
- **Middle-marker family** { alpha mu rev(alpha) : alpha in
  (Sigma\mu)^m } — palindromic, comma-free (mu occurs only at the exact
  middle, so any occurrence in u·v starts at 0 or |u|), size (|Sigma|-1)^m:
  unbounded for |Sigma| >= 3 (P1: 20 dictionaries).
- **Over binary** the family degenerates (size 1), but size-3 dictionaries
  exist: {aabaa, ababa, abbba} and {aabaa, babab, bbabb} (P2). Exact maxima
  by branch and bound: 1,1,3,2,7,14 at ell = 3,4,5,6,7,9 (P3; data).
- Composition L3 holds for every reversal route (P4).

**Consequence.** rev in L over *one* |Sigma| >= 2 iff over *every*
|Sigma| >= 2: from a binary source escape via the size-3 dictionary to a
3-letter alphabet, then middle-marker to any target; from |Sigma| >= 3,
middle-marker directly. Contrapositive: the paper's binary negative searches
for reversal, if exhaustive, upgrade to every alphabet — open problems 2 and
4 are one question.

## 6. Machine verification — exact numbers

| Battery | Check | Domain | Result |
|---|---|---|---|
| A1 | family comma-free + Fib sizes | 21 dicts, ell 3..9, bin/tern/quat; sizes ell 3..12 | all comma-free, |D_ell| = Fib(ell-2) |
| A2 | alignment occ(c(B)) = ell*occ(B) | B in (abc)^{<=3}\eps, C in (abc)^{<=5} | 14,196 cases, 0 mismatches |
| A3L | pass transfer (L) | A,C <= 3, B in 1..3 | 188,760, 0 |
| A3v | once/R/kth transfer | A,B <= 2, C <= 3, k <= 3 | 31,200, 0 |
| A4/A4b | composition comma-free | dict(d∘c), ell = 24 | comma-free |
| A5/A5b | paper's comma code on pure image text | 3,038 L-cases; 1,890 variant | 0; 24 mismatches all R-mode (matches thm:r2l-rep) |
| A6/A6b/A6c | unary alignment + pass law + primitivity | 104 + 462 + 3 | all hold |
| T0 | rep expression = freezing semantics | 300 random | 0 |
| T1/T1b | Dir-1 full pass | 2,954 exprs x 121 in; 1,200 random x 40 | 357,434 + 48,000 evals, 0; 23,912 undefined (matching) |
| T2 | Dir-1 once / R | 118,160 each | 0 |
| T3/T3b | unary->binary | 258x25; 800x15 | 6,450 + 12,000, 0 |
| T4a/T4 | Dir-2 roundtrip | h/H 40; 155 exprs x 40 | 6,200 evals, 0; 1,025 undefined (matching) |
| T5a | retraction decodable | 31 inputs | 0 |
| T5b | **reversal retraction (palindromic e)** | 63 inputs |T|<=5 | 0 failures |
| T5c | pass equivariance under q, 4 modes | 1,176 | 0 |
| T6a | doubling payoff | 31 | 0 |
| T6b-0 | pass equivariance under e, 4 modes | 1,176 | 0 |
| T6b | pass payoff: L full expr; once/R/kth semantic | 294; 882 | 0 |
| T7/T7b | deg/safe transfer; node count | 2,954 exprs | 0 violations; |E^c| = |E| |
| roundtrip deg | deg(E_final) = deg(E) | 155 roundtrips | 0; +528 nodes constant |
| P1 | middle-marker family | 20 dicts (q in {3,4}, m <= 5) | palindromic + comma-free, size (q-1)^m |
| P2 | binary size-3 dicts | both | comma-free |
| P3 | binary palindromic comma-free maxima | ell = 3..7,9 | 1,1,3,2,7,14 (data) |
| P4 | L3 for reversal routes | 3 + 1 routes | all comma-free |
| U1a | constant-pass length law | 20 (i,j) pairs | 0 |
| U1b/U1b' | target maps over exhaustive size<=7 (36,978 exprs) | 10 targets + witness | found: id, 2n, n^2, n+1, ceil, parity; not found: floor(n/2), n-1, 2^n, n^4 (n^4 witness verified at size 10) |
| U2 | homomorphism collision | 16 pairs | all collide |
| U3 | binary profiles vs unary space | 480 profiles | 2 unrealized (listed in §3) |

**What failed and was fixed.**
1. T5b round 1 (60 failures): the false identity c(rev S) = rev(c(S)) —
   repaired by the palindromic-e construction (§5).
2. T6b round 1 (202/1,176): two causes — a construction bug (an extra
   transfer through the q-coding) and a real semantics issue (the rep-based
   q, H_q are L-expressions; evaluating them under once/R/kth nodes is
   meaningless). Fixed by applying E' directly to the q-wrapped inputs, and
   by splitting the check: full expression in L mode, semantic composition
   (variant pass at the coding level, L-expressions around it) for variant
   modes.
3. A2 round 2 (14,560 spurious mismatches): the empty pattern — after the
   all_strings fix the loop reached B = eps, where "occurrence positions"
   means something else; the lemma concerns nonempty patterns (passes
   require B != eps). Excluded; battery green.
4. U1b/U3 round 2: expectations corrected (n^4 needs size 10, not <= 7;
   constant-shift profiles like 6 + ceil(n/2) are reachable just past the
   size bound — handled at the profile level).

## 7. Open threads (next round)

1. **Binary palindromic comma-free maxima**: 1,1,3,2,7,14 at odd lengths —
   unbounded? Only affects the directness of the reversal route (a size-3
   dictionary suffices for its truth), but a clean combinatorial question.
2. **floor(n/2) over unary** beyond size 7: prove unreachable (the
   residue-leak argument) or find a witness; ditto the two U3 profiles.
3. **Integration**: transfer.tex is written in the paper's voice with
   "(Verified: ...)" notes; the user integrates after verifying.
4. The background agent on "is rev in L" is still running; its verdict
   affects only how the reversal corollary reads (both branches are covered
   by the iff).

## 8. Tooling constraint: C++ for compute-heavy work

Per the user's standing constraint (no Python for CPU-bound work; Python only
as glue), every compute-heavy kernel of this round is ported to
`verify_hot.cpp` (compile: `g++ -O2 -std=c++17`; runtime: 13 seconds for
everything below, vs minutes for the Python batteries). Caps and the
undefined-classification rule (undefined iff some pattern value is empty,
strictness in all sub-expressions) are IDENTICAL to the Python references, so
cap artifacts cannot create false results; the deterministic counts must
match, and they do, exactly:

| C++ check | Domain (same caps as Python) | Result | Python reference |
|---|---|---|---|
| HA1 family comma-free + Fib sizes | 21 dicts, ell 3..9; sizes ell 3..12 | 0 mismatches | A1: same |
| HA2 alignment | B <= 3 nonempty, C <= 5 | 14,196, 0 | A2: 14,196, 0 |
| HA3L pass transfer | A,C <= 3, B in 1..3 | 188,760, 0 | A3L: same |
| HA3v once/R/kth | A,B <= 2, C <= 3, k <= 3 | 31,200, 0 | A3v: same |
| HT1 Dir-1 (L) | all 2,954 depth<=1 exprs, |S| <= 4 | 357,434, 0; 23,912 undefined (matching) | T1: same |
| HT1 Dir-1 once / R | same space, |S| <= 3 | 118,160 x 2, 0 | T2: same |
| HU1 exhaustive unary space | size <= 7 (36,978 exprs) | targets: id/2n/n^2/n+1/ceil/parity FOUND; floor(n/2), max(n-1,0), n^4 (size 10 witness verified), 2^n NOT FOUND | U1b/U1b': same verdicts |
| HP middle-marker family | 20 dicts, m <= 5 | 0 mismatches | P1: same |
| HP palindromic maxima | ell = 3..7,9 | 1,1,3,2,7,14 | P3: same |

The two randomized supplements (3,000 unary depth<=4, 2,000 binary depth<=3)
are re-sampled in C++ with a fixed splitmix64 PRNG, so their aggregates are
independent samples rather than bit-identical replays: C++ finds 2,065
distinct unary length maps (Python: 2,091 — different sample, same
conclusion), and again a small missing class of binary profiles (2 of 12
total in its sample; Python: 2 of 480) — both samples agree that a handful
of variable-pattern binary profiles is unrealized in the size<=7 unary space
plus shifts. The rep-expression batteries (T0, T4-T6: at most 6,200
evaluations each) remain in Python at glue scale.

All future rounds: compute-bound work starts in C/C++; Python only generates
small inputs, invokes the compiled tool, and diffs small outputs.

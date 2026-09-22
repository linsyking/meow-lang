# ROUND 9 REPORT — FINAL: the two-color TL LaTeX, mask Boolean closure, the replication-degree correction

Lane B (rev-split). Charter (coordinator round-9 message): update the
paper-ready TL LaTeX (ROUND7_REPORT.md §5) to the two-color refinement —
items (a)–(e) — output ROUND9_REPORT.md with the FINAL LaTeX block
(paper-ready, self-contained, Lane A mounts it verbatim); optional only if
the LaTeX lands early: p = 7 (ord₇(3) = 6), closing disclosed scope item (i).
Family D(k;3). Theory first; machine confirms.

Artifacts: `gram9.c`, `gram9`, `gram9.log` (`./gram9 gram`: 511 checks, 0
failures), `gram9_meas.log` (`./gram9 meas`: 144 checks, 0 failures),
`tl_witness.c`, `tl_witness`, `tl_witness.log` (`./tl_witness`: 29 checks, 0
failures — the replication witness backing two corrections below). All
earlier artifacts frozen; nothing committed.

**Verdict: the LaTeX is delivered (§1) with all five charter items, and it
required TWO CORRECTIONS to the round-7 §5 statement beyond the chartered
wording — both machine-witnessed or hand-derived and flagged below
(C-R9-1 the expansion exponent, C-R9-2 the ambient-index anchoring), plus
one hand-derived count correction (C-R9-3 the directive-count recursion
under replication). The optional p = 7 candidate IS delivered (§3), closing
scope item (i) and surfacing a fourth finding: round 8's single-residue
masks were an ENGINE artifact — the formalism's Boolean-closed Ind masks
(AIS-CLOSURE) are what mod7 needs.**

---

## 1. THE FINAL TL LATEX (paper-ready, self-contained; mounts verbatim)

```latex
\begin{theorem}[Truncation Ledger over $\mathcal D(k;3)$]
\label{thm:TL}
Fix a substitution expression $V$ over the two-letter alphabet
$\{a,b\}$, and let $\mathcal D(k;3)=a^{3^0}ba^{3^1}\cdots ba^{3^k}$
and $S=(3^{k+1}-1)/2$. Let $d$ be the $S$-depth of $V$ (the maximum
nesting of substitution nodes), $\#S(V)$ its number of substitution
nodes, and $M_V$ the ledger bound $8\,\#S(V)+O_V(1)$ of clause
{\rm(ii)} below. Collect the pattern and tiling moduli occurring in
$V$ — the lengths of the pattern values whose segments tile runs, and
the moduli of their window arithmetic — and set
\[
T_V=\operatorname{lcm}\Bigl(\{2\}\cup
\{\operatorname{ord}_p(3):\ \text{$p$ such a modulus, }\gcd(p,3)=1\}
\cup\{p:\ \text{$p$ such a modulus, }\gcd(p,3)=1\}\Bigr),
\]
where $\operatorname{ord}_p(3)$ is the multiplicative order of $3$
modulo $p$; a modulus divisible by $3$ imposes no order, its residue
dependence vanishing past a $V$-fixed site index (eventual
dominance). Then every maximal monochromatic run of
$V(\mathcal D(k;3))$ — of either letter — has value
\[
v=\sum_{i\le M}q_i\,3^{e_i}+(Ak+B)+\beta,
\]
where:
\begin{enumerate}
\item[\rm(i)] \emph{strata.} The slopes $q_i\in\mathbb Q$ and the
affine data $A,B$ are $V$-fixed on each residue class of $k$ modulo
$T_V$; each exponent $e_i$ is \emph{anchored}: a sum of at most
three terms of the forms $k-c$, $\iota-c'$, $c''$ with $V$-fixed
offsets, where the indices $\iota$ are the ambient family indices
of the run's emission path — at most $d$ of them, each an input
site or affine in the input sites; for ambient arity one, the input
sites $0,\dots,k$.
\item[\rm(ii)] \emph{term ledger.} The site-reference count obeys
$M\le M_V$; the first and last runs satisfy $M\le 2$, with only
top-anchored (and products of two top-anchored) exponents.
\item[\rm(iii)] \emph{junk.} $|\beta|=O(k)$, and $\beta$ collects
to a $k$-affine part plus a $T_V$-periodic part.
\end{enumerate}
Moreover the run \emph{profile} is pinned in the same sense, as a
\emph{two-color} object. The output text decomposes uniquely as an
alternating sequence of maximal runs
$a_0\,b_0\,a_1\,b_1\cdots b_{m-1}\,a_m$ with $b_i\ge1$, interior
$a_i\ge1$, $a_0,a_m\ge0$; run-length decoding is a bijection on
texts, while the $a$-lengths alone are not
(Remark~\ref{rem:TLprof}). There is a \emph{profile grammar}: on
each residue class of $k$ modulo $T_V$ — at most $T_V$ of them — a
$V$-fixed directive tree of $N_V$ nodes ($N_V\le 3^{d}\,(2|V|+1)$
whenever every fired set is one-dimensionally indexed, and
$N_V\le 2^{|V|^{2}}$ in general), whose directives are single values,
masked index families — $j\in[\ell(k)..h(k)]$ with $\ell,h$ affine
in $k$, refined by a $V$-fixed Boolean combination of residue tests
$j\equiv r\pmod T$ — and outer families instantiating sub-lists.
Its expansion, over forms as in (i)–(iii), is exactly the two-color
run sequence. Writing $\Delta_V\le|V|$ for the tree's nesting
depth — additive under replication,
$\Delta(S(R,P,F))\le\Delta(F)+\Delta(R)$ — the expansion has at
most $2\,N_V\,(k+2)^{\Delta_V}$ entries up to $V$-fixed constants
(the leading $2$ is $b$-run bookkeeping, absorbable if runs are
counted per color), and may have length $\Theta(k^{\Delta_V})$:
$V=[u/b]\,u$ with $u=[x/b]\,x$ ($x$ the input) has $\Delta_V=4$
and $k^{4}+1$ runs. Each emitted entry is a merge of at most $d+2$
form pieces (the Merge Lemma, uniformly over both colors), so the
expansion carries at most
$2\,N_V\,(k+2)^{\Delta_V}\,(d+2)\,M_V$ form terms in all. Every
tree is $k$-independent.
\end{theorem}

\begin{remark}
\label{rem:TLprof}
Here $[R/P]F$ denotes the pass replacing each occurrence of $P$'s
value in $F$'s value by $R$'s value — greedy, leftmost,
non-overlapping, never rescanning inserted text.
\textnormal{(1)~The two-color refinement is necessary. Passes may
output consecutive $b$'s, and then the $a$-lengths alone both fail
to determine the text ($ab$ and $abb$ have the same collapsed
$a$-runs) and can be exponentially long in $k$: $[b/a^4]\mathcal
D(k;3)$ has $\Theta(3^{k})$ $a$-runs, all but $k+1$ of them empty,
so no $k$-independent grammar can pin them. Its two-color profile
has $2k+1$ entries, and its $b$-entries are anchored exponentials
with periodic corrections — forms of class (i)–(iii).
(2)~The periodic masks genuinely occur, with period an order
$\operatorname{ord}_p(3)$ of the inner tiling modulus $p$. For
$V=[b/\mathit{bab}]\,[b/a^4]\,\mathcal D(k;3)$ the pattern
$\mathit{bab}$ fires exactly at the sites $j$ with $3^j\equiv
1\pmod 4$, i.e.\ at the residue class $\{j\ \mathrm{even}:\,
2\le j\le k-1\}$ of period $\operatorname{ord}_4(3)=2$ — a residue
class, not an interval. The surviving family is the complementary
class; each firing deletes its interior run and merges the two
flanking $b$-runs with the inserted letter into a single $b$-entry
(three Merge pieces, within the $d+2$ budget); and the two cells
$k\bmod 2$ carry structurally different tails. The modulus $7$
behaves identically with period $\operatorname{ord}_7(3)=6$: the
fired set of $[b/\mathit{bab}]\,[b/a^{7}]\,\mathcal D(k;3)$ is
$\{j:\ 6\mid j,\ 1\le j\le k-1\}$, its surviving family the
complement class $j\not\equiv 0\pmod 6$.}
\end{remark}
```

### 1.1 Change log vs ROUND7_REPORT.md §5 (what and why)

Chartered items, all in:
- **(a) two-color profile clause**: "maximal a-runs and b-runs", the
  uniqueness sentence (run-length decoding bijective; a-lengths not —
  the coordinator's rule-Z non-injectivity witnesses ab/abb), the entry
  bound with the leading 2 stated and the absorb rule inline.
- **(b) Merge Lemma, both colors**: "uniformly over both colors";
  mod2's 3-piece b-merge is the remark's exhibit.
- **(c) S-i masks**: "refined by a V-fixed Boolean combination of residue
  tests j ≡ r (mod T)"; mod2 the exhibit (fired set {even j ∈ [2..k−1]},
  period ord₄(3) = 2); mod7 added as the second exhibit (period 6,
  complement class).
- **(d) T_V's domain**: spelled out exactly as specified, both sets with
  the coprimality, the eventual-dominance sentence for 3-divisible
  moduli. Note 4 is coprime to 3 with ord₄(3) = 2 — the mod2 exhibit is
  the smallest instance of the domain; ord₇(3) = 6 is the second.
- **(e) per-cell selection**: "on each residue class of k modulo T_V —
  at most T_V of them"; mod2 demonstrates the per-cell face (the two
  cells' tails differ structurally); mod7 demonstrates the other face
  (a single k-uniform tree with T_V-periodic form coefficients) — both
  are "V-fixed per residue class".

Corrections beyond the chartered wording (the reason the final statement
differs from round 7's in three more places):

- **C-R9-1 (the expansion exponent — machine-witnessed).** Round 7's
  "expansion ≤ (k+2)^{d(u)}" with d the substitution/tree depth is
  REFUTED by replication: V = [u/b]u with u = [x/b]x has tree height 3
  but k⁴+1 runs (machine: 82/257/626/1297 at k = 3..6, `tl_witness.log`);
  the triple composition has k⁸+1 = 6562 runs at k = 3. The degree is
  the NESTING depth Δ_V, which is ADDITIVE under replication
  (Δ(S) ≤ Δ(F) + Δ(R), Δ ≤ |V|), and the expansion is k^{Δ_V} exactly
  along the replication chain (2, 4, 8 → k², k⁴, k⁸). The mounted
  statement uses Δ_V. Why round 7's max-recursion fails: the fired set
  of a pass over a REPLICATED scrutinee is indexed by the scrutinee's
  own family tuples (dimension Δ(F)), not one affine parameter — every
  battery expression so far (rounds 5–8) has a one-dimensional fired
  set, which is why the max-form held there.
- **C-R9-2 (clause (i)'s anchoring — wording fix per the accepted round-7
  S-ii rule).** Round 7's "where j ranges over the input sites" (one
  site variable) is insufficient under nested replication: ambient
  indices accumulate (arity ≤ d), and a single run's value can anchor at
  more than one of them. Machine-witnessed by the decb² value table at
  k = 3 (`tl_witness.log`): the seam values 59 = 2·3^k + 3¹ + 2 and
  65 = 2·3^k + 3² + 2 anchor at k and the OUTER site index, while the
  interior junctions 31 = 3^k + 3^{c′+1} + 1 anchor at the INNER copy
  index, and the junction seam 87 = 3·3^k + 3^{c+1} + 3 mixes levels
  (each single value still uses at most one ambient — multi-AMBIENT
  forms arise only for replacements with family-dependent heads; see
  §5). The mounted clause states the ambient-index anchoring; for
  arity one it reduces verbatim to round 7's wording.
- **C-R9-3 (the directive-count recursion under replication —
  hand-derived, flagged).** Round 7's N ≤ 3^d(2|V|+1) holds whenever
  the fired set is one-dimensionally indexed (all battery expressions,
  coordinator-verified); under replication the insertion subtrees ride
  each b-emitting directive KIND of the scrutinee's grammar, giving the
  recursion D(S) ≤ 3·D(F) + B(F)·(Δ(F) + D(R)) + c₀ with B(F) = the
  b-emitting kinds (≤ D(F)), which along replication chains outgrows
  3^d·poly(|V|) (decb composed with itself 4 times exceeds
  3^d(2|V|+1) by the recursion; the m ≤ 3 cases still satisfy it).
  The mounted two-tier bound N_V ≤ 3^d(2|V|+1) (1-D fired sets) /
  N_V ≤ 2^{|V|²} (general; the induction closes: |S| ≥ |F|+3 gives
  |S|²−|F|² ≥ 6|F|+9, absorbing the D(F)·|F| term) is certified.
  Not machine-pinned (no decb⁴ grammar built); the derivation is
  three lines and in this change log.

### 1.2 Notes for Lane A

1. **Symbol mapping** to the coordinator's letters: my Δ_V is the
   coordinator's "d" in the expansion formula; my d (S-depth) is their
   D_V. The mounted formula keeps N_V explicit: the tighter literal
   product 2(k+2)^{Δ_V}(d+2)M_V (N_V dropped) is NOT certified in
   general — the directive count is not dominated by (d+2)M_V for deep
   V — keep N_V.
2. **Constants decision unchanged**: 8·#S+O_V(1) at run level (clause
   ii), (d+2)·M_V per form; both kept. Single-constant form if the
   integration wants it: (d+2)·8·#S(V)+O_V(1).
3. The remark is part of the mounted block; its first sentence (the
   pass gloss) can be dropped if Section 2 defines [R/P]F.
4. The unconditional status rests on: PO-1(v)+PO-3+EPT (round 6), the
   production rules and AIS-CLOSURE (round 7), the two-color/mask
   hardening (round 8), and this round's mod7/replication witnesses.
5. Every exhibited claim in the block is machine-verified (gram8/gram9
   logs rounds 8–9; tl_witness.log this round; the round-5/6 batteries
   for the value clauses).

---

## 2. The replication witness (backing C-R9-1/C-R9-2)

`tl_witness.c` (artifact; `./tl_witness`, 29 checks, 0 failures,
rebuild reproduces the log byte-identically):

- decb = [x/b]x: a-runs k²+1, b's k² (regression, k = 3..6).
- decb² = [decb/b]decb: a-runs k⁴+1, b's k⁴, two-color entries 2k⁴+1
  (k = 3..6: 82/257/626/1297 a-runs — the height-3/k⁴ refutation).
- decb³ = [decb²/b]decb² at k = 3: 6562 a-runs, 6561 b's — k⁸+1
  (Δ = 8, exactly k^{Δ}).
- The k = 3 decb² value table with hand decompositions, all machine-
  checked: head 4 = 2+2; sites 3, 9 (27 each); junctions 31 = 27+3+1,
  37 = 27+9+1 (9 each); seams 59 = 54+3+2, 65 = 54+9+2 (3 each);
  junction seams 87 = 54+31+2, 93 = 54+37+2; end 108 = 54+54. The
  seam values are 3-piece merges (insert tail + span + next insert
  head) — the Merge Lemma's budget in action, and the anchoring
  exhibit for clause (i)'s ambient wording.

The theory (hand, before the machine): a pass over a replicated
scrutinee fires at its b-entries, indexed by the scrutinee's family
tuples — dimension Δ(F) — so the insertion directives ride inside the
scrutinee's family structure with R's nesting stacked under: additive
Δ. The a-run count recursion: each firing of [w/b] over a text with B
b's and A a-runs inserts w's value (a-runs R_w) with two seam merges:
A′ = A + B·(R_w − 2); unrolled on the replication chain it gives
k² → k⁴ → k⁸ with B, R_w squaring each level — matching Δ = 2 → 4 → 8.

---

## 3. The p = 7 candidate (optional, delivered): mask Boolean closure

`gram9.c` = gram8.c plus: (1) `mneg` — mask complements: j is in the
index set iff mmod = 0, or ((j mod mmod) = mres) XOR mneg; (2) two new
battery entries and grammars:

- **tile7 = [b/'aaaaaaa']X**: remnant Λ_j = 3^j mod 7 — period 6
  (ord₇(3) = 6; cycle 1,3,2,6,4,5). Two-color profile: OF j = 0..k−1:
  [a = Λ_j; b = 1+⌊3^{j+1}/7⌋]; a = Λ_k. 4 directives, machine-exact
  k = 3..13 (head at k = 13: 1 1 3 2 2 4 6 12 4 35 5 105 1 …).
- **mod7 = [b/'bab']tile7**: the pattern 'bab' (c₁ = 1) fires exactly
  at a-runs with Λ_j = 1 ⟺ 3^j ≡ 1 (mod 7) ⟺ 6 | j: **fired set =
  {j : 6 | j} ∩ [1..k−1]** — period 6, TWO full periods at k = 13
  (fires at j = 6 and j = 12). The surviving family is the COMPLEMENT
  class j ≢ 0 (mod 6): one order-preserving masked OF with mneg = 1
  (a class-by-class split would scramble the profile order — five
  single-class families cannot interleave in the directive algebra;
  the complement mask is the correct and general device, and it is
  exactly the Boolean closure AIS-CLOSURE always specified). The
  b-forms branch on j mod 6 (periodic coefficient): merged
  (⌊3^{j−1}/7⌋ + 1 + ⌊3^j/7⌋) before j ≡ 1 (mod 6) (j ≥ 7 automatic
  inside [2..k−1]), plain otherwise; the tail branches on k mod 6
  (merged iff k ≡ 1). SINGLE cell — the tree structure is k-uniform;
  the k mod 6 dependence lives in the periodic-coefficient forms: the
  other face of the formalism's per-cell × periodic-forms
  decomposition (mod2 demonstrates the per-cell face, mod7 the forms
  face; both are "V-fixed per residue class of k"). 8 directives,
  machine-exact k = 3..13 (head at k = 13: 1 1 3 2 2 4 6 12 4 35 5
  417 3 …; the merged 417 = 104+1+312 before a-run 7), with the
  fired-count cross-check #fired = ⌊(k−1)/6⌋ at every k.

Results: `./gram9 gram` — **21 grammars (17 round-7 regression in both
modes + tile4 + mod2 + tile7 + mod7), 511 checks, 0 failures, 0.5s**;
`./gram9 meas` — the round-8 measure forms re-verified, 144 checks, 0
failures. Mutation tests (scratch copies): mask complements disabled →
mod7 fails at every k (the surviving/deleted classes swap); the merged
b-form replaced by the plain one → 6 FAILs; round 8's three mutations
re-verified through the new engine. Rebuild reproduces both logs
byte-identically.

**The engine finding**: round 8 implemented single-residue masks; that
was an engine artifact, not a formalism restriction — AIS-CLOSURE's Ind
predicates are closed under Booleans, and the p = 7 case needs the
complement class. The formalism's S-i mask consumption point is
unchanged (it always said "Boolean combination"); the engine now
matches it.

---

## 4. Machine record

- `gram9.c`/`gram9`/`gram9.log`/`gram9_meas.log`: as §3. Invocation
  lines first in both logs; totals 511 + 144 checks, 0 failures;
  runtimes 0.5s / 0.1s.
- `tl_witness.c`/`tl_witness`/`tl_witness.log`: §2. 29 checks, 0
  failures; rebuild byte-identical.
- No machine-caught hand errors this round: tile7/mod7 were hand-derived
  and text-verified at k = 6/7 before coding (the k = 6 no-firing case
  and the k = 7 single-firing merged tail 417), and the witness counts
  were hand-predicted (k⁴+1, k⁸+1) before running. The mutation tests
  certify that wrong derivations would have been caught.
- **Scope still not directly machine-verified** (disclosed): (i) the
  decb²/decb³ GRAMMARS themselves (4- and 8-level nesting; would need
  multi-ambient forms in the engine — the counts and value
  decompositions are verified, the grammar pins are not); (ii)
  multi-AMBIENT forms (a merge combining two family-dependent pieces
  from different ambient levels — arises for replacements with
  family-dependent heads, e.g. an Eleak-type replacement under
  replication); (iii) masked F (kind 1) — implemented, unexercised;
  (iv) moduli beyond the {2, 4, 6, 7}-pattern family; (v) the Merge
  Lemma's (d+2) piece count remains the accepted three-line sketch;
  (vi) C-R9-3's count recursion beyond m ≤ 3 is hand-derived only.

---

## 5. Honest ledger and handoff

- The main line (TL at full altitude, unconditional) and the INV4
  formalism now stand with: two-color profiles (round 8 + this
  round's LaTeX), periodic masks including complements (rounds 8–9,
  periods 2 and 6 machine-exact), per-cell and periodic-form
  faces both executable, the measure form on the same footing
  (round 8 §3 — the Lane D OL-2 channel), and the replication
  corrections of this round witnessed.
- What I would hand a successor if the campaign continues: (1) the
  multi-ambient engine extension + decb²/decb³ grammar pins (closes
  scope items (i)–(ii) and machine-anchors C-R9-1/C-R9-3 fully);
  (2) an Eleak-head replacement under replication (the true
  multi-ambient merge); (3) the INV3 proofs if Lane D's OL-2 lands.
- Standing notes already delivered: T_V wording (§1, item d); both
  constants kept (§1.2 item 2); the two-color restatement is
  load-bearing for the induction (coordinator's round-8 verdict) and
  is now the mounted text.

*— Lane B, rev-split, 2026-09-22. Machine checks confirm hand
derivations; they do not replace them.*

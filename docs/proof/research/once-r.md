# once-r: replacing only the RIGHTMOST occurrence

Research report on the primitive `[A/B]₁ᴿC` — replace exactly the rightmost
occurrence of `B` by `A` in `C` (identity when `B ⊄ C`). Companion variant to
the baseline note `docs/proof/main.tex` (which studies replace-all `[A/B]` in
the L-to-R greedy semantics, called **L** below). All experiments live in
`docs/proof/research/scratch/once-r/`; every claim is labeled
**PROVEN** (proof given or routine from it), **COMPUTATIONAL** (verified
exhaustively/heuristically by machine, in the stated finite scope),
**CONJECTURE** (believed, unproven; computational evidence stated),
or **REFUTED** (disproved).

Notation follows the paper: `⊂` substring, `⊏/⊐` prefix/suffix, `Γ(W)` alphabet,
`rev(W)` reversal, `#u(W)` number of occurrences of `u`, `ε` empty string,
`X ⊴ Y` means "every function computable in calculus X is computable in
calculus Y" (Y *expresses* X). The four calculi compared: **L** (paper
baseline), **R2L** (replace-all scanning right-to-left), **once-l**
(leftmost occurrence only), **once-r** (this report). "Core" = no Cat nodes;
"size" = number of grammar nodes (Subst node = 4 leaves' worth: core sizes
are 1, 4, 7, ...).

---

## 1. Semantics

**Definition 1' (once-r).** For `A, C ∈ Σ*` and `B ∈ Σ* \ {ε}`:

    [A/B]₁ᴿ C = C₀·A·C₁   where C = C₀·B·C₁ and B ⊄ C₁   (rightmost occurrence)
    [A/B]₁ᴿ C = C         if B ⊄ C
    [A/ε]     undefined

Equivalently `[A/B]₁ᴿC = C[:j]·A·C[j+|B|:]` with `j = rfind(B, C)`.
The expression calculus (variables, constants, `[R/P]E`, concatenation,
denotation, definedness when a pattern value is `ε`) is the paper's
Definitions verbatim, with the node `[R/P]E` now denoting the once-r pass.
*PROVEN* (this is a definition; implementations in `scratch/once-r/core.py`
cross-checked against reference implementations and the identities below).

**Divergence of the four semantics.** For `[b/aa]` (replace `"aa"` by `"b"`;
*COMPUTATIONAL*, `test_sem.py`):

| input | L | R2L | once-l | once-r |
|---|---|---|---|---|
| `aaa` | `ba` | `ab` | `ba` | `ab` |
| `aaaa` | `bb` | `bb` | `baa` | `aab` |
| `aaaaaa` | `bbb` | `bbb` | `baaaa` | `aaaab` |

once-r agrees with R2L on strings with ≤ 2 pattern occurrences but not in
general (6 a's: `bbb` vs `aaaab`); once-l relates to L the same way. The
once-primitives differ from the replace-all primitives on *every* input with
≥ 2 occurrences.

**Mirror identities.** (*PROVEN*, verified on 3000 random instances each,
`test_sem.py`)

- **(M1)** `R2L(A,B,C) = rev(L(rev A, rev B, rev C))`.
- **(M2)** `[A/B]₁ᴿC = rev([rev A / rev B]₁ᴸ rev C)`; dually
  `[A/B]₁ᴸC = rev([rev A / rev B]₁ᴿ rev C)`.
- **(M3, calculus level)** Let `φ` map an expression to the expression with
  every constant reversed and Cat children swapped. Then
  `⟦E⟧_once-r(S⃗) = rev(⟦φ(E)⟧_once-l(rev S⃗))`. So a function `f` is
  once-r-reachable **iff** `rev∘f∘rev` is once-l-reachable; identically for
  the pair (L, R2L).

**What transfers without settling reversal.** From (M3):

- `reverse ∈ once-r ⟺ reverse ∈ once-l`, and
  `reverse ∈ L ⟺ reverse ∈ R2L` (since `rev∘reverse∘rev = reverse`).
  *PROVEN*. The cross-family statements (`reverse ∈ once-r` vs
  `reverse ∈ L`) do **not** transfer — reversal is exactly the missing bridge.
- The paper's `head, tail ∈ L` transfer to `lastchar = rev∘head∘rev ∈ R2L`
  and `droplast = rev∘tail∘rev ∈ R2L`. *PROVEN*. They do **not** transfer to
  once-r or once-l.
- `L ⊴ once-r ⟺ R2L ⊴ once-l` (conjugate both sides of the inclusion by
  reversal), and `once-l ⊴ once-r ⟺ once-r ⊴ once-l`. *PROVEN*. If
  additionally `reverse ∈ once-r`, then `L ⊴ once-r ⟺ R2L ⊴ once-r`, etc.
- `delete-rightmost-b = rev∘(delete-leftmost-b)∘rev`, so
  `delete-rightmost-b ∈ once-r` (one node) and its reachability status in
  once-l is the mirror of `delete-leftmost-b`'s status in once-r. All
  "left/right asymmetric" questions come in mirror pairs; proving one side
  settles the other.

---

## 2. Basic algebra (Section 2 of the paper, once-r edition)

Trivial three (all *PROVEN*, same statements as the paper, easier proofs):
**Identity Substitution** `[A/A]₁ᴿS = S` (`A ≠ ε`); **Direct Substitution**
`[A/B]₁ᴿB = A` (`B ≠ ε`); **Substitution Elimination** `B ⊄ S ⇒ [A/B]₁ᴿS = S`.

**Lemma (Suffix Substitution — once-r's replacement for Stepping-into).**
`A ≠ ε ⇒ [C/A]₁ᴿ(B·A) = B·C`. *PROVEN* — with no hypothesis on `B` at all:
every occurrence of `A` other than the suffix starts strictly before `|B|`,
so the *rightmost* occurrence is always the final `A`. (The paper's
Stepping-into `[C/A](AB) = C([C/A]B)` recurses on the remainder; the once-r
version is a single unconditional splice. This asymmetry powers everything in
§4.) Dual: `[C/A]₁ᴿ(A·B) = C·B` whenever the prefix is the only occurrence of
`A` (e.g. `A ⊄ B` and no straddler — checkable for constants).

**Lemma (Independent Substitution).** If `Γ(A)∩Γ(B) = ∅`, `Γ(A)∩Γ(C) = ∅`,
`C ≠ ε`, **and `B ≠ ε`**, then `A ⊂ [B/C]₁ᴿS ⟺ A ⊂ S`. *PROVEN* — simpler
than the paper's: the pass makes a single splice `S = XCY ↦ XBY`; an
occurrence of `A ≠ ε` in `XBY` cannot touch `B`'s positions (disjoint
alphabets), hence lies in `X` or in `Y`, both of which sit inside `S`; the
converse is symmetric (an occurrence of `A` in `S = XCY` cannot straddle `C`).
Note **the extra hypothesis `B ≠ ε` is necessary and the paper's own Lemma is
false without it**: with replacement `B = ε` (deletion), gluing creates
occurrences — `A = "aa"`, `B = ε`, `C = "b"`, `S = "aba"`:
`"aa" ⊂ [ε/b]("aba") = "aa"` but `"aa" ⊄ "aba"`. This counterexample works
verbatim against the paper's baseline greedy semantics, so the paper's
statement has a latent edge case (*erratum candidate*).

**Lemma (Double Substitution).** `X, Y ≠ ε`, `X ⊂ Y`, `Y` unbordered ⇒
`[X/Y]₁ᴿ[Y/X]₁ᴿZ = Z`. *PROVEN*, with a simpler proof than the paper's:
if `X ⊄ Z` then also `Y ⊄ Z` (as `X ⊂ Y`) and both passes are no-ops;
otherwise `Z = U·X·V` with `X ⊄ V` and `[Y/X]₁ᴿZ = U·Y·V =: W`. In `W`, the
occurrence of `Y` starting at `|U|` is the rightmost one: occurrences inside
`V` would contain an `X` inside `V`; occurrences starting at `|U|+j` (`j ≥ 1`,
straddling into `V`) force a proper border of `Y`; anything starting in `U`
starts earlier. Hence `[X/Y]₁ᴿW = U·X·V = Z`.

**Remark (the paper's counterexamples do not break once-r).** *COMPUTATIONAL*,
`test_exact.py`:
- `X = ba ⊂ Y = aba` (bordered), `Z = baabba`:
  `[Y/X]₁ᴿZ = baababa`, and `[X/Y]₁ᴿ(baababa) = baabba = Z` — the spurious
  straddling `aba` at position 3 loses to the true copy at position 4,
  because once-r takes the *rightmost* match.
- `X = a, Y = bb, Z = aba` (X ⊄ Y fails): round-trips too.
So for once-r, unborderedness is sufficient but **not necessary**.

**Theorem (exact characterization of the once-r round-trip).**
`[X/Y]₁ᴿ[Y/X]₁ᴿZ = Z` for **all** `Z` iff

1. `X ⊂ Y`, and
2. for every period `j ∈ [1, |Y|)` of `Y` there is **no admissible** `Q`
   beginning with `Y`'s length-`j` suffix, where `Q` is admissible iff
   `X ⊄ Q` and, for every period `j′ ∈ [1, |X|)` of `X`,
   `Q[:j′] ≠ X[|X|−j′:]`.

*Derivation* (sufficiency *PROVEN* by the case analysis above; the necessity
direction exhibits `Z = P·X·Q` from an admissible `Q`, creating a straddling
`Y`-occurrence at `|P|+j` that wins the rightmost race and mis-replaces):
`Z = P·X·Q` with `X ⊄ Q` gives `W = P·Y·Q`; the round-trip fails exactly when
the rightmost `Y` in `W` is a straddler starting at `|P|+j`, which needs `j`
to be a period of `Y` and `Q[:j] = Y[|Y|−j:]`; the two admissibility
conditions exclude `Q`'s that either cannot occur (they contain `X`) or whose
mis-replacement coincidentally reproduces `Z`.
*COMPUTATIONAL*: confirmed exactly on all 900 pairs `X, Y` over `{a,b}` with
`|X|,|Y| ≤ 4`, against **all** `|Z| ≤ 7 — the predictor and the round-trip
agree on every pair. Census: the paper's condition (`X ⊂ Y`, `Y` unbordered)
holds on 72 pairs; the exact condition on 148 — i.e. the exact condition is
strictly weaker, and the paper's hypotheses are not necessary for once-r.

**Lemma (Commutation).** If `Γ(B₁)∩Γ(B₂) = ∅`, `Γ(A₁)∩Γ(B₂) = ∅`,
`Γ(A₂)∩Γ(B₁) = ∅`, and `A₁, A₂ ≠ ε`, then
`[A₂/B₂]₁ᴿ[A₁/B₁]₁ᴿC = [A₁/B₁]₁ᴿ[A₂/B₂]₁ᴿC`. *PROVEN*: the two patterns never
share a position, replacing one does not disturb the other's occurrence set,
and inserted text cannot create the other pattern (disjoint alphabets) — the
nonemptiness of replacements rules out deletion-gluing. *COMPUTATIONAL*:
0 failures / 4080 fully-disjoint-alphabet cases (`|C| ≤ 7`); also 0/2032 for
the weaker "disjoint patterns, shared replacement alphabet" case. **Empty
replacements break commutation even with fully disjoint alphabets**:
`[ε/aa]` then `[ε/b]` on `aba` gives `aa` vs `ε` (124 such failures in the
disjoint-alphabet enumeration, all involving an empty replacement). Smallest
same-alphabet failure with nonempty replacements: `[a/b]` vs `[b/a]` on `a`
(`b` vs `a`).

**Lemma (k-fold iteration).** If `Γ(A)∩Γ(B) = ∅` and `B ≠ ε`, then `k`
successive applications of `[A/B]₁ᴿ` effect the simultaneous replacement of
the `k` rightmost non-overlapping occurrences of `B`, chosen greedily from the
right. *PROVEN* (each application takes the rightmost surviving occurrence;
inserted `A`s, having disjoint alphabet, neither create nor destroy `B`s) and
*COMPUTATIONAL* (all `|C| ≤ 7`, `A,B` of length ≤ 3, `k ≤ 3`: 0 mismatches).
The tempting weaker hypothesis "`B ⊄ A`" is **REFUTED**: `[a/aa]₁ᴿ` twice on
`aaa` gives `a`, but the simultaneous-2-rightmost gives `aa` — the first
pass's inserted text is re-matched by the second pass (exactly the re-matching
hazard the task brief warns about).

---

## 3. Structural invariants

Throughout, `E` is a fixed once-r expression, `S⃗` inputs, `L_E` = number of
variable leaves of `E`, `C_E`-type constants depend only on `E`.

**Theorem (Occurrence Bound).** For `u ≠ ε`,
`#u(⟦E⟧(S⃗)) ≤ L_E · max_i #u(S_i) + C_E(u)`, with
`C_E(u) = Σ_constants #u(W) + 2|u|·#Subst(E) + |u|·#Cat(E)`.
*PROVEN*. Key step: one pass is a single splice
`T = T₀BT₁ ↦ T₀AT₁`, and a splice satisfies
`#u(T₀AT₁) ≤ #u(T) + #u(A) + 2|u|` (occurrences of `u` straddling the two
cut points are lost, those inside `A` are gained, at most `2|u|` straddlers).
*COMPUTATIONAL*: 2833 random defined evaluations, 0 violations (`test_bounds.py`).

**Theorem (Linear Length).**
`|⟦E⟧(S⃗)| ≤ L_E · max_i |S_i| + K_E` with `K_E` = total length of the
constants of `E`. *PROVEN* by structural induction: `|[R/P]E| ≤ |E-value| +
|R-value|` because a splice replaces `|P| ≥ 1` characters by `|R|`. This is a
**strictly stronger growth ceiling than the baseline's**
`C_E·(1+M)^{deg E}` (paper's Length Bound): once-r outputs grow at most
*linearly* in the input length, with slope = number of variable leaves.
*COMPUTATIONAL*: 2833 evaluations, 0 violations.

**Theorem (Block/Track Decomposition).** Each output character of
`⟦E⟧(S⃗)` can be tagged with the leaf occurrence (variable or constant at a
fixed tree position) and position inside that leaf's value it came from.
Then (T1) each leaf occurrence contributes its characters **in source
order** (its contribution is a subsequence of its value), and (T2) the
contributions split into `d` intervals with
`Σ_leaves d ≤ #leaves(E) + 2·#Subst(E)`.
*PROVEN* (splices never reorder; each pass adds at most 2 cut points and the
replacement's own budget; Cat adds none). *COMPUTATIONAL*: origin-annotated
evaluator on 2944 defined evaluations — 0 order violations, 0 interval-count
violations, worst-case ratio `total/bound = 1.00` (tight) (`test_blocks.py`).
Consequence: the output is a shuffle of at most `#leaves + 2#Subst`
"reads" — interval-subsequences of leaf values — plus constant material.

**Limit of the invariants (COMPUTATIONAL).** These invariants separate many
functions (§4) but **do not separate `reverse`**. Exact minimum-interval
feasibility (`test_shuffle.py`, `test_minint.py`, DP over read states):
`reverse(X)` is a shuffle of only **2** reads with ≤ 2–4 total intervals for
random binary strings of length 8–10; 2 intervals for the run families
`(aⁿb)^k` and `(ab)^k`; and for the superincreasing-run family
(`X = a^{n₁}b…a^{n_k}b`, `n_{i+1} = 4n_i+1`) `t = 2` reads need only
2, 2, 2, 2, 3 intervals for `k = 1..5`. Two attempted strengthenings were
**computationally REFUTED** (per-read `b`-accounting: `b`s are
indistinguishable; full-run block accounting: reads may take partial runs,
e.g. `4 = 2+2`). Conclusion: *no invariant currently known separates
`reverse` from once-r* — the mirror of the paper's own open problem.

---

## 4. Toolkit

### 4.1 What once-r CAN build (all PROVEN; verified on 4000 random
instances each, `test_sel.py`)

The engine is the **zipper**, two consecutive once-r passes on the constant
`ba` (sizes below are core sizes; `E = [W/a]₁ᴿ(V·a) = V·W` whenever the last
character is the appended `a` — it always is, by the Suffix Substitution
lemma):

| function | once-r expression | size |
|---|---|---|
| `cat(X,Y) = X·Y` | `[Y/a]₁ᴿ[X/b]₁ᴿ(ba)` | 7, **core** |
| `dup(X) = X·X` | `[X/a]₁ᴿ[X/b]₁ᴿ(ba)` | 7, core |
| append const | `[X/a]₁ᴿ(ab) = X·b` | 4 |
| prepend const | `[X/a]₁ᴿ(ba) = b·X` | 4 |
| whole-replace | `[R/X]₁ᴿX = R` (`X ≠ ε`) | 4 |
| delete-rightmost-`b` | `[ε/b]₁ᴿX` | **4** |
| unary doubling | `[bb/b]₁ᴿ[X/b]₁ᴿX : b^m ↦ b^{2m}` | 7 |

Proof of `cat`: pass 1 `[X/b]₁ᴿ` on the constant `ba` replaces the rightmost
`b` (position 0) — `X·a`; pass 2 `[Y/a]₁ᴿ` on `X·a` replaces the rightmost
`a`, which is the final character regardless of `X`'s content — `X·Y`.

**Theorem (concatenation is eliminable).** Since `cat` is core-reachable in
2 passes, every with-concat once-r expression converts to a core one — the
mirror of the paper's `thm:core`, at a fraction of the cost (the baseline's
`cat` needs the full `enc`/`dec` marker machinery). *PROVEN*.

**Single-character escape (enc₁/dec₁).**
`enc₁ = [xc/b]₁ᴿ` (escape the rightmost `b`), `dec₁ = [c/xc]₁ᴿ`:
`dec₁∘enc₁ = id` by the Double Substitution lemma (`X = c ⊂ Y = xc`, `xc`
unbordered for `x ≠ c`). *PROVEN*. Note `enc₁` escapes **one** character, not
all — see §4.2.

**Iterated doubling (rep-like growth).** Composing the doubling expression
with itself `k` times maps `b^m ↦ b^{2^k m}`; the composed expression has
`2^k` variable leaves and size `Θ(2^k)`. By the Linear Length theorem this is
**optimal**: any once-r expression mapping `b^m ↦ b^{2^k m}` (all `m`) needs
`L_E ≥ 2^k`, hence size `≥ 2^k`. *PROVEN*. Contrast: the baseline reaches
`X^{|X|}` (quadratic growth) with a 2-pass expression of fixed size; once-r
needs exponentially growing size even to reach coefficient `2^k` in unary.

### 4.2 What once-r CANNOT build

**PROVEN separations** (via Occurrence Bound / Linear Length; all carry over
to the with-concat calculus since the invariants cover Cat):

| function | input family | separating count |
|---|---|---|
| replace-all `[a/b]` | `b^m ↦ a^m` | `#_{aa}`: 0 ↦ m−1 |
| full `enc` (`b ↦ xb`, all) | `b^m ↦ (xb)^m` | `#_{xb}`: 0 ↦ m |
| `σ^{|X|}` | `b^m ↦ a^m` | `#_a`: 0 ↦ m |
| `X^{|X|}` | `b^m ↦ b^{m²}` | length: m vs `L·m + K` |
| double-each-char | `a^{n₁}b…a^{n_k}b` (no `bb`) | `#_{bb}`: 0 ↦ k |

Each violates `#u(⟦E⟧) ≤ L_E·max #u(S_i) + C_E` or the linear length bound
with the input counts on the left being 0 (so the bound degenerates to the
constant `C_E`). In particular **once-r cannot express the paper's `enc`**,
and therefore none of the baseline constructions that pass through it
(border-decoded equality, `head`, `tail`, `if`, `rep_n`) carry over.

**CONJECTURE (unreachable), with exhaustive-search evidence.** The following
are absent from *all* once-r core expressions of size ≤ 7 and all
with-concat expressions of size ≤ 7 over `Σ = {a,b}`, constants ≤ 2
(239,688 expressions, 147,528 total; `search_oncer.py`, `test_sel.py`), and
from all constant-pattern pipelines of depth ≤ 4 (1,192,366 distinct
functions; `search_const.py`), and (for `tail`, `eq`) from a 6-round beam
search with pools of 15k–20k expressions (`search_beam.py`, best score
36/63 for `tail`, 240/256 for `eq` — no better than a constant):

- `head`, `tail` — first-character extraction / removal.
- `lastchar`, `droplast` — last-character analogues.
- `eq` — equality test.
- `if` / selection: even the anchored tests
  `sel-ends-b : X ↦ "a" if X ends with b else "b"` and
  `sel-starts-a : X ↦ "a" if X starts with a else "b"` are absent.
- `delete-leftmost-b` (once-l's one-node function) — absent from all
  once-r pipelines of depth ≤ 3 over the rich form vocabulary
  {constants ≤ 2, X, Xc, cX} (578,923 distinct functions; `search_xfamily.py`).
- `reverse` — absent from all of the above.

**Why destructuring fails (informal).** once-r edits the *rightmost* match of
a pattern; `head`/`tail` require deleting a *left-anchored, variable-length*
region ("all but the first character"). The only variable-length deletions
available are `[ε/P]` with `P` a computed pattern; to make `P` cover "all but
the first character" one must already be able to compute that suffix — which
is `droplast`-of-`reverse`-flavored, i.e. exactly as hard. The destructive
toolkit is circular in a way the baseline's `enc`-based escape hatch breaks
for L (from the left) — and once-r provably cannot run that escape hatch
(§4.2, `enc` separation). No proof of unreachability is known for any of
these; cf. §7.

**Calibration of the searches.** The same enumerations *do* find everything
reachable at these sizes: `identity`, `append-b`, `prepend-b`, `XX`,
`delete-rightmost-b` (all constructions of §4.1), `cat` at binary core size 7
(exactly the two zipper variants `[X1/a]₁ᴿ[X0/b]₁ᴿ(ba)` and
`[X1/b]₁ᴿ[X0/a]₁ᴿ(ab)`); for the other semantics their natives
(`replace-all-b->a`, `delete-all-b` for L and R2L at size 4;
`delete-leftmost-b` for once-l at size 4; `cat` for once-l at core size 7 via
the mirror zipper `[X0/a]₁ᴸ[X1/b]₁ᴸ(ab)` — provable by M3, and found).
Notably `cat` and `eq` are **absent from all L and R2L expressions of
size ≤ 7** — the baseline needs its full `enc`-machinery for `cat` — while
once-r and once-l get `cat` in 2 passes. The absences above are therefore
calibrated but only bound small expressions.

---

## 5. Expressibility vs the baseline L

**(a) Can once-r express L? — No. PROVEN.**
`[a/b]` (replace-all) is once-r-unreachable (§4.2, `#_{aa}` on `b^m`), so
`L ⊄ once-r` strictly: **`L ⊴ once-r` is REFUTED.** The same argument kills
any L-function whose output multiplies an occurrence count absent from the
input (`enc`, `σ^{|X|}` via single counts, `rep_n` insertions...).

**(b) Can L express once-r? — Conjecturally no.**
The single-node once-r function `delete-rightmost-b` is **absent** from:

- all L **core** expressions of size ≤ 7 (98,824 expressions) and all
  with-concat expressions of size ≤ 7 (140,872) over `Σ = {a,b}`,
  constants ≤ 2 (`search_other.py`); the identical statement holds for R2L
  (its enumerations coincide with L's on all targets);
- all L and R2L **pipelines** of depth ≤ 3 over the form vocabulary
  {constants ≤ 2, X, Xc, cX} — 514,116 distinct depth-3 functions each
  (`search_xfamily.py`); the same enumeration finds the L/R2L-natives
  (`replace-all`, `delete-all-b`) at depth 1, and finds `head`, `tail`,
  `lastchar`, `droplast`, `reverse`, `swap`, `delete-leftmost-b`,
  `delete-rightmost-b` all absent — i.e. even L's own paper-built toolkit
  functions do not appear at this scale, so the datum is calibrated but
  bounded.

**CONJECTURE:** `once-r ⊴ L` is false — `delete-rightmost-b ∉ L`. Rationale:
L's passes replace *all* occurrences and scan left-to-right without
rescanning; every mechanism the paper builds (enc, markers, borders) is
left-anchored, and "the rightmost b" is not an L-definable region without a
right-anchored primitive or reversal. By mirror-symmetry (M3) the equivalent
statement is `delete-leftmost-b ∉ R2L`. (Note the parallel open problem
`delete-leftmost-b ∈ L?` — same flavor; the paper's toolkit does not
obviously build it either: all its deletions are unmarked or left-greedy.)

**(c) once-l vs once-r.** By (M3) the two calculi are reversal-conjugate, so
*nothing provable separates them without settling reversal*. Computationally:
`delete-leftmost-b` is absent from all once-r expressions of size ≤ 7 and
once-r depth-≤3 pipelines (above), and `delete-rightmost-b` is absent from all
once-l expressions of size ≤ 7 (`search_other.py`, once-l section: among the
targets only `identity`, `delete-leftmost-b`, and `cat` are found) *and* from
all once-l depth-≤3 pipelines over the rich form vocabulary (578,923 distinct
functions — the exact mirror of the once-r enumeration, which likewise misses
`delete-leftmost-b`; `search_xfamily.py`).
**CONJECTURE:** `once-r ⊴ once-l` and `once-l ⊴ once-r` are both false (the
pair {`delete-rightmost-b`, `delete-leftmost-b`} are mutual witnesses), making
once-r and once-l *incomparable*. Note this is exactly the reversal
conjecture localized to a single function: `delete-rightmost-b =
rev∘delete-leftmost-b∘rev`, and by M3 the two non-inclusions are *equivalent*
statements.

**(d) r2l vs once-r.** `R2L` is `rev∘L∘rev` (M1). `R2L ⊴ once-r` is REFUTED
(its `replace-all` has the same `#_{aa}` separation). `once-r ⊴ R2L`:
**CONJECTURE false** (`delete-rightmost-b` absent from all R2L core/with-concat
size ≤ 7 — the R2L enumeration mirrors L's — and from R2L depth-≤3 pipelines).
Provable without reversal: `R2L ⊴ once-r ⟺ L ⊴ once-l` (M3); and `lastchar`,
`droplast ∈ R2L` (conjugates of the paper's `head`, `tail`) — the functions
once-r itself seems unable to reach.

**(e) The reverse bridge, stated precisely.** All cross-family inclusions
among {L, once-l} and {R2L, once-r} factor through reversal:
`L ⊴ once-r ⟺ R2L ⊴ once-l` (PROVEN). If `reverse ∈ once-r` then
`L ⊴ once-r ⟺ R2L ⊴ once-r` — and since `L ⊴ once-r` is already REFUTED,
that would REFUTE `R2L ⊴ once-r` too. Without settling reversal, each
"horizontal" claim in the web must be (and here: is) established separately.

**Summary web** (all four calculi, over any `|Σ| ≥ 2`):

- `L ⊴ once-r` — **REFUTED** (`replace-all`).
- `R2L ⊴ once-r` — **REFUTED** (same witness).
- `once-l ⊴ once-r` — **CONJECTURE false** (`delete-leftmost-b`).
- `once-r ⊴ L`, `once-r ⊴ R2L`, `once-r ⊴ once-l` — **CONJECTURE false**
  (`delete-rightmost-b`).
- Within-family: `cat`, `dup`, append/prepend, whole-replace all once-r-
  reachable (PROVEN); `head/tail/eq/if/enc/reverse` not (mixed PROVEN for
  enc; CONJECTURE for the rest).

---

## 6. Complexity

**Growth.** once-r-reachable functions satisfy
`|f(S⃗)| ≤ L_E·max|S_i| + K_E` — **linear** (PROVEN, §3), versus the
baseline's polynomial `C(1+M)^{deg}`. The bound is tight at both ends:
`dup` realizes slope 2 with `L_E = 2`; iterated doubling realizes any slope
`2^k` at size `Θ(2^k)`, and no smaller expression can (§4.1). Functions of
superlinear growth (`X^{|X|}`, `σ^{|X|}` by occurrence count, `enc`) are
unreachable (PROVEN). So: **the once-r calculus computes exactly
linear-growth-limited work, and pays leaf-for-coefficient.**

**Time.** Evaluating a once-r expression is a pipeline of `k` passes, each a
rightmost-match (find with `rfind`, linear in the current length) plus a
splice; every intermediate has length `≤ L_E·M + K_E` by the Linear Length
theorem. Total time `O(k·(L_E·M + K_E)·(pattern+replacement bound))` —
polynomial, indeed **near-linear**, in the input size. *PROVEN* (mirror of
the paper's Soundness theorem, with a stronger length invariant; the
baseline needs the degree bookkeeping, once-r does not).

**Contrast with the baseline.** The baseline sits strictly higher on the
growth ladder (quadratic `X^{|X|}` reachable in fixed size); once-r is pinned
to the bottom (linear) yet still affords `cat` at size 7 — a construction the
baseline only achieves through its polynomial-growth `enc` machinery. The two
calculi incomparably trade growth for anchoring.

---

## 7. Open problems

1. **Is `reverse` once-r-reachable?** The block/interval invariants provably
   (computationally) do not separate it (§3). By (M3) this is *equivalent* to
   `reverse` being once-l-reachable, and *not equivalent* to the baseline's
   own reversal question without a bridge. The most interesting open problem
   of this variant.
2. **`head`/`tail`/`lastchar`/`droplast`/`eq`/`if` ∈ once-r?** Conjectured
   no; absent from all enumerations tried (≤ 7 exhaustive, depth-4 pipelines,
   beam search). A proof needs a new invariant — the occurrence and interval
   invariants do not separate `tail` either (its reads structure is trivial:
   1 read, 1 interval minus a variable-length prefix... the obstruction is
   precisely that *deleting* a left-anchored variable region is not a
   "read" question).
3. **`delete-rightmost-b ∈ L`? `∈ once-l`? `∈ R2L`?** Conjectured no
   (§5b,c,d) — would make once-r strictly incomparable with all three
   sibling calculi. Note the L-side needs a *lower-bound technique for L*,
   which the baseline paper also lacks (its only separation is growth-based).
4. **Exact characterization of once-r-reachable functions.** With constant
   patterns, each pass is a rightmost-anchored rational-transduction-like
   map; the class is closed under composition and (core-)concatenation,
   linearly bounded, and contains no left-anchored destructuring. Is it a
   known class? Is expression equivalence decidable (paper's open problem 3,
   mirrored)?
5. **Optimality of the toolkit.** Is `cat` achievable at core size < 7?
   (Size-4 expressions are single passes — no; so 7 is optimal.) Is
   `delete-rightmost-b`+`cat` together enough to generate all *reachable*
   functions with few passes (a normal-form/pass-count hierarchy)?
6. **Alphabet effects.** The zipper needs one constant with two distinct
   characters and works over any `|Σ| ≥ 2`. Over `Σ = {a}` (unary), every
   once-r pass is a length map `m ↦ m + c` or identity, so the reachable
   functions are exactly `m ↦ m + c` — the calculus collapses. Does a third
   letter ever add power beyond constant-factor size (cf. the paper's
   alphabet-sensitive hypotheses)?
7. **The erratum.** The paper's Independent Substitution lemma needs
   `B ≠ ε` (empty replacement glues new occurrences; counterexample in §2).
   Verify whether the downstream uses of that lemma in `main.tex` ever
   instantiate it with an empty replacement.

---

## 8. Relations summary

`EXPR: <source> ⊴ <target> STATUS: <PROVEN|COMPUTATIONAL|CONJECTURE|REFUTED> — <justification>`

```
EXPR: cat ⊴ once-r(core)            STATUS: PROVEN — cat(X,Y)=[Y/a]₁ᴿ[X/b]₁ᴿ(ba), 2 passes; concat eliminable (zipper, Suffix Substitution lemma).
EXPR: dup/append/prepend/whole-replace ⊴ once-r STATUS: PROVEN — one/two-pass zipper instances, verified on 4000 random inputs.
EXPR: delete-rightmost-b ⊴ once-r    STATUS: PROVEN — [ε/b]₁ᴿX, a single pass (1 Subst node).
EXPR: enc₁/dec₁ round-trip ⊴ once-r  STATUS: PROVEN — Double Substitution with X=b ⊂ Y=xb, xb unbordered.
EXPR: unary doubling b^m↦b^{2m} ⊴ once-r STATUS: PROVEN — [bb/b]₁ᴿ[X/b]₁ᴿX; 2^k iteration needs and achieves size Θ(2^k) (Linear Length).
EXPR: replace-all [a/b] ⊴ once-r     STATUS: REFUTED — Occurrence Bound: #_{aa}(a^m)=m−1 from inputs b^m with #_{aa}=0.
EXPR: full enc/dec ⊴ once-r          STATUS: REFUTED — Occurrence Bound: #_{xb}((xb)^m)=m from inputs b^m with 0.
EXPR: σ^{|X|} ⊴ once-r               STATUS: REFUTED — Occurrence Bound: #_a(a^m)=m from b^m with 0.
EXPR: X^{|X|} ⊴ once-r               STATUS: REFUTED — Linear Length: m² > L_E·m+K_E for large m.
EXPR: double-each-char ⊴ once-r      STATUS: REFUTED — Occurrence Bound: #_{bb} grows on inputs with no bb.
EXPR: L ⊴ once-r                     STATUS: REFUTED — replace-all [a/b] is L-reachable (size 4) and once-r-unreachable.
EXPR: R2L ⊴ once-r                   STATUS: REFUTED — same witness (R2L also computes replace-all).
EXPR: once-r ⊴ L                     STATUS: CONJECTURE — delete-rightmost-b absent from all L core/with-concat exprs ≤ 7 and 514k depth-3 pipelines; no proof.
EXPR: once-r ⊴ R2L                   STATUS: CONJECTURE — same witness absent from R2L enumerations (mirror of L's).
EXPR: once-l ⊴ once-r                STATUS: CONJECTURE — delete-leftmost-b absent from all once-r exprs ≤ 7 + depth-3 pipelines; equivalent (M3) to once-r ⊴ once-l via reversal.
EXPR: once-r ⊴ once-l                STATUS: CONJECTURE — delete-rightmost-b absent from all once-l exprs ≤ 7 and 578k depth-3 pipelines; mirror statement.
EXPR: head ⊴ once-r                  STATUS: CONJECTURE — absent from 239,688 exprs ≤ 7, depth-4 constant pipelines, beam search; no invariant separates it.
EXPR: tail ⊴ once-r                  STATUS: CONJECTURE — same evidence (beam best 36/63); right-anchored calculus cannot delete left-anchored variable regions.
EXPR: lastchar ⊴ once-r              STATUS: CONJECTURE — absent from all enumerations; contrast: PROVEN ∈ R2L as rev∘head∘rev.
EXPR: droplast ⊴ once-r              STATUS: CONJECTURE — absent from all enumerations; contrast: PROVEN ∈ R2L as rev∘tail∘rev.
EXPR: eq ⊴ once-r                    STATUS: CONJECTURE — absent from all enumerations; beam search never beats the constant 'b' (240/256).
EXPR: if/selection ⊴ once-r          STATUS: CONJECTURE — even anchored tests sel-ends-b/sel-starts-a absent from 239,688 exprs ≤ 7.
EXPR: reverse ⊴ once-r              STATUS: CONJECTURE — absent everywhere searched; interval/read invariants computationally shown NOT to separate reverse; equivalent to reverse ⊴ once-l (M3).
EXPR: L ⊴ once-r ⟺ R2L ⊴ once-l      STATUS: PROVEN — reversal conjugacy of the two inclusion statements (M3).
EXPR: reverse ⊴ once-r ⟺ reverse ⊴ once-l STATUS: PROVEN — rev∘reverse∘rev = reverse (M3); cross-family (vs L) transfer unknown without the bridge.
EXPR: lastchar ⊴ R2L                 STATUS: PROVEN — rev∘head∘rev with head ∈ L (paper) and M3.
EXPR: droplast ⊴ R2L                 STATUS: PROVEN — rev∘tail∘rev with tail ∈ L (paper) and M3.
```

---

*All scripts referenced live in `/home/cc/projects/meow-lang/docs/proof/research/scratch/once-r/`:
`core.py` (semantics + calculus), `test_sem.py` (semantics/mirror identities),
`test_exact.py` (exact double-substitution characterization + commutation),
`test_algebra2.py` (k-fold iteration, weak-hypothesis refutation),
`test_bounds.py` (occurrence/length bounds), `test_blocks.py` (block
decomposition), `test_shuffle.py`, `test_minint.py` (read/interval
feasibility for reverse), `search_oncer.py` (exhaustive once-r ≤ 7),
`search_other.py` (exhaustive L/R2L/once-l ≤ 7), `search_xfamily.py`
(depth-3 pipelines, four semantics), `search_const.py` (depth-4/5
constant-only pipelines), `search_beam.py` (beam searches), `test_sel.py`
(selection search + toolkit verification).*

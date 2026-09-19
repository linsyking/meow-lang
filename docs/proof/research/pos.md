# pos — positional (index-aware) replacement: an expressivity study

Variant family **pos**. Baseline for comparison: the paper's calculus **L** (Definition 1: `[A/B]C`
= replace every occurrence of `B` by `A`, left-to-right, leftmost-first, non-overlapping, never
rescanning inserted text). The once-family (another agent's variant) is compared against where noted.

**Method.** Every nontrivial claim below is labeled exactly one of:

- **PROVEN** — careful proof written out (all proofs also verified computationally on small domains),
- **COMPUTATIONAL** — exhaustively verified on the stated finite domain (typically: enumeration of
  all strings up to length 5–6 over |Σ| = 2, patterns to length 3, indices to 4; or exhaustive BFS
  over an enumerated expression space to a stated depth),
- **CONJECTURE** — evidence (computational or structural) but no proof,
- **REFUTED** — counterexample or separation proof.

`X ⊴ Y` means: every (total) function reachable in calculus `X` is reachable in `Y`.
Scripts: `docs/proof/research/scratch/pos/` (`poslib.py`, `verify_constructions.py`,
`search_pos.py`, `search_L.py`, `search_exotics.py`, `search_pos_lit_main.py`). All construction
checks in `verify_constructions.py` report `FAILURES: 0`.

Notation: `Σ` alphabet, `|S|` length, `S[i]` the i-th character (0-based), `#c(S)` the number of
occurrences of char `c` in `S`, `ε` the empty string. `occ(S, B)` = list of start positions of the
greedy leftmost non-overlapping occurrences of `B` in `S` (exactly the scan of Definition 1 in the
paper, stopped at each hit).

---

## 0. Executive summary

pos replaces *all* occurrences at once (L) by *one addressed* occurrence at a time. The address is
either an absolute index (`setAt(i, c)`) or an occurrence rank (`repOcc(k, B, A)`). One-line summary
of what happens:

1. **pos is a strict sub-calculus of "one edit at a time"** — every pos node performs at most one
   contiguous-site edit. This yields a sharp invariant (Theorem B1, the *single-site alphabet
   bound*): on inputs avoiding a character `c`, a pos term can introduce at most `C_E` copies of
   `c`, where `C_E` counts the `c`'s in the term's constants. **PROVEN.** It kills
   letter-changing replace-all (e.g. `[b/a]`) and `enc` in *every* pos fragment (including
   computed patterns, replacements, indices, and concat).
2. **pos output length is at most linear** (Theorem B2): `X ↦ X^{|X|}` (quadratic duplication,
   reachable in L) is unreachable. **PROVEN.** Hence `L ⊴ pos` is **REFUTED** on every alphabet.
3. **The other direction is exactly the once-hinge**: `setAt(i, c) ∈ L` **PROVEN** (explicit
   construction from the paper's eq/if/cat/head/tail machinery), and
   `repOcc(k,B,A) = once_l(B,M)^k ∘ once_l(B,A) ∘ once_l(M,B)^k` **PROVEN** (fresh marker `M`).
   Therefore **`pos ⊴ L ⟺ once_l ∈ L`** (Theorem H) — the same open hinge that governs the
   once-family. All my L-side searches (literal ≤ 4 nodes, macro ≤ 3 nodes, 2-var computed ≤ 3
   nodes) failed to find `once_l`: **CONJECTURE: no.**
4. pos still reaches a real toolkit: `tail` (2 literal nodes, every alphabet incl. |Σ| = 1),
   `head` (in pos_concat via a scaffold construction; **not** in pos_lit — bounded-deletion
   lemma), `char_j`, `prefix_j`, joins of computed characters, `setAt`-last via computed indices,
   and — on the unary alphabet — *replace-all-with-growth* `[a^j/a] ∈ pos_concat` **PROVEN**,
   giving a genuine alphabet-size dichotomy: replace-all is pos-unreachable for |Σ| ≥ 2 (alphabet
   bound) yet pos-reachable in its growing variants for |Σ| = 1.
5. Complexity: evaluation is polynomial (indeed near-linear per node); output size is at most
   linear. Nothing breaks poly-time; pos is *strictly more parsimonious* than L, which can write
   quadratic-size outputs.

---

## 1. Semantics

### 1.1 The primitives

**Definition 1 (setAt).** `setAt(i, c, S) = S[:i] + c + S[i+1:]` if `0 ≤ i < |S|`; otherwise `S`
(the identity).

*Edge-case decision and justification.* Out-of-range writes are identity, not errors, not clamping,
not extension. Reasons: (a) **totality** — the paper's `[A/B]` is total (for `B ≠ ε`), and the
paper's framework studies total reachable functions; a partial setAt would import definedness
conditions foreign to the baseline; (b) **no length smuggling** — extending the string to reach
index `i` would let a *constant* index create unbounded length (`setAt(n, c, ε)` would have length
n+1), destroying the linear-growth theorem below; clamping (write at the last position) is a less
canonical reading of "address i" and is anyway expressible when wanted (see setAt-last, §3.6);
(c) it matches the register-addressing intuition: writing to a nonexistent register changes nothing.

**Definition 2 (occurrence discipline).** `occ(S, B)` for `B ≠ ε` is computed by the greedy scan:
sweep left to right; whenever the current position starts an `S`-factor equal to `B`, record it and
jump past it (occurrences are leftmost-first and non-overlapping). This is *exactly* the scan of the
paper's Definition 1, so pos and L agree on what an "occurrence" is; pos only stops at a chosen hit.

**Definition 3 (repOcc).** `repOcc(k, B, A, S)`: let `O = occ(S, B)` (requires `B ≠ ε`). If
`|O| ≥ k+1`, delete the occurrence at `O[k]` (length `|B|`) and insert `A` in its place — a single
contiguous-site edit, with **no rescanning** of the inserted text. If `|O| ≤ k`, the result is `S`
(the identity). `B = ε` is **undefined** (matching the paper's exclusion of empty patterns; also
forced: infinitely many occurrences otherwise).

*Edge-case justification.* "Identity when insufficient occurrences" mirrors both Definition 1 and
the paper's design philosophy (a substitution that finds nothing changes nothing); "no rescan"
matches the paper's never-rescan-inserted-text convention; the k-th occurrence is 0-based and
counted in scan order (leftmost-first), so `repOcc(0, B, A)` is precisely the once-replacement
`once_l(B, A)` studied by the once-family agent. Note the rank is *re-indexed after each edit*:
`repOcc(0,a,b)²` on `"aaaa"` = `"abba"` (the second application addresses the *new* first
occurrence), not `"bbaa"` — see Lemma A4 for when iteration equals replace-first-m.

**Definition 4 (how the index enters).**
- **(a) literal (primary):** `i`, `k` are numerals in the term — the analogue of the paper's
  constant patterns. This is the variant studied most fully below.
- **(b) computed (secondary):** `setAtI(E_idx, c, S)` with index `|⟦E_idx⟧|`, and
  `repOccI(E_idx, B, A, S)` with rank `|⟦E_idx⟧|`. Length is the only number a string calculus
  has; the numeral `k` is the special case `E_idx = σ*ᵏ` (a constant of length `k`). The computed
  fragment is **pos_idx**.

**Definition 5 (fragments).**
- `pos_lit`: indices/k literal; pattern `B`, replacement `A`, character `c` are string constants.
- `pos_core`: as pos_lit but `B`, `A`, `c` are arbitrary sub-terms (computed values; the setAt
  character sub-term must evaluate to a single character, else undefined); indices/k still literal;
  **no concat**.
- `pos_concat` = pos_core + `cat`.
- `pos_idx` = pos_concat + computed indices/k (as in Def. 4b). "pos" unqualified = the full
  calculus pos_idx.

**Definition 6 (terms, denotation, reachability).** Terms are trees over `x_i` (variables),
constants, `cat`, `setAt`/`setAtI`, `repOcc`/`repOccI`, mirroring the paper's Section 3. Denotation
`⟦E⟧ : (Σ*)^n → Σ*` is the evident bottom-up evaluation (a sub-term's value is computed once, from
the *variables*, never from the current mutated text — so pos has the same "no feedback" discipline
as L). A term may be partial (empty pattern value, or a setAt character value of length ≠ 1, or a
repOccI rank/ index … all give "undefined" on that input); a function is **reachable** if it is the
*total* denotation of some term. In pos_lit, every term whose literal patterns are nonempty is
total.

**Remark (a deliberate partiality).** `repOcc(0, ε, X, X)` (computed pattern = whole input,
replacement ε) equals `ε` for `X ≠ ε` but is undefined at `X = ε` (empty pattern). So "delete
everything" is *not* a total pos function this way — on |Σ| = 1 the function `X ↦ ε` is instead
the constant `ε`, trivially reachable. This ε-edge (patterns built from `tail` go empty on short
inputs) is the recurring obstruction in §3–§4 and is the reason `head` needs a scaffold.

---

## 2. Basic algebra

Throughout, `E` ranges over pos terms; constants of `E` = the strings at its constant leaves.

### 2.1 Structure lemmas

**Lemma A1 (pipeline normal form).** Every pos_lit / pos_core term is a composition
`n_m ∘ … ∘ n_1` of single nodes applied to a variable or constant (no binding, no duplication).
PROVEN — immediate from Def. 5 (the only interesting normal forms live in pos_concat, where cat
makes the term a DAG-like combination of pipelines).

**Lemma A2 (stepping-in / rank shift).** For `k ≥ 1` and `|P| ≥ 1`:
`repOcc(k, R, P, P·E) = P · repOcc(k−1, R, P, E)`, and `repOcc(0, R, P, P·E) = R·E`.
*Proof.* The greedy scan matches `P` at position 0 first (it is the leftmost possible start), then
resumes at `|P|`, scanning `E` afresh; so occurrence #j of `P` in `P·E` (j ≥ 1) is `|P|` plus
occurrence #(j−1) of `P` in `E`. Replacing the k-th and re-prefixing `P` gives the claim; k = 0
replaces `[0,|P|)` by `R`. ∎ (COMPUTATIONAL: verified for k ≤ 2, P ∈ {a, ab, ba}, R ∈ {ε, X, ab},
all E over {a,b} ≤ 3.)

**Lemma A3 (first-occurrence head extraction).** For every `V` with `|V| ≥ 2`:
`repOcc(0, ε, tail(V), V) = head(V)`.
*Proof.* `tail(V)` occurs at position 1; the only way an occurrence starts at 0 is
`V[:|V|−1] = V[1:]`, i.e. `V` is uniform (`c^n`), in which case the leftmost occurrence of
`c^{n−1}` starts at 0 and deleting `[0, n−1)` leaves `c = V[n−1] = head(V)`; if `V` is not
uniform the leftmost occurrence starts at 1 and deleting `[1, |V|)` leaves `V[0]`. ∎
(COMPUTATIONAL: all V, |V| ≤ 6 over {a,b}, ≤ 5 over {a,b,c}, ≤ 8 unary.) This one-node "delete all
but the first character" is the engine of the head construction in §3.3 — and it is exactly the
|V| ≤ 1 edge (tail(V) = ε: empty pattern ⇒ undefined) that makes totality hard.

**Lemma A4 (replace-prefix powers).** If `chars(A) ∩ chars(B) = ∅` and `|A| ≥ |B| ≥ 1`, then for
all m: `repOcc(0, B, A)^m = replace-first-m-occurrences`.
*Proof sketch (full induction in scratch).* Disjointness forbids any `B`-occurrence from touching
inserted `A`-material (a straddling `B` would have to contain a char of `A`); `|A| ≥ |B| ≥ 1` keeps
`A` nonempty, so adjacent surviving text never becomes adjacent across a deleted site. Hence after
each step the remaining occurrences of `B` are exactly the original ones, shifted; induction on m. ∎
(COMPUTATIONAL: m ≤ 3, B ∈ {a, b, ab, ba}, four A's, all S ≤ 5 over {a,b}.)
**REFUTED without the hypotheses:** `B = "ab"`, `A = ε`, `S = "aabb"`: one application gives
`"ab"` — the deletion joins an `a` and a `b` into a *new* occurrence (rank re-indexing). Also note
`|A| < |B|` with disjointness fails likewise. This is the pos analogue of the paper's caution that
substitutions interact with their own output; in L the interaction is *saturating* (all
occurrences at once, and `[a/b]` is idempotent), in pos it is *incremental* (each application
advances a rank).

**Lemma A5 (commutation).** `setAt(i,c) ∘ setAt(j,c') = setAt(j,c') ∘ setAt(i,c)` for `i ≠ j`
(distinct indices touch disjoint positions; out-of-range is identity). PROVEN — trivial. By
contrast, `setAt` does **not** commute with `repOcc` in general: `setAt(1,c) ∘ repOcc(0,"ab","X")`
on `"ab"` gives `"X"`, while `repOcc(0,"ab","X") ∘ setAt(1,c)` gives `"ac"` — the write destroys
the pattern occurrence. (COMPUTATIONAL; also a counterexample to any independent-substitution
analogue.)

### 2.2 What fails from the paper's Section 2 (saturation vs. rank)

| paper (L) | pos analogue | status |
|---|---|---|
| `[A/B]` total, all occurrences at once (saturation) | one occurrence per node (rank) | definitional |
| idempotence `[a/b]² = [a/b]` | `repOcc(0,a,b)² ≠ repOcc(0,a,b)`: `"aa" → "ba" → "bb"` | **REFUTED** (counterexample) |
| Independent substitution (disjoint alphabets commute) | setAt/repOcc do not commute (above) | **REFUTED** (counterexample) |
| Double Substitution Lemma | no analogue: second application addresses the *next* occurrence | — |

The conceptual difference worth recording: **L-nodes are saturating rewrites; pos-nodes are
resource-consumption steps.** Iterating a pos node m times consumes m occurrences (Lemma A4), so
pos naturally expresses "replace the first m", "replace the k-th", and fixed-position edits — but
never "replace all" (Theorem B1).

### 2.3 The three invariants

**Theorem B1 (single-site alphabet bound).** Let `E` be any pos term (any fragment up to the full
calculus: computed patterns, replacements, characters, indices, concat) and let `c` be a character.
Define `C_E` = total number of `c`'s in the constant leaves of `E` (tree syntax; shared subterms
would count per use). Then for every input tuple in which each component avoids `c`:
`#c(⟦E⟧(X⃗)) ≤ C_E`. **PROVEN.**
*Proof.* Induction on `E`. Variable: 0 (input is c-free). Constant: its own c-count. `setAt(i, r, E')`
(or setAtI): output differs from `⟦E'⟧` in at most one position, written with the single character
`⟦r⟧`; by IH `#c(⟦r⟧) ≤ C_{r}` and `#c(⟦E'⟧) ≤ C_{E'}`, so `#c(out) ≤ C_{E'} + C_r` — and the
*index sub-term's value is discarded* (only its length is used), so it contributes nothing.
`repOcc(k, B, A, E')` (or repOccI): the output is `⟦E'⟧` with one contiguous occurrence of
`⟦B⟧` deleted and `⟦A⟧` inserted — deletion cannot increase `#c`, insertion adds `#c(⟦A⟧) ≤ C_A`;
the rank/index value is discarded. `cat(E1, E2)`: sum. Adding the budgets along the tree gives
`C_E`. The crux, used three times: **each node performs at most one site-edit and each subterm
value is used once (tree syntax) — nothing duplicates.** ∎

**Corollary B1a.** Replace-all `[b/a] ∉ pos` (every fragment) for |Σ| ≥ 2: on input `a^n`,
`[b/a](a^n) = b^n` has `#b = n > C_E`. **PROVEN.**
**Corollary B1b.** `enc ∉ pos` (every fragment): `enc(b^n) = (ab)^n` has `#a = n`. **PROVEN.**
(Corollary B1c, |Σ| = 1, is different — see Theorem B5.)

**Theorem B2 (linear growth).** For every pos term `E` there are constants `V_E, K_E` with
`|⟦E⟧(X⃗)| ≤ V_E · M + K_E` where `M = Σᵢ |Xᵢ|`. **PROVEN.**
*Proof.* Induction: variable: `M`-part 1. Constant: `K`-part. setAt/setAtI: length unchanged.
repOcc/repOccI: `|out| ≤ |⟦E'⟧| − |⟦B⟧| + |⟦A⟧| ≤ |⟦E'⟧| + (V_A·M + K_A)` (patterns are nonempty).
cat: sum of the two bounds. So `V_E` = sum of the replacement-subtree slopes. ∎

**Corollary B2a.** `X ↦ X^{|X|} ∈ L` (paper) is **not** in pos, on any alphabet, any fragment:
its output length is `M²`. **PROVEN.** In the paper's terms, pos has duplication degree ≤ 1.

**Lemma B3 (bounded deletion; pos_lit).** For every pos_lit term `E` there is `D_E` with
`|⟦E⟧(X)| ≥ |X| − D_E` for all X. **PROVEN.**
*Proof.* Induction: variable: 0. Constant: ≥ 0. setAt: equal length. repOcc(k, B, A, E'):
`≥ |⟦E'⟧| − |B| ≥ |⟦E'⟧| − L̄` with `L̄` = max literal pattern length. cat(E1, E2):
`|⟦E1⟧| + |⟦E2⟧| ≥ (|X| − D₁) + (|X| − D₂) ≥ |X| − (D₁ + D₂)`. ∎ (Note this *survives concat*
but *needs literal patterns*: a computed pattern can be as long as the input.)

**Corollary B3a.** `head ∉ pos_lit`, `truncate_j ∉ pos_lit`, `dec = [b/ab] ∉ pos_lit`.
**PROVEN** — `head(a^n) = "a"`, `truncate_j(a^n) = a^j`, `dec((ab)^n) = b^n` each need `n − O(1)`
net deletions. (Consistency check: `tail(a^n) = a^{n−1}` deletes exactly 1 — and tail *is* in
pos_lit, §3.3.)

**Theorem B4 (unary length arithmetic).** On |Σ| = 1, for every pos-computable total `f` the map
`n ↦ |f(a^n)|` is piecewise `ℤ`-affine with finitely many pieces (each piece `n ↦ αn + β`, `α ∈ ℤ`).
**PROVEN.**
*Proof sketch.* On a unary alphabet every string is determined by its length, so the calculus is
pure arithmetic: `occ(a^q, a^p) = q − p + 1` occurrences, and
`repOcc(k, a^p, a^r, a^q) = a^{q−p+r}` if `q ≥ p + k` else `a^q`; setAt(i, c, a^q) = a^q` (writing
`a` over `a`); computed indices/ranks are themselves piecewise-affine lengths. Inductively each
subterm's length is piecewise-affine in `n` with breakpoints where a fire-condition
(`q(n) ≥ p + k`, affine) flips; with m nodes there are ≤ m breakpoints. ∎

**Corollary B4a.** `[a/a²] ∉ pos` on |Σ| = 1: `n ↦ ⌈n/2⌉` has slope 1/2 on infinitely many points.
**PROVEN.** (This is the paper's "half" — a single L node! So L reaches functions pos provably
cannot, even on unary.) **Corollary B4b.** `X^{|X|} ∉ pos` on |Σ| = 1 (`n²` is not piecewise-affine).
**PROVEN.**

**Theorem B5 (unary dichotomy for replace-all).** On |Σ| = 1, `[a^j/a] ∈ pos_concat` for every
`j ≥ 0`; on |Σ| ≥ 2, every replace-all that introduces a letter absent from its input (e.g.
`[b/a]`, `enc = [ab/b]`) is unreachable (Theorem B1). **PROVEN.**
*Construction.* `j = 0`: the constant `ε`. `j = 1`: identity. `j ≥ 2`:
`[a^j/a](a^n) = a^{jn}` and
`repOcc(0, "a", cat(tail(X), …, tail(X), "a"^j), X)` with `j−1` copies of `tail(X)` — the
replacement has length `(j−1)(n−1) + j = (j−1)n + 1`, and replacing the first `a` gives total length
`n − 1 + (j−1)n + 1 = jn`. (COMPUTATIONAL: verified j ≤ 5, n ≤ 24, 0 failures. Note the output is
`a^{jn}` because on unary strings content is determined by length.) ∎
So: *replace-all dies in pos exactly when a second letter exists to count.* The alphabet bound
(B1) is genuinely a two-letter phenomenon; the unary obstruction is arithmetic instead (B4).

---

## 3. Toolkit (enc/dec, cat, head/tail, eq, if)

The paper's yardstick: enc, dec, cat, head, tail, eq, if, char_j, rep_n. Rebuilding it with pos only:

### 3.1 enc / dec

- `enc ∉ pos` (every fragment): **PROVEN** (Corollary B1b). The b-encoding `[ab/b]` makes
  unboundedly many site edits.
- `dec = [b/ab] ∉ pos_lit`: **PROVEN** (Corollary B3a). `dec ∈ pos_core` / `pos_concat`:
  **OPEN**. Two observations: (i) a near-miss pipeline `repOcc(0, "aba", "b")` iterated
  computes `dec((ab)^n)` exactly on even n and fails on odd n (`n = 4`: `"abababab" → "bbabab" →
  "bbbb"`; `n = 5` gets stuck at `"bbbbab"`), a pretty illustration of why short-domain searches
  mislead; (ii) `dec` contracts length by a factor 2 while being piecewise-affine-compatible on
  unary — the obstruction on general alphabets is that the deleted `a`'s sit at *unboundedly many
  scattered sites* and each pos node edits one contiguous site.

### 3.2 cat

- In pos_concat, cat is a constructor (free). In pos_core: **CONJECTURE: `cat ∉ pos_core`**
  (COMPUTATIONAL: 2-variable search, ≤ 3 nodes over a 9-value pattern/replacement pool, 49 input
  pairs — not found; ≤ 2 nodes over 225 pairs with a 15-value pool — not found). Structural
  obstruction ("append barrier"): without cat, a term's output is the input with ≤ m contiguous-site
  edits; `cat(X, Y)`'s output ends with a copy of `Y` whose length is unbounded in a way no fixed
  number of in-place edits can produce unless Y-material is *moved*, and pos moving is limited to
  deletion+reinsertion of computed values at a *first-occurrence* site (rank 0) — the only robust
  anchor. No proof; this is the cleanest open structural question about the cat-free fragment.

### 3.3 head / tail

- **`tail ∈ pos_lit_core`: PROVEN.** `tail = repOcc(0, ε, c, setAt(0, c, X))` — mark position 0
  with any alphabet character `c`, then delete the first `c`. Two literal nodes, total on every
  input, on every alphabet including |Σ| = 1. (COMPUTATIONAL: all strings ≤ 6 over {a,b}, ≤ 5 over
  {a,b,c}, ≤ 8 unary and 4-letter, every choice of c — 0 failures. Also rediscovered
  independently by the depth-3 pos_lit search: FOUND at depth 2 via `repOcc(0,a→ε)` after
  `setAt(0,a)`.)
- **`head ∈ pos_concat`: PROVEN.** The naive `repOcc(0, ε, tail(X), X)` (Lemma A3) is undefined at
  `|X| ≤ 1` (empty pattern). Scaffold construction, total on *all* inputs, on *every* alphabet
  including |Σ| = 1:
  `head(X) = repOcc(0, ε, tail(tail(X·c³)), repOcc(0, ε, tail(X·c³), X·c³))` for any character c
  (`S = c³ = "aaa"`, or more generally any scaffold `S` with `|S| = 3` and `S[2] = S[0]`, e.g.
  `"dwd"` when two distinct letters exist).
  *Proof.* Let `V = X·c³`, `|V| ≥ 3`, so Lemma A3 applies: the inner node yields `T = head(V)`,
  which is `X[0]` if `X ≠ ε` and `S[0] = c` if `X = ε`. The cleanup pattern is
  `P₂ = tail(tail(V))`: if `|X| ≥ 1` then `|P₂| = |X| + 1 ≥ 2 > 1 = |T|`, no occurrence, identity —
  output `X[0]`. If `X = ε` then `P₂ = c` and `T = c`, the node fires and deletes it — output `ε`.
  Totality and correctness on all X. ∎ (COMPUTATIONAL: exhaustive on all strings ≤ 5–8 over five
  alphabets incl. unary, plus ~500 random strings ≤ 14 and adversarial periodic inputs — 0
  failures; both scaffolds `c³` and `dwd` verified.)
- **`head ∉ pos_lit`: PROVEN** (Corollary B3a). **`head ∈ pos_core`: OPEN** — the ε-edge
  obstruction: without cat the scrutinee cannot be padded, and on input `ε` every pattern value
  built without constants is `ε` (undefined), while constant-material patterns either do not occur
  or destroy the input's head. **CONJECTURE: no** (COMPUTATIONAL: pos_core 2-var search ≤ 3 nodes —
  not found).
- Consequences: `char_j`, `prefix_j`, `truncate_j` — see §3.4.

### 3.4 char_j, prefix_j, truncate_j, joins, prepend

- **`char_j`, `prefix_j ∈ pos_concat`: PROVEN** (compose: `char_j = head ∘ tail^j`,
  `prefix_j = cat(head(X), cat(char_1(X), …))` with the §3.3 constructions; verified j ≤ 3
  exhaustively). **`truncate_j ∉ pos_lit`: PROVEN** (B3a).
- **`join2 ∈ pos_lit_core`: PROVEN.** Given two computed single characters r₁, r₂:
  `join2 = setAt(0, r₂, setAt(1, r₁, "uv"))` over a fresh 2-character constant — a fixed scaffold
  whose positions 0, 1 are always in range. This is the pos replacement for the paper's cat when
  joining *characters*, and it is the mechanism behind prepend/joins in pos_lit.
- Prepending a computed value needs cat (`cat(v, X)`); in pos_core, **CONJECTURE: unreachable**
  (same append barrier as §3.2).

### 3.5 eq / if

- **`eq ∈ pos`: CONJECTURE: no** (every fragment). Evidence: (i) COMPUTATIONAL: 2-variable
  searches — pos_concat ≤ 2 nodes (225 pairs, 15-value pools incl. `XY`, `YX`): not found; pos_idx
  ≤ 3 nodes (49 pairs, 2424-node space with computed-index writes and computed-pattern repOcc):
  not found; (ii) structural: eq must broadcast a *global* comparison into a 2-character output,
  and pos detection mechanisms are local (fire/no-fire at one site). The paper's eq uses enc +
  marker machinery = unboundedly many sites.
- **`if ∈ pos`: CONJECTURE: no** (it would give eq on Boolean arguments; and the same searches
  fail). Note pos *does* have conditional *behavior* (fire vs. no-fire) — what it lacks is
  conditional *canonicalization* into a fixed output alphabet.
- **pos_idx subtlety worth recording:** `setAtI(X, 'z', Y)` writes `z` at position `|X|` of `Y`
  iff `|X| < |Y|` — a *length comparison detector* with a visible effect (the output differs from
  `Y` exactly when `X` is shorter). So pos_idx detects `|X| < |Y|`; what it (conjecturally) cannot
  do is turn the detection into a canonical `aa`/`bb` answer (the "lt" target was searched and not
  found, ≤ 3 nodes).

### 3.6 Computed indices (pos_idx)

- **`setAt-last ∈ pos_idx`: PROVEN.** `setAtI(tail(X), 'z', X)` — index = `|tail(X)| = |X|−1`,
  writes at the last position (identity on ε). (COMPUTATIONAL: all strings ≤ 6 over {a,b}.)
  The last position is *not* addressable by literal indices; this witnesses that pos_idx ≥ pos_lit
  in addressing power (strictness is conjectural — see Open Problem 9).
- **`droplast ∈ pos`: CONJECTURE: no** (COMPUTATIONAL: pos_lit ≤ 3 nodes on |s| ≤ 5 — not found;
  pos_concat 2-var ≤ 2 nodes — not found). Note droplast is *not* killed by B3 (it deletes exactly
  one character); the obstruction is that the deleted site must be the *end*, and pos sites are
  occurrence-anchored or literal-indexed, not end-anchored. (With computed indices one can write at
  the end (§ above) but not *shorten* at the end without an end-anchored pattern, which would have
  to be a suffix of every input — impossible.)
- **Rank-by-computed-length:** `f(X, Y)` = "replace the `(|Y|+1)`-th `a` of `X` by a marker", on
  unary `X`: **PROVEN ∈ pos_concat** via
  `repOcc(0, Y·a, Y·M·a, X)` then `repOcc(0, M·a, M, ·)` (the pattern `Y·a` occurs first exactly at
  the `(|Y|+1)`-th `a` on unary inputs; the second node removes the scaffolding). Verified n, m ≤ 8.
  **`f ∈ L`: CONJECTURE: no** (COMPUTATIONAL: 2-var L search, ≤ 3 nodes, computed patterns from an
  8-value pool — not found; 348,756 states). This is the pos_idx-flavored separation candidate.

### 3.7 Micro-reductions across calculi

- **`setAt(i, c) ∈ L`: PROVEN.** Construction (paper's machinery, workspace alphabet as in the
  paper's §2–3 constructions; verified on |Σ| = 2 with tt/ff inside Σ):
  `setAt(i,c)(X) = if(eq(tail^i(X), ε), X, cat(prefix_i(X), c, tail^{i+1}(X)))`.
  *Proof.* `i ≥ |X| ⟺ tail^i(X) = ε`, in which case the output is `X` (out-of-range = identity,
  Def. 1); otherwise the cat reassembles `X[:i]·c·X[i+1:]`. ∎ (COMPUTATIONAL: exhaustive i ≤ 3,
  all strings ≤ 5 over {a,b}; also with the 2-letter workspace, 0 failures.)
- **`repOcc(k, B, A) ⊴ once_l^{2k+1}`: PROVEN (fresh marker).**
  `repOcc(k, B, A) = once_l(B, M)^k ∘ once_l(B, A) ∘ once_l(M, B)^k` where `M` is a constant fresh
  w.r.t. `B`, `A` and the input (e.g. `"ZZ"` when the workspace provides it).
  *Proof.* The first k applications convert occurrences o₀ … o_{k−1} into fresh `M`-blocks (each
  `once_l(B, M)` addresses the current leftmost `B`; `M`-blocks never contain `B`), the middle one
  addresses o_k, and the last k restore the `M`-blocks. If there are < k+1 occurrences, marking
  stops early (once_l with no occurrence = identity), the middle application is the identity, and
  unmarking restores — total identity, matching Def. 3. ∎ (COMPUTATIONAL: k ≤ 3, B up to length 3,
  A ∈ {ε, X, ab, bbb}, all strings ≤ 5 over {a,b} avoiding the marker — 0 failures.)
  Caveat: needs a fresh marker constant, i.e. the paper's workspace-alphabet convention (on a bare
  2-letter alphabet no `M` is fresh for *all* inputs — see Open Problem 11).

---

## 4. Expressibility vs the baseline L

### 4.1 L into pos: REFUTED, three ways

**Theorem.** `L ⊴ pos` is **REFUTED**, in every fragment, on every alphabet. Three independent
witnesses: (i) replace-all `[b/a]` — alphabet bound B1a (|Σ| ≥ 2); (ii) `enc` — B1b; (iii)
`X ↦ X^{|X|}` — linear growth B2a (any |Σ|). On |Σ| = 1 additionally: `[a/a²]` = half — piecewise-
affine obstruction B4a. **PROVEN.**

### 4.2 pos into L: the once-hinge

**Theorem H (hinge).** Over an alphabet with the paper's workspace conventions (fresh markers
available; term-level constructions), the following are equivalent:
(i) `once_l ∈ L` (as a term-level construction `once_l(P, R, X)` with computed pattern and
replacement); (ii) `pos ⊴ L`. **PROVEN (as an equivalence).**
*Proof.* (ii ⟹ i): `repOcc(0, B, A) = once_l(B, A)` is a pos_lit term, so it must be L-reachable.
(i ⟹ ii): `setAt(i, c) ∈ L` (§3.7) and `repOcc(k, B, A)` is a composition of `2k+1` once_l terms
with a fresh marker constant (§3.7); computed patterns/replacements/characters/indices are pos
sub-terms, translated recursively (once_l is term-level by hypothesis; the marker is an L
constant). Every pos constructor is thereby simulated. ∎

**Status of the hinge itself:** `once_l ∈ L` — **CONJECTURE: no.** Evidence (COMPUTATIONAL, all
negative): L with literal patterns, ≤ 4 nodes, all strings ≤ 4 over {a,b} (417,853 states) —
`once_l(a→X)`, `once_l(b→X)`, `once_l(ab→ε)`, `repOcc(1,a→X)`, `repOcc(2,a→X)`, `setAt(1,a)`,
`setAt(0,b)` all NOT FOUND (controls: `L(a,b)` found at depth 1); L + enc/dec/head/tail/cat-with-
constant macros, ≤ 3 nodes (25,909 states) — same targets NOT FOUND (controls: head, tail, L(a,b)
found); 2-variable L with computed patterns, ≤ 3 nodes (348,756 states) — once-flavored and
rank-flavored targets NOT FOUND. Structural intuition: L-nodes are saturating; producing exactly
one replacement seems to require "counting to one" against a rewrite that fires everywhere, and the
paper's own machinery (markers, enc) is itself replace-all-based. No proof either way.

**Particular cases inside the hinge:** `setAt ⊴ L` **PROVEN**; `repOcc(k) ⊴ L` **PROVEN modulo
once_l + fresh markers**; the genuinely open residue is exactly `once_l`.

### 4.3 pos vs the once-family

- `once_l ⊴ pos_lit_core`: **PROVEN** (definitional: `repOcc(0, B, A)`).
- `repOcc(k) ⊴ once_l-calculus`: **PROVEN** (§3.7 marker composition; the once-calculus with
  concat and constants).
- **Replace-all ∉ once_l-calculus: PROVEN** — the single-site alphabet bound induction (B1)
  transfers verbatim (once_l fires at most once per node; cat does not duplicate). So the
  once-calculus, like pos, is separated from L by B1a. (COMPUTATIONAL: once-calculus search ≤ 4
  nodes on |s| ≤ 6 — 166,937 states — `L(a,b)` NOT FOUND; the domain is artifact-safe because
  replace-all on `a⁶` needs 6 single-edit nodes > 4.)
- `pos_lit ⊴ once_l-calculus`: **CONJECTURE: no.** (COMPUTATIONAL: same search — `tail`, `head`,
  `setAt(0,b)` NOT FOUND ≤ 4 nodes. Structural: once-sites are occurrence-anchored; pos needs
  position-0 anchoring, which requires writing a fresh marker at position 0 — but once_l's own
  leftmost-addressing cannot canonicalize "position 0" without a pattern that means "the start",
  and any value pattern means "some occurrence".) Conjecturally, then: **once ⊊ pos_lit_core ⊆ …**,
  with `tail` as the concrete separating candidate (tail ∈ pos_lit_core PROVEN; tail ∉
  once-calculus CONJECTURE).

### 4.4 The unary alphabet: a sharper picture

On |Σ| = 1 (Σ = {a}), pos and L are provably different, and conjecturally incomparable:

- `head ∈ pos`: **PROVEN** (§3.3, scaffold `a³` — verified on unary, all n ≤ 8).
- `tail ∈ pos_lit_core`: **PROVEN** (§3.3, c = a).
- `[a^j/a] ∈ pos_concat` for all j: **PROVEN** (Theorem B5) — replace-all *with growth* is
  pos-reachable on unary.
- `[a/a²]` (half), `X^{|X|}` ∈ L ∖ pos: **PROVEN** (B4).
- `head ∈ L(|Σ|=1)`, `tail ∈ L(|Σ|=1)`: **CONJECTURE: no** (COMPUTATIONAL: unary L search,
  literal patterns `a^i`, i ≤ 3, plus computed pattern `[a^j/X]`, ≤ 3 nodes, n ≤ 30 — not found;
  controls replace-all and half found. An earlier run on n ≤ 8 "found" head via `[a/a²]³` —
  re-verified beyond the search domain and it fails at n ≥ 9: a domain-size artifact, see
  Appendix).
- If that conjecture holds, pos and L are **incomparable on |Σ| = 1** (head separates pos from L;
  half separates L from pos — the latter separation is already PROVEN via B4a).

### 4.5 Search-evidence table (all runs; see scratch/pos/ for scripts)

| # | search (space, depth, domain) | states | target | result |
|---|---|---|---|---|
| 1 | pos_lit (134 literal nodes), ≤ 3, all \|s\| ≤ 5 | 586,952 | head, L(a,b), truncate2, droplast, reverse | NOT FOUND |
| 1 | (same) | | tail | FOUND, depth 2 (control; my construction rediscovered) |
| 2 | L-lit (42 nodes [A/B]), ≤ 4, all \|s\| ≤ 4 | 417,853 | once_l(a→X), once_l(b→X), once_l(ab→ε), repOcc(1,a→X), repOcc(2,a→X), setAt(1,a), setAt(0,b), reverse, truncate2 | NOT FOUND |
| 2 | (same) | | L(a,b) | FOUND, depth 1 (control) |
| 3 | L + enc/dec/head/tail/cat-const macros (48), ≤ 3 | 25,909 | once_l(a→X), once_l(b→X), repOcc(1,a→X), setAt(1,a) | NOT FOUND |
| 3 | (same) | | head, tail, L(a,b) | FOUND (controls) |
| 4 | L-unary (patterns a^i ≤ 3, + [a^j/X]), ≤ 3, n ≤ 30 | — | head, tail | NOT FOUND |
| 4 | (same) | | replace-all, half | FOUND (controls) |
| 5 | L 2-var, computed patterns (8-value pool), ≤ 3, \|X\|,\|Y\| ≤ 3 | 348,756 | f = replace-the-\|Y\|-th-a, head(X) | NOT FOUND |
| 5 | (same) | | L(a,b) | FOUND (control) |
| 6 | pos_core 2-var, computed patterns (9-value pool), ≤ 3 / ≤ 2 | 12,266+ | cat(X,Y), head(X), L(a,b) | NOT FOUND |
| 7 | pos_concat 2-var (15-value pool + cat), ≤ 2, 225 pairs | 12,266 | eq(X,Y), L(a,b), droplast | NOT FOUND |
| 7 | (same) | | cat(X,Y) | FOUND (control) |
| 8 | once-calculus (once_l all pool pairs + prepend/append), ≤ 4, \|s\| ≤ 6 | 166,937 | tail, head, setAt(0,b), L(a,b) | NOT FOUND |
| 8 | (same) | | once_l(a→b) | FOUND, depth 1 (control) |
| 9 | pos_idx 2-var (2424 nodes: computed-index writes, computed-pattern repOcc, cat), ≤ 3 | 587,625 | eq(X,Y), \|X\|<\|Y\| as aa/bb | NOT FOUND |
| 9 | (same) | | cat(X,Y) | FOUND (control) |

Methodology notes (see Appendix): states are tuples of outputs over the finite domain, deduplicated;
any state containing an undefined (None) value is dropped — i.e., candidates are total on the
domain; "FOUND" results were re-verified beyond the search domain (this caught two artifacts).

**Invariant scans.** Exhaustive scans of all ≤ 2-node pos_lit pipelines on inputs a⁵–a⁷: 0 violations
of the alphabet bound; all ≤ 3-node pipelines on random strings: 0 violations of linear growth.
(COMPUTATIONAL.)

---

## 5. Complexity

- **Evaluation is polynomial — PROVEN.** Each repOcc node is one greedy scan: `O(|text|·|pattern|)`
  (naive; `O(|text| + |pattern|)` with two-way matching, irrelevant at this level). Bottom-up
  evaluation of a term with N nodes on inputs of total length M: by Theorem B2 every intermediate
  value has length `≤ V_E·M + K_E = O(M)` (for fixed E), so the total cost is `O(N·M²)` worst-case
  (`O(N·M·L̄)` for pos_lit with literal patterns of length ≤ L̄). Computed indices add one length
  computation of a sub-value: still polynomial. Nothing in pos breaks poly-time.
- **Output size is at most linear — PROVEN (B2).** Contrast: L reaches quadratic output
  (`X^{|X|}`, paper's duplication degree machinery; the paper's length bound `C(1+M)^deg` has
  deg ≥ 2 examples). pos has deg ≤ 1 *always*: pos cannot even *write down* a quadratic string
  except by cat-ing O(n) linear pieces — a representational gap, not a time gap.
- **pos is to L as "one pass with a fixed number of edits" is to "saturation."** The number of
  site-edits of a pos term is ≤ its node count; an L node performs `|occ(S,B)|` edits — unbounded
  in the input. This is the quantitative content of Theorem B1.
- **No speed-up pathologies:** the semantic subtleties (rank re-indexing, Lemma A4's join-effects)
  are all locally checkable in one scan; the "aba→b halving" (§3.1) shows *short* pipelines can
  produce nontrivial contractions, but always within the linear/affine envelope of B2/B4.

---

## 6. Open problems

1. **`once_l ∈ L`?** The hinge (Theorem H): it alone gates `pos ⊴ L`, and equally gates
   `repOcc(≥1) ⊴ L`. All searches say no; no proof. This is in my view the most interesting
   single open problem in the whole comparison program.
2. **`head ∈ pos_core`?** (cat-free). The ε-edge obstruction suggests no; the scaffold needs cat.
   Similarly **`cat ∈ pos_core`?** — the append barrier. Both searched to depth 3 without success.
3. **`eq ∈ pos`?** (any fragment, incl. pos_idx). pos_idx can *detect* `|X| < |Y|` (marker write at
   a computed index) but seemingly cannot *canonicalize* the detection (aa/bb output). A pos_idx
   search with 2,424 node types to depth 3 found nothing.
4. **`dec ∈ pos_core` / `pos_concat`?** (∉ pos_lit PROVEN.) The `repOcc(0,"aba","b")` halving
   computes dec on even-length `(ab)^n` and fails on odd — is there a parity-breaking pipeline?
5. **`droplast ∈ pos`?** (Any fragment; ∉ pos_lit is only conjectural here — B3a does not apply
   since droplast deletes one char.) The obstruction: end-anchoring. Note setAt-last ∈ pos_idx
   writes at the end, so the *asymmetric* pair (write-at-end: yes; delete-at-end: ?) is itself
   interesting.
6. **`head, tail ∈ L(|Σ| = 1)`?** Would upgrade the unary incomparability of §4.4 from conditional
   to PROVEN. (The n ≤ 8 "head via [a/a²]³" was an artifact; the n ≤ 30 run finds nothing.)
7. **Is `f(X, Y)` = replace-the-`(|Y|+1)`-th occurrence in L?** (PROVEN ∈ pos_concat on unary X;
   L 2-var search fails.) A cleaner pos_idx-vs-L separation candidate than eq.
8. **Characterize pos on unary completely:** Theorem B4 says piecewise ℤ-affine; B5 shows all
   slopes j are reachable; which *piece structures* (breakpoints, saturating mins/maxes) are
   reachable, and is the piecewise-affine picture exact?
9. **`pos_idx ⊋ pos_lit` strictly?** Witness candidate: `setAt-last` (write at `|X|−1`; PROVEN in
   pos_idx) — conjectured ∉ pos_lit (its site must track the end; literal indices are fixed).
10. **`pos_lit ⊴ once_l-calculus`?** (Conjecture no, tail as separator.) Dual: is the once-calculus
    exactly the "rank-0 restriction" of pos_lit, i.e. pos_lit minus absolute addressing?
11. **Marker-free reductions:** §3.7's composition needs a fresh marker constant. On a bare
    2-letter alphabet with no workspace, is `repOcc(1, B, A)` still once_l-expressible? (The
    marker must be fresh for *all* inputs, which a 2-letter constant never is; but a *computed*
    marker, e.g. one built from the input, might evade this. Untested.)
12. **`reverse ∈ pos`?** (Searched: NOT FOUND ≤ 3 nodes pos_lit.) Reordering seems to need
    unboundedly many moves; no proof. (Same question for L is the paper's own open problem; a pos
    separation would be the easier half.)

---

## 7. Relations summary

```
EXPR: pos_lit ⊴ pos_core STATUS: PROVEN — fragment inclusion (literal arguments are constant subterms).
EXPR: pos_core ⊴ pos_concat STATUS: PROVEN — fragment inclusion (add cat).
EXPR: pos_concat ⊴ pos_idx STATUS: PROVEN — literal index i = |"a"^i| via a constant index subterm.
EXPR: once_l-calculus ⊴ pos_lit_core STATUS: PROVEN — once_l(B,A) = repOcc(0,B,A), definitional.
EXPR: repOcc(k,·,·) ⊴ once_l-calculus STATUS: PROVEN — repOcc(k,B,A) = once_l(B,M)^k ∘ once_l(B,A) ∘ once_l(M,B)^k, fresh marker M, 2k+1 nodes (verified k ≤ 3).
EXPR: setAt(i,c) ⊴ L STATUS: PROVEN — if(eq(tail^i X,ε), X, cat(prefix_i X, c, tail^{i+1} X)); verified i ≤ 3 exhaustively, workspace alphabet.
EXPR: pos_lit ⊴ L STATUS: CONJECTURE — equivalent to once_l ∈ L (Theorem H, PROVEN as an equivalence); setAt-part PROVEN, repOcc-part PROVEN modulo once_l; all L searches (≤ 4 literal / ≤ 3 macro / ≤ 3 two-var nodes) fail to find once_l.
EXPR: pos (full) ⊴ L STATUS: CONJECTURE — same hinge at term level; needs once_l as a term-level L construction with computed pattern/replacement.
EXPR: L ⊴ pos STATUS: REFUTED — [b/a] and enc violate the single-site alphabet bound (B1); X^{|X|} violates linear growth (B2); holds for every pos fragment incl. pos_idx and every alphabet (on |Σ|=1 via half, B4).
EXPR: L ⊴ once_l-calculus STATUS: REFUTED — replace-all needs unboundedly many single-site edits; the alphabet-bound induction transfers to once_l + concat verbatim.
EXPR: pos_lit ⊴ once_l-calculus STATUS: CONJECTURE — tail, head, setAt(0,c) not found ≤ 4 once-nodes (|s| ≤ 6); once-sites are occurrence-anchored and cannot canonicalize absolute positions.
EXPR: pos_idx ⊴ L STATUS: CONJECTURE — rank-by-|Y| selection f(X,Y) has a PROVEN pos construction (unary) but was not found in two-variable L ≤ 3 nodes.
EXPR: L ⊴ pos_idx STATUS: REFUTED — alphabet-bound and linear-growth inductions hold verbatim with computed indices.
EXPR: tail ⊴ pos_lit_core STATUS: PROVEN — repOcc(0,ε,c,setAt(0,c,X)); 2 literal nodes; total on every alphabet incl. |Σ| = 1.
EXPR: head ⊴ pos_concat STATUS: PROVEN — scaffold repOcc(0,ε,tail²(X·c³), repOcc(0,ε,tail(X·c³), X·c³)); total, verified on every alphabet incl. |Σ| = 1.
EXPR: head ⊴ pos_lit STATUS: REFUTED — bounded-deletion lemma B3: |E(X)| ≥ |X| − D_E but head(a^n) = "a"; same for truncate_j, dec.
EXPR: cat ⊴ pos_core STATUS: CONJECTURE — two-variable searches ≤ 3 nodes fail; append/junction barrier (no proof).
EXPR: eq ⊴ pos (incl. pos_idx) STATUS: CONJECTURE — searches ≤ 2–3 nodes fail in pos_concat (225 pairs) and pos_idx (2424-node space); pos lacks global-test canonicalization.
EXPR: [b/a] (letter-changing replace-all) ⊴ pos STATUS: REFUTED — |Σ| ≥ 2: alphabet bound B1a on a^n; |Σ| = 1: [a/a²] = half is not piecewise-ℤ-affine (B4a). Dichotomy: [a^j/a] ∈ pos_concat on unary IS PROVEN (B5). (Replace-all-to-empty [ε/a]: ∉ pos_lit by B3, open for pos_core.)
EXPR: X^{|X|} ⊴ pos STATUS: REFUTED — linear growth theorem B2 (quadratic output; duplication degree ≤ 1 in pos).
EXPR: enc ⊴ pos STATUS: REFUTED — alphabet bound B1b: enc(b^n) = (ab)^n has n copies of a.
EXPR: droplast ⊴ pos STATUS: CONJECTURE — not found ≤ 3 nodes pos_lit / ≤ 2 nodes pos_concat-two-var; end-anchoring obstruction (setAt-last ∈ pos_idx shows writes at the end are possible; deletion is the open half).
EXPR (|Σ|=1): head ⊴ pos STATUS: PROVEN — a³-scaffold construction, verified on unary n ≤ 8.
EXPR (|Σ|=1): head ⊴ L STATUS: CONJECTURE — L-unary search ≤ 3 nodes, n ≤ 30, not found; together with [a/a²] ∈ L ∖ pos (PROVEN) this yields conditional incomparability of pos and L on |Σ| = 1.
```

---

## Appendix: computational methodology and artifact log

**Engine.** `search_pos.py`: breadth-first search in *function space* — a state is the tuple of a
candidate expression's outputs over the finite input domain; states are deduplicated; a state
containing an undefined value (None) is discarded, so only candidates total on the domain survive;
targets are matched against complete output tuples. Nodes are parameterized by the fragment:
pos_lit (134 literal nodes), L-lit (42), L-macro (48), pools of computed pattern/replacement
values for the two-variable searches, once-calculus (36 + prepend/append), pos_idx (2424).

**Verification.** `verify_constructions.py` checks every PROVEN construction above exhaustively on
the stated domains (paper machinery sanity; setAt-in-L; tail; head with both scaffolds; join2;
char_j/prefix_j; setAt-last; repOcc-via-once; replace-first-m; the unary rank-selection f; the
stepping-in lemma). Final tally: **FAILURES: 0**.

**Domain-size artifacts (both caught and documented).**
1. once-calculus/pos searches on short domains "FOUND" replace-all-like behavior because
   replace-all on `a^n` for small n equals a few single edits (e.g. on strings of length ≤ 2).
   Fix: enlarge the domain until the target needs more edits than the depth allows (|s| ≤ 6 with
   depth 4: replace-all on `a⁶` needs 6 nodes).
2. L-unary on n ≤ 8 "FOUND" head via `[a/a²]³` (three halvings reduce n ≤ 8 to ≤ 1). Re-verified
   beyond the domain: fails at n ≥ 9. Fix: n ≤ 30, NOT FOUND.
3. The dec near-miss (§3.1): `repOcc(0,"aba","b")²` computes dec on `(ab)^n` exactly for even
   n ≤ 8 — a reminder that "verified on a finite domain" is not "proven", and that parity-type
   behavior only shows up at odd lengths.
4. pos_lit search target `once_l(a→X)` uses the character X not present in the node constants —
   a target/node-set mismatch (once_l is *definitional* in pos via repOcc(0), so nothing rides on
   that particular NOT FOUND).

**Lesson recorded for all searches:** every FOUND is re-verified on a strictly larger domain
before being believed; every NOT FOUND is only evidence, never proof — such claims are labeled
CONJECTURE above.

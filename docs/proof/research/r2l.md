# The r2l Variant: Right-to-Left Replace-All

Research report on the primitive **`[A/B]ᴿC`** — the exact mirror of the paper's Definition 1:
scan `C` from the **right**; replace every occurrence of `B` by `A` taking **rightmost-first**,
non-overlapping matches; after a match the scan resumes to the **left** of the inserted text
(inserted text is never rescanned). Baseline `L` = the paper's calculus with `[A/B]C` (leftmost-first).
All experiments are reproducible: scripts under `docs/proof/research/scratch/r2l/`
(`sem.py`, `test_duality.py`, `test_lemmas.py`, `test_independent.py`, `toolkit.py`,
`test_toolkit.py`, `test_rep.py`, `test_escape.py`, `search_const.py`, `test_misc.py`).

Status labels used throughout: **PROVEN** (proof written), **COMPUTATIONAL** (exhaustively verified
on a stated finite domain), **CONJECTURE** (evidence, no proof), **REFUTED** (counterexample).

---

## 1. Semantics

**Definition 1ᴿ (Right-to-Left Substitution).** Given strings `A, B` with `B ≠ ε`, for any
string `C`,

```
[A/B]ᴿC = ([A/B]ᴿX) · A · Y     where (X, Y) = arg min { |Y'| : C = X'BY' }
```

i.e. `C = XBY` with the **rightmost** occurrence of `B`. The mirror image of the paper's
Definition 1 (which takes `arg min |X'|`, the leftmost occurrence, and recurses on `Y`).
`[A/ε]ᴿC` is undefined behavior, as in the paper. Equivalent formulation (used in the code):
a pointer sweeps from `|C|` down to `0`; whenever `B` ends exactly at the pointer, emit `A` and
jump the pointer to the start of the inserted text; otherwise emit the character under the
pointer. The two formulations were cross-verified on all `(A,B,C)` with `|Σ| ∈ {2,3}`,
`1 ≤ |B| ≤ 3`, `|A| ≤ 3`, `|C| ≤ 6` — 0 mismatches. **COMPUTATIONAL**

### 1.1 The mirror duality

**Theorem 1 (Rev Duality).** For all `A`, `B ≠ ε`, `C`:

```
[A/B]ᴿC = rev ( [rev A / rev B] (rev C) )
```

*Proof.* Induction on `|C|`. Occurrences of `B` in `C` at position `s` correspond bijectively to
occurrences of `rev B` in `rev C` at position `|C|−|B|−s`, so the rightmost occurrence of `B`
corresponds to the **leftmost** occurrence of `rev B`. Write `C = XBY` with `Y` minimal; then
`rev C = rev Y · rev B · rev X` exhibits the leftmost occurrence of `rev B`. By Definition 1,
`[rev A/rev B](rev C) = rev Y · rev A · [rev A/rev B](rev X)`. Applying `rev`:
`rev(…) = rev([rev A/rev B](rev X)) · A · Y = [A/B]ᴿX · A · Y` by the induction hypothesis
(`|X| = |C|−|B|−|Y| < |C|`), which equals `[A/B]ᴿC` by Definition 1ᴿ. If `B ⊄ C` then
`rev B ⊄ rev C` and both sides equal `C`. ∎

Verified exhaustively on the domain above (both `|Σ| = 2` and `3`): **0 failures. COMPUTATIONAL**

This one-line theorem is the backbone of everything below: *the r2l calculus is the
`rev`-conjugate of the paper's calculus* (Section 4), which (i) lets every paper theorem be
mirrored mechanically, and (ii) reduces all cross-direction expressibility questions to the
paper's final open problem "is `rev` reachable?".

### 1.2 Where the two directions differ

**Proposition (examples).** Differences require a **bordered** pattern `B` and overlapping
occurrences:

| expression | l2r (paper) | r2l |
|---|---|---|
| `[b/aa]` on `aaa` | `ba` | `ab` |
| `[ε/aba]` on `ababa` | `ba` | `ab` |
| `[a/bb]` on `abbba` | `aaba` | `abaa` |

On a maximal run `aⁿ`, `[b/aa]` pairs from the left (leftover parity `a` at the *end*),
`[b/aa]ᴿ` pairs from the right (leftover at the *front*). Minimal difference instance by
`(|C|,|B|,|A|)`: `A=a, B=bb, C=bbb` (also `A=b, B=aa, C=aaa`). **COMPUTATIONAL**

**Theorem 2 (Agreement).**
(i) If `B` is unbordered, then `[A/B]ᴿ = [A/B]` as functions (for all `A`).
(ii) If the occurrences of `B` in `C` are pairwise disjoint, then `[A/B]ᴿC = [A/B]C`.
(iii) In particular single-character patterns give identical functions in both directions.

*Proof.* (i) If two occurrences of `B` overlap at offset `d < |B|`, then `B` has period `d`,
hence a border of length `|B|−d`; unbordered `B` excludes this, so all occurrences in any `C`
are pairwise disjoint. By induction on `|C|`, each greedy (leftmost resp. rightmost) scan then
selects **all** occurrences: after replacing the extreme one, the remaining text still contains
exactly all the others (none overlapped), and both recursions terminate on the same set of
disjoint intervals replaced by `A` — the same output string. (ii) is the same induction
relative to the given `C`. (iii) A single character is unbordered. ∎

Verified: all unbordered `(A,B)` pairs (`|B| ≤ 4`, `|A| ≤ 3`, `|C| ≤ 8`, `|Σ| = 2`): 0
differences; all strings with pairwise-disjoint occurrences (`|B| ≤ 4`, `|C| ≤ 7`): 0
differences. **COMPUTATIONAL** (matches the proof).

**Observation (bordered but equal).** For bordered `B` the functions *can* still coincide for
special `A`. Over `Σ = {a,b}`, `|A|,|B| ≤ 3`: 90 bordered `(A,B)` pairs, of which 70 differ and
20 agree; the agreeing ones are exactly `A = B` (Identity Substitution), `B = cᵏ` with `A ∈ c*`
(parity leftover is invisible inside a pure run), and `B ∈ {aba, bab}` with `A` the border
character (e.g. `A=a, B=aba`). A complete characterization of pairs `(A,B)` with
`[A/B]ᴿ = [A/B]` is open. **COMPUTATIONAL** (classification open)

---

## 2. Basic algebra (dualization of the paper's Section 2)

| Paper theorem | Status under r2l | Notes |
|---|---|---|
| Identity Substitution `[A/A]ᴿS = S` | **PROVEN** | mirror induction: with the rightmost occurrence, the remainder `Y` is occurrence-free by minimality of `|Y|` |
| Direct Substitution `[A/B]ᴿB = A` | **PROVEN** | the occurrence of `B` in `B` is unique |
| Substitution Elimination `B ⊄ S ⟹ [A/B]ᴿS = S` | **PROVEN** | immediate |
| Independent Substitution | **PROVEN** with an added hypothesis — and the **paper's own lemma is false as stated** | see below |
| Tail Elimination `CB ⊂ AB ⟹ C ⊒ A` | **PROVEN** (string fact, unchanged) | its *role* swaps with Head Elimination under the mirror |
| Head Elimination `BC ⊂ BA ⟹ C ⊑ A` | **PROVEN** (string fact, unchanged) | mirror of Tail Elimination |
| Stepping-into `[C/A](AB) = C[C/A]B` | **REFUTED** under r2l; mirror statement **PROVEN** | see below |
| Double Substitution `[X/Y][Y/X]Z = Z` (X⊂Y, Y unbordered) | **PROVEN** | mirror proof below |
| Encoding/Decoding round trip, monoid morphism | **PROVEN** | `encᴿ = enc` exactly; see §3 |

**A bug in the paper (direction-independent).** The paper's Lemma *Independent Substitution*
states: if `A ∩ B = ∅`, `A ∩ C = ∅`, `C ≠ ε` then `A ⊂ [B/C]S ⟺ A ⊂ S`. This is **false as
stated** when the replacement `B = ε`: take `A = aa`, `B = ε`, `C = b`, `S = aba`; then
`[B/C]S = aa ⊇ aa` but `aa ⊄ aba`. The proof step "an occurrence of `A` intersecting the
inserted `B`-block must share a character with `B`" is vacuous when the block is empty, and
deletion merges neighbors. With the added hypothesis **`B ≠ ε`** the lemma holds for l2r *and*
for r2l (the mirror induction runs on `X` instead of `Y`). Verified exhaustively
(`|Σ| ∈ {2,3}`, `|A|,|B|,|C| ≤ 4`, `|S| ≤ 6`): all 198+6174 failures (per alphabet) of the
statement-as-written have `B = ε`; **0 failures with `B ≠ ε`**, in both directions. **COMPUTATIONAL**
+ proofs above. *(This corrects the paper; it affects the l2r original, not only the variant.)*

**Stepping-into.** The original statement fails under r2l: `[z/aa]ᴿ(aab…)` — concretely
`[z/aa]ᴿ "aaa" = "az"` while `[z/aa]"aaa" = "za"` (**REFUTED**): the rightmost occurrence of `A`
in `AB` need not be at position 0 (it can overlap into `B`). The correct mirror is:

**Lemma (Stepping-into, mirror).** `A ≠ ε ⟹ [C/A]ᴿ(BA) = ([C/A]ᴿB) · C` — the rightmost
occurrence of `A` in `BA` is the final one. **PROVEN** (and verified). Note the mirror swaps
"step into a prefix" (l2r) with "step into a suffix" (r2l); likewise Tail/Head Elimination swap
roles — the paper itself notes they are symmetric.

**Double Substitution, mirror.** If `X, Y ≠ ε`, `X ⊂ Y`, `Y` unbordered, then
`[X/Y]ᴿ[Y/X]ᴿZ = Z`. *Proof.* The greedy r2l scan of `[Y/X]ᴿZ` yields the same decomposition
`W = Z₀YZ₁YZ₂⋯YZ_k` with X-free gaps `Zᵢ` (the greedy selection is the mirror of the paper's;
the decomposition exists by the same induction from the right). The paper's claim — *every
occurrence of `Y` in `W` starts at the head of an exhibited copy* — is a direction-free string
analysis (cases (i)–(iii) use only unborderedness of `Y`). Hence the r2l greedy scan of
`[X/Y]ᴿ` takes the **last** exhibited copy first, replaces it by `X`, resumes to its left
facing a string of the same form; induction from the right gives `[X/Y]ᴿW = Z₀XZ₁⋯XZ_k = Z`. ∎
Both hypotheses remain necessary in the mirror (bordered `Y` fails, e.g. `X=a, Y=aa, Z=aaa`;
`X ⊄ Y` fails, e.g. `X=a, Y=bb, Z=aba`). **PROVEN** + verified exhaustively (0 failures;
54 bordered-`Y` counterexample families found, mirroring the paper's Remark). **COMPUTATIONAL**

---

## 3. Toolkit

### 3.1 enc / dec / cat / head / tail / eq / if — all work verbatim under r2l

**Theorem 3 (Toolkit).** The paper's constructions, *as written* (same expressions, same
constants), compute the same functions under r2l semantics:
`enc_{b,x} = [xb/b]`, `dec_{b,x} = [b/xb]`, `cat`, `tail`, `head`, `eq`, `if`.

*Proof.* Every substitution pass that occurs in these constructions is **direction-robust**, in
one of three ways:
(a) its pattern is a single character (Theorem 2(iii)) — this covers `enc` (pattern `b`), the
`[enc(X)/⊤]` pass of `if` (pattern `⊤`), and `[σ/Σ]`-style passes;
(b) its pattern is a fixed unbordered constant — `xb`, `xb²`, `xb³` (all of the form `xbᵏ`,
`x ≠ b`), covering `dec` and the marker passes of `cat`;
(c) its pattern has at most one occurrence in every string that arises at that point of the
pipeline — this is exactly what the paper's own occurrence analyses establish for the passes of
`cat` (unique `xb³` resp. `xb²`), `tail` (each deletion pattern matches only at position 0 of
`σ₁σ₁enc(X)`, since `enc`-images contain no `σ₁σ₁`), `head` (the unique suffix occurrence of
`enc(tail X)σ₁σ₁`), and `eq`/`if` (by Border Injectivity, `benc(Y)` occurs in `benc(X)` iff
`X = Y`, in which case the occurrence is the whole string; likewise `bb` and `⊤` are either
absent or the whole string where they arise). Note these variable patterns (`benc(Y)`,
`enc(tail X)σ₁σ₁`) are *not* always unbordered — e.g. `benc(ε) = xbbxbb` is bordered — so (c),
not (b), is what carries `eq` and `head`. All the underlying occurrence analyses are
direction-free string facts. A pass that is direction-robust computes the same function under
`[·/·]` and `[·/·]ᴿ`; composing the pipeline pass-by-pass gives the result. ∎

Consequences, each verified with **0 failures** on `|Σ| ∈ {2,3,4}`, `|S| ≤ 5` (cat: pairs of
inputs), `|X|,|Y| ≤ 4` (eq, if) — `test_toolkit.py`:
- `encᴿ = enc` *exactly* (single-char pattern), so it is trivially a monoid morphism, images
  contain no `bb`, and `decᴿ ∘ encᴿ = id`. In particular the "rightmost-based enc" asked about
  in the brief is *the same function* as the paper's enc.
- The mirror encoder also works: `enc′ = [bx/b]ᴿ` (escape each `b` into `bx`, escape char
  *after*), `dec′ = [b/bx]ᴿ`; both are single-char/unbordered patterns so direction-free;
  `dec′∘enc′ = id` by the mirrored Double Substitution (verified: 0 failures). The mirror of
  escaping is "post-fix" rather than "pre-fix" — both are available in the r2l calculus.
- `cat` is reachable in r2l, hence **concatenation is eliminable in the r2l calculus** as well
  (the paper's Concatenation Elimination proof transfers verbatim, using r2l-reachable `cat`):
  core = with-concat for r2l too. **PROVEN**

### 3.2 rep_n: the paper's construction is *not* direction-robust

This is the first genuine asymmetry. Let freezing semantics be the paper's Definition
(`rep_n`, leftmost-freezing) and its mirror (`rep_nᴿ`, rightmost-freezing; the greedy scan of
each round takes rightmost-first — equivalently `rev∘rep_n(rev·)`, by the position bijection of
Theorem 1).

**Theorem 4 (r2l rep_n — mirrored construction).** Replace every constant of the paper's
construction by its reversal — `enc′ = [bx/b]ᴿ` (each `b` becomes `bx`, so every `b` of a
fragment is *followed* by its `x`), markers `m′ᵢ = b^{i+1}x`, rename pass `[m′ᵢ/E′ᵢ]ᴿ`, repair
pass `[b·E′ᵢ / b^{i+2}x]ᴿ`, instantiation `[enc′(Yᵢ)/m′ᵢ]ᴿ`, final `dec′ = [b/bx]ᴿ` — and run it
under r2l semantics. It computes **rightmost-freezing** `rep_nᴿ`, under the **mirrored
hypothesis**: `|Xᵢ| = 1` or `Xᵢ` does not **begin** with `x`.

*Proof.* Conjugate the paper's theorem by `rev` (Theorem 1, lifted to expressions — see the
Conjugation Theorem in §4). The conjugated expression, applied to the original variables,
computes `rev(rep_n(rev S; rev Xᵢ, rev Yᵢ)) = rep_nᴿ(S; Xᵢ, Yᵢ)` (leftmost-greedy freezing of
`rev Xᵢ` in `rev S` = rightmost-greedy freezing of `Xᵢ` in `S`). The hypothesis transfers as
`rev Xᵢ` does not end with `x` ⟺ `Xᵢ` does not begin with `x`. ∎
Verified: 0 failures over `|Σ| ∈ {2,3}`, `n ∈ {1,2}`, all `S, Xᵢ, Yᵢ` with `|S| ≤ 5`,
`1 ≤ |Xᵢ| ≤ 2`, `|Yᵢ| ≤ 2` satisfying the mirrored hypothesis (≈ 5.0M instances for `|Σ| = 3`,
`n = 2`). **COMPUTATIONAL** (+ the conjugation proof)

**Theorem 5 (original construction under r2l: REFUTED).** The paper's construction *with its
own constants* (`enc = [xb/b]`, markers `xbᵏ⁺¹`), run under r2l semantics, does **not** compute
rightmost-freezing `rep_n`, even when the paper's hypothesis (`|Xᵢ| = 1` or `Xᵢ` not ending in
`x`) holds.

*Counterexample* (`|Σ| = 3`, `b, x, c`): `S = bbc`, `X₁ = c`, `Y₁ = ε`, `X₂ = bb`, `Y₂ = ε`.
Construction output `bb`; rightmost-freezing (and leftmost-freezing!) output `ε`.
*Why:* after round 1 renames every `c` to the marker `m₁ = xbb`, the round-2 pattern
`E₂ = enc(bb) = xbxb` has a genuine match ending at the marker's start **and** a spurious match
`[m₀−2, m₀+2)` straddling into the marker (`…xb | xbb` → the spurious `xbxb` ending inside the
marker). The paper's no-shadowing analysis proves that whenever a spurious match overlaps a
genuine one, *the genuine one starts strictly earlier* — which is exactly what **leftmost**
greedy needs, and exactly what **rightmost** greedy violates: the r2l rename pass takes the
spurious (later) match first, the genuine match is never frozen, and the repair pass then
restores the text as if nothing had happened. Verified: 812/49392 (|Σ|=2) and 15158/4982796
(|Σ|=3) failing instances under the paper's hypothesis (first failure exactly the family
above). **REFUTED** (the paper's own l2r construction was re-validated on ≈5.0M instances with
0 failures, and reproduces the paper's Remark counterexample exactly — see `test_rep.py`,
`test_escape.py`.) **COMPUTATIONAL**

**Theorem 6 (r2l rep_n — original constants, stronger hypothesis).** If every `Xᵢ` with
`|Xᵢ| ≥ 2` **ends with a character outside `{b, x}`** (possible iff `|Σ| ≥ 3`), then the
paper's original construction under r2l semantics does compute rightmost-freezing `rep_nᴿ`.

*Proof.* In a normal-form text (fragments = `enc`-images, markers `xbᵏ`), every `b` is preceded
by `x` (units `xb`, marker heads) or by `b` (marker tails). A match of `Eᵢ = enc(Xᵢ)` that ends
immediately before a `b` — the paper's exact characterization of *spurious* — therefore has last
character `x` (if the next `b` is a unit's or a marker's first `b`) or `b` (marker-internal
`b`). Since `enc` preserves last characters, `Xᵢ` ending in `c ∉ {b,x}` makes `Eᵢ` end in `c`:
**no spurious matches exist at all**. Every match is genuine; the r2l greedy then freezes the
rightmost-first non-overlapping set of genuine matches, i.e. exactly the round-`i`
rightmost-freezing; the repair pass is inert (its pattern `xb^{i+2}` arises only at spurious
junctions — the paper's occurrence analysis is direction-free), and the instantiation passes
have unbordered patterns. ∎ Verified: 0 failures (28392 resp. 2.2M instances for `n = 1,2`,
`|Σ| = 3`). **COMPUTATIONAL** (+ proof)

### 3.3 escape / unescape: leftmost-dependence, and the mirrored scheme

**Theorem 7 (r2l escape — mirrored scheme).** Define, with `u₁ = u_k` the fixed point
enumerated first ((H1)) and `x ∉ V` ((H2)),

```
escapeᴿ_f(S) = rep′_n(S; u₁, f(u₁)u₁; …; u_n, f(u_n)u₁)      (post-fix pairs)
unescapeᴿ_f(S) = rep′_n(S; f(u₁)u₁, u₁; …; f(u_n)u₁, u_n)
```

with the *mirrored* rep construction `rep′` of Theorem 4. Then
`unescapeᴿ_f(escapeᴿ_f(S)) = S` for all `S`.

*Proof.* Conjugation of the paper's Character Escaping theorem: `rev(escape_f(rev S))` replaces
each `uᵢ` by `f(uᵢ)u₁`, and the round trip composes to the identity by the paper's theorem
applied to `rev S`. The mirrored-rep hypothesis holds: escape patterns are single characters;
unescape patterns `f(uᵢ)u₁` do not begin with `x` by (H2). ∎
Verified: **0 failures over all enumerated `(U, f, u₁)` configurations** with `|Σ| ∈ {3,4}`,
`|S| ≤ 5` (7644 resp. 185640 round trips) — in fact 0 failures even **without (H2)**. **COMPUTATIONAL**

**Theorem 8 (paper's escape scheme under r2l: REFUTED).** With the paper's pair structure
(`u ↦ u₁f(u)`, pre-fix), neither the original- nor the mirrored-constants rep construction makes
the round trip hold under r2l in general. *Counterexample* (`|Σ| = 3`): `U = {b,x}`,
`f(b) = b`, `f(x) = c`, `u₁ = b`,
`S = bx`: `escape(S) = bbbc`; round 1 of unescape has the bordered pattern `bb`, whose
occurrence at position 1 (straddling the two pairs) is taken **first** by rightmost-greedy,
freezing `[1,3)`, which blocks the genuine pair `[2,4)` = `bc`; the result is `bbc ≠ bx`. The
straddler starts *later* than the genuine pair — precisely the configuration leftmost-greedy
kills and rightmost-greedy takes. Even the strengthened hypothesis `V ∩ {b,x} = ∅` fails
(|Σ|=4: `U={b,c}`, `f(b)=d`, `f(c)=c`, `u₁=c`, `S=cb`: `cccd` → `ccd`). Verified: 528/2184
resp. 15732/53235 failures under (H1),(H2). **REFUTED**

The escape scheme is **direction-locked in both directions** (verified exhaustively; the
mirror of Theorem 8 fails under l2r, e.g. `U={b,x}`, `f(b)=b`, `f(x)=x`, `u₁=b`, `S=xb`:
escapeᴿ = `xbbb`, round trip gives `xbb`; 3112/7644 resp. 72872/185640 failures):

| pair scheme | under l2r | under r2l |
|---|---|---|
| paper (`u ↦ u₁f(u)`, pre-fix) | works (paper's theorem) | **REFUTED** |
| mirrored (`u ↦ f(u)u₁`, post-fix) | **REFUTED** | works (Theorem 7) |

**Necessity of (H1) in the mirror.** With the fixed point not enumerated first, the mirrored
scheme fails too — e.g. `Σ = {b,x,c}`, `U = {b,x}`, `f(b) = b` (fixed point `u_k = b`),
enumeration starting `u₁ = x`, `S = cb`: `escapeᴿ(S) = cbb` but the round trip returns `xb ≠ cb`
(the mirror of the paper's own Remark failure). Verified: 1320/24024 resp. 99000/2.4M failures
over all such configurations. So (H1) is needed in both directions. **COMPUTATIONAL**

**Bonus (paper's open remark, computationally answered).** The paper asks whether (H2)
(`x ∉ V`) can be dropped from the escape round trip. Computationally, **yes**, for l2r and for
the mirrored r2l scheme: 0 failures over *all* configurations violating (H2) on the enumerated
domains (including 185640 round trips at `|Σ| = 4`). **CONJECTURE** (proof not written)

---

## 4. Expressibility vs baseline L

**Conjugation Theorem.** For every expression `E` (with variables, constants, concatenation)
let `Ē` be its rev-conjugate: every constant `W` replaced by `rev W`, every node `[R/P]`
replaced by `[R̄/P̄]ᴿ` (conjugate sub-expressions), and every concatenation node's children
**swapped** (`rev(XY) = rev Y · rev X`). Then

```
⟦Ē⟧ᴿ(rev S₁, …, rev Sₙ) = rev(⟦E⟧_L(S₁, …, Sₙ))
```

with both sides undefined together. *Proof.* Induction on `E`; the node case is Theorem 1, the
concat case is `rev(XY) = rev Y rev X`, variables and constants are immediate, and undefinedness
(`pattern = ε`) is preserved because `rev ε = ε`. ∎ Spot-verified on concrete
variable-using expressions (including `[X/aa](bX)`, `[Xa/ab]X` and nested pipelines): 0
mismatches. **PROVEN** (+ **COMPUTATIONAL** spot check)

**Corollaries.**
1. **`rev ∈ L ⟺ rev ∈ r2l`.** (⟸: if `⟦E⟧_L = rev` then `⟦Ē⟧ᴿ(rev S) = rev(rev S) = S`,
   so `⟦Ē⟧ᴿ = rev`. ⟹ is the mirror.) **PROVEN**
2. If `rev` is reachable in *either* calculus, then **`L` and `r2l` are the same class of
   reachable functions** (each node of one direction is expressible in the other via
   `[A/B]ᴿ = rev∘[rev A/rev B]∘rev` resp. `[A/B] = rev∘[rev A/rev B]ᴿ∘rev`, plus closure under
   composition and eliminability of concatenation in both). **PROVEN**
3. `r2l ⊴ L` holds **if** `rev ∈ L`; `L ⊴ r2l` holds **if** `rev ∈ r2l`. **PROVEN** (conditional)
4. Unconditionally, **neither `r2l ⊴ L` nor `L ⊴ r2l` is known**: by Corollary 1 both reduce to
   the paper's final open problem "is `rev` reachable?" — the variant adds no new leverage.
   Even *equality* of the two calculi does not visibly imply `rev ∈ L` (an equalizing simulation
   need not expose `rev` itself), so the implications in (2) are not obviously reversible. **OPEN**

**Theorem 9 (constant-pattern core fragments are incomparable).** Consider the *core*
(concat-free) pipelines over a single variable scrutinee in which every pattern and replacement
is a constant string: `[R_k/P_k]⋯[R_1/P_1]X₁`.
(i) Every such l2r pipeline is a **left-subsequential** function (deterministic one-way
streaming transducer with final output): a single pass is realized by the KMP-style machine
whose state is the longest pending suffix that is a prefix of `B`, emitting the finalized part,
resetting to `ε` on each match (this is exactly Definition 1); and left-subsequential functions
are closed under composition (product construction: feed the first machine's online output into
the second). 
(ii) `[b/aa]ᴿ` is **not** left-subsequential: on `aⁿ` its output is `b^{n/2}` (n even) resp.
`a·b^{(n−1)/2}` (n odd) — the first output character depends on the parity of an unbounded
run, but a deterministic streaming machine's first emission on `a^∞` occurs at a fixed step
with fixed content (or outputs are length-bounded, contradicting `|out| = ⌈n/2⌉`). 
(iii) Mirror: r2l constant core pipelines are right-subsequential, and `[b/aa]` is not
right-subsequential. 
Hence `[b/aa]ᴿ ∈ r2l-core-const \ L-core-const` and `[b/aa] ∈ L-core-const \ r2l-core-const`:
**the constant-pattern core fragments are incomparable.** **PROVEN**

Bounded searches agree (and guard against an error in the streaming argument): no l2r pipeline
of depth ≤ 2 (`|A|,|B| ≤ 3`; 32,315 distinct functions) nor depth ≤ 3 (`|A| ≤ 3, |B| ≤ 2`;
297,534 distinct functions) computes `[b/aa]ᴿ` on all `|C| ≤ 6`; mirror result for `[b/aa]`
in r2l; sanity: the search *finds* `[b/aa]ᴿ` at depth 1 in r2l. Extending the schema to
variable patterns/replacements (`X₁`, `aX₁`, `X₁a`, `aaX₁`, … — 18 shapes each side), depth ≤ 2
(16,751 distinct functions): `[b/aa]ᴿ` still not found in l2r, `[b/aa]` not found in r2l. **COMPUTATIONAL**

**Conjecture (full calculi incomparable).** `[b/aa]ᴿ ∉ L` and `[b/aa] ∉ r2l` (hence neither
`r2l ⊴ L` nor `L ⊴ r2l`). Evidence: Theorem 9 for the constant fragment + the failed bounded
variable-schema searches. The subsequentiality invariant cannot be extended: the full calculi
contain non-subsequential functions (e.g. `X ↦ X^|X|`) via variable patterns, and no
length-growth, counting, or periodicity invariant is known that separates these single
functions. **CONJECTURE**

**What survives without settling reversal.**
- The **always-unbordered fragment**: any expression in which every substitution node's pattern
  is unbordered for *every* instantiation computes the same function in both calculi (Theorem
  2, node-wise). This covers `enc`, `dec`, `cat` and all marker passes. (The toolkit functions
  `eq`/`head` use variable patterns that are *not* always unbordered — e.g. `benc(ε)=xbbxbb` —
  but they still agree in both directions by the unique-occurrence analysis of Theorem 3, a
  different route to the same conclusion.) **PROVEN**
- `rev`-bounded searches: `rev` was not found in l2r or r2l constant pipelines (depth ≤ 2) nor
  variable-schema pipelines (depth ≤ 2), on all inputs `|S| ≤ 6` over `Σ = {a,b}`. **COMPUTATIONAL**

---

## 5. Complexity

**Lemma (Length Bound, mirror).** For `B ≠ ε`: `|[A/B]ᴿT| ≤ |T|·(1+|A|)`. The greedy matches are
pairwise disjoint intervals of length `|B| ≥ 1`, so there are at most `|T|` of them, each
contributing `|A|` characters in place of at least one. Verified: 0 violations
(`|A| ≤ 4`, `|B| ≤ 3`, `|C| ≤ 7`). **PROVEN** (+ **COMPUTATIONAL**)

**Theorem 10 (Poly-time soundness, mirror).** Every r2l-reachable function is computable in
polynomial time, with the exponent bounded by a function of a defining expression alone.
The paper's Section 4 transfers verbatim: the duplication degree `deg` is unchanged; the
induction for `|⟦E⟧ᴿ(S⃗)| ≤ C_E(1+M)^{deg E}` uses the mirrored Length Bound at the node step;
concatenation is eliminable in r2l (Theorem 3); and a single r2l pass runs in linear time via
the mirrored streaming machine (the pointer scan of §1 — measured: 0.15 ms → 2.41 ms for
`|C| = 2 000 → 32 000` on a match-saturated input, cleanly linear; the iterative and recursive
definitions agree on the full small domain). **PROVEN**

Nothing about the variant breaks polynomial time or polynomial growth: `X ↦ σ^|X|` and
`X ↦ X^|X|` are r2l-reachable (all patterns single-character, hence direction-free; verified),
and `X ↦ X^{2^|X|}` is not r2l-reachable (same length argument as the paper). **PROVEN**

---

## 6. Open problems

1. **Is `rev` reachable — in either calculus?** By Corollary 1 of the Conjugation Theorem,
   `rev ∈ L ⟺ rev ∈ r2l`: the paper's final open problem 2 is *direction-independent*, and by
   Corollary 2 it is equivalent to the equality of the two calculi. This is, in my view, the
   single most interesting open problem the variant surfaces.
2. `r2l ⊴ L`? `L ⊴ r2l`? Both are equivalent to calculi equality *given* `rev`; whether either
   holds without `rev` (or whether equality could hold without `rev`) is open. The constant
   fragments are provably incomparable (Theorem 9), so any proof must use variable patterns on
   at least one side.
3. Is the single function `[b/aa]ᴿ` (rightmost pairing) in `L`? Is `[b/aa]` in `r2l`?
   (Weak form of 2; bounded searches fail.)
4. Characterize the pairs `(A, B)` with `[A/B]ᴿ = [A/B]` (bordered `B`, special `A` — data in §1.2).
5. Can (H2) (`x ∉ V`) be dropped from the escape round trip? Computationally yes for both
   direction-matched scheme pairs (l2r + paper scheme; r2l + mirrored scheme) over all
   enumerated configurations with `|Σ| ∈ {3,4}`, `|S| ≤ 5` — the mismatched pairs fail
   regardless of (H2), since the scheme itself must match the scan direction (table in §3.3).
6. Exact pattern families for which the *original-constants* rep construction is correct under
   r2l: "every `|Xᵢ| ≥ 2` ends outside `{b,x}`" is sufficient (Theorem 6) and the paper's
   hypothesis is not (Theorem 5); the exact boundary is open (mirrors the paper's own open
   remark on its pattern families).
7. The paper's Independent Substitution lemma needs `B ≠ ε` (§2); worth fixing in `main.tex` /
   the Lean development (not modified here — outside my write scope).

---

## 7. Relations summary

```
EXPR: r2l-toolkit (enc,dec,cat,head,tail,eq,if) ⊴ L STATUS: PROVEN — constructions are direction-robust (single-char/unbordered patterns or unique occurrences); identical functions, 0 failures exhaustive |Σ|≤4.
EXPR: L-toolkit (enc,dec,cat,head,tail,eq,if) ⊴ r2l STATUS: PROVEN — same constructions under r2l semantics compute the same functions (Theorem 3).
EXPR: r2l-concat-calculus ⊴ r2l-core STATUS: PROVEN — cat is r2l-reachable, so concatenation is eliminable (mirror of the paper's Concatenation Elimination).
EXPR: r2l-core-const ⊴ L-core-const STATUS: REFUTED — [b/aa]ᴿ is a single r2l constant pass but not left-subsequential; L-core-const ⊆ left-subsequential (Theorem 9).
EXPR: L-core-const ⊴ r2l-core-const STATUS: REFUTED — mirror: [b/aa] is not right-subsequential (Theorem 9).
EXPR: r2l-unbordered-pattern fragment ⊴ L STATUS: PROVEN — unbordered patterns make the two primitives equal (Theorem 2), node-wise.
EXPR: L-unbordered-pattern fragment ⊴ r2l STATUS: PROVEN — same theorem, other direction.
EXPR: r2l ⊴ L (full, with concat) STATUS: CONJECTURE (open) — PROVEN conditional on rev ∈ L; unconditionally unknown; constant fragment refutes only the const sub-calculus.
EXPR: L ⊴ r2l (full, with concat) STATUS: CONJECTURE (open) — PROVEN conditional on rev ∈ r2l; rev ∈ L ⟺ rev ∈ r2l (PROVEN), so both conditionals rest on one question.
EXPR: r2l ⊴ L under rev ∈ L STATUS: PROVEN — rev-conjugation of every r2l node (Conjugation Theorem).
EXPR: L ⊴ r2l under rev ∈ r2l STATUS: PROVEN — mirror conjugation; note rev ∈ r2l ⟸ rev ∈ L (PROVEN), so one hypothesis suffices for equality.
EXPR: L = r2l under rev ∈ (either) STATUS: PROVEN — Corollary 2 of the Conjugation Theorem.
EXPR: rep_n (paper constants, paper hypothesis) under r2l semantics ⊴ rightmost-freezing rep STATUS: REFUTED — S=bbc, X₁=c, X₂=bb, Y=ε,ε: construction gives 'bb', semantics gives 'ε' (Theorem 5).
EXPR: rep_nᴿ (mirrored constants, mirrored hypothesis: Xᵢ ∤ begins-with x) under r2l ⊴ r2l STATUS: PROVEN — conjugation of the paper's theorem; 0 failures on ≈5M instances (Theorem 4).
EXPR: rep_nᴿ (paper constants, Xᵢ ends outside {b,x}) under r2l ⊴ r2l STATUS: PROVEN — no spurious matches exist, greedy-right = rightmost-freezing; 0 failures on ≈2.2M instances (Theorem 6).
EXPR: escape/unescape round trip (paper pair scheme) under r2l STATUS: REFUTED — S=bx, f(b)=b, f(x)=c, u₁=b: escape 'bbbc' → unescape 'bbc' (straddler taken first by rightmost-greedy) (Theorem 8).
EXPR: escapeᴿ/unescapeᴿ round trip (mirrored pair scheme f(u)u₁) under r2l STATUS: PROVEN — conjugation; 0 failures over all enumerated (U,f,u₁), |Σ|∈{3,4} (Theorem 7).
EXPR: escapeᴿ/unescapeᴿ round trip (mirrored pair scheme f(u)u₁) under l2r STATUS: REFUTED — direction-lock: the scheme must match the scan direction (e.g. S=xb, f(b)=b, f(x)=x, u₁=b: 'xbbb' → 'xbb'; 72872/185640 failures, see §3.3 table).
EXPR: r2l-reachable ⊆ poly-time STATUS: PROVEN — mirrored length bound |[A/B]ᴿT| ≤ |T|(1+|A|), unchanged degree calculus, linear single passes (Theorem 10).
EXPR: X↦X^|X| in r2l STATUS: PROVEN — [X₁/σ][σ/Σ]ᴿX₁, all patterns single-character hence direction-free.
EXPR: X↦X^{2^|X|} in r2l STATUS: REFUTED — exceeds the degree length bound, as in the paper.
```

### How to reproduce

```
cd docs/proof/research/scratch/r2l
python3 test_duality.py      # Theorem 1 + Theorem 2 + difference classification (~4 s)
python3 test_lemmas.py       # Section 2 mirrors, stepping refutation, paper B=ε bug (~29 s)
python3 test_independent.py  # pinning the B=ε bug to the paper itself (~33 s)
python3 test_toolkit.py      # Theorem 3 (~33 s)
python3 test_rep.py          # Theorems 4–6 (~6.5 min)
python3 test_escape.py       # Theorems 7–8 + (H2)-dropping evidence (~50 s)
python3 test_escape_cross.py # direction-lock table (l2r x mirrored scheme) (~25 s)
python3 search_const.py      # Theorem 9 searches (~3 min)
python3 test_misc.py         # minimal examples, agreement, length bound, timing (~1 s)
```

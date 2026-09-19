# The restart variant `[A/B]ᵐ C`: single-rule Markov (fixpoint) substitution

Research report on the expressive power of the **restart** primitive, studied against the
baseline calculus of `docs/proof/main.tex` (and its Lean formalization `docs/proof/lean/Subst.lean`,
both read in full and treated as read-only; nothing outside `docs/proof/research/` was modified).

**Semantics under study.** `[A/B]ᵐ C` = repeat *{find the leftmost occurrence of `B` in the current
string; replace it by `A`; restart the scan from position 0}* until `B` no longer occurs. This is
the leftmost-strategy normalization of the single rewrite rule `B → A` — a one-rule Markov
algorithm, and the exact semantics the paper's Remark contrasts with bounded pipelines.

Throughout: `Σ` is a finite alphabet with `|Σ| ≥ 2`; `b = σ₁` and `x = σ₂` are the two designated
characters of the paper's encoding; `ε` is the empty word; `U ⊂ V` means "`U` occurs in `V` as a contiguous substring"; `chars(W)` is the set of characters of `W`.
`[A/B]C` is always the paper's Definition 1 (left-to-right, leftmost-first, non-overlapping, never
rescanning inserted text); `G_{A,B}(C) := [A/B]C`. `#b(S)` is the number of `b`'s in `S`.

**Calculus names.**

| name | grammar | node semantics |
|---|---|---|
| `L` | the paper's `Exp_n` (variables, constants, `[R/P]E`, concatenation) | paper Definition 1 |
| `V` | same grammar | `[R/P]` interpreted as restart `[R/P]ᵐ` |
| `L-core`, `V-core` | no `E₁E₂` nodes | — |
| `L-cc`, `V-cc` | core, and every `P`, `R` in `[R/P]` a constant word | — |
| `V[enc,dec]` | `V-core` plus `enc`, `dec` as primitive sub-expressions | — |

`X ⊴ Y` means: every function reachable in calculus `X` is reachable in calculus `Y`; for each
claim we say whether it concerns **total** functions (the paper's Definition *reachable*) or
**partial** functions. Every claim below carries exactly one label: **PROVEN**, **COMPUTATIONAL**
(brute-force verified, sizes stated), **CONJECTURE**, **REFUTED**. Scripts live in
`docs/proof/research/scratch/restart/` (`substlib.py` + `exp1…exp11`); the inventory is in the
Appendix.

---

## 1. Semantics

### 1.1 Definition (restart)

**Definition R.** For words `A, B, C ∈ Σ*` with `B ≠ ε`, `[A/B]ᵐ C` is defined by the trajectory
`s₀ = C`, `s_{k+1} = s_k[:i] · A · s_k[i+|B|:]` where `i` is the position of the *leftmost*
occurrence of `B` in `s_k` (which exists as long as the process continues). If the trajectory
reaches a `B`-free string `s*`, then `[A/B]ᵐ C = s*` and the number of steps is `k`. If `B = ε` the
expression is **undefined** (as in the paper); if the trajectory is infinite, `[A/B]ᵐ C` is
**undefined by divergence**. So `[A/B]ᵐ : Σ* ⇀ Σ*` is a partial function, and the denotation
clauses of the paper's Definition (den) carry over with "undefinedness" now meaning *either*
empty pattern *or* divergence.

**Proposition 1.2 (fixpoints are B-free). PROVEN.** If `[A/B]ᵐ C` is defined then its value
contains no occurrence of `B`. *Proof:* the process stops exactly when `B` no longer occurs.
By contrast baseline outputs may contain `B` (e.g. `[ab/b]"b" = "ab"`), and this is the structural
root of every difference between the two semantics.

### 1.2 Termination (totality) of a single node

Totality of `[A/B]ᵐ` is termination of the single-rule string-rewriting (semi-Thue) system
`{B → A}` under the leftmost strategy — a classical topic (see Sources).

**Theorem 1.3 (termination classification).**
1. `|A| < |B|` ⟹ `[A/B]ᵐ` is total, in ≤ `|C|` steps. **PROVEN** (each step shortens the string).
2. `|A| = |B|` and `A ≠ B` ⟹ total. **PROVEN.** Let `i₁` be the first position where `A`, `B`
   differ; give `A[i₁]` digit 0, `B[i₁]` digit 1, all other characters digit 0, and set
   `V(s) = Σ_j digit(s[j])·2^{-j}`. A step at position `i` changes the first differing digit of
   the block at `i` from 1 to 0 (value strictly drops by `2^{-(i+i₁)}`) and may only raise later
   digits by a total `< 2^{-(i+i₁)}` (finite geometric tail), so `V` strictly decreases along a
   trajectory; `V` takes ≤ `2·2^{|C|-1}` values on strings of the fixed length, giving termination
   in ≤ `2^{|C|}` steps.
3. `A = B` ⟹ `[A/A]ᵐ` diverges on every input containing `A`, and is the identity elsewhere.
   **PROVEN** (the replacement re-contains the pattern). So the paper's *Identity Substitution*
   lemma fails (see §2).
4. `B ⊂ A` ⟹ diverges on every input containing `B`. **PROVEN** (`A = uBv` re-seeds `B` at the
   same site).
5. Corollary: for `|A| ≤ |B|`, `[A/B]ᵐ` is total **iff** `A ≠ B`. **PROVEN.**
6. For `|A| > |B|` with `B ⊄ A` there is **no known criterion**. It is *not* the case that
   "growing and pattern-not-inside-replacement" implies divergence, nor that it implies
   termination:
   - 144 total & growing rules exist already with `|A| ≤ 4 > |B|` (e.g. `[aa/b]ᵐ`, `[baa/ab]ᵐ`);
   - **REFUTED** as a criterion "growing ⟹ divergent": the four minimal counterexamples
     `[aabb/ba]ᵐ`, `[abba/bab]ᵐ`, `[baab/aba]ᵐ`, `[bbaa/ab]ᵐ` (binary, `|A| = 4`, `|B| = 2`,
     `B ⊄ A`) all **diverge**, with minimal diverging inputs `baa`, `babb`, `aaba`, `aab`
     respectively; the trajectory of `[aabb/ba]ᵐ` on `baa` regenerates a junction `ba` at each
     step and grows by 2 characters forever. **COMPUTATIONAL** (each diverging input is a
     certificate, so the four divergences are PROVEN; their *minimality* is COMPUTATIONAL).
   - Exhaustive classification, binary alphabet, all `|A| ≤ 4`, `|B| ≤ 4` (930 rule pairs, inputs
     up to length 9, step cap 200k): **764 total, 166 divergent, 0 disagreements** with the
     predictions of items 1–5; divergent with `B ⊄ A`: exactly the four rules above. Extending to
     `|A| ≤ 6, |B| ≤ 3` finds 66 divergent rules with `B ⊄ A`. **COMPUTATIONAL.**

**Remark 1.4 (decidability).** Totality of a restart node = termination of one-rule semi-Thue
rewriting under the leftmost strategy. Known: decidable for length-decreasing rules (trivial),
length-preserving rules, *single-threaded* rules (Moczydłowski–Geser, RTA 2005), grid rules,
one-overlap-pair rules (Geser); the general one-rule termination problem is a long-standing open
problem — see the survey and the MathOverflow discussion in Sources. Which of these classes
captures the leftmost strategy exactly is not established here. Strategy-insensitivity is
however complete in the small: among all leftmost-total rules with `|A|,|B| ≤ 3`, **no** rule was
found (inputs ≤ 10) for which the *rightmost* strategy diverges. **COMPUTATIONAL.**

### 1.3 Agreement with the baseline

**Theorem 1.5 (Agreement). PROVEN.** If `chars(A) ∩ chars(B) = ∅`, `A ≠ ε`, `B ≠ ε`, then
`[A/B]ᵐ = [A/B]` (as total functions on all of `Σ*`).
*Proof.* Occurrences of `B` overlapping the span of an inserted `A` would force a common character,
so no new occurrence ever appears at or across the insertion; every other occurrence of `B` in
`s' = s[:i]·A·s[i+|B|:]` sits at the same offset in `s` and does not overlap the replaced block.
Hence each step destroys the leftmost occurrence and creates none: the count of occurrences
strictly decreases (termination in ≤ #occurrences steps), no occurrence survives overlapping a
replaced block, and after the step the next leftmost occurrence starts at `s`-offset ≥ `i+|B|` —
exactly where the baseline's greedy scan resumes. Induction gives identical outputs. ∎
The hypothesis `A ≠ ε` is needed: `[ε/ab]ᵐ "aabb" = ε ≠ "ab" = [ε/ab]"aabb"` (deleting `ab` at
position 1 makes positions 0–1 a *new* `ab`). The deletion counterexample is the smallest of all
disagreements (key `|A|+|B|+|C| = 6`).

**Theorem 1.6 (Exact Agreement).** `[A/B]ᵐ = [A/B]` as partial functions **iff** `[A/B]C` is
`B`-free for every `C ∈ Σ*`.
- (⟹) **PROVEN** (trivially, by Proposition 1.2).
- (⟸) **CONJECTURE**; exhaustive computational support: over the binary alphabet, all 210 rule
  pairs with `|A| ≤ 3`, `|B| ≤ 3` were classified by (i) restart-vs-baseline agreement on all 511
  inputs of length ≤ 8 and (ii) baseline-output-`B`-freeness on the same inputs: the two
  classifications coincide with **0 mismatches** (86,626 defined runs); same for the ternary
  alphabet, `|A|, |B| ≤ 2`, `|C| ≤ 6` (156 pairs, 149,055 defined runs). **COMPUTATIONAL.**
  (⟸) is the load-bearing transfer lemma for the toolkit (§3): every pass of the paper's
  constructions has a pattern-free baseline output, which — given (⟸) — makes the pass restart-safe.

**Smallest disagreements (restart ≠ baseline). COMPUTATIONAL.** By key `|A|+|B|+|C|`:
`[ε/ab]ᵐ"aabb" = ε` (vs `ab`); `[a/aa]ᵐ"aaa" = "a"` (vs `"aa"`); `[a/ab]ᵐ"abb" = "a"` (vs `"ab"`);
`[b/ab]ᵐ"aab" = "b"` (vs `"ab"`). The smallest with `A ∩ B = ∅` but `A = ε` is the deletion case;
with `A ≠ ε` and `A ∩ B = ∅` there are **none** (Theorem 1.5).

### 1.4 The paper's "make A∩B = ∅ precise" suggestion

Theorem 1.5 is the precise form: character-disjointness of *replacement* and *pattern* with
nonempty replacement makes restart and baseline literally the same total function. The exact
boundary is Theorem 1.6: agreement holds precisely when the baseline never emits an occurrence of
its own pattern. Between the two sits a large practical middle ground (growing replacements,
overlapping alphabets) where the two semantics differ but both are total — e.g. `[ba/ab]ᵐ` is a
correct *sort* to `b*a*` while baseline `[ba/ab]` is a single bubble pass.

---

## 2. Basic algebra: audit of the paper's Section 2

| paper lemma | status under restart | witness / note |
|---|---|---|
| Identity Substitution `[A/A]S = S` | **REFUTED** | `[A/A]ᵐ` diverges iff `A ⊂ S` (Theorem 1.3.3); verified 930 pairs |
| Direct Substitution `[A/B]B = A` | **HOLDS, weakened** | `[A/B]ᵐB = [A/B]ᵐA`, and `= A` iff `B ⊄ A`; PROVEN, verified |
| Substitution Elimination (`B ⊄ S ⟹ [A/B]ᵐS = S`) | **HOLDS** | PROVEN (no occurrence, no step) |
| Independent Substitution | **HOLDS** for restart on its defined domain | key ingredient `A ⊂ [B/C]ᵐS ⟺ A ⊂ S` (under `A∩B = A∩C = ∅`, `C ≠ ε`) proven via occurrence invariance; verified on 2,162,160 instances |
| *— paper erratum* | **REFUTED as stated** | the lemma omits `B ≠ ε`: with `A = "aa"`, `B = ε`, `C = "b"`, `S = "aba"`: `[B/C]S = "aa" ⊃ A` but `S = "aba" ⊄ A`. Fails for **both** semantics (the paper's own proof step "`A ⊂ XB([B/C]Y) ⟹ A ⊂ X ∨ A ⊂ [B/C]Y`" needs `B ≠ ε`) |
| Tail / Head Elimitation (string lemmas) | **HOLDS** | purely string-theoretic, no substitution involved |
| Stepping-into `[C/A](AB) = C([C/A]B)` | **REFUTED** | `(A,B,C) = ("aa","a","a")`: restart gives `"a"`, baseline `"aa"`; verified |
| Double Substitution `[X/Y][Y/X]Z = Z` | **HOLDS vacuously, precisely** | inner `[Y/X]ᵐ` diverges whenever `X ⊂ Z` (since `X ⊂ Y` is a hypothesis); defined ⟺ `X ⊄ Z`, then `= Z`; verified 5,660 inner divergences, 0 failures on defined cases |
| Single-character commutation, `σ^{|S|}` | **HOLDS** | single-char patterns: restart = baseline (one-char pattern occurrences are positions); `X ↦ σ^{|X|} ∈ V-cc` **PROVEN** |
| Composition / β-lemma | **HOLDS** | same structural induction; node behavior depends only on the pattern/replacement values, so divergence matches on both sides |
| Pipeline normal form | **HOLDS** | syntactic (core = finite pipeline of passes over an atomic scrutinee) |
| enc / dec | **REFUTED / changed** | see §3 |

**enc and dec under restart.** `enc = [xb/b]`: `B = b ⊂ xb = A`, so `[xb/b]ᵐ` **diverges iff
`b ∈ S`** (Theorem 1.3.4) — the paper's encoder is not a restart node. **REFUTED** (as a direct
construction). `dec = [b/xb]`: `|A| = 1 < 2 = |B|` so `[b/xb]ᵐ` is total, but it computes a
*different* function: **PROVEN** (easy induction; verified on all 511 strings over `{x,b}` ≤ 9)
`decᵐ(S) = S` with every `x` that has a `b` to its right deleted; smallest difference
`S = "xxb"`: `dec = "xb"`, `decᵐ = "b"` (290/511 inputs differ). The round trip `decᵐ(enc(S))`
is therefore not the identity in general — the escape mechanism itself is what restart destroys.

---

## 3. Toolkit

The paper's architecture is: enc/dec ⇒ cat ⇒ head/tail ⇒ eq ⇒ if ⇒ rep_n. Under restart the
keystone **enc is missing**, so we measure what survives *given enc and dec as black boxes*
(`V[enc,dec]`), and what is intrinsically blocked.

| item | status in `V[enc,dec]` (core, restart nodes) | evidence |
|---|---|---|
| `enc` | **REFUTED** as the paper's node; open whether *any* V-expression computes it (IC conjecture, §4) | `[xb/b]ᵐ` diverges iff `b ∈ S` |
| `dec` | not the paper's node; `decᵐ` = "drop every `x` that has a `b` to its right" | §2 |
| `bdec = [ε/xb²]ᵐ` | **PROVEN** (deletion; borders are the only `xb²` occurrences, none created at junctions) | 0 failures on all `benc(X)`, `\|X\| ≤ 5` |
| `tail`, `head` | **PROVEN** — the paper's constructions transfer *verbatim* | all passes are deletions of patterns containing `bb`, images contain none, so each pass performs exactly one deletion and rescans inertly; verified: 1,365 inputs each, 0 wrong; total deletion steps per tail = 1 as predicted |
| `cat(X,Y) = dec([enc(X)/xb²][enc(Y)/xb³](xb²xb³))` | **PROVEN** in `V[enc,dec]` | each pass replaces the single whole marker (patterns contain `bb`, images don't, images never begin with `b`), output is pattern-free, restart inert after one step; verified 0/7,225 wrong (\|X\|,\|Y\| ≤ 3) |
| `eq` | **PROVEN** in `V[enc,dec]` (paper's construction) | patterns are `benc` images, `\|pattern\| ≥ 4 > 1 =` \|replacement\|, so each pass is one replacement then inert; verified 0 wrong of 116,281 pairs |
| `if` (paper's) | **REFUTED** | 945/3,570 instances diverge: the node `[enc(X)/⊤]ᵐ` has single-char pattern `⊤ ⊂ enc(X)` whenever `X` contains `⊤` — the `B ⊂ A` divergence |
| `if` (redesigned) | **PROVEN** in `V[enc,dec]` | deletion-based: `S = enc(X)·M·C·enc(Y)·M`, nodes `[ε/enc(X)M⊥]`, `[ε/M⊤enc(Y)M]`, `[ε/M]` — the control character `C` sits *inside* the patterns, so each pass deletes exactly its branch; all passes are deletions (total); verified 0/14,450 wrong |
| `rep_n` (paper's, hypothesis (H)) | **REFUTED** as stated | 3,605/21,760 (H)-respecting instances diverge (all failures are divergences, never wrong outputs) |
| `rep_n` under (H) **+ (H′′)** | **COMPUTATIONAL: correct** | (H′′): `X_i ∉ {b, x}` for all `i`. Then 0 failures in 520,898 instances (rep₁: 23,800; rep₂: 295,988; rep₃: 201,110). Divergence mechanism **PROVEN**: the renaming pass `[m_i/enc(X_i)]ᵐ` has `enc(X_i) ∈ {x, xb}` a substring of the marker `m_i = xb^{i+1}` exactly when `X_i ∈ {b, x}`, i.e. `B ⊂ A` — and all 3,605 observed divergences occur in renaming passes with `X_i ∈ {b, x}` |
| single-node primitives | **PROVEN + verified** | `[ba/ab]ᵐ = sort` to `b*a*`; `[ab/ba]ᵐ` = reverse sort; `[a/aa]ᵐ` = run-collapse of `a`-runs (a *single node*!); the two collapse nodes commute; spread round trip `[b/xb]ᵐ ∘ [bxb/bb]ᵐ = id` on `xb`-free inputs |

**Theorem 3.1 (rep_n transfer, precise statement).** With the paper's hypothesis (H)
(`|X_i| = 1` or `X_i` does not end in `x`) *plus* (H′′) (`X_i ∉ {b, x}` for all `i`), the paper's
rep_n construction, read with restart nodes and `enc/dec` as black boxes, agreed with the same
construction read with baseline nodes (which the Lean development proves correct, i.e. computes
the freezing semantics of the paper's Definition (rep)) on **520,898 / 520,898** tested instances.
**COMPUTATIONAL.** The per-pass story is subtle: in 81 of 33,320 renaming passes the restart pass
*differed* from the baseline pass (restart replaces an occurrence overlapping a marker that greedy
skips), yet the repair and instantiation stages absorbed every such difference in all tested
cases. A proof of the transfer — presumably by re-running the paper's Stage-1 "no shadowing"
argument with restart bookkeeping — is open (Problem 7).

**Theorem 3.2 (what the architecture reduces to). PROVEN (as a reduction).** If `enc, dec ∈ V`
(by *any* V-expressions), then `cat`, `eq`, `if`, `head`, `tail`, `bdec`, and `rep_n` (the last
under (H)+(H′′), computationally) are all in `V`, by the rows above. Conversely, every one of
these constructions must *duplicate or relocate* variable text — operations that force a total
injective growing map — which is exactly what IC (§4) conjectures impossible in the core. So the
paper's whole Section 2–3 tower stands or falls with two questions: **is `enc` (any total
injective growing function) reachable in V?** — blocked by IC in the core fragment — and **is
`dec` reachable in V?** — a separate open question, since the natural node `[b/xb]ᵐ` computes a
different (total) function (§2) and greedy non-overlapping behavior has no known restart
simulation (Problem 3).

---

## 4. Expressibility versus the baseline L

### 4.1 The no-injective-node theorem

**Lemma 4.1. PROVEN.** Let `[A/B]ᵐ` be total on all of `Σ*`. Then `B ⊄ A`, and `f(A) = f(B) = A`
with `A ≠ B`. In particular no total restart node is injective.
*Proof.* Totality forces `B ⊄ A` (Theorem 1.3.4: input `B` contains `B`). Then `A` contains no
`B`, so `f(A) = A`; and the trajectory from `B` is `B → A` after one step, so `f(B) = A`; and
`A = B` would give `B ⊂ A`. ∎

**Theorem 4.2 (no total injective constant-pattern core V-expressions). PROVEN.** For any arity
`n ≥ 1`, every *total* `V-cc` expression with at least one node is non-injective (on `(Σ*)ⁿ`).
*Proof.* By the pipeline normal form write `E = h_k ∘ ⋯ ∘ h₁` applied to an atomic scrutinee
(variable `X_j` or constant). If the scrutinee is a constant, `E` is constant, not injective.
Otherwise, since `E` is total, the innermost pass `h₁ = [A₁/B₁]ᵐ` is defined on all of `Σ*`, hence
total; Lemma 4.1 gives `h₁(A₁) = h₁(B₁) = A₁ ≠ B₁`, and `A₁, B₁` differ only in the scrutinee's
value, so `E(…, A₁, …) = E(…, B₁, …)`. ∎
**Corollary 4.3. PROVEN.** The only total injective 1-variable function in `V-cc` is `X₁` (the
identity; zero nodes). Verified computationally: among the 162 total single nodes with
`|A|, |B| ≤ 3`, **0 are injective** (on all 511 inputs of length ≤ 8); depth-2 search is vacuous
(the first node is never injective).

### 4.2 Two separations

**Theorem 4.4 (V-cc ⊄ L, on total functions). PROVEN.** The *amplifier* `[baa/ab]ᵐ` is a single
`V-cc` node, total, with exponential growth (Theorem 5.1): on input `ab^{n-1}` its output has
length `2^{n-1} + n − 1`. Every `L`-reachable function satisfies the paper's Length Bound
`|⟦E⟧(S⃗)| ≤ C_E(1+M)^{deg E}` on its domain, which exponential growth eventually exceeds. ∎
(The same witness refutes `V ⊴ L` for **partial** functions, since the Length Bound constrains
defined values only.)

**Theorem 4.5 (L-cc ⊄ V-cc, on total functions). PROVEN.** Doubling-the-a's, `D = [aa/a]`
(replace each `a` by `aa`), is a total, injective (`[a/aa]` inverts it on the image), growing
single `L-cc` node. By Theorem 4.2, `D ∉ V-cc`. ∎ (Injectivity of `D` verified on all inputs of
length ≤ 8.)

**Corollary 4.6. PROVEN.** `L-cc` and `V-cc` are **incomparable** (on total functions, and on
partial functions: both witnesses are total).

**Theorem 4.7 (safe fragment transfer). PROVEN.** Every `L`-expression all of whose nodes
`[R/P]` have constant, nonempty, character-disjoint `R`, `P` computes, read in `V`, the same
partial function as in `L`. (Theorem 1.5, node by node.) So `L-safe ⊴ V`.

### 4.3 The IC conjecture

**Conjecture (IC).** No 1-variable *core* V-expression (variable patterns allowed, no
concatenation) computes a **total, injective, somewhere-growing** function.
Evidence, all **COMPUTATIONAL**:
- Theorem 4.2 settles the constant-pattern case (**PROVEN**).
- 324 one-node variable-pattern expressions over an 18-function library of V-computable parameter
  functions (id, constants, deletions, collapses, sort, disjoint replacers): **0** total +
  injective + growing.
- Two-node expressions: vacuous — the library contains no injective first component to build on.
- Every natural injective-growing candidate (doubling `S ↦ SS`, `enc`, `X ↦ X^{|X|}`-variants)
  either needs concatenation or is a variable-pattern node whose replacement contains its pattern
  (the `B ⊂ A` divergence, in variable form: e.g. `[X₁X₁/X₁]ᵐ` diverges on every nonempty input).

**Consequences.** IC ⟹ `enc ∉ V-core` ⟹ `cat`, `rep_n`-style text relocation is not available
without concatenation ⟹ `V ⊴ V-core` fails and (conjecturally) `L ⊄ V`. Note the converse
direction is wide open: even `L ⊴ V` on total functions is open, since it would require e.g.
`D = [aa/a] ∈ V` in full `V` (with concat) — and `S ↦ SS` shows concatenation *does* give
injective growing maps in `V`-with-concat, so IC does not immediately block it.

### 4.4 Concatenation eliminability

The paper's Theorem (core) — `L ⊴ L-core`, concatenation is conservative sugar — is **PROVEN**
there. For `V` the analogous statement `V ⊴ V-core` is **OPEN** and conjectured **false**:
eliminating concatenation requires `cat`, whose construction relocates variable text at marked
positions (`enc`-images inserted at markers), the operation IC predicts unavailable; moreover
`cat ∈ V` trivially (the constructor itself). Related evidence: run-collapse `[a/aa]ᵐ` — a single
V node — is conjectured outside every *bounded-depth baseline* pipeline: `k` sequential baseline
halvings `[a/aa]` collapse exactly the runs of length ≤ `2^k` (smallest failing run `2^k + 1`,
verified for `k = 1..4`: 3, 5, 9, 17), so no fixed baseline pipeline collapses all runs.
**CONJECTURE.**

---

## 5. Complexity and length growth

### 5.1 The amplifier

**Theorem 5.1 (amplifier). PROVEN.** For every `S ∈ {a,b}*`,
`[baa/ab]ᵐ(S) = b^{#b(S)} · a^{v(S)}`, where `v(S)` is the value of `S` read as a base-2 numeral
in Horner order (`a = +1`, `b = ×2`): `v(ε) = 0`, `v(aT) = 1 + v(T)`, `v(bT) = 2·v(T)`.
*Proof.* Track three quantities along the trajectory: `#b`, `v` (as defined), and `#a`.
The step replaces the leftmost `ab` by `baa`. (i) `#b` is preserved (both blocks contain one
`b`). (ii) `v` is preserved: an `a` *left of the site* sees the same number of `b`'s to its right
(one, either way); inside the block, the single `a` of `ab` has `1 + k` `b`'s to its right
(where `k = #b` of the tail) and contributes `2^{1+k}`, while the two `a`'s of `baa` each see
`k` and contribute `2·2^k` — equal; `a`'s right of the site are untouched. (iii) `#a` increases
by exactly 1 per step, and (iv) `v ≥ #a` always (every `a` contributes ≥ 1 to `v`). Hence the
trajectory has **exactly `v(S) − #a(S)` steps**, and the fixpoint has `#a = v`; being `ab`-free
with `#b = #b(S)` and `#a = v(S)` it is `b^{#b(S)}a^{v(S)}`. ∎
Verified: 0 mismatches on **all** binary strings of length ≤ 10; base-`k` variants
`[ba^k/ab]ᵐ`, `k = 3..6`, verified on all strings ≤ 7; the exact step count `v(S) − #a(S)`
verified on samples. **COMPUTATIONAL** corroboration.
Growth on `ab^{n-1}`: output length `2^{n-1} + n − 1` and **exactly** `2^{n-1} − 1` steps
(verified `n ≤ 12`). The whole amplifier family `{[aab/ba]ᵐ, [abb/ba]ᵐ, [baa/ab]ᵐ, [bbaa/ab]ᵐ}`
shares this growth curve (verified); proving the other three is routine symmetry.

### 5.2 Consequences for the paper's complexity theorems

- **Length Bound: REFUTED for V.** A single V node has exponential output growth
  (Theorem 5.1), exceeding `C(1+M)^{deg}` for every `C, deg`.
- **Soundness (reachability ⟹ polynomial time): REFUTED for V.** The amplifier runs for
  `2^{n-1} − 1` steps. (Total V-functions are still computable, and V-pipelines are bounded, so
  `V` sits inside the partial computable functions; whether `V` — even with variable patterns and
  concatenation — is Turing-complete is open, Problem 4.)
- **The paper's growth-based separation (`X ↦ X^{2^{|X|}} ∉ L`) does not lift to `V`:** `V-cc`
  already contains the amplifier (§5.1), and the towers of §5.3 dominate `2^{cn}` growth with a
  handful of nodes. Whether that *particular* function is `V`-reachable is a separate, unaddressed
  question — the point is that growth arguments cannot separate `V` from anything above it.

### 5.3 Tower growth (how far does it go?)

**Theorem 5.2 (tower pipeline). PROVEN** (component formulas; verified `n ≤ 6`, where the final
string has length 131,091). On input `ab^{n-1}` (`n ≥ 2`):
1. `t₁ = [baa/ab]ᵐ(ab^{n-1}) = b^{n-1} a^{2^{n-1}}` (Theorem 5.1);
2. `t₂ = [ab/aa]ᵐ(t₁) = b^{n-1}(ab)^{2^{n-2}}` — *spread*: each step turns the leading `aa` of
   the trailing `a`-run into `ab`, invariant `b^{n-1}(ab)^k a^{2^{n-1}−2k}`, terminating at
   `k = 2^{n-2}`;
3. `t₃ = [baa/ab]ᵐ(t₂) = b^{n-1+2^{n-2}} · a^{2^{2^{n-2}+1}−2}` — the amplifier evaluates the
   spread string as a binary numeral: each `a` of `(ab)^{2^{n-2}}` has `2^{n-2}−i+1` `b`'s to its
   right, so `v(t₂) = Σ_{j=1}^{2^{n-2}} 2^j = 2^{2^{n-2}+1} − 2`.

So **three constant-pattern nodes give double-exponential growth** (`|t₃| ~ 2^{2^{n-2}}`).
Iterating the 2-node block `[baa/ab]ᵐ ∘ [ab/aa]ᵐ` maps `b^m a^K ↦ b^{m+⌊K/2⌋} a^{Θ(2^{K/2})}`
(same invariant calculations; the `b^m a^K` form is preserved), so each additional block adds one
exponentiation: `2t−1` constant-pattern nodes give output of tower height `t` in the input length.
**PROVEN** (block formula + induction; verified for `t = 1`, `n ≤ 12` and the 3-node pipeline
`t = 2`, `n ≤ 6`).

### 5.4 Growth spectrum at small pattern sizes

Among the **162 total** binary rules with `|A|, |B| ≤ 3` (inputs ≤ 11, cap 6,000):
**144** grow at most linearly (slope ≤ 1, e.g. deletions, disjoint replacers),
**14** grow with slope 2–3 (e.g. `[aa/b]ᵐ`, `[aaa/b]ᵐ`), and exactly **4** grow exponentially —
the amplifier family. No rule with intermediate (superpolynomial, subexponential) growth was
found. **COMPUTATIONAL.** Whether total restart growth exhibits a poly-vs-exponential dichotomy
is open (Problem 8).

### 5.5 Where the paper's polynomial-time architecture still holds

Everything in `L-safe` (§4.2) is restart-compatible and inherits the paper's bounds verbatim;
deletion nodes `[ε/B]ᵐ` are always total (**PROVEN**, length-decreasing) and linear-time; the
amplifier-free fragments of the toolkit (eq, if-redesign, head, tail, bdec, cat) are all
linear-pass pipelines whose restart runs perform exactly the baseline's single effective
operation per pass.

---

## 6. Open problems

1. **IC conjecture** (§4.3): no total injective growing 1-variable *core* V-expression. Positive
   or negative, it is the hinge of the comparison: IC ⟹ `enc ∉ V-core` ⟹ `L ⊄ V-core`; ¬IC
   plausibly yields `enc ∈ V` ⟹ the paper's whole toolkit (cat, eq, if, head, tail, rep_n)
   inside V (Theorem 3.2).
2. **Exact Agreement (⟸)** (Theorem 1.6): does "baseline output always pattern-free" force
   restart = baseline? The engine behind every toolkit transfer.
3. **`L ⊴ V` on total functions?** Even the single node `D = [aa/a]` (doubling-a's) in full `V`
   (concat + variable patterns allowed) is open.
4. **Is `V` Turing-complete?** Bounded pipelines of single-rule fixpoints already compute towers
   (Theorem 5.2); is unbounded control (a universal construction) reachable with variable
   patterns and concatenation? (In `L` the answer is no — polynomial time — so any such
   construction must exploit divergence-freedom of growing nodes.)
5. **Concatenation eliminability in V** (`V ⊴ V-core`?): conjectured false via `cat`.
6. **Totality/termination of a restart node**: is leftmost-strategy one-rule termination
   decidable? (Cf. Moczydłowski–Geser's single-threaded decidability, and the general one-rule
   open problem.) Also: complexity of deciding it.
7. **Proof of the rep_n transfer** under (H)+(H′′): why do the 0.2% of renaming passes that
   deviate from greedy (overlapping-occurrence replacements) get absorbed by the repair and
   instantiation stages?
8. **Growth dichotomy**: does every total `[A/B]ᵐ` grow either polynomially or ≥ `2^{cn}`?
   Nothing intermediate was found (§5.4). Related: can a length-preserving rule take
   super-quadratically many steps? (The weight proof gives ≤ `2^{|C|}`; the maximum observed is
   `O(n²)`, e.g. `[ab/ba]ᵐ` = bubble sort, `n(n−1)/2` steps, PROVEN by inversion count.)
9. **Characterize the exotic divergent rules** (`[aabb/ba]`, `[bbaa/ab]`, `[abba/bab]`,
   `[baab/aba]`, and the 66 with `|A| ≤ 6, |B| ≤ 3`): all have `|A| > |B|`, `B ⊄ A`, and a
   junction-regenerating overlap structure; do they fall into a known decidable class (grid
   rules? one-overlap-pair?) — and is every length-increasing rule with ≤ 1 overlap pair
   terminating?
10. **Inherited from the paper**: is reversal `S ↦ reverse(S)` reachable in V? (In L it is the
    paper's open problem 2; V's sort/collapse primitives make it no easier a priori.)

---

## 7. Relations summary

Classes: as defined in the header table; "total" = claim about total functions (paper's
*reachable*), "partial" = claim about partial functions (undefined = empty-pattern or divergence).

- `EXPR: L-safe ⊴ V — total — STATUS: PROVEN — character-disjoint nonempty-replacement passes agree with baseline node-by-node (Theorem 1.5).`
- `EXPR: V-cc ⊴ L — total — STATUS: REFUTED — the amplifier [baa/ab]ᵐ is total with exponential output growth, violating L's Length Bound (Theorem 5.1).`
- `EXPR: V ⊴ L — partial — STATUS: REFUTED — same witness; the Length Bound holds on defined values of every L-expression.`
- `EXPR: L-cc ⊴ V-cc — total — STATUS: REFUTED — doubling-a's [aa/a] is total injective growing in L-cc; every total ≥1-node V-cc expression is non-injective (Theorem 4.2).`
- `EXPR: L-cc ⊴ V-cc — partial — STATUS: REFUTED — both witnesses are total, so the separation holds for partial functions too.`
- `EXPR: L ⊴ V — total — STATUS: CONJECTURE (against) — blocked at minimum by doubling-a's ∉ V (open) and, via IC, by the absence of any total injective growing core V-function; only the safe fragment is known to transfer.`
- `EXPR: L ⊴ V — partial — STATUS: CONJECTURE (against) — same obstructions; the baseline's greedy non-rescanning scan has no known restart simulation.`
- `EXPR: V ⊴ V-core — partial — STATUS: CONJECTURE (against) — would need cat (insertion of variable text at marked sites) in core V, which IC blocks; cat ∈ V trivially via the concatenation constructor.`
- `EXPR: L ⊴ L-core — partial — STATUS: PROVEN — the paper's Theorem (core); its proof needs cat, hence does not lift to V.`
- `EXPR: {sort, reverse-sort, run-collapse, spread} ⊴ V-cc — total — STATUS: PROVEN — each is a single constant-pattern restart node (verified; sort/collapse formulas proven).`
- `EXPR: {cat, eq, if, head, tail, rep_n|(H)+(H′′)} ⊴ V[enc,dec] — total — STATUS: PROVEN for cat, eq, if(redesigned), head, tail, bdec (single-effective-step passes; Theorems 3.1–3.2 rows) — COMPUTATIONAL for rep_n (0 failures in 520,898 instances; per-pass deviations observed).`
- `EXPR: enc ⊴ V — total — STATUS: REFUTED for the paper's node ([xb/b]ᵐ diverges iff b ∈ S); OPEN for arbitrary V-expressions (equivalent to ¬IC-core in the core fragment).`
- `EXPR: run-collapse ⊴ bounded L pipelines (fixed depth k) — total — STATUS: CONJECTURE (against) — k baseline halvings fail on runs of length 2^k+1 (verified k ≤ 4); one restart node suffices.`

---

## Appendix: computational protocol

All scripts in `docs/proof/research/scratch/restart/` (`python3`, library `substlib.py`:
`subst` (paper Definition 1), `restart` (Definition R, step cap, `Diverge`/`Undefined`
exceptions), enumerators). Every experiment is exhaustive over the stated finite domain unless
"sampled" is said.

| script | verifies | headline numbers |
|---|---|---|
| `exp1_agreement.py` | Theorems 1.5, 1.6; smallest disagreements | binary 210 pairs × 511 inputs (86,626 defined runs), ternary 156 pairs (149,055 runs), 0 mismatches |
| `exp2_termination.py` | Theorem 1.3 classification | 930 pairs, 764 total / 166 divergent, 0 prediction errors, 4 exotic divergent rules |
| `exp2b_exotic.py` | minimal diverging inputs + traces | `baa`, `aab`, `aaba`, `babb`; linear growth forever |
| `exp3_amplifier.py` | Theorems 5.1, 5.2 | 0 mismatches (len ≤ 10); base-`k` ≤ 7; growth `2^{n-1}+n−1`, steps `2^{n-1}−1` (n ≤ 12); tower `n ≤ 6` (|t₃| = 131,091) |
| `exp4_algebra.py`, `exp4b_algebra_fix.py` | §2 audit | Independent Substitution 2,162,160 instances; Double Substitution 5,660 inner divergences; `decᵐ` formula 511 inputs |
| `exp5_erratum_injectivity.py` | paper erratum; Lemma 4.1 survey | erratum witness; 162 total nodes, 0 injective; 22 total growing single nodes |
| `exp6_toolkit.py` | eq / if / primitives | eq 0 wrong of 116,281 pairs; paper-if 945/3,570 diverge; redesigned-if 0/14,450; sort/collapse/spread confirmed |
| `exp7_growth_strategy.py` | growth classes; rightmost sensitivity | 144 linear / 14 slope-2–3 / 4 exponential; 0 strategy flips |
| `exp8_ic_search.py` | IC search | 324 one-node variable-pattern expressions, 0 hits |
| `exp9_wrapup.py` | growth audit; enc divergence; doubling injectivity; deletion totality; bdec | 16 rules above linear; `[aa/a]` injective (len ≤ 8); all `[ε/B]ᵐ` total (|B| ≤ 4) |
| `exp10_cat_rep.py`, `exp10b/c/d_rep.py` | cat; rep_n transfer + per-pass analysis | cat 0/7,225; rep_n (H): 3,605/21,760 diverge, all renaming passes; (H)+(H′′): 0/520,898; 81/33,320 renaming passes deviate |
| `exp11_headtail.py` | head/tail transfer | 1,365 + 1,365 inputs, 0 wrong; 1 deletion step per tail |

## Sources

One-rule semi-Thue termination (context for §1.2):
- [A survey on the one-rule termination problem (arXiv:2608.19397)](https://arxiv.org/html/2608.19397v2)
- [Moczydłowski & Geser, *Termination of single-threaded one-rule semi-Thue systems*, RTA 2005](https://link.springer.com/chapter/10.1007/978-3-540-32033-3_25)
- [Geser, *Termination of one-rule semi-Thue systems with one overlap pair*](https://link.springer.com/chapter/10.1007/3-540-44881-0_29) ([NASA report version](https://ntrs.nasa.gov/citations/20020088729))
- [Kraus & Sattler, notes on string rewriting](https://nicolaikraus.github.io/docs/stringrewriting.pdf)
- [Geser, Hofbauer & Waldmann, *Match-bounded string rewriting systems*](https://link.springer.com/article/10.1007/s00200-004-0162-8)
- [MathOverflow: state of the one-rule semi-Thue termination problem](https://mathoverflow.net/questions/181057/whats-the-current-state-of-one-rule-semi-thue-system-termination-problem)
- [Geser, Waldmann & Wenzel, termination enumeration experiments](https://www.imn.htwk-leipzig.de/~waldmann/talk/16/wst/paper.pdf)
- [Hofbauer & Waldmann, termination exercises](https://www.imn.htwk-leipzig.de/~waldmann/talk/08/isr/questions.pdf)
- [On one-rule grid semi-Thue systems](https://hal.inria.fr/hal-00749289v1/file/on-one-rule-grid-semi-thue-systems.pdf)

Primary references: `docs/proof/main.tex` (baseline calculus, all Section 2–4 results audited
above), `docs/proof/lean/Subst.lean` (formalization, used as ground truth for the baseline rep_n
construction in `exp10*`).

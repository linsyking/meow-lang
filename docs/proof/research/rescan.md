# The Rescan Variant: `[A/B]ᵘ C` — unsafe substitution that re-enters inserted text

Research report on the expressive power of the **rescan** primitive, studied against the
baseline calculus **L** of *String Substitution Theory for Finite Charset* (`main.tex`).
Throughout, `X ⊴ Y` means "every function reachable in calculus X is reachable in calculus Y".

- **V = `[A/B]ᵘC`** ("unsafe rescan"): a single left-to-right scan; on a match of `B`, replace
  it by `A` and **continue the scan at the first character of the inserted text** (contrast
  the paper's Definition 1, where the scan resumes *after* the inserted text). Partial
  function — may diverge.
- Calculi: **U** = paper-style expressions with `[R/P]ᵘ` nodes; **U-core** = concat-free
  fragment; **U-concat** = with concatenation nodes `E₁E₂`; **L**, **L-core** analogous with
  safe nodes. Scripts: `docs/proof/research/scratch/rescan/` (`substlib.py`,
  `exp_semantics.py`, `exp_algebra*.py`, `exp_toolkit.py`, `exp_express*.py`,
  `exp_runcollapse.py`, `exp_perpair*.py`).
- Status labels: PROVEN (proof written), COMPUTATIONAL (exhaustive on a stated finite
  domain), CONJECTURE, REFUTED.

---

## 1. Semantics

### Definition R (Rescan Substitution)
Given strings `A`, `B` with `B ≠ ε` and any `C`, the process maintains a frozen output
prefix `O` and a work string `T` (initialized `O = ε`, `T = C`):

```
while B ⊑ T:
    q := position of the leftmost occurrence of B in T
    O := O · T[:q]           # freeze everything before the match
    T := A · T[q+|B|:]       # replace; scan re-enters inserted A at its first character
return O · T
```

`[A/B]ᵘC` is the value if the loop terminates, ⊥ (divergent) otherwise. `[A/ε]` is
undefined exactly as in the paper. This is Definition 1 of the paper with the single
clause "the scanning never restarts inside inserted text" **deleted** — that clause is
the entire difference between the two primitives.

### Lemma 1 (Stack Process) — PROVEN
`[A/B]ᵘC` is the leftmost rewriting of `C` by the single rule `B → A`, restricted to the
never-refrozen suffix: state `(O, T)` as above; each step pops the prefix of `T` up to and
including the leftmost `B` and pushes `A` on top (a stack whose top is the front).
*Cross-validation*: a direct implementation of the scan-with-position semantics and the
`(O,T)` process agree on 3000 random instances (|A|,|B| ≤ 3, |C| ≤ 7): 0 mismatches.
COMPUTATIONAL.

### Theorem 2 (Agreement with the Baseline) — PROVEN
For `B ≠ ε`:

  **`[A/B]ᵘ = [A/B]` (as functions of `C`) ⟺ `B ⊄ A` AND no nonempty suffix of `A` is a
  proper prefix of `B`.**  (Call the right-hand side *condition (∗)*.)

*Proof.* (⟸) Under (∗), no occurrence of `B` can start inside an inserted copy of `A`:
one lying entirely inside would give `B ⊂ A`; one straddling the end of the copy makes a
nonempty suffix `A[i:]` of `A` a proper prefix of `B`. Hence after every insertion the
first possible match start is the position just past the inserted text — exactly the safe
resume point — and induction over match events shows the two scans freeze identical
prefixes. (⟹) If `B ⊂ A`, take `C = B`: `T₁ = A`, and `T_k` has prefix `A ⊋ B` for all
`k ≥ 1`, so the process never halts while `[A/B]B = A`. Otherwise let `i` be minimal
with `A[i:]` a proper prefix of `B`, and put `β := B[|A|−i:]`, `C := B·β`. Safe:
`[A/B](B·β) = A·β` (the residue `β` is shorter than `B`). Unsafe: after the first match
`T₁ = A·β`; the leftmost match of `B` in `T₁` is at position `i` (none earlier by
minimality of `i` and `B ⊄ A`), consuming exactly `A[i:]·β = B`, so `T₂ = A`, which is
`B`-free; the result is `A[:i]·A`. If `A[:i]·A ≠ A·β` we are done. If equal, then
`β = A[|A|−i:]` (last `i` characters) and comparing the middle gives `A[k−i] = A[k]` for
`i ≤ k < |A|`, i.e. `A` has period `i`; then `B = A[i:]·β = A[:|A|−i]·A[|A|−i:] = A`,
contradicting `B ⊄ A`. ∎

COMPUTATIONAL: biconditional verified with 0 violations on Σ={a,b}, |A|≤4, |B|≤3, |C|≤6
and Σ={a,b,c}, |A|≤3, |B|≤2, |C|≤5. **Smallest value difference**: `[a/aa]ᵘ"aaa" = "a"`
vs `[a/aa]"aaa" = "aa"` (a 6-character triple `(A,B,C)`).

### Theorem 3 (Totality and Bounds) — PROVEN
1. **`[A/B]ᵘ` is total ⟺ `B ⊄ A`.** The divergence domain is exactly
   `{C : B ⊂ A ∧ B ⊂ C}`.
2. When `B ⊄ A`, the number of matches is **≤ `|C| − |B| + 1`**, and
   **`|[A/B]ᵘC| ≤ |C|·(1+|A|)`** — the same shape as the paper's safe Length Bound.

*Proof.* If `B ⊂ A` and `B ⊂ C`, then `T₁ = A·(suffix)` and every `T_k (k ≥ 1)` has
prefix `A ⊇ B`, so the loop never exits. If `B ⊄ A`: `T_k` has prefix `A` for all `k ≥ 1`;
a match with `q_k + |B| ≤ |A|` would give `B ⊂ A`, so `q_k + |B| ≥ |A|+1`, whence
`|T_{k+1}| = |A| + |T_k| − q_k − |B| ≤ |T_k| − 1` — every step after the first strictly
decreases `|T|`, while `|T_k| ≥ |A|`. So at most `|T₁| − |A| ≤ |C| − |B|` steps follow the
first. Net length change per match is `|A| − |B|`, so `|out| = |C| + m(|A|−|B|)` with
`m ≤ |C|−|B|+1 ≤ |C|`, giving `|out| ≤ |C|(1+|A|)`. ∎

COMPUTATIONAL: 0 violations over Σ={a,b}, |A|≤4, |B|≤3, |C|≤6 and Σ={a,b,c} analog; step
bound violated only vacuously (C = ε); both length bounds verified with 0 violations.
Note the surprising corollaries: **no straddle-induced divergence exists at all**
(divergence ⟺ pattern ⊆ replacement), and total instances do at most *linearly many*
matches — one ᵘ-node cannot perform super-linear cascades.

### Corollary (Partial Identity) — PROVEN
`[A/A]ᵘC = C` if `A ⊄ C`, ⊥ otherwise. (The paper's Identity Substitution theorem
degenerates to a partial identity.) COMPUTATIONAL: 0 violations, |A|≤3, |C|≤5.

### Comparison with the restart variant `[A/B]ʳ` — PROVEN/COMPUTATIONAL
Restart (rescan the *whole* string from 0 after each replacement) has **the same
divergence domain** `{C : B ⊂ A ∧ B ⊴ C}` (the leftmost match position is non-decreasing
and advances by ≥ `|A|−|B|+1` per step when `B ⊄ A`; verified: 0 violations,
Σ={a,b}, |A|≤3, |B|≤3, |C|≤5), and the **same totality condition** `B ⊄ A`. But the
values differ: restart re-matches text that rescan has frozen. Examples
(`(A,B,C) → safe / ᵘ / ʳ`):
- `('b','ab','aab') → 'ab' / 'ab' / 'b'`  (ᵘ = safe, ʳ differs)
- `('', 'ab','aabb') → 'ab' / 'ab' / ''`
- `('aa','ba','bba') → 'baa' / 'baa' / 'aaa'`
Census: 1922 agreeing pairs vs. 6 distinct difference patterns found (Σ={a,b}, |A|≤2,
|B|≤2, |C|≤5). So **ᵘ ≠ ʳ as partial functions** (REFUTED: equality), both total exactly
on `B ⊄ A`, and both compute run-collapse for the pair `('a','aa')` (verified |S|≤10).
Mutual expressibility: OPEN.

---

## 2. Basic Algebra — the paper's Section 2 under V

| Paper result | Status under ᵘ |
|---|---|
| Identity Substitution `[A/A]S = S` | **Degenerate**: partial identity (above). |
| Direct Substitution `[A/B]B = A` | **Survives with hypothesis `B ⊄ A`** (else ⊥). PROVEN + verified (|A|≤3, |B|≤3): `[A/B]ᵘB = A` iff `B ⊄ A`. |
| Substitution Elimination | **Survives** trivially (`B ⊄ S ⇒` no match). |
| Independent Substitution | **Survives** for total nodes with nonempty replacement (verified 0 violations; proof: chars of `A` are never consumed nor inserted, and adjacent `A`-chars stay adjacent). **But see the erratum below** — the lemma is false for *empty* replacement in the baseline itself. |
| Stepping-into `[C/A](AB) = C·[C/A]B` | **REFUTED.** `[a/aa]ᵘ("aa"·"a") = "a"` but `"a"·[a/aa]ᵘ"a" = "aa"`. Survives under condition (∗) (immediate from Theorem 2). |
| Head/Tail Elimination | **Survive verbatim** — pure occurrence combinatorics in `AB`, no scanning involved. |
| Double Substitution Lemma | **REFUTED as a round trip; exact degeneration**: for `X ⊊ Y`, `[X/Y]ᵘ[Y/X]ᵘZ` is defined iff `X ⊄ Z`, and then equals `Z` (both passes inert). PROVEN (needs no unborderedness — vacuous) + verified (Σ={a,b,c}, |X|≤2, |Y|≤3, |Z|≤4: 0 violations; first divergence case `(X,Y,Z)=('a','ab','a')`). |
| Encoding/Decoding Theorem | **REFUTED.** `enc = [xb/b]ᵘ` diverges on every `b`-containing input (`'b' ⊂ 'xb'`): 57/63 inputs |S|≤5 diverge; the round trip works only on `b`-free strings where enc is the identity. `dec = [b/xb]ᵘ` alone **survives** (safe pair; equals safe dec on all |S|≤6). |
| cat (Thm `cat`) | **REFUTED**: ok=26, diverged=114, **wrong values=501** (Σ={a,b}, |X|+|Y|≤6). |
| tail, head | **REFUTED**: ok only on `b`-free inputs (6/63), 57 diverge. |
| eq | **REFUTED**: ok=26, diverged=615, wrong=0 (diverges cleanly). |
| if (Selection) | **REFUTED**: ok=63, diverged=1219, wrong=0. |
| rep_n (Multiple Substitution) | **REFUTED at its foundation**: the construction's internal encoder `[x'b'/b']ᵘ` diverges on every `b'`-containing scrutinee, so `enc′(Y_i)` cannot be computed for data `Y_i ∋ b'`. Even cat-via-rep₂ over |Σ|=4 (patterns `a,b` avoiding the encoding chars `c,d`): ok=169, diverged=272 (first at data `∋ c`), wrong=0. |
| Totality (`Safe(E) ⇒ total`) | **REFUTED**: `[a/a]ᵘX₁` satisfies the paper's syntactic `Safe` (anchored constant pattern, all components safe) but diverges on all 26/31 inputs ≤ 4 containing `a`. |
| Single Character Subst. / `σ^{|S|}` | **As stated REFUTED** (`[σ/σ]ᵘ` diverges on `σ`-containing inputs). **Repaired — PROVEN**: `σ^{|S|} = ∏_{c≠σ}[σ/c]ᵘ · X₁` (each pass a safe pair); e.g. over Σ={a,b}: `[a/b]ᵘ[b/a]ᵘX₁ = a^{|X₁|}`, 0/127 failures. |
| Polynomial Growth (`X^{|X|}`) | **REFUTED as constructed**: the instantiation pass `[X₁/σ]ᵘ` diverges iff `σ ⊂ X₁` (26/62 test failures, first at `X='a'`). Not found in bounded ᵘ-searches (73,205 depth-2 pipelines over variable/constant pools) — CONJECTURE: not U-reachable at all (see §5). |
| Unreachable `X^{2^{|X|}}` | **Survives**: still unreachable in U (total fragment), by the transferred Length Bound (§6). |

### Erratum in the baseline paper (found via this study) — PROVEN
The paper's **Independent Substitution** lemma ("`A∩B=∅, A∩C=∅, C≠ε ⇒ A⊂[B/C]S ⟺ A⊂S`")
is **false when the replacement `B = ε`**, under the paper's own safe semantics: deletions
can juxtapose formerly separated characters. Smallest counterexample:
`A='cc'`, `B=ε` (replacement), `C='a'` (pattern), `S='cac'`:
`[ε/a]'cac' = 'cc' ⊇ 'cc'` but `'cc' ⊄ 'cac'`. COMPUTATIONAL: 20 violations over
A ∈ {c,cc,ccc}, |C|≤2, |S|≤4; **0 violations with nonempty replacement** (|B| ≤ 2).
The gap in the paper's induction: with `B = ε` an occurrence of `A` may straddle the
(empty) insertion junction `X·[B/C]Y`. The hypothesis `B ≠ ε` should be added. (The
lemma survives under ᵘ as well, for nonempty replacement and total nodes.)

---

## 3. Toolkit under ᵘ: the no-escape circularity

Why does *everything* in the paper's toolkit break? The paper's architecture is a
**marker discipline**: encode data into `enc`-images that cannot contain marker patterns
(`xb^k`), then move data around with passes whose *patterns* are markers. Under ᵘ, a pass
`[R/P]ᵘ` diverges iff `P ⊆ R` — so every pass whose **replacement contains its own
pattern** is fatal. The discipline has exactly one load-bearing violation:

- The **encoder** `[xb/b]` inserts `xb` *for* `b`: the replacement contains the pattern.
  This single pass is what the "never restarts inside inserted text" clause buys.
- Conversely every *instantiation* pass `[enc(Y)/marker]` is safe *only because*
  `enc`-images are marker-free — which requires the encoder.

**Lemma 4 (Constant-Pipeline Non-Injectivity — "no escape from constant passes") — PROVEN.**
Let `E = [W_k/P_k]⋯[W_1/P_1]·X₁` with all `W_i, P_i` constants, `P_i ≠ ε`. If `⟦E⟧` is
total, it is **not injective**.
*Proof.* If `P₁ ⊆ W₁`, the rightmost pass diverges on the raw input `X₁ = P₁`
(Theorem 3), contradicting totality. Otherwise `[W₁/P₁]ᵘ(P₁) = W₁` (insert, rescan a
`P₁`-free `W₁`, halt) and `[W₁/P₁]ᵘ(W₁) = W₁` (`P₁ ⊄ W₁`), with `P₁ ≠ W₁`; both inputs
feed the identical suffix pipeline, so `⟦E⟧(P₁) = ⟦E⟧(W₁)`. ∎

Corollaries: no constant-pattern ᵘ-pipeline computes an injective escaping; in particular
**every** per-character encoding scheme `c ↦ w_c` (`c ∉ w_c`, forced by totality) fails —
verified exhaustively for all 32 total 2-pass per-char pipelines over Σ={a,b}: all
non-injective. The paper's `enc` works *precisely because* its replacement contains its
pattern — the one thing ᵘ forbids.

**Bootstrapping attempts (all blocked, documented for the record):**
- Third-character encodings over |Σ|≥3 (`y ↦ xx`, `b ↦ xb`): the `[xb/b]ᵘ` pass still
  diverges; any per-char code avoiding its own character collides with the code itself
  (Lemma 4).
- Digram codes, marker-wrapped data, head-anchored self-referential codes
  (`[m·(X∖c)·m/c]ᵘX`): each needs a marker character disjoint from all possible data —
  impossible since data ranges over all of Σ*, or diverges when the head equals a marker
  character.
- **cat in U-core**: CONJECTURE unreachable. Theoretical blocker: any pass instantiating
  a marker with data `[R/P]ᵘ` diverges on data containing `P`; escaping the data first
  requires enc; enc requires a replacement containing its pattern. Bounded search
  (18,816 depth-2 core 2-ary pipelines over variable/constant pools, Σ={a,b}): nothing.
  Consequence: the paper's **Concatenation Elimination theorem (Thm `core`) does not
  transfer** — under ᵘ, the with-concat and core calculi plausibly differ.
- **eq / if / head / tail**: all route through enc (REFUTED by census); no alternative
  found. Note simple bracketing `β(X)=m·X·m` fails (marker chars can occur in data, so
  `β(Y) ⊂ β(X)` does not imply `X=Y` — e.g. `X='acb', Y='a'` with `m='c'`).

**What survives or is repairable in U:** `dec = [b/xb]ᵘ` (safe pair); `σ^{|S|}`
(repaired, above); safe-pair passes generally (= safe semantics, Theorem 2); run-collapse
(one node, §5); all of L's *constant-pattern* passes whose pairs satisfy (∗).

---

## 4. Complexity

**Theorem 5 (Length Bound and Poly-Time Soundness for U) — PROVEN (transfer of the
paper's Section 4).**
1. Whenever defined and `B ⊄ A`: `|[A/B]ᵘC| ≤ |C|·(1+|A|)` (Theorem 3) — the exact shape
   of the paper's safe per-pass bound.
2. By the paper's pipeline normal form (pure syntax; unchanged) and induction on
   expressions with `deg` as in the paper, every U-reachable *total* function `f`
   satisfies `|f(S⃗)| ≤ C_E(1+M)^{deg E}`, `M = max(1,|S_i|)`.
3. Hence **every total U-reachable function is computable in polynomial time**: a
   pipeline of `k` nodes, each doing ≤ `|T|+1` matches (Theorem 3) with naive scanning
   `O(|T|·|B|)` per match, costs `O(|T|²·|B|)` per node with all intermediates
   polynomially bounded.

So although a ᵘ-node *feels* like unbounded iteration ("repeat until fixpoint" inside one
node), Theorem 3 caps it: **totality ⟺ `B ⊄ A`, and then at most linearly many matches.**
The divergence side is where the unbounded work went — it is partiality, not time.
- `X ↦ X^{2^{|X|}}` is not U-reachable (total fragment): same proof as the paper.
- But the converse direction is damaged: `X^{|X|}` (L-reachable by the paper's
  Proposition) plausibly is **not** U-reachable (its construction diverges; bounded
  searches fail) — see §5.

---

## 5. Expressibility vs the Baseline L

### 5.1 A new positive result for the baseline: run-collapse is in L — PROVEN
Let `collapse(S)` map every maximal `a`-run of `S` to a single `a` (other characters
untouched). Then, reading the pipeline right-to-left:

```
collapse(S) = [ε/ab] [ε/aba] [aab/a] S          (three constant safe passes)
```

*Proof sketch.* Pass 1 maps each `a ↦ 'aab'` (`b`'s unchanged), so each maximal `a`-run
becomes `(aab)^n` and every `'aba'` in the image sits at offset 1 mod 3 inside a run
image (blocks are `aab`/`b`; only the `aab|aab` junction spells `aba`). Pass 2 deletes
greedily: each deletion at offset 1 removes one block and the safe resume at the
deletion point re-exposes the next `aba`, so an isolated run image collapses `(aab)^n →
'aab'` — deletions cannot straddle run boundaries (junctions with `b`-blocks spell
`abb`/`baa`, never `aba`). Pass 3 deletes the `ab` at offset 1 of each remaining
`'aab'`, leaving `'a'`; the junction `'a'+'b'` never re-matches because the scan has
already passed the surviving `a`. ∎

COMPUTATIONAL: verified on all |S|≤14 over {a,b}, all |S|≤9 over {a,b,c}, 3000 random
strings of length 15–60, and `a^300`, `b·a^m`, `a^m·b` up to m=300: 0 mismatches.
(The mechanism — a *deletion* pass resuming at the deletion point and re-exposing
junctions — is available in the paper's own safe semantics; the paper never exploits it.)

### 5.2 run-collapse is in U — PROVEN
`collapse(S) = [a/aa]ᵘS`: in the stack process, matches of `'aa'` only occur inside
`a`-runs, each match shortens the current run by one, and the frozen prefix already
carries the collapsed part. Verified on all |S|≤10. So run-collapse separates nothing —
and this is *why* the 3-ary `[A/B]ᵘ` no longer yields an easy separation from L.

### 5.3 Direction U ⊴ L (can L express the rescan primitive?) — OPEN
If the 3-ary `[A/B]ᵘ` were L-reachable, so would be `[a/ab]ᵘ`; per-pair evidence:
- Trivially yes for safe pairs (`[b/a]ᵘ`, `[ab/aab]ᵘ`, …: one safe pass).
- **Nontrivially yes** for `('ab','ba')` and `('ba','ab')` (equal-length non-safe pairs):
  found and post-verified (2000 random strings up to length 40 + long runs):
  `[ab/ba]ᵘ = [ε/bab][ab/a][aa/a]`,  `[ba/ab]ᵘ = [ε/aba][bab/b][ba/b]`.
  Also `[a/aa]ᵘ` = run-collapse (§5.1).
- **NOT FOUND** (deep constant-pipeline searches: depth ≤3 with |A|,|B|≤3; depth ≤4 with
  |A|,|B|≤2; depth ≤2 with |A|,|B|≤4; witnesses = all strings ≤7 over {a,b} plus
  `a^m,b^m,(ab)^m,(ba)^m,a^m b^n,…` up to m=16; any hit post-verified on 2000 randoms
  up to length 40 and `a^60/b^60`) for six total pairs:
  `(a,ab)`, `(aa,ab)`, `(aab,ba)`, `(b,ba)`, `(ba,aab)`, `(bba,ab)`.
  **Candidate separation witness**: `f(S) = [a/ab]ᵘS = "keep the leading b's, then
  a^{number of a's}"` (an "a-flood": `b^i·a^j·(anything) ↦ b^i a^{#a's}`; identity on
  a-free strings). CONJECTURE: `f` is not L-reachable, hence **U(total) ⊄ L**.
  (Caveat: variable patterns were not searched; the paper's `rep₁` makes safe data-replace
  L-reachable, so the conjecture concerns the genuinely-cascading pairs.)

### 5.4 Direction L ⊴ U (can U express the baseline?) — OPEN
Every paper construction breaks (§2 census), and the blocker is structural:
- The **no-escape** Lemma 4 kills constant-pass encodings; per-char schemes all fail.
- Any "instantiate marker with data" pass `[R/P]ᵘ` diverges on data `∋ P`; escaping data
  into a marker-free subspace requires an encoder; an encoder's pass has replacement ⊇
  pattern — the exact ᵘ-divergence condition. This circularity is the precise content,
  for the toolkit, of the paper's "never restarts inside inserted text" clause.
- **Candidate separation witness**: `X^{|X|}` is L-reachable (paper) but plausibly not
  U-reachable: its construction's instantiation pass `[X₁/σ]ᵘ` diverges iff `σ ⊂ X₁`, and
  bounded ᵘ-searches (73,205 depth-2 pipelines over pools with variables, `b^{|X₁|}`,
  concatenations) find nothing. A route around would need e.g. patterns tuned to the
  data (`b^{maxrun+1}`) — themselves of unknown reachability. CONJECTURE:
  **L(total) ⊄ U**, witnessed by `X^{|X|}` (so the two calculi are incomparable on total
  functions, modulo the two conjectures above).

### 5.5 Partial functions
`[a/a]ᵘ` is the partial identity (undefined on a-containing inputs). For L to express it,
some L-pattern must evaluate to ε exactly on a-containing inputs. Bounded ε-set searches
(25,600 + 14,400 depth-1/2 pipelines over constant/variable pattern pools incl.
`X₁`, `[ε/a]X₁`, `[ε/b]X₁`, char-swaps, `[a/X₁]X₁`, `[X₁/a]X₁`): every realized ε-set is
an "avoidance" (∀-style) condition (`a`-free, `b`-free, tile-languages, …), never a
"contains" (∃-style) condition. CONJECTURE: the partial identity is not L-expressible,
i.e. **U(partial) ⊄ L**.

### 5.6 Restart vs rescan
Same totality condition and divergence domain; different values (§1); both compute
run-collapse for `('a','aa')`. Whether either calculus expresses the other's primitive:
OPEN.

---

## 6. Open Problems

1. **L ⊴ U?** Is safe (data-)replace `[Y/X]S` U-expressible — equivalently, can U
   rebuild any escaping at all? (No-escape Lemma 4 blocks all constant routes.)
2. **U ⊴ L?** Is `[a/ab]ᵘ` (the a-flood) L-reachable? (Six total pairs resist all
   searched pipelines.)
3. Is `X^{|X|}` U-reachable? (Candidate for L ⊄ U; blocked at data-instantiation.)
4. Is `cat` U-core-reachable? (Candidate failure of Concatenation Elimination; would make
   U's with-concat vs core fragments genuinely different, unlike L.)
5. Is the partial identity `[a/a]ᵘ` L-expressible (ε-set "contains-a")?
6. Is `b^{maxrun(S)}` U-reachable (needed for data-tuned marker patterns)?
7. Mutual expressibility of rescan and restart; exact characterization of pairs `(A,B)`
   for which `[A/B]ᵘ` is L-reachable (per-pair it is pair-dependent: 4 yes / 6 no-found
   of 10 tested).
8. Erratum follow-up (baseline): audit uses of Independent Substitution for
   `B = ε`; add hypothesis `B ≠ ε`.

---

## 7. Relations Summary

Notation: `U` = rescan calculus, `U-core`/`U-concat` its fragments, `L` = baseline,
`R` = restart calculus. "total"/"partial" states which class of functions the claim is about.

```
EXPR: U-core ⊴ U-concat                         STATUS: PROVEN — syntax inclusion.
EXPR: U-concat ⊴ U-core (total)                 STATUS: CONJECTURE — cat needs data-instantiation passes that diverge on data containing the pattern (no-escape, §3); bounded search negative. [Contrast: PROVEN for L by the paper's Thm `core` — the transfer FAILS.]
EXPR: L-safe-pair-passes ⊴ U                    STATUS: PROVEN — nodes with B ⊄ A and no suffix-of-A/prefix-of-B straddle coincide with safe passes (Theorem 2, condition (∗)).
EXPR: L ⊴ U-concat (total functions)            STATUS: CONJECTURE (false) — every paper toolkit construction breaks under ᵘ (census §2); enc circularity (§3); witness candidate X^{|X|} ∈ L (paper) with diverging U-construction and negative bounded searches. Not disproven.
EXPR: X^{|X|} ∈ U (total, 1-ary)                 STATUS: CONJECTURE (false) — [X1/σ]ᵘ diverges iff σ ⊂ X1 (REFUTED as constructed: 26/62 failures); 73,205-pipeline bounded search negative.
EXPR: σ^{|S|} ∈ U (total, 1-ary)                 STATUS: PROVEN — repaired construction ∏[σ/c]ᵘ (c ≠ σ); 0/127 failures. As literally written in the paper ([σ/Σ]ᵘ): REFUTED ([σ/σ]ᵘ diverges on σ-containing inputs).
EXPR: run-collapse ∈ U (total, 1-ary)            STATUS: PROVEN — [a/aa]ᵘS; verified |S|≤10.
EXPR: run-collapse ∈ L (total, 1-ary)            STATUS: PROVEN — [ε/ab][ε/aba][aab/a]S; verified exhaustively |S|≤14 ({a,b}), |S|≤9 ({a,b,c}), 3000 randoms ≤60, a^300. (New baseline result; no separation from run-collapse.)
EXPR: U ⊴ L (total functions)                   STATUS: CONJECTURE (false) — per-pair: safe pairs and (ab,ba),(ba,ab),(a,aa) ARE L-expressible (PROVEN by found+verified pipelines); six total pairs incl. (a,ab) NOT FOUND in deep constant-pipeline searches (COMPUTATIONAL negative); witness candidate: the a-flood [a/ab]ᵘ.
EXPR: [a/ab]ᵘ ∈ L (total, 1-ary "a-flood")       STATUS: CONJECTURE (not reachable) — COMPUTATIONAL negative over depth≤3 (|A|,|B|≤3), depth≤4 (≤2), depth≤2 (≤4) constant pipelines with extended witnesses + post-verification.
EXPR: [ab/ba]ᵘ ∈ L                              STATUS: PROVEN — [ε/bab][ab/a][aa/a], post-verified (equal-length non-safe pair).
EXPR: U ⊴ L (partial functions)                 STATUS: CONJECTURE (false) — partial identity [a/a]ᵘ: ε-set searches for "contains-a" all negative (25,600+14,400 pipelines).
EXPR: U ⊴ R and R ⊴ U (total or partial)        STATUS: OPEN — same divergence domain (PROVEN), values differ (REFUTED: ('b','ab','aab'): ᵘ='ab', ʳ='b').
EXPR: every total U-reachable f is poly-time    STATUS: PROVEN — matches ≤ |C|−|B|+1, |out| ≤ |C|(1+|A|) (Theorem 3,5); no complexity separation between the total fragments of U and L.
EXPR: X^{2^{|X|}} ∈ U (total)                    STATUS: REFUTED — length-bound proof transfers.
EXPR: paper's Section-2 toolkit (enc/dec round trip, cat, head, tail, eq, if, rep_n) ⊴ U STATUS: REFUTED — the specific expressions diverge or miscompute (census §2); existence of alternative U-constructions: OPEN (no-escape Lemma 4 blocks all constant-pattern routes).
EXPR: [A/B]ᵘ total ⟺ B ⊄ A (divergence = B⊂A ∧ B⊂C) STATUS: PROVEN — Theorem 3; 0 violations on stated domains. [This is the exact semantic content of the paper's "never restarts inside inserted text" clause.]
```

### Headline findings
1. The paper's Definition-1 clause is *exactly* what makes the encoder possible: under
   ᵘ, totality ⟺ pattern ⊄ replacement (PROVEN), and the encoder `[xb/b]` is the one
   load-bearing pass that violates it — the entire toolkit (cat, head, tail, eq, if,
   rep_n) collapses with it (REFUTED, census), and no constant-pattern escape exists
   (Lemma 4, PROVEN).
2. The totality theorem `Safe ⇒ total` fails (REFUTED, `[a/a]ᵘX₁`), but semantic
   totality restores everything: total ᵘ-nodes do at most linearly many matches, so the
   poly-time soundness theorem survives verbatim for the total fragment (PROVEN).
3. The calculi are plausibly **incomparable**: `X^{|X|} ∈ L` but (conjecturally) ∉ U;
   `[a/ab]ᵘ ∈ U` but (conjecturally) ∉ L; run-collapse lies in **both** (PROVEN both
   ways — including a new 3-pass construction for the baseline, exploiting deletion
   passes' junction re-exposure).
4. Bonus erratum in the baseline paper: Independent Substitution is false for empty
   replacement (`[ε/a]'cac'='cc' ⊇ 'cc'`, but `'cc' ⊄ 'cac'`) — PROVEN, with the fix
   `B ≠ ε`.

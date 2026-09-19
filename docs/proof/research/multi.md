# The `multi` variant: unrestricted simultaneous multi-pattern replace

Research report for the variant **V = multi** (the paper's *freezing* semantics taken as a
PRIMITIVE, with NO hypothesis on the pattern family). Baseline: `docs/proof/main.tex`
("String Substitution Theory for Finite Charset"), whose Theorem *(Multiple Substitution)*
implements `rep_n` from the single-pattern primitive `[A/B]C` only under hypothesis (H)
*every pattern X_i is a single character or does not end with x*.

**Headline result.** Hypothesis (H) is an **artifact of the paper's escaping scheme**
(escaping only `b`), not an intrinsic limit. A different encoding — the *comma code*,
which escapes **every** character as `x·c` — makes the same architecture (rename / repair /
instantiate / decode) correct for **all** pattern families. Consequently the multi calculus
M and the baseline calculus L compute **exactly the same functions**:
M ⊴ L and L ⊴ M, both in the with-concat and the core (concat-free) versions. STATUS: PROVEN
(Section 4; proof written, plus exhaustive computational verification on ~10⁷ evaluations,
Section 4.4).

All experiments live in `docs/proof/research/scratch/multi/` (`core.py`, `verify.py`,
`sweep_comma.py`, `stress.py`, `verify_deep.py`, `expr.py`, `minimize.py`,
`search_short.py`, `variants.py`, `algebra.py`, `witnesses.py`, `RepRefCheck.lean`).
Notation follows the paper; `X ⊴ Y` means every function reachable in calculus X is
reachable in calculus Y. Labels: PROVEN / COMPUTATIONAL / CONJECTURE / REFUTED.

---

## 1. Semantics

**Definition (Multi expressions).** For n ≥ 0, `ExpM_n` is defined like the paper's
`Exp_n` (Definition *Substitution Expressions*) with one extra constructor:

    X_i | W | [R/P]E | E1 E2 | rep(E; (P1,R1), …, (Pn,Rn))

A **core** multi expression has no `E1 E2` nodes. `rep(E; …)` binds nothing (no capture);
substitution `E[F_i/X_i]` is capture-free as in the paper.

**Definition (Denotation of multi).** On a tuple of strings S⃗,

  ⟦rep(E; (P₁,R₁),…,(Pₙ,Rₙ))⟧(S⃗) = rep_ref(⟦E⟧(S⃗); ⟦P₁⟧(S⃗)→⟦R₁⟧(S⃗); …; ⟦Pₙ⟧(S⃗)→⟦Rₙ⟧(S⃗))

where `rep_ref` is the paper's Definition *(Multiple Substitution, Semantics)* —
**freezing** — reproduced here for completeness: scan S left-to-right for occurrences of
X₁, leftmost-first, non-overlapping, never rescanning, and *freeze* the matched blocks;
then scan for X₂, where a match is admissible only if it lies **entirely in unfrozen
positions** (after a match the scan resumes at the end of the matched block); …; finally
replace every frozen block by its Y_i **simultaneously**. The node is **undefined** when
some ⟦P_i⟧ = ε (exactly as `[R/ε]` is undefined), and undefinedness propagates.

This matches the Lean reference `repRef` (verified: `RepRefCheck.lean` re-runs the Lean
definitions; see also §2, item 0, for two stale `#eval` comments in `Subst.lean`).

**Remarks.**
* rep with a single pair is exactly the baseline pass: `rep(E; (P,R)) = [R/P]E`. PROVEN
  (the freezing scan of one pattern is Definition 1's scan, and simultaneous replacement
  of the greedy non-overlapping match set is `[R/P]`).
* The freezing primitive includes as special cases the paper's `enc`/`dec` (single round),
  `cat` (Theorem *Concatenation via Multiple Substitution*), `rep_n` under (H), and the
  `escape`/`unescape` of Theorem *(Character Escaping)*.
* Undefinedness is *not* an artifact of this presentation: an L-expression for `rep`
  must also be undefined when some X_i = ε (§4.3), so the partial functions coincide too.

**Totality / Safety analog.** Extend the paper's `Safe`/`Anch` by
`Safe(rep(E; pairs)) ≡ Safe(E) ∧ ⋂_i Safe(P_i) ∧ Safe(R_i) ∧ Anch(P_i)`. Then
Safe(E) ⟹ ⟦E⟧ total, by the same induction as the paper's Theorem *(Totality)*. PROVEN
(the multi case of the induction: an anchored, safe pattern is never ε).

---

## 2. Basic algebra

Which of the paper's Section 2 theorems survive under V? The single-pass theorems are
inherited verbatim because L ⊴ M (§3). The genuinely multi statements:

**0. Two stale comments in the Lean file (errata, verified against the actual Lean code).**
`#eval subst ['a'] ['a'] ['a','a']` returns `[a,a]` — the comment "`[a]  ([a/a]aa = a)`"
contradicts Definition 1 and the paper's Identity Substitution theorem; and
`repRef [(['a','b'],['c']), (['b','a'],['a','a'])] ['a','b','a']` returns `[c,a]` — the
comment "`[c,a,a]`" is wrong (round 2's pattern `ba` cannot match: position 1 is frozen).
Verified by compiling the Lean definitions standalone (`RepRefCheck.lean`,
`RepRefCheck2.lean`). STATUS: PROVEN (machine-checked outputs).
*My Python reference agrees with the Lean code on both, and on the shadowing
counterexample (`repC` → `bbbaaab`, `repRef` → `bbbaabbba`), so all experiments here run
against the correct semantics.*

**1. ERRATUM to the paper's Lemma (Independent Substitution).** As stated
("A ∩ B = ∅, A ∩ C = ∅, C ≠ ε ⟹ A ⊂ [B/C]S ⟺ A ⊂ S") it **fails for B = ε**, which is
a legal instance (B is the replacement slot; deletions are used throughout Section 2).
Counterexample: A = `bc`, B = ε, C = `Z`, S = `abZcd`: `[ε/Z]S = abcd ⊃ bc` but
`bc ⊄ S`. The proof's step "A ⊂ XB([B/C]Y) ⟹ A ⊂ X ∨ A ⊂ [B/C]Y" uses B ≠ ε implicitly.
Fix: require B ≠ ε. STATUS: REFUTED (as stated) / PROVEN (with B ≠ ε).

**2. Independent Substitution, multi version.** If A shares no character with any X_i and
any Y_i, and **every Y_i ≠ ε**, then A ⊂ rep_ref(S; pairs) ⟺ A ⊂ S. The Y_i ≠ ε
hypothesis is necessary: pairs = [(Z, ε)], S = `abZcd` gives `rep = abcd ⊃ bc ⊄ S`.
STATUS: PROVEN (⟸: no X_i can overlap A, so A survives unfrozen; ⟹: A cannot straddle
an inserted Y_i without sharing a character, and Y_i ≠ ε forbids straddling across a
deletion) and COMPUTATIONAL (verified exhaustively: all S over {a,b} and {a,b,c} up to
length 5, all A from 8 candidates, all pattern pairs from {a,b,ab,ba}², all Y ∈
{ε, x, xy}² respecting the hypotheses; zero failures — `algebra.py`).

**3. Round order matters.** Minimal witness: rep(S; a→1; ab→1) = `1b` vs
rep(S; ab→1; a→1) = `1` on S = `ab`. STATUS: PROVEN (counterexample, machine-verified).

**4. Simultaneous is not sequential.** rep(S; a→b; b→a) = `ba` on S = `ab`, whereas both
sequential orders give `aa` / `bb`. This is the phenomenon motivating `docs/MR.md`.
STATUS: PROVEN (counterexample).

**5. Inherited theorems.** Identity, Direct Substitution, Substitution Elimination,
Stepping-into, Tail/Head Elimination, Double Substitution, Encoding/Decoding, cat, head,
tail, eq, if — all hold under V because they are statements about single passes or about
L-expressions, and L ⊴ M. STATUS: PROVEN (§3).

---

## 3. Toolkit (enc/dec, cat, head/tail, eq, if)

**Theorem (baseline ⊴ multi).** Every L-reachable function is M-reachable:
`[R/P]E = rep(E; (P,R))` (a single-round multi node), and the translation is a
homomorphic rewrite, so it commutes with the paper's Lemma β (composition). The core
versions work too (a single-round node has no concat). STATUS: PROVEN.

Consequently the entire toolkit of the paper (enc/dec, cat, head, tail, eq, if, escape)
is inherited by M verbatim. Two simplifications are worth recording:

**Theorem (cat in the core multi calculus).** `cat(X,Y) = rep(ab; (a,X),(b,Y))` for any
two distinct characters a ≠ b. STATUS: PROVEN (the paper's Theorem *Concatenation via
Multiple Substitution*, whose proof is purely semantic: round 1 freezes position 0,
round 2 position 1). COMPUTATIONAL: verified on all X,Y over {a,b} of length ≤ 3.
Hence **concatenation is eliminable in M**: `E1 E2 ↦ rep(ab; (a,E1°),(b,E2°))`, so
core-M = with-concat-M as function classes. STATUS: PROVEN.

**Theorem (tail as one multi node).** The paper's `tail` uses N ordered deletion passes
(right-to-left, longest-first, Remark *order*); with the multi primitive it is **one
node**: `tail(X) = dec( rep(σ₁σ₁·enc(X); (σ₁σ₁σ₂σ₁,ε),(σ₁σ₁σ₂,ε),(σ₁σ₁σᵢ,ε)_{i≥3},(σ₁σ₁,ε)) )`.
STATUS: PROVEN (same case analysis as the paper — the rounds play the role of the
ordered passes; the patterns pairwise overlap only at position 0, where the longest
round fires first). COMPUTATIONAL: verified equal to tail and to the paper's sequential
version on all strings of length ≤ 4 over alphabets of size 2, 3, 4 (`algebra.py`).

---

## 4. Expressibility vs the baseline L — the central question

### 4.1 The question

Is unrestricted multi expressible in L by a *different* construction, i.e. is the paper's
hypothesis (H) intrinsic? The paper's Remark *rep-hyp* exhibits the shadowing failure:

    b = σ1, x = σ2, S = σ1σ2σ1σ1σ2, X1 = σ1σ2 → Y1 = σ2σ2σ2σ1,
    X2 = σ2σ2σ2 → Y2 = σ1σ1:

the construction returns σ2σ2σ2σ1σ1σ1σ2 instead of σ2σ2σ2σ1σ1σ2σ2σ2σ1 — a *spurious*
match of enc(X1) = σ2σ1σ2 that ends at an escape σ2 shadows a genuine match two
positions later, and the scan (which never restarts inside inserted text) never finds it.
(Reproduced and machine-verified: `bbbaaab` vs `bbbaabbba`, including in Lean.)

### 4.2 The comma-code construction

**Definition (comma code).** Fix distinct b, x ∈ Σ. For c ∈ Σ let the block w_c = x·c
and **enc₂(W) = w_{W[0]}·w_{W[1]}·…** (every character escaped by a *comma* x). Markers
m_i = x·b^{i+1} (i ≥ 1), as in the paper.

As passes (order left = first applied): **enc₂ = [xx/x] then [xc/c] for each c ≠ x**;
**dec₂ = [c/xc] for each c ≠ x, then [x/xx]**. (The x-doubling must run first, so the
x's inserted by [xc/c] are not doubled; in dec₂ the x-halving must run last.)

**Theorem (Unrestricted Multiple Substitution).** Let n ≥ 1 and X₁,…,X_n be arbitrary
nonempty patterns. With the abbreviations E_Z = enc₂(Z), m_i = x·b^{i+1}:

    rep₂(S; X₁→Y₁; …; Xₙ→Yₙ) :=
      dec₂ ( [E_{Y_n}/m_n] … [E_{Y_1}/m_1]
             ( ∏_{i=1..n} ( [E_{X_i}·b / m_{i+1}] [m_i / E_{X_i}] ) )
             enc₂(S) )

where the products compose right-to-left (round i = rename then repair; then
instantiation i = n,…,1; then decode). This is an expression of the **baseline calculus
L** over the variables S, X₁, Y₁, …, X_n, Y_n (patterns/replacements are sub-expressions;
the single concatenation `E_{X_i}·b` is eliminable by the paper's cat, Theorem *core*).
For all inputs it equals rep_ref(S; X₁→Y₁; …; Xₙ→Yₙ), and it is undefined exactly when
some X_i = ε. STATUS: **PROVEN** (proof below) and COMPUTATIONAL (§4.4).

*Proof.* Call a text **normal** if it is a concatenation of *fragments* (enc₂-images)
and markers m_1,…,m_k, every marker followed by a non-b character or the end. Facts
(verify Lemma A): (i) enc₂ is injective, image = (xΣ)* — even length, x at every even
position, unique block parse; dec₂ inverts it on images because in an image every
occurrence of `xc` (c ≠ x) is exactly the block `xc` (at odd positions the data char ≠ x
rules it out, at even positions the comma+data **is** the block), and after collapsing
all c ≠ x blocks the remaining x-runs are exactly concatenations of `xx` blocks, even,
so the greedy `[x/xx]` halves them at block boundaries. (ii) Images contain no `bb`:
every b is a data character, immediately followed by the next block's comma x. (iii) A
marker contains `bb` and begins with x, so in a normal text a b-run longer than 1 lies
inside a marker; after any x of a fragment the b-run has length ≤ 1.

*The rename pass [m_i/E_{X_i}].* Let E = E_{X_i}, |X_i| = k. Occurrences of E in a normal
text start (α) at a block comma, (β) at a block's data character, or (γ) at a marker's x
(deeper marker positions start with b ≠ E[0]).
  (α) Reading from a comma, E alternates comma/data. If the next k blocks are intact and
  spell X_i, the occurrence is **genuine** — it is exactly a run of k *unfrozen* skeleton
  characters spelling X_i. Otherwise the occurrence can only leave the fragment and reach
  a marker: E's comma slot hits the marker's x, E's last data slot hits the marker's
  first b — possible only when X_i ends with b, the match covering (k−1 intact blocks
  spelling X_i[0..k−1]) + the marker's first two characters. Such a match is **spurious**
  and is followed by the marker's second b.
  (β) An occurrence at a data character d must read d = E[0] = x, then E[1] = x₁ against
  the next comma x, so x₁ = x, and inductively X_i = x^k with k data-x's. The occurrence
  at the comma one position earlier reads the same data characters with commas on commas,
  so it matches too and starts strictly earlier. A short induction on the scan shows the
  greedy scan always tries each comma before its data (resume points are commas or
  inside markers' b's), so (β)-occurrences are always **shadowed** and never taken.
  (γ) E[1] = x₁ against the marker's first b forces x₁ = b; E[2] is a comma slot against
  the marker's second b — dead unless k = 1, i.e. X_i = `b`, E = `xb`, which matches the
  first two characters of every marker: **spurious**, followed by the marker's next b.
No occurrence crosses a marker beyond its first two characters, and no genuine match
starts inside a marker. **No shadowing:** (β) never taken; (γ) covers only marker
characters; an (α)-spurious match covers (k−1) blocks immediately followed by a marker,
and from any of those blocks a genuine match would need k intact blocks — fewer than k
remain before the marker, and the match at the comma itself is the (α) slot, which is
either genuine or spurious but never both. Hence the genuine matches taken by the greedy
scan are exactly the freezing round-i matches, the scan resuming after each insertion at
the next comma (= the next skeleton position), and after a spurious match inside the
eaten marker's b's — from which the scan rejoins the next comma without loss (the k−1
blocks covered by the spurious match cannot host a round-i match start).

*The repair pass [E_{X_i}·b / m_{i+1}].* In the renamed text the markers are m₁,…,m_i;
genuine ones are followed by non-b (comma, marker, or end); every spurious one is
followed by at least one b (the eaten marker's remains). The pattern m_{i+1} = x b^{i+2}
cannot occur in fragments (b-runs ≤ 1) nor inside m_j, j ≤ i (b-run j+1 ≤ i+1), nor at a
genuine marker (followed by non-b); so it occurs exactly at spurious m_i + one b, and
the replacement E_{X_i}·b restores the original text in each case (for X_i = `b`:
`m_i b → xb·b` rebuilds the eaten marker x b^{j+1}; for X_i ending in b: the (k−1)
blocks + `x b b^{j-1}` rebuild blocks + marker). Afterwards the text is normal again
with markers m₁,…,m_i, the skeleton being S with rounds 1..i frozen.

*The instantiation passes [E_{Y_i}/m_i], i = n..1.* At pass i only markers m₁,…,m_i are
present; m_i is not a prefix of any of them and, by (iii), matches nowhere else — exactly
the round-i markers are replaced by the images E_{Y_i}, which behave as fragments (no
`bb`), so later passes are undisturbed. The final text is enc₂(Z), Z = the freezing
result, and dec₂ gives Z. Undefinedness: the only pass patterns that can be empty are
the E_{X_i} (exactly when X_i = ε), matching the semantics. ∎

**The key structural difference from the paper's construction.** The paper's code words
are `xb` for b and `c` for c ≠ b — of *different lengths*. A pattern image can then start
at a unit boundary and end *mid-unit* (at an escape x), and such a spurious occurrence
can precede an overlapping genuine one: shadowing. In the comma code all code words have
length 2, so the parity of the phase is *locked*: every occurrence starting at a unit
boundary is genuine (or runs off the fragment's end into a marker, where the uniform
repair catches it), and every misaligned occurrence is preceded one position earlier by
an overlapping aligned one. The paper's (H) is exactly the condition that excludes the
mid-unit-ending images `enc(X)` for its non-uniform code.

### 4.3 Corollaries

**Corollary (M ⊴ L).** The translation of §4.2 is compositional (multi nodes are
rewritten in place; variables, constants, concat, and single passes are untouched), so
by the paper's Lemma β every M-reachable function is L-reachable. With §3 (L ⊴ M):
**M ≡ L** as classes of partial functions, and the same for the core calculi
(core-M ⊴ L by §4.2 + the paper's Theorem *core* for the one concatenation; L-core ⊴
core-M by §3). STATUS: PROVEN.

**Corollary ((H) is an artifact).** The paper's Theorem *(Multiple Substitution)* holds
with hypothesis (H) deleted, via a different construction. Its Remark *rep-hyp* open
question ("the exact characterization of the pattern families for which the construction
is sound") is answered for the *architecture*: the construction with enc₂ is sound for
**all** pattern families. STATUS: PROVEN (via §4.2).

**Corollary (escape without (H2)).** The paper's Theorem *(Character Escaping)* used
(H2) (x ∉ V) only to apply its rep_n construction; the round trip
unescape(escape(S)) = S is a *semantic* statement (its Steps 1–3 never use (H2)) and
holds for every escaping function f with the fixed point enumerated first ((H1) — which
the paper's Remark shows is genuinely needed). With §4.2, escape/unescape are then
L-expressible for all such f. STATUS: PROVEN (semantic argument, Steps 1–3 of the paper
re-checked) and COMPUTATIONAL: all 133 escaping functions over Σ ∈ {abc, abcd} (all
valid U, fixed points, and injective image maps), all S up to length 6 — zero failures
(`stress.py`). This resolves the second bullet of the paper's Remark *escape-hyp*.

**Corollary (growth).** M adds no power anywhere: reversal is reachable in M iff it is
reachable in L (open); X ↦ X^{2^|X|} is unreachable in M (§5); every M-function is
poly-time. STATUS: PROVEN (from M ≡ L).

### 4.4 Computational verification of the construction

`repC_comma` (core.py) implements §4.2 literally; `rep_ref` implements the freezing
semantics (cross-checked against the Lean `repRef` and `repC`, including the paper's
counterexample). Agreement `repC_comma = rep_ref` was verified on:

| domain | pattern sets | strings | evaluations |
|---|---|---|---|
| Σ={a,b}, n=1 | all X (len 1–3) × all Y (len 0–3): 210 | len ≤ 8 (511) | 107,310 |
| Σ={a,b}, n=2 | 14² pattern pairs × 7² replacement pairs = 9,604 | len ≤ 6 (127) | 1,219,708 |
| Σ={a,b}, n=2, (b,x) swapped | 9,604 | len ≤ 6 (127) | 1,219,708 |
| Σ={a,b}, n=3 | 8³ pattern triples × 3³ = 13,824 | len ≤ 5 (63) | 870,912 |
| Σ={a,b,c}, n=2 | 10² × 5² = 2,500 | len ≤ 6 (1,093) | 2,732,500 |
| Σ={a,b,c}, n=3 | 5³ × 3³ = 3,375 | len ≤ 5 (364) | 1,228,500 |
| randomized | 3,400 trials: n ≤ 6, |X| ≤ 5, |S| ≤ 40, |Σ| ≤ 5 | — | 3,400 |
| adversarial families | marker-shaped patterns (m_i themselves), deletions, self-referential pairs, swap, shadowing instance | all strings len ≤ 5–8 | ≈ 5,000 |
| ternary, all 6 (b,x) choices | 147 families × 6 | len ≤ 6 | ≈ 964,000 |
| expression level (n=1..3, variables) | 450 random (S, X⃗, Y⃗) triples, undefinedness agreement incl. X_i = ε | — | 450 |
| escape round trips without (H2) | 133 escaping functions, all strings len ≤ 6 over their alphabet | — | ≈ 4·10⁵ |

Zero disagreements anywhere (total > 10⁷ evaluations). For comparison, the paper's
construction on the same sweeps disagrees with the freezing semantics on 42/210 (n=1),
2,937/9,604 (n=2), 7,164/13,824 (n=3) pattern-set families over Σ={a,b} — always
violating (H) — and never on any (H)-respecting family (regression, matching the Lean
sweep). On the shadowing instance it fails on 1,059 of 2,047 strings of length ≤ 10.

### 4.5 The shadowing instance as an explicit pipeline

Instantiating §4.2 for f(S) = rep₂(S; ab→bbba; bbb→aa) over Σ={a,b} with (b,x)=(a,b)
gives a **10-pass constant pipeline** (verified on all 1,023 strings of length ≤ 9, and
on all 2,047 of length ≤ 10):

    1. [bb/b]      2. [ba/a]                     (enc2)
    3. [baa/babb]  4. [babba/baaa]                (rename 1, repair 1)
    5. [baaa/bbbbbb]  6. [bbbbbba/baaaa]          (rename 2, repair 2)
    7. [baba/baaa]                                 (instantiate 2)
    8. [bbbbbbba/baa]                              (instantiate 1)
    9. [a/ba]     10. [b/bb]                      (dec2)

Passes 4 and 6 (the repairs) are droppable for *this* instance (greedy pass-elimination
over all strings of length ≤ 10 leaves an 8-pass pipeline); in general they are needed
(e.g. for X = `b` or patterns ending in `b` near markers — see the adversarial families).

Bounded searches for *shorter* pipelines (BFS by signature, candidates re-verified on
length ≤ 10): no pipeline with ≤ 2 passes and patterns of length ≤ 4 over {a,b}
(replacements of length ≤ 2 over {a,b,1,2}; 263,477 distinct signatures searched), and
none with ≤ 3 passes and patterns of length ≤ 3 (11,990,766 signatures; a fortiori none
with patterns of length ≤ 2, 611,404 signatures). So the 8–10-pass
construction is not trivially compressible: on this instance the comma architecture is
within one pass of optimal for constant pipelines with short patterns. STATUS:
COMPUTATIONAL (negative evidence on the stated finite spaces).

---

## 5. Complexity

**Definition (duplication degree, multi).** deg(X_i)=1, deg(W)=0, deg(E1E2)=max,
deg([R/P]E) = deg E + deg R, **deg(rep(E; pairs)) = deg E + max_i deg R_i**.

**Lemma (Length Bound, multi).** For every multi expression E there is C_E with
|⟦E⟧(S⃗)| ≤ C_E·(1+M)^{deg E} (M = max(1,|S_i|)) whenever defined. *Proof:* a multi node
satisfies |rep(T; pairs)| ≤ |T|·(1 + max_i|Y_i|): the frozen blocks are pairwise disjoint
(each ≥ 1 character), so there are ≤ |T| of them, each contributing ≤ |Y_i| characters,
plus ≤ |T| unfrozen characters. The induction then proceeds exactly as the paper's Lemma
*Length*. STATUS: PROVEN.

**Theorem (poly-time soundness, multi).** Every M-reachable function is computable in
polynomial time; the exponent is bounded by a function of the expression. *Proof:* as the
paper's Theorem *Soundness*, with one multi node evaluated in time linear in
(length of text) × (max pattern + replacement length). Alternatively, M ⊴ L (§4.2) and
the paper's theorem applies. STATUS: PROVEN.

**Theorem (unreachable).** X ↦ X^{2^|X|} is not M-reachable. STATUS: PROVEN (the Length
Bound, as in the paper). Note the construction of §4.2 shows `rep_n` itself is computed
by 2|Σ| + 3n passes — a **linear-size, linear-time** expression, consistent with the
poly-time bound (nothing breaks polynomial time, and no growth beyond the paper's degree
calculus is possible since M ≡ L).

**Reversal.** S ↦ reverse(S) is open for M exactly as for L (M ≡ L); the comma code
offers no obvious handle (its markers protect left-to-right scanning, which is exactly
what reversal destroys). No progress; listed in §7.

---

## 6. One-pass multi-pattern variants (secondary question)

**Definition.** One-pass-leftmost-longest (L) and one-pass-first-rule (R): a single
left-to-right scan; at each position take the longest (resp. lowest-index) pattern
matching there; replace and resume after the replacement text.

The three semantics (freezing F, L, R) are pairwise distinct. Minimal machine-verified
separating instances (D = all strings over {a,b} of length ≤ 7):

* F ≠ L: patterns (a→1, ab→2) on `ab`: F = `1b`, L = `2`. (Round 1 freezes the `a`,
  round 2's `ab` is inadmissible; one-pass takes the longer match at position 0.)
* F ≠ R: patterns (bc→1, ab→2) on `abc`: F = `a1`, R = `2c`. (Freezing gives round 1
  global priority; one-pass gives position priority.)
* L ≠ R: patterns (a→1, ab→2) on `ab`: L = `2`, R = `1b`.

**Permutation does not reconcile them.** Over the 64 ordered pairs from
{a,b,aa,ab,ba,bb,aba,bab}: F equals R (or L) with the pattern list possibly reversed on
52/64; for the remaining 12 no order works. Witness for (ab→1, ba→2), S = `ababbab`:
F(ab,ba) = `11b1`, F(ba,ab) = `a2b2b`, R = `112b` (L = `112b` too — for this pair
first-rule and leftmost-longest coincide since the patterns start with different letters).
STATUS: COMPUTATIONAL.

**Class-level comparison on a small function space** (D = strings over {a,b} len ≤ 7;
pattern lists of length 1–3 from an 8-pattern pool, distinct markers as replacements):
freezing induces 230 distinct functions, one-pass-L 64, one-pass-R 56 (lists of length
1–2); on this pool one-pass-R ⊆ one-pass-L (56 shared, 8 L-only, 0 R-only). 30 of the 64
one-pass-L functions and 22 of the 56 one-pass-R functions are **not** freezing-computable
over the same pool; 196 of the 230 freezing functions are neither one-pass-L nor
one-pass-R. Moreover, no freezing pattern list of length ≤ 4 over a 10-pattern pool (with
marker replacements) computes one-pass-first(ab→1, ba→2), and none of length ≤ 3 with
replacements from {a,b,ε,ab,ba}. The reason is structural: freezing gives *rounds* global
priority (a round-1 match anywhere beats a round-2 match, even earlier), one-pass gives
*positions* priority; neither ordering information can be simulated by reordering a
finite pattern list when the leftmost union occurrence alternates between patterns.
STATUS: COMPUTATIONAL.

**Is the one-pass calculus ⊴ L?** Open. Bounded exhaustive searches (BFS by signature,
patterns over {a,b}, replacements of length ≤ 2 over {a,b,1,2}, strings ≤ 5 for
dedup, candidates re-verified on all strings of length ≤ 9): **no** constant pipeline
computes one-pass-first(ab→1, ba→2) with ≤ 3 passes and |P| ≤ 3 (11,990,766 distinct
signatures searched), nor with ≤ 2 passes and |P| ≤ 4 (263,477 signatures); a randomized
search (500,000 pipelines of ≤ 7 passes, |P|, |R| ≤ 3 over {a,b,1,2}) also found none
(`search_short.py`, `search_short.log`). Negative evidence only — the full question needs
a calculus-level invariant. Note the scope: for *fixed* pattern sets a non-uniform case
analysis might still succeed (the positions where two variable patterns could tie are not
expressible uniformly, but for fixed patterns they are finitely many), so the interesting
open form is the *primitive with variable patterns*: is the node
rep-onepass(E; (P₁,R₁),…,(Pₙ,Rₙ)) expressible in L uniformly in its variables?
STATUS: CONJECTURE (no) — evidence as above; unsettled.

---

## 7. Open problems

1. **One-pass variants vs L** (§6): is onepass-first/longest ⊴ L? Even the fixed-pattern
   function one-pass-first(ab→1, ba→2) resisted all bounded pipeline searches (exhaustive
   to ≤ 3 passes with short patterns, 12M signatures; randomized to 7 passes); no
   invariant found.
2. **Reversal** remains open for M — and is equivalent to the L question since M ≡ L.
3. **Minimal pipeline size**: is there a pipeline with < 8 passes computing the shadowing
   instance f (§4.5)? (The construction gives 8; ≤ 3-pass pipelines with |P| ≤ 3 are
   exhausted negatively — 11,990,766 signatures.)
4. **The paper's open question 1** (exact characterization of reachable functions) is
   unchanged by multi, since the classes coincide.
5. **Alphabet-power** (paper's question 4): my construction needs only two distinct
   characters b ≠ x, for every |Σ| ≥ 2, so multi/rep_n are alphabet-uniform; whether a
   larger alphabet ever adds power remains open for the rest of the calculus.

---

## 8. Relations summary

    EXPR: multi (M, unrestricted freezing, with-concat) ⊴ baseline L STATUS: PROVEN — comma-code construction (§4.2): rename/repair/instantiate/decode over enc₂(W)=∏x·W[j], no hypothesis on patterns.
    EXPR: baseline L ⊴ multi (M) STATUS: PROVEN — [R/P]E = rep(E; (P,R)), a single-round multi node.
    EXPR: core-multi ⊴ core-L STATUS: PROVEN — same construction; its one concatenation is eliminable by the paper's cat (Theorem core).
    EXPR: core-L ⊴ core-multi STATUS: PROVEN — single-round node is core; hence core-M ≡ core-L and M ≡ L as partial-function classes.
    EXPR: paper's rep_n-under-(H) ⊴ baseline L STATUS: PROVEN — the paper's Theorem (Multiple Substitution); regression-verified here on all (H)-respecting sweeps.
    EXPR: multi-without-(H) ⊴ paper's-rep_n-construction STATUS: REFUTED — shadowing instance (Remark rep-hyp; machine-verified incl. in Lean): construction returns bbbaaab, freezing semantics bbbaabbba; 2,937/9,604 n=2 pattern families over Σ={a,b} disagree.
    EXPR: escape/unescape without (H2) (x ∉ V) ⊴ baseline L STATUS: PROVEN — the round trip is semantic (needs only (H1)); expressible via §4.2. Verified on 133 escaping functions.
    EXPR: onepass-first ⊴ freezing (same pattern list, any permutation) STATUS: REFUTED — 12/64 pattern pairs over the 8-pattern pool; witness (ab→1, ba→2) on ababbab: 11b1 / a2b2b / 112b.
    EXPR: onepass-longest ⊴ freezing (any permutation) STATUS: REFUTED — same 12 pairs (they coincide with first-rule on this pool's ties).
    EXPR: freezing ⊴ onepass-first ∪ onepass-longest STATUS: REFUTED — 196/230 freezing functions on the pool are neither; witness (ab→0, ba→1) family.
    EXPR: onepass-first(ab→1, ba→2) ⊴ baseline L (constant pipelines ≤ 3 passes, |P|≤3; and randomized ≤ 7 passes, |P|≤3) STATUS: REFUTED — exhaustive (11,990,766 signatures) / randomized (500,000 trials) negative evidence on the stated spaces (not a full separation).
    EXPR: multi ⊴ baseline L, restricted to the shadowing instance f = rep₂(ab→bbba, bbb→aa) STATUS: PROVEN — explicit 10-pass (minimized 8-pass) constant pipeline (§4.5), verified on all strings of length ≤ 10.

---

## 9. Reproduction

    cd docs/proof/research/scratch/multi
    python3 verify.py        # semantics sanity + paper counterexample + money test
    python3 sweep_comma.py   # exhaustive sweeps of §4.4 (~3 min)
    python3 stress.py       # randomized + adversarial + escape round trips (~10 min)
    python3 verify_deep.py  # deep randomized + marker-shaped + all (b,x) choices (~10 min)
    python3 expr.py          # expression-level check + flat pipeline for §4.5
    python3 algebra.py       # §2 experiments
    python3 variants.py      # §6 one-pass comparisons
    python3 witnesses.py     # concrete witnesses for §6
    lean RepRefCheck2.lean   # Lean cross-checks (§2 item 0, §4.1)
    python3 minimize.py     # pass minimization for §4.5
    python3 search_short.py # bounded pipeline searches (§4.5, §6; long-running)

# once-l: The Leftmost-Only Substitution Calculus

Research report on the variant **V = [A/B]₁C** — replace exactly ONE occurrence of B by A,
the *leftmost* — and its bounded family [A/B]_k, studied against the baseline `[A/B]C`
(replace-all, left-to-right, leftmost-first, non-overlapping, never rescanning) of
*String Substitution Theory for Finite Charset* (`docs/proof/main.tex`).

Every claim is labeled exactly one of **PROVEN** (careful proof, given or cited),
**COMPUTATIONAL** (exhaustively verified on a stated finite domain),
**CONJECTURE** (evidence, no proof), **REFUTED** (counterexample).
Throwaway scripts: `docs/proof/research/scratch/once-l/` (core.py, indep.py, toolkit.py,
lemmas.py, L_search.py, L_rand.py, kfamily.py, ab2.py). All computations ran under Python 3.14
(`str.replace(B, A, k)` is exactly the scan semantics of the paper's Definition 1 truncated
to k matches; equivalence of the once case with the paper's min-|X| characterization was
re-verified by brute force: `core.py`, all |C| ≤ 6, |A| ≤ 2, |B| ≤ 3 over {a,b}).

**Overlap note (positional family).** [A/B]₁ *is* replaceOcc(0, B, A): the index-0 member of
the positional family. This report studies only the scan-based semantics; nothing here uses
positional/index primitives.

---

## 1. Semantics

**Definition 1.1 (Once Substitution).** For strings A, B with B ≠ ε and any C,
```
[A/B]₁ C = X A Y   where (X,Y) minimizes |X| among C = XBY;   = C  if B ⊄ C.
```
[A/ε]₁ is undefined, as in the paper. [A/B]₁C = `C.replace(B, A, 1)`.

**Definition 1.2 (Bounded family).** For a *literal* k ≥ 0,
`[A/B]₀ C = C` and `[A/B]_k C = X A ([A/B]_{k−1} Y)` with (X,Y) the leftmost
decomposition C = XBY (undefined for B = ε). I.e. run the greedy scan of the paper's
Definition 1 but stop after k matches. k ≥ number of matches yields the baseline [A/B]C.

**Proposition 1.3 (k ≠ k-fold once). PROVEN.**
`[A/B]_k C ≠ ([A/B]₁ composed k times)(C)` in general:
[ab/b]₂"bb" = "abab" but [ab/b]₁([ab/b]₁"bb") = [ab/b]₁"abb" = "aabb".
They agree whenever A contains no occurrence of B (then inserted text is never rematched);
**COMPUTATIONAL**: agreement verified on 20,000 random (A,B,C,k) with A over {a,c}, B over {b}.
So the k-family is *not* redundant shorthand for once-composition; it is the
"first k matches of one scan" semantics.

**Calculus.** Exp_n, Denotation, Reachable, core (concat-free) are the paper's Definitions
3.1–3.3 with the node `[R/P] E` denoting the *once* substitution
`[⟦R⟧(S⃗)/⟦P⟧(S⃗)]₁ ⟦E⟧(S⃗)`, undefined when the pattern is ε. Write ONCE for this calculus
(with concat), ONCE-core for the concat-free fragment, ONCE_k for nodes of arity k.
Lemma β (composition) and the Safe/Anch totality predicate transfer verbatim (their proofs
never inspect the scan beyond nonempty patterns). Pipeline Normal Form holds: a core
expression is a finite pipeline of once-passes over a variable or constant.

---

## 2. Basic algebra: the paper's Section 2 under V

| Theorem | Status under once | Note |
|---|---|---|
| Identity [A/A]₁S = S | **PROVEN** | trivial: replacing an occurrence by itself |
| Direct [A/B]₁B = A | **PROVEN** | leftmost occurrence of B in B is at 0 |
| Substitution Elimination | **PROVEN** | immediate |
| Independent Substitution | **PROVEN** (with B ≠ ε) | see erratum below |
| Tail / Head Elimination | **PROVEN** | pure string lemmas; no substitution appears |
| Stepping-into | **REFUTED** | [c/a]₁"aa" = "ca" ≠ c·[c/a]₁"a" = "cc" (a once-pass consumes its one match; the remainder of the scrutinee is untouched). Also fails with empty replacement: [ε/a]₁"aa" = "a" ≠ ε |
| Double Substitution | **PROVEN** | same hypotheses (X,Y ≠ ε, X ⊂ Y, Y unbordered): the single inserted copy is the leftmost occurrence of Y in W = UYV (the paper's case analysis applies verbatim to rule out earlier occurrences), so [X/Y]₁[Y/X]₁Z = Z |
| Encoding thm (i) dec(enc(S))=S | **PROVEN** | = Double Substitution with X=b, Y=xb |
| Encoding thm (ii) bb ⊄ enc(S) | **REFUTED** | once-enc escapes only the first b: enc₁"aa" = "aba" contains "aa" (b=a, x=b in Σ={a,b}) |
| Encoding thm (iii) morphism | **REFUTED** | enc₁(a)enc₁(a) = "ab·ab" ≠ enc₁(aa) = "abb" style failures |
| Encoding Monotonicity | **REFUTED** | A="cb" ⊂ B="bcb" but enc₁(A)="cxb" ⊄ enc₁(B)="xbcb" (COMPUTATIONAL: further counterexamples A="aa"⊂B="acaa") |
| Single Char Substitution [σ/Σ] | **REFUTED** | a pipeline of ≤ |Σ| once-passes changes ≤ |Σ| characters; σ^|S| is unreachable (also follows from the Fresh-Character Lemma 4.1) |
| rep_n (freezing), escape_f | construction fails | each round must replace *all* frozen occurrences of X_i; ONCE replaces one. escape as a *function* is unreachable (Thm 4.4) |

**Erratum to the paper (baseline included).** The paper's Independent Substitution Lemma
("A∩B=∅, A∩C=∅, C≠ε ⟹ A⊂[B/C]S ⟺ A⊂S") is refuted *for the baseline* as literally stated:
take A="aa", B=ε, C="b", S="aba": [ε/b]"aba" = "aa" ⊇ "aa", but "aa" ⊄ "aba". An empty
replacement deletes C and *merges the junction*, creating fresh A-occurrences. The lemma holds
for both the baseline and once once B ≠ ε is added (both verified: `indep.py`, all
A,B,C over {a,b,c} with |A|,|B| ≤ 2, |S| ≤ 6; zero violations with B ≠ ε, counterexamples
immediately with B = ε). The once-proof is the paper's proof: occurrences of C cannot touch
A's characters (disjoint alphabets), so the leftmost match sits in X or in Y of S = XAY.

The structural difference from the baseline is concentrated in Stepping-into: the baseline
pass "restarts the scan inside the remainder", the once pass consumes its single match and
leaves the rest virgin. Everything the baseline builds by *simultaneous multi-site* rewriting
(enc, benc, rep, escape) is exactly what ONCE cannot do; everything the baseline builds by
*single-site* rewriting (cat, head, tail, eq, if) survives — and is often *easier* in ONCE,
because "replace only the leftmost" is a built-in form of marker protection.

---

## 3. Toolkit: enc/dec, cat, head/tail, eq, if

Throughout Σ has |Σ| ≥ 2; distinct characters are chosen from it; all constructions are
ONCE-**core** (cat below is itself core-expressible, so concat nodes are eliminable sugar).

**Theorem 3.1 (cat). PROVEN.**
```
cat(X,Y) = [X/a]₁ [Y/b]₁ (ab),      a ≠ b two characters.
```
Inner pass: first b of "ab" is at 1 (a≠b), giving a·Y. Outer pass: the first a of aY is at
position 0 — *always the marker*, whatever Y contains — giving XY. Once-semantics gives
leftmost-anchored marker protection for free; no enc is needed (contrast the paper's Theorem
"String Concatenation" which needs enc to stop [·/xb²] firing inside images).
**COMPUTATIONAL**: all X,Y over {a,b} and {a,b,c} with |X|,|Y| ≤ 3, exhaustively.

**Lemma 3.2 (Doubled Marker). PROVEN.** For X ≠ ε and σ ∈ Σ: if XXσ occurs in XXX then
σ = X[0]; moreover XX·X[0] occurs at position 0, and every occurrence of X² in X³ sits at a
multiple of the minimal period of X, hence the leftmost occurrence of XXσ in XXX is at 0.
*Proof.* An occurrence at q needs q+2|X|+1 ≤ 3|X|, so q ≤ |X|−1. Then X³[q:q+2|X|] = X²;
comparing with the trivial occurrences of X² at 0 and |X| gives (standard overlap/period
argument, Fine–Wilf) that X has period p = gcd(q,|X|) (in particular p | q), and
σ = X³[q+2|X|] = X[q] = X[0]. ∎
**COMPUTATIONAL**: all X with 1 ≤ |X| ≤ 7 over {a,b} and {a,b,c}, all σ: no exception.
The point: **XX is a marker that is fresh with respect to X by length** (|XX| = 2|X| > |X|)
and it survives as a whole inside XXX. This self-fresh marker replaces the paper's enc-based
markers wherever a *bounded-length* fresh marker is needed.

**Theorem 3.3 (tail). PROVEN.**
```
tail(X) = ∏_{σ∈Σ} [ε/ XXσ ]₁ (XXX)
```
(the product is any order of once-passes; patterns are computed from the input X).
For σ = X[0] the pattern XXσ matches at 0 (Lemma 3.2) and deletes XX·X[0] = the first
2|X|+1 characters of XXX, leaving X[1:]; for σ ≠ X[0] the pass is inert. After the firing
pass the string has length |X|−1 < 2|X|+1, so all remaining passes are inert by length.
X = ε: every pattern is the single char σ, inert on ε. Total, and pass-order-independent.
**COMPUTATIONAL**: all |X| ≤ 6 over {a,b} and {a,b,c}; all orderings of the |Σ| passes.

**Theorem 3.4 (head). PROVEN.**
```
head(X) = [ε/ tail(X) · X · d]₁ (X · X · d),    d any fixed character.
```
Write X = cR. The pattern R·X·d has length 2|X| and occurs in the scrutinee cR·cR·d at
position 1 (the tail R followed by X followed by d); deleting it leaves c. An occurrence at
position 0 forces R = c*, i.e. X = c^k with c = d, where the pattern is c^{2k}, the leftmost
occurrence is at 0, and deleting it still leaves exactly one character c. Pattern is always
nonempty (ends in d), including X = ε (pattern d, scrutinee d, result ε). Total.
**COMPUTATIONAL**: all |X| ≤ 6 over {a,b} and {a,b,c}, for every choice of d.

**Theorem 3.5 (isε). PROVEN.** `isε(X) = [⊥/d]₁ [⊤/ X·d]₁ (d)` with fixed chars ⊤≠⊥, d≠⊤:
X = ε makes the pattern X·d = d fire on the whole scrutinee d (→⊤, second pass inert);
X ≠ ε makes |X·d| ≥ 2 > 1 = |d| (inert, then [⊥/d]₁ fires on d → ⊥). For |Σ| = 2 take d = ⊥.
**COMPUTATIONAL**: all |X| ≤ 6, both alphabets.

**Theorem 3.6 (eq). PROVEN.** With fixed distinct ⊤, ⊥ and any d:
```
eqind(X,Y) = [⊥ / X·YY·⊥d]₁ (Y·YY·⊥d)
eq(X,Y)    = [⊤ / eqind(X,Y)]₁ (⊥)
```
*Proof.* If X = Y the pattern and scrutinee of eqind coincide, so the whole string is the
(only, leftmost) occurrence and eqind = ⊥. If X ≠ Y: an occurrence of X·YY·⊥d in Y·YY·⊥d
that is *whole* would force |X| = |Y| and X·YY = Y·YY, i.e. X = Y — excluded; so eqind is
either inert (result Y·YY·⊥d, length ≥ 2) or a proper match (result U⊥V with U ≠ ε or
V ≠ ε, length ≥ 2); in all cases eqind ≠ ⊥ and eqind ≠ ε. The final pass fires on the
fixed scrutinee ⊥ iff eqind is a substring of a single character, i.e. iff eqind = ⊥, i.e.
iff X = Y. ∎
The trick replacing the paper's border-injectivity machinery: (i) make the *whole-string
match* the only way to produce the signal, (ii) *test* a computed string against a fixed
one-char scrutinee ([⊤/computed]₁(⊥) fires iff computed ∈ {⊥} up to a substring of ⊥).
**COMPUTATIONAL**: all |X|,|Y| ≤ 4 over {a,b} and {a,b,c}: exact ⊤/⊥ outputs.

**Theorem 3.7 (if). PROVEN.** For C ∈ {⊤,⊥}, fixed distinct ⊤,⊥, any d:
```
if(C,X,Y) = [Y / ⊥dXdYd]₁ [X / ⊤dXdYd]₁ (C·d·X·d·Y·d)
```
*Proof.* The first pattern ⊤dXdYd has exactly the length of the scrutinee, so it can only
occur at position 0, and it does iff C = ⊤, replacing the whole string by X. If C = ⊥ the
first pass is inert. The second pattern ⊥dXdYd likewise matches the ⊥-scrutinee wholly, and
on the C = ⊤ result (the string X) it is inert by length (|⊥dXdYd| = |X|+|Y|+4 > |X|). ∎
No enc-protection is needed at all — "pattern as long as the whole scrutinee" is the
once-calculus's replacement for it. **COMPUTATIONAL**: all X,Y ≤ 4, both C, both alphabets.

**Theorem 3.8 (Concatenation Elimination for ONCE). PROVEN.** By the paper's induction,
(E₁E₂)° = cat°[E₁°/X₁, E₂°/X₂] with cat° = [X₁/a]₁[X₂/b]₁(ab). Hence core = full for the
once-calculus: every concat-free denotation is denotable without concat nodes.

**Proposition 3.9 (native destructuring). PROVEN.**
(i) delete-first-occurrence-of-constant: [ε/B]₁ is a single node (the paper's tail is the
special case B = a single character *at position 0*, which needs the machinery of Thm 3.3);
(ii) prepend a computed string: [R/m]₁(m·X) = R·X for any constant m ≠ ε;
(iii) whole-input replacement: [R/X]₁X = R (e.g. doubling X ↦ XX);
(iv) replace-first-occurrence is the primitive itself. What is *missing* compared to the
baseline's derived head/tail is the ability to consume a *variable-length* chunk around the
match, e.g. "suffix after the first B" or "prefix before the first B" — see §6.

**Theorem 3.10 (enc, dec are NOT once-reachable). PROVEN.** See §4: enc is killed by the
Fresh-Character Lemma (on b^n, enc(b^n) = (xb)^n has #x = n), dec by the Max-Run Lemma (on
(xb)^n, dec((xb)^n) = b^n has max run n). Consequently the paper's whole enc-based
architecture — benc, Border Injectivity, rep_n, escape/unescape, and the baseline's
constructions of cat/head/tail/eq/if — must be, and above was, rebuilt from other
principles (leftmost-anchoring, doubled markers, whole-length patterns).

---

## 4. Expressibility vs the baseline L

### 4.1 Three potentials and linear growth

**Lemma 4.1 (Fresh-Character). PROVEN.** For E ∈ ONCE and c ∈ Σ define
fc(X_i,c)=0, fc(W,c)=#c(W), fc(E₁E₂)=fc(E₁)+fc(E₂), fc([R/P]E)=fc(E)+fc(R)+fc(P); and
vc_i likewise counting variable occurrences. Then for all inputs where defined:
```
#c(⟦E⟧(S⃗)) ≤ fc(E,c) + Σ_i vc_i(E) · #c(S_i).
```
*Proof.* Induction on E. Pass case: [R₀/P₀]₁T = U R₀ V (or T): #c ≤ #c(T) − #c(P₀) + #c(R₀)
≤ #c(T) + #c(⟦R⟧(S⃗)); apply the IH to E and R and note fc, vc add up. ∎
**COMPUTATIONAL**: the inequality was checked on 527,232 evaluations of 3,000 random
once-expressions (depth ≤ 3, 1- and 2-ary) against the recursively computed coefficients —
zero failures (`lemmas.py`).

**Lemma 4.2 (Max-Run). PROVEN.** Let mr(T) = longest run of a fixed character. There are
α(E), β(E) with mr(⟦E⟧(S⃗)) ≤ α(E) + Σ β_i(E)·mr(S_i); take β(X_i)=1, β(W)=0,
β(E₁E₂)=β₁+β₂, β([R/P]E)=2β(E)+β(R) (a deletion can merge the two runs adjacent to the
match, doubling; an insertion contributes additively). ∎ (Same computational check.)

**Lemma 4.3 (Balance). PROVEN.** For characters x≠y and Ψ(T)=#x(T)−#y(T): |Ψ(⟦E⟧(S⃗))| ≤
K(E) + Σ v_i(E)·|Ψ(S_i)| with K, v defined by K(X_i)=0, v(X_i)=1; K(W)=|Ψ(W)|;
K(E₁E₂)=K₁+K₂; K([R/P]E)=K(E)+K(P)+K(R). ∎ (Same computational check.)

**Lemma 4.4 (Linear Growth). PROVEN.** |⟦E⟧(S⃗)| ≤ C_E + w(E)·max_i|S_i|, where w counts
variable occurrences (w(X_i)=1, w(W)=0, w(E₁E₂)=w₁+w₂, w([R/P]E)=w(E)+w(R)). A once-pass
adds |R₀| in place of |P₀| ≥ 1 at one site. **ONCE has degree ≤ 1**; the baseline has
unbounded degree (the paper's X ↦ X^|X| = [X₁/σ][σ/Σ]X₁ has degree 2, verified).

### 4.2 The separation L ⊄ ONCE

**Theorem 4.5 (Replace-all is not once-reachable). PROVEN.**
The function C ↦ [a/b]C (replace every b by a) is not denoted by any ONCE expression.
*Proof.* On C = b^n it outputs a^n, so #a = n. By Lemma 4.1, #a ≤ fc(E,a) + vc(E)·#a(b^n)
= fc(E,a), a constant. For n > fc(E,a): contradiction. ∎

**Corollary 4.6. PROVEN.** Each of the following L-reachable functions is *not* once-reachable:
- [a/b]C and [xb/b]C = enc (Fresh-Character, Lemma 4.1);
- [b/xb]C = dec (Max-Run, Lemma 4.2: on (xb)^n output b^n has mr = n, input mr = 1);
- [xx/x]C "double every x" (Balance, Lemma 4.3: on (xy)^n the output (xxy)^n has Ψ = n,
  input Ψ = 0);
- X ↦ X^{|X|} and S ↦ σ^{|S|} (Linear Growth, Lemma 4.4);
- escape_f for any escaping function with |U| ≥ 2 (Fresh-Character: on u₂^n the image has n
  fresh f(u₂)'s).

Hence **L ⊴ ONCE is REFUTED** — strictly, ONCE does not contain the baseline.

### 4.3 Is ONCE ⊴ L? (Does the baseline express the once-primitive?)

This is the central open question of this variant. Status: **OPEN**, with substantial
evidence in both directions.

**(+) Theorem 4.7 (unary simulation). PROVEN.** Over the unary domain {b}*, the L-calculus
(with variable patterns) computes delete-exactly-one-b, i.e. [ε/b]₁ restricted to b*:
```
H(X)   = [b/a]₁ [ε/b]₁ [a/bb]₁ X            (floor-halving: b^n ↦ b^⌊n/2⌋)
D(X)   = [H(X) / H(X)·b] (X)
```
*Proof.* On b^n the pattern H(X)·b = b^{⌊n/2⌋+1} has length > n/2, so the greedy scan finds
**exactly one** match (a second disjoint occurrence would need 2·(⌊n/2⌋+1) > n characters),
necessarily at position 0; replacing it by b^{⌊n/2⌋} leaves b^{n−1}. n = 0: pattern b,
scrutinee ε, inert. ∎ **COMPUTATIONAL**: verified n = 0..499 (exactly one greedy match each
time). The same ">half-length needle" idea expresses [A/B]_k on unary inputs for any k
(k disjoint needles of length > n/k). *Moral:* any proof that L cannot express once must use
general position — on unary (or otherwise anchored) domains, computed needles do the job.

**(−) Negative evidence (all COMPUTATIONAL, `L_search.py`, `L_rand.py`).** Target functions:
delete-first-b and replace-first-b-by-a, test domain all {a,b}* up to length 6 (254
strings; a witness for the full function must in particular match these):
- Constant-pattern L-pipelines, patterns ≤ 2 and replacements ≤ 2 over Σ={a,b,c}
  (156 passes/level), exhaustive BFS with behavior dedup: **324,765 distinct behaviors at
  depth 3 — no witness** (control: delete-all-b found at depth 1).
- Constant patterns ≤ 3 (39 patterns), depth 2: 36,153 behaviors — no witness.
- Variable-pattern pipelines (patterns/replacements from {X, XX, aX, Xa, bX, Xb, cX, Xc,
  halve(X)·b, constants}, 96 passes/level), depth 3: 8,668 behaviors — no witness.
- Randomized search: **74,965,097 constant pipelines of 4–7 passes** (patterns/replacements
  ≤ 2 over {a,b,c}, tested on all {a,b}* ≤ 7) — **no witness**; the closest misses differed
  at exactly one position.
The same BFS also proves no *once*-expressibility-based shortcut exists at these sizes for
the k-family item in §4.4.

**Conjecture 4.8 (Incomparability). CONJECTURE.** [ε/b]₁C (delete the leftmost b) is not
L-expressible; hence ONCE and L are incomparable (L ⊴ ONCE fails by Thm 4.5, ONCE ⊴ L fails
by this conjecture). Supporting reasoning beyond the searches: every L pass treats all
matches of its needle symmetrically; the asymmetries available are (i) the string boundary,
(ii) overlap parity inside runs (greedy non-overlapping scan), (iii) needles of computed
shape (variable patterns) — but a needle anchored at the *first* occurrence in general
position must contain the prefix up to that occurrence, and computing "the b-free prefix"
(or dually "the suffix from the first b") appears to require the very capability being
simulated: all attempted constructions (marker sandwiches, doubled strings C·m·C, escape then
restore, protect-then-replace) regress into the same problem one level up. Note this is the
mirror image of the once-side's difficulty: ONCE cannot protect *all* occurrences (no enc),
L cannot single out *one*.

### 4.4 The bounded family [A/B]_k inside ONCE

- **A disjoint from B (A contains no occurrence of B): PROVEN** [A/B]_k = k once-nodes
  [A/B]₁∘…∘[A/B]₁ (inserted text is never rematched).
- **Overlapping (A contains B), e.g. [ab/b]₂:** the naive k-fold composition is wrong
  (Prop 1.3), and the marker needed to protect the first site must be *b-free* (so the next
  scan finds the second site) *and fresh w.r.t. the input* (so the final restore pass is
  unambiguous) — ONCE has no enc to build one. **COMPUTATIONAL**: over the restricted domain
  {b,c}* (character 'a' reserved as marker) the 3-pass once-pipeline
  **[a/b]₁, [ab/b]₁, [ab/a]₁** computes [ab/b]₂ exactly (verified on 20,000 random
  {b,c}-strings of length ≤ 14); over the full domain {a,b,c}* ≤ 4 no constant-pattern
  once-pipeline with ≤ 3 passes (2.57M behaviors, patterns/replacements ≤ 2) computes it.
  **CONJECTURE**: [ab/b]₂ is not once-expressible on the full Σ* (any fixed finite supply
  of marker constants fails on inputs containing them; variable b-free fresh markers are
  blocked by Fresh-Character applied to the marker's alphabet).

---

## 5. Complexity

**Theorem 5.1 (Growth and time). PROVEN.** By Lemma 4.4 every intermediate value of an ONCE
pipeline has length ≤ C_E + w(E)·M (M = max input length): **linear growth, degree exactly ≤ 1**,
versus the baseline's unbounded polynomial degree (X^|X| ∈ L has degree 2; verified
numerically). Evaluation of a once-pass is one leftmost search plus one splice, O(current
length) — but note patterns/replacements are themselves computed by sub-pipelines over the
*original* inputs, each O(poly) by the same bound; a pipeline of k passes costs
O(k · (C_E + w(E)M) · (1 + max pattern length)) ≤ O(|E|² · M) up to constants. So
**ONCE ⊆ (near-)linear time**; nothing in the once-calculus can break polynomial time, let
alone linear growth. The paper's Duplication Degree for the once-node degenerates:
deg([R/P]E) = deg(E) + deg(R) is still well-defined but the match-count factor |T| in the
paper's length bound disappears (one match, not ≤ |T| matches), collapsing all degrees to 1.

**Expressive limits as complexity-style invariants.** The three potentials
(Fresh-Character, Max-Run, Balance) are necessary conditions on ONCE functions that are
*independent of growth*: e.g. a ↦ a^|X| has linear growth but is still unreachable
(Fresh-Character). They are the once-calculus's analog of the paper's Length Bound lemma,
and strictly stronger than it.

---

## 6. Open problems

1. **Is ONCE ⊴ L?** i.e. is [A/B]₁C (equivalently [ε/b]₁C, delete-first-b) expressible in the
   baseline calculus? The central open problem (Conjecture 4.8: no). Any proof must handle
   variable patterns (Thm 4.7 kills all unary/quasi-linear-growth approaches) and would
   presumably show that "prefix-extraction at the first match" is not L-computable.
2. **Is [A/B]_k (overlapping A,B, k ≥ 2) once-expressible on full Σ*?** Restricted-domain
   witness exists (§4.4); the obstruction is a b-free fresh marker.
3. **Suffix/prefix extraction at a delimiter:** is "C with everything up to and including
   the first B deleted" once-computable? L-computable? (For ONCE this is strictly harder
   than [ε/B]₁ and seems to need exactly what eq/if cannot supply; for L it is the same
   obstacle as problem 1.) Related: is "second occurrence" addressable in either calculus?
4. **Exact characterization of ONCE-reachable functions** (analog of the paper's open
   question 1 for L): somewhere inside linear-growth + Parikh-bounded (three potentials)
   functions, strictly containing cat/head/tail/eq/if-combinations. Is it decidable whether
   a finite function table extends to an ONCE-reachable function?
5. **Is the once-calculus closed under the k-family?** (i.e. ONCE_k ⊴ ONCE_1 for all k?)
   True for disjoint patterns (PROVEN), open for overlapping ones (problem 2).
6. The paper's own opens transplanted: is reversal once-reachable? (Clearly no harder tools
   than L, but also no more; both open.) Do larger alphabets add power to ONCE? (The
   constructions of §3 need only |Σ| = 2; the separations of §4 are alphabet-insensitive.)
7. **Erratum carry-over:** does the baseline paper's Independent Substitution Lemma get used
   anywhere with an empty replacement (where the B ≠ ε hypothesis would matter)?

---

## 7. Relations summary

Notation: X ⊴ Y = every function reachable in calculus X is reachable in calculus Y
(paper-style expressions; "core" = concat-free fragment; L = the paper's baseline calculus).

```
EXPR: ONCE ⊴ L STATUS: OPEN (conjectured FALSE — Conjecture 4.8) — no L-expression known for the once-node [A/B]₁; exhaustive searches (constant patterns ≤3 passes: 324,765 behaviors; variable grammar ≤3 passes: 8,668; randomized 4–7 passes: 74,965,097 pipelines) all negative; unary case IS expressible (Thm 4.7), so no easy invariant separates them.
EXPR: L ⊴ ONCE STATUS: REFUTED — replace-all [a/b]C is not once-reachable (Fresh-Character Lemma, Thm 4.5, PROVEN); also dec, escape_f, [xx/x], X^{|X|} unreachable (Cor. 4.6).
EXPR: ONCE-core ⊴ ONCE-with-concat STATUS: PROVEN — cat is once-core: [X/a]₁[Y/b]₁(ab) (Thm 3.1); paper's elimination induction transfers (Thm 3.8).
EXPR: cat, head, tail, isε, eq, if ∈ ONCE-core STATUS: PROVEN — Thms 3.1–3.7; verified computationally over |Σ|=2 and 3, exhaustive small domains.
EXPR: enc, dec ∈ ONCE STATUS: REFUTED — enc by Fresh-Character (b^n ↦ (xb)^n), dec by Max-Run ((xb)^n ↦ b^n) (Thm 3.10, PROVEN).
EXPR: [A/B]_k ∈ ONCE (A contains no B) STATUS: PROVEN — k once-nodes suffice; inserted text is never rematched (Prop 1.3).
EXPR: [ab/b]_2 ∈ ONCE on {b,c}* (reserved marker char) STATUS: COMPUTATIONAL — witness [a/b]₁[ab/b]₁[ab/a]₁, verified on 20,000 random strings ≤14; fails on inputs containing 'a'.
EXPR: [ab/b]_2 ∈ ONCE on full Σ* STATUS: CONJECTURE (no) — full-domain search ≤3 passes, 2.57M behaviors, no witness; b-free fresh marker obstruction.
EXPR: [ε/b]₁ (delete-first-b) ∈ L restricted to b* STATUS: PROVEN — [H/H·b](X), H = floor-halving pipeline; needle longer than half the string has exactly one greedy match (Thm 4.7).
EXPR: ONCE ⊆ linear-growth, ⊆ linear-time STATUS: PROVEN — Lemma 4.4 + §5; contrast L ∋ X^{|X|} (degree 2), so ONCE ⊊ L in growth dimension.
EXPR: once-calculus ⊴ positional calculus replaceOcc(0,B,A) STATUS: PROVEN (definitional identity of the k=1 primitives; the positional family with general indices is strictly larger and studied separately).
EXPR: paper's Independent Substitution Lemma (B = ε allowed) in L STATUS: REFUTED — A="aa",B=ε,C="b",S="aba": [ε/b]"aba"="aa" ∋ "aa" but "aa" ⊄ "aba"; holds in both calculi with B ≠ ε.
```

**One-line summary of the variant.** ONCE is the baseline with all *simultaneity* removed
and all *anchoring* kept: it cannot touch two match-sites with one node, so enc/dec/rep/escape
and replace-all itself are gone (proven), but leftmost-anchoring is such strong marker
protection that cat, head, tail, eq and if are all rebuildable (proven) — often more simply
than in the baseline — leaving the two calculi, conjecturally, incomparable.

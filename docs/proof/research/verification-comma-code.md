# Verification Report: The Comma-Code Construction

Independent verification of the central claim of [multi.md](multi.md) §4 — that the
paper's freezing multi-replace with **unrestricted** patterns (no hypothesis (H))
is expressible in the baseline calculus via the comma code, hence **M ≡ L** —
plus its corollaries. Conducted 2026-09-19 by the coordinator, separately from the
research agent that produced the claim.

## 1. Method

- **Independent reimplementation.** `scratch/verify_comma/verify.py` re-implements,
  from the report's specification and the paper's definitions only (none of the
  agent's scripts were used or consulted):
  - `subst` — the paper's Definition 1 (greedy leftmost, non-overlapping, no restart);
  - `rep_ref` — the freezing semantics (the paper's Definition *rep*);
  - `repC_comma` — the §4.2 construction, applied **entirely as baseline `subst`
    passes** (enc₂ = `[xx/x]` then `[xc/c]` ∀c≠x; rename `[m_i/E_Xi]`; repair
    `[E_Xi·b / m_{i+1}]`; instantiate `[E_Yi/m_i]` descending; dec₂ = `[c/xc]` ∀c≠x
    then `[x/xx]`), which simultaneously verifies the "expression of the baseline
    calculus" claim;
  - `repC_paper` — the paper's original (H)-restricted construction, for anchors.
- **Anchoring against Lean.** All implementations are anchored to the actual
  `#eval` outputs of `lean/Subst.lean` (compiled 2026-09-19): the Definition-1
  examples, `repRef`/`repC` on the two test pair-sets, and the shadowing instance
  where the paper's construction gives `bbbaaab` but the freezing semantics gives
  `bbbaabbba` — reproduced exactly by the reimplementation.
- **Spec conformance.** The pass list generated for the shadowing instance equals
  the 10-pass pipeline printed in multi.md §4.5, character for character, and
  running it end-to-end yields the freezing result. (The check earned its keep: it
  initially failed on a transcription typo in the *expected* list — 7 b's instead
  of 6 in repair 2 — which re-derivation confirmed was my typo, not the report's.)

## 2. Structural proof audit (multi.md §4.2)

The written proof was checked clause by clause. Key steps re-derived by hand:

- **Lemma A (code properties).** enc₂(W) = (xΣ)*: even length, x at every even
  position, unique block parse; dec₂ inverts on images (an `xc` (c≠x) occurrence
  in an image is necessarily a block: at odd positions the data char would have to
  equal x, and after the c-collapses the x-runs are exact concatenations of `xx`
  blocks, so the greedy `[x/xx]` halves at block boundaries). Images have b-runs
  ≤ 1; markers m_i = x·b^{i+1} have b-run i+1 ≥ 2 and begin with x. ✔
- **Occurrence classification.** E = enc₂(X_i) begins with x, so occurrences start
  at (α) block commas, (β) data characters, or (γ) marker x's — exhaustive, since
  deeper marker positions hold b ≠ E[0]. ✔
- **(β) shadowing — the crux.** A (β) start requires the data char to equal E[0] = x,
  then the following comma to equal E[1], inductively forcing X_i = x^k, i.e.
  E = (xx)^k, an all-x pattern; and then the comma at p−1 (which is always x) starts
  an aligned occurrence covering [p−1, p+2k−1) — the same all-x region minus its
  last character — so the aligned occurrence exists and starts strictly earlier.
  The greedy scan tries p−1 before p in every resume configuration, so (β) is
  never taken. ✔ (This is exactly what the paper's non-uniform code lacks: there,
  a misaligned image can end mid-unit and precede an overlapping genuine match —
  the shadowing failure that motivated (H).)
- **(α)-spurious shape.** Leaving the fragment forces E's comma slot onto the
  marker's x and its last data slot onto the marker's first b, so X_i ends with b
  and the match covers (k−1 blocks) + the marker's first two characters — always
  followed by ≥ 1 further b (the marker has ≥ 2 b's for i ≥ 1). (γ) collapses to
  the single case X_i = `b` (E = `xb`), matching every marker's first two
  characters, likewise followed by a b. ✔
- **Repair arithmetic.** Rename turns a spurious site into m_i followed by the
  eaten marker's b^j (j ≥ 1). m_{i+1} = x·b^{i+2} occurs nowhere else (fragment
  b-runs ≤ 1; older markers' b-runs ≤ i+1 and markers are followed by non-b;
  genuine markers are followed by non-b), and replacing it by E·b restores the
  original text exactly: E·b + b^{j−1} = (k−1 blocks) + x·b^{j+1} — verified by
  character count and by the two special shapes (X_i = `b`; X_i ending in b). ✔
- **Instantiation and decoding.** m_i is not a prefix of any m_j (j < i) and
  matches nowhere else; inserted E_{Y_i} are fragments (no bb), undisturbed by
  later passes; the final text is enc₂ of the freezing result. Undefinedness
  matches: the only possibly-empty pattern is E_{X_i}, exactly when X_i = ε. ✔

No gaps found. The argument is complete and correct as written.

## 3. Computational verification

`repC_comma == rep_ref` on every evaluation, by chunk (all statuses COMPUTATIONAL
on the stated finite domains):

| Chunk | Domain | Evals | Failures |
|---|---|---|---|
| base | anchors vs Lean; §4.5 pipeline; n=1 exhaustive Σ={a,b} (pat ≤ 3, rep ≤ 3, str ≤ 6), both (b,x) | 168,021 | 0 |
| n2a | n=2 exhaustive Σ={a,b} (all 9,604 pattern-set families, str ≤ 4), (b,x)=(a,b) | 297,724 | 0 |
| n2b | same, mirrored (b,x)=(b,a) | 297,724 | 0 |
| n3 | n=3 exhaustive Σ={a,b} (pat ≤ 2, rep ≤ 1, str ≤ 4) | 180,792 | 0 |
| tri | Σ={a,b,c}, n=1 (str ≤ 4) and n=2 (str ≤ 3), two orientations | 222,072 | 0 |
| adv | shadowing instance (all strings ≤ 8, both orientations); marker-shaped patterns; 30,000 randomized trials (n ≤ 4, |pat| ≤ 4, |S| ≤ 20, |Σ| ≤ 4) | 88,172 | 0 |
| **total** | | **1,254,505** | **0** |

Coverage notes: n=2 binary is the agent's own full pattern-set space (9,604
families) at string depth 4 (the agent used 6); n=1 binary is fully exhaustive at
depth 6 with replacements to length 3. Randomized stress reaches pattern length 4
and 4-character alphabets. This is a smaller total than the agent's >10⁷, but it
is an *independent* implementation reaching the same verdict, which is the point.

## 4. Corollary checks

- **Escape without (H2).** All 21 escaping functions over Σ = {a,b,c} (every
  bijection f: U → V with the fixed point enumerated first, including those with
  x ∈ V — the (H2) violators): the semantic round trip unescape∘escape = id holds
  on all strings ≤ 6, and the comma-code construction agrees with the freezing
  semantics on both the escape and unescape pair-sets over **all six** (b,x)
  orientations. 0 failures. This independently corroborates multi.md §4.3's
  resolution of the paper's Remark (escape-hyp), second bullet.
- **Paper's construction genuinely needs (H).** Cross-checked via anchors: the
  paper's repC on the shadowing instance returns `bbbaaab` ≠ `bbbaabbba`, matching
  the Lean `#eval` — the failure is real, the comma code fixes it, and both facts
  now have two independent implementations agreeing.

## 5. Verdict

**The comma-code construction is verified.** The structural proof is complete and
correct on audit, and an independent reimplementation agrees with the freezing
semantics on 1,254,505 evaluations across binary and ternary alphabets, n ≤ 3
exhaustive plus randomized n ≤ 4, all (b,x) orientations, marker-shaped and
shadowing-adversarial families — zero disagreements. The PROVEN status of
multi.md §4.2/§4.3 (M ≡ L; (H) is an artifact of the paper's encoding; (H2)
droppable) is corroborated.

## 6. Implications for promotion

1. **Paper.** The Multiple Substitution theorem can be restated without hypothesis
   (H) (arbitrary nonempty patterns), proved via the comma code; Remark (rep-hyp)
   should be updated to say the *original* construction requires (H) — with the
   2,937/9,604 disagreement rate as quantification — while the architecture itself
   is unrestricted. The paper's enc/dec, cat, head/tail, eq, if are unaffected (they
   only need the enc₂-free parts). The escape theorem loses hypothesis (H2).
2. **Lean.** The port is mechanical in structure: `enc2`/`dec2` as compositions of
   `subst` passes (mirroring the existing `enc`/`dec` lemmas: a doubling pass then
   per-character passes — same shape as the existing `tail` cascade), the same
   `marker` and the same `repC` skeleton with `enc2` in place of `enc`. A
   `repC2_correct` without (H) would then subsume the current `repC_correct` (whose
   proof is still `sorry`), upgrading the formalization to full generality. The
   proof effort is comparable to the paper's staged argument: the (β)-shadowing
   lemma (all-x patterns) and the repair-restoration lemma are the two new
   workhorses.

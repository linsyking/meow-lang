# Replace Primitives: Expressive Power — Research Overview

Synthesis of the seven per-variant studies (Phase 2). Each variant was studied by an
independent research agent that read `../main.tex`, defined its variant in the paper's
style, verified claims computationally by brute force, and wrote a report:

| ID | Primitive | Report |
|----|-----------|--------|
| `L` | baseline: leftmost-first, non-overlapping, no-restart replace-all (paper Def. 1) | `../main.tex` |
| `r2l` | mirror: rightmost-first replace-all | [r2l.md](r2l.md) |
| `once-l` | replace leftmost occurrence only | [once-l.md](once-l.md) |
| `once-r` | replace rightmost occurrence only | [once-r.md](once-r.md) |
| `restart` | single-rule Markov: replace leftmost, rescan from 0, until fixpoint | [restart.md](restart.md) |
| `rescan` | single left-to-right pass that re-enters inserted text | [rescan.md](rescan.md) |
| `multi` | unrestricted simultaneous multi-pattern replace (freezing) | [multi.md](multi.md) |
| `pos` | positional: `setAt(i,c)`, `repOcc(k,B,A)` | [pos.md](pos.md) |

**Status policy.** All claims below carry the status assigned in the source report:
PROVEN (agent-written proof), COMPUTATIONAL (exhaustive on a stated finite domain),
CONJECTURE (evidence only), REFUTED (counterexample). Agent proofs have not been
independently re-verified except where noted. Scripts live under `scratch/<id>/`.
Notation `X ⊴ Y`: every function reachable in calculus X is reachable in calculus Y.

## 1. Headline results

1. **`multi ≡ L` (PROVEN, both directions; core versions too).** The paper's freezing
   multi-replace with *unrestricted* patterns is reachable in the baseline via the
   **comma code** (escape every character as `x·c`: all code words length 2,
   phase-locked) running the same rename/repair/instantiate/decode architecture.
   The paper's hypothesis (H) — patterns single-char or not ending in `x` — is an
   artifact of its escaping scheme, not an intrinsic boundary. The paper's own
   shadowing counterexample instance *is* computable by an explicit 10-pass
   (minimizable to 8) constant pipeline. *(multi.md §4)*
   **PROMOTED (2026-09-19):** this is now the paper's Theorem (Multiple
   Substitution) — the old (H)-restricted Theorem 2.9 was removed and replaced
   by the comma-code version (full phase-locking proof); the enc-based variant
   survives only as Remark rem:comma (its shadowing failure + the open
   characterization question), and the escape theorem lost hypothesis (H2).
2. **Escape hypothesis (H2) is droppable (PROVEN).** The paper's Remark (escape-hyp)
   asked whether `x ∉ V` can be dropped; answer: yes, the round trip needs only (H1)
   (fixed point enumerated first). Verified on 133 escaping functions. *(multi.md)*
3. **`restart` breaks the paper's complexity theorems (PROVEN).** A single restart
   node `[baa/ab]ᵐ` computes binary Horner evaluation: output `2^{n-1}+n-1` in
   `2^{n-1}−1` steps; `2t−1` nodes give towers of any height. The paper's Length
   Bound and poly-time soundness are REFUTED for this calculus. Termination is
   total ⟺ `B ⊄ A` when `|A| ≤ |B|` (`A ≠ B`); in general it embeds the open
   one-rule semi-Thue termination problem. *(restart.md)*
4. **`rescan`'s divergence is exactly the paper's non-restart clause (PROVED).**
   `[A/B]ᵘ` is total ⟺ `B ⊄ A`, and `[A/B]ᵘ = [A/B]` iff additionally no nonempty
   suffix of A is a proper prefix of B. The whole Section-2 toolkit collapses under
   ᵘ (enc diverges; a no-escape lemma: every total constant-pattern ᵘ-pipeline is
   non-injective), while the total fragment keeps the Length Bound and poly-time.
   *(rescan.md)*
5. **`r2l` is L's mirror, and their relation *is* the reversal problem (PROVEN).**
   Rev Duality `[A/B]ᴿC = rev([revA/revB](revC))` lifts to a Conjugation Theorem:
   `rev ∈ L ⟺ rev ∈ r2l`, and if rev is reachable in either, the calculi are
   **equal**. Unconditionally the constant-pattern cores are incomparable
   (left- vs right-subsequential); the unbordered-pattern fragments are equal;
   the whole Section-2 toolkit and concatenation elimination work verbatim under
   r2l. But the paper's `rep_n` construction is NOT direction-robust — under r2l
   it fails even with (H); fixes: mirrored construction ("Xᵢ doesn't *begin* with
   x") or the stronger "Xᵢ ends outside {b,x}" (both PROVEN). *(r2l.md)*

## 2. The two hinge problems

The inclusion web hangs on two ropes; together they decide everything.

- **Hinge 1: `once_l ∈ L`?** (replace-leftmost-occurrence in the baseline)
  Decides `ONCE ⊴ L` and `pos ⊴ L` (PROVEN equivalence, pos.md Theorem H).
  `setAt(i,c) ∈ L` is PROVEN (explicit construction); `repOcc(k,B,A)` =
  `2k+1` once-nodes with a fresh marker (PROVEN). All searches negative
  (L-lit ≤ 4, L-macro ≤ 3, ~75M randomized pipelines; unary case IS expressible —
  floor-halving needles — so no easy invariant separates).
- **Hinge 2: `rev ∈ L`?** (the paper's open problem 2)
  `rev ∈ L ⟺ rev ∈ r2l ⟺ rev ∈ once-l ⟺ rev ∈ once-r` (PROVEN).
  Decides `r2l = L`; `L ⊴ once-r ⟺ R2L ⊴ once-l` (PROVEN). If both hinges
  resolve positively, once-l, once-r, r2l and pos all collapse into L.

## 3. The expressibility landscape (vs baseline L)

| Variant | V ⊴ L | L ⊴ V | Growth / time |
|---|---|---|---|
| `multi` | **PROVEN** (comma code) — hence **M ≡ L** | **PROVEN** (single round) | = L: poly, `X^{\|X\|}` yes, `X^{2^{\|X\|}}` no |
| `r2l` | OPEN ⟺ `rev ∈ L` | OPEN ⟺ `rev ∈ L` (equality if rev) | = L (mirrored bound) |
| `restart` | **REFUTED** (amplifier ∉ L; also partial) | **REFUTED** (core-const: `[aa/a]` ∉ V by no-injective-node); full: conj. against | unbounded (towers); poly-time REFUTED |
| `once-l` | OPEN (conj. **no**) | **REFUTED** (Fresh-Character Lemma) | linear growth, near-linear time |
| `once-r` | OPEN (conj. **no**) | **REFUTED** (Occurrence Bound) | linear growth + occurrence bound |
| `pos` | OPEN ⟺ `once_l ∈ L` | **REFUTED** (single-site alphabet bound + linear growth) | output ≤ linear — cannot write quadratic strings |
| `rescan` | OPEN (conj. no; candidate witness: a-flood `[a/ab]ᵘ`) | OPEN (conj. no; toolkit collapses, no-escape lemma) | total fragment: poly-time (Length Bound verbatim); `Safe ⇒ total` REFUTED |

Reading: **`multi` = L exactly; `restart` is the only variant *above* L (in growth);
`once-l`, `once-r`, `pos` sit *below* L in different, mostly incomparable ways;
`r2l` is L's mirror image; `rescan`'s total fragment looks incomparable.**

## 4. Toolkit survival

Which of the paper's constructions can be rebuilt with the variant as the only primitive:

| | enc/dec | cat | head/tail | eq | if | concat-elim |
|---|---|---|---|---|---|---|
| `r2l` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ (mirrored) |
| `once-l` | **✗ (proven: Fresh-Character / Max-Run)** | ✓ | ✓ | ✓ | ✓ | ✓ |
| `once-r` | ✗ single-char round-trip ✓ | ✓ **optimal zipper** `[Y/a]₁ᴿ[X/b]₁ᴿ(ba)`, size 7 | head/tail: conj. ✗ | conj. ✗ | conj. ✗ | ✓ (zipper) |
| `restart` | ✗ (diverges) — black-box enc/dec recover the rest | ✓ (given enc/dec) | ✓ (given enc/dec) | ✓ | ✓ (redesigned) | open (IC conjecture) |
| `rescan` | ✗ (diverges; no-escape lemma) | conj. ✗ | ✗ | ✗ | ✗ | conj. ✗ |
| `pos` | ✗ (alphabet bound) | conj. ✗ (core) | tail ✓ (2 nodes); head w/ concat | conj. ✗ | — | n/a |

Notable asymmetry: `once-l` rebuilds head/tail/eq/if (left-anchoring matches the
paper's own leftmost-scan design), while `once-r` conjecturally cannot (its anchors
are on the right). `restart` with enc/dec as black boxes recovers cat/eq/head/tail
and needs (H) plus a new condition `X_i ∉ {b,x}` for rep_n (0 failures / 520,898
instances).

## 5. Erratum in the paper (confirmed independently by 6 of 7 agents)

**Independent Substitution Lemma is false as stated**: it needs `B ≠ ε`
(empty replacement merges neighbors and creates new occurrences).
Counterexamples: `A="aa", B=ε, C="b", S="aba"` — `[ε/b]"aba" = "aa" ∋ "aa"` but
`"aa" ⊄ "aba"`; also `A="bc", S="abZcd"` (multi.md). The lemma is never
referenced later in the paper (only the `\label` at main.tex:148), so the fix is
to add the hypothesis to the statement — no downstream proofs are affected.

**FIXED (2026-09-19):** hypothesis `B ≠ ε` added to the lemma statement in
`main.tex`, together with a necessity remark and a proof clarification (the
inserted nonempty, character-disjoint `B` is what blocks straddling
occurrences). Also fixed: three stale `#eval` comment lines in
`lean/Subst.lean` (`[a/a]aa = aa`, not `= a`; the repRef/repC pair gives
`[c, a]`, not `[c, a, a]`), confirmed against a full recompile — outputs now
match the comments.

## 6. Paper open questions — status after this research

| Paper's open question | Status |
|---|---|
| Exact characterization of sound pattern families for rep_n (Remark rep-hyp) | **Resolved and promoted**: no restriction needed — comma code gives multi ≡ L, now the paper's Theorem (Multiple Substitution); the enc-based construction genuinely needs (H) (2,937/9,604 n=2 families disagree without it) and is now a remark with the characterization question |
| Can (H2) (`x ∉ V`) be dropped from the escape round trip? (Remark escape-hyp) | **Resolved and promoted**: yes, PROVEN (only (H1) needed); (H2) removed from the theorem |
| Is string reversal reachable? | Still open — but now the proven hinge of the whole direction web (`rev ∈ L ⟺ rev ∈ r2l ⟺ rev ∈ once-l ⟺ rev ∈ once-r`); partial: `lastchar, droplast ∈ R2L` PROVEN |
| Alphabet-sensitivity | Partial: pos shows a strict unary dichotomy (`[a^j/a] ∈ pos` iff `|Σ| = 1`); once-l's unary case is expressible |
| Poly-time characterization | Refined: restart is the first variant breaking it (towers); all other variants' total fragments stay poly-time |

New open problems introduced by this research, roughly by value:

1. `once_l ∈ L` — decides the once-family and pos relations to L (the shared hinge).
2. `rev ∈ L` — decides r2l = L and bridges the once web.
3. **IC conjecture** (restart): no total, injective, growing core restart-expression exists even with variable patterns — the hinge for restart's entire toolkit; constant-pattern case PROVEN.
4. Is one-pass multi-replace (first-rule or leftmost-longest position-priority) expressible in L? Freezing (round-priority) is; one-pass variants are pairwise distinct from it and from each other; all searches negative.
5. Is the a-flood `[a/ab]ᵘ` L-expressible? (candidate separator for rescan vs L)
6. `cat ∈ rescan-core`, `eq ∈ pos`, `head ∈ once-r` — blocked conjectures.

## 7. Promotion candidates (into the paper / Lean)

Priority-ordered, with suggested target:

1. **Fix the Independent Substitution lemma** (add `B ≠ ε`) — verified erratum,
   no downstream impact.
2. **Comma-code construction** — strengthens the Multiple Substitution theorem by
   removing hypothesis (H); also lets `repC_correct` in `lean/Subst.lean` be stated
   and proven in full generality (replacing the current `sorry`'s (H) hypothesis).
   **VERIFIED (2026-09-19)**: structural proof audited clause-by-clause, and an
   independent reimplementation (from the report's spec only, anchored to the
   Lean `#eval` outputs) agreed with the freezing semantics on **1,254,505
   evaluations, 0 failures** — see
   [verification-comma-code.md](verification-comma-code.md).
   **DONE (2026-09-19)**: promoted into the paper. The old (H)-restricted
   Theorem 2.9 was *removed* and the comma-code construction is now Theorem
   (Multiple Substitution), with Definition/Lemma (Comma Code) and the full
   phase-locking proof; Remark rem:comma keeps the enc-variant's shadowing
   counterexample and its open characterization question; the escape theorem
   dropped (H2). Lean port: `enc2`/`enc2Pass`/`dec2Pass`/`repC2` added with the
   code layer (`enc2Pass_eq`, `dec2Pass_enc2`); `repC2_correct` stated without
   (H) — the staging proof remains open (roadmap in its docstring).
3. **A "direction" remark/section** — **DONE (2026-09-19)**: promoted as the
   paper's §5.3 (The Other Direction): Rev Duality, Conjugation (rev reachable
   iff in L iff in R; decides L = R), unbordered agreement, the direction-robust
   toolkit, the comma construction NOT direction-robust (counterexample + 708/5292
   census) with the mirrored repair (16,140 checks) and the ends-outside variant
   (23,996 checks), escape direction-lock, and left-subsequentiality giving
   incomparable constant fragments.
4. **A "weaker primitives" section** — **DONE (2026-09-19)**: promoted as §5.1
   (Once) + §5.2 (Positional): Doubled Marker lemma, once-toolkit (cat/tail/
   head/eq/if without enc), once-invariants (fresh-character, max-run, balance,
   linear growth) ⟹ L ⊴ ONCE, unary simulation; positional toolkit (tail 2
   nodes, head scaffold), invariants, unary dichotomy, and the once hinge
   (POS ⊴ L ⟺ once-primitive ∈ L, via setAt ∈ L and repOcc-via-markers).
   All constructions re-verified in
   [scratch/paper_variants/verify_variants.py](scratch/paper_variants/verify_variants.py)
   (chunks `once`, `pos`) plus the agents' own scripts.
5. **An "unbounded iteration" section** — **DONE (2026-09-19)**: promoted as §5.4
   (Unsafe/rescan: totality, exact agreement characterization, encoder-collapse,
   no-escape, run-collapse in L and U) + §5.5 (Markov/restart: termination
   classification, amplifier, towers, no-injective-nodes, IC conjecture,
   black-box-encoder toolkit). **Corrections found during re-verification**
   (verify_variants.py chunk `rescan`/`restart` + `verify_extra.py`/
   `verify_extra2.py`): the divergent length-increasing binary rules with
   |A|,|B| ≤ 4 are EIGHT, not four (add [aaab/ba], [abbb/ba], [baaa/ab],
   [bbba/ab]); 170 of 930 rules diverge, not 166; the growth census of the 162
   total rules |A|,|B| ≤ 3 is 140 linear / 18 superlinear (≤ 3n) / 4 exponential,
   not 144/14/4; sort and collapse nodes do NOT commute (claim removed); the
   report's amplifier v-recursion was garbled (correct: v(Ta) = v(T)+1,
   v(Tb) = 2v(T)); comma-with-restart correct iff no X_i = b (8,370 checks,
   364/2604 unconditional failures exactly X_1 = b ∧ b ∈ S).
6. **Update the open-problems list** — **DONE (2026-09-19)**: the paper's §5.6
   (The Landscape) tabulates the five variants, names the two hinges (once ∈ L,
   rev ∈ L) and lists seven open problems; methodology remark documents the
   computational-verification discipline.

**Verification status**: (1) comma-code construction — verified (proof audit +
independent reimplementation, see
[verification-comma-code.md](verification-comma-code.md)); (2) the Independent
Substitution erratum — verified and **fixed** in `main.tex` (+ the stale Lean
`#eval` comments). Fresh-Character Lemma / `L ⊴ ONCE` refutation and the restart
amplifier + no-injective-node theorem were re-verified 2026-09-19 during the
§5 promotion (verify_variants.py chunks `once`, `restart`; census re-checked in
`verify_extra.py`/`verify_extra2.py`, which found and fixed the errors listed in
item 5 above). Search-evidence statistics quoted in remarks (depth-3/4 bounded
searches, randomized 75M-pipeline sweep) are taken from the reports and
described qualitatively in the paper.

## 8. Polish pass (2026-09-19, later)

Template, rigor audit and front-matter rewrite of `main.tex`:

- **Template**: switched from `article` to **Springer LNCS (`llncs.cls` v2.26,
  `[runningheads,envcountsect]`)** — the field-standard template available in
  TeX Live. LIPIcs (the other current cs.FL standard: STACS/ICALP/DLT/WORDS)
  is NOT on CTAN and Dagstuhl's URLs were unreachable from here; swap is
  mechanical if targeting a LIPIcs venue. amsthm is incompatible with llncs's
  predefined theorem family — resolved by going fully native (llncs envs,
  `\renewenvironment{remark}` for unnumbered remarks, a patched `\endproof`
  that appends the QED box; the single `\qedhere` was dropped). 25 unused
  packages removed. Compiles clean: 37 pages, **0 overfull boxes, 0 undefined
  refs**. One cosmetic font warning (`U/stmry/b/n` — llncs+stmaryrd+hyperref
  artifact, brackets render in the only stmary shape there is).
- **Front matter**: new title ("A Theory of String Substitution over Finite
  Alphabets"), abstract + keywords, rewritten concrete introduction (worked
  enc/dec and cat examples, contributions by section, related-work
  positioning: Thue systems, Markov algorithms, monadic rewriting, rational
  transductions).
- **Rigor fixes** (from a full read-through of Sections 2-4):
  - notation block now defines Σ*, |A|, concatenation, powers, and **slices**
    S[i], S[i:j], S[:j], S[i:] (previously used but never defined); "charset"
    → "alphabet" throughout.
  - |Σ|-convention restated: Sections 2-4 assume |Σ| ≥ 2; Section 5 tracks the
    unary case explicitly.
  - **thm:rescan-agree (⇒) proof fixed**: the claim "T₂ = A[:i]·A is B-free"
    was FALSE (120 counterexamples); corrected route: the match at i consumes
    exactly the suffix of T₁ (since i+|B| = |A|+|β|), leaving work string A
    (B-free by hypothesis), so the process halts with value A[:i]·A.
  - **cor:once-sep unary case added**: over |Σ| = 1, X ↦ X^{|X|} is
    L-reachable ([X₁/σ][σ/Σ]X₁ verbatim, [σ/Σ] being the identity there) and
    killed by invariant (iv) — L ⋢ ONCE holds over every finite alphabet.
  - **Remark (total rep) CORRECTED**: the naive guard
    if(eq(X_i,ε), id, round_i) FAILS — the calculus evaluates eagerly
    (def:den), so the guarded expression still evaluates round_i's empty
    pattern. Correct construction (verified, see below): patch each renaming
    pattern to enc²(X_i)·G_i with G_i = if(eq(X_i,ε), m_{n+3}, ε) — appends
    nothing when X_i ≠ ε, an unmatchable marker when X_i = ε (round inert).
    prop:instances(iii) reworded accordingly; def:reachable extended with the
    partial-function notion.
  - **Comma Code Lemma (ii) restated**: "every occurrence of a marker is a
    whole marker" was false (a short marker occurs as a proper prefix of a
    longer one); now: every occurrence starts at a marker head and is its
    prefix — with the instantiation-pass citation updated (m_i is longest
    remaining).
  - Independent Substitution proof: A = ε trivial case split added; the
    X-choice in the induction restated as the leftmost occurrence (C ⊄ X was
    too weak).
  - head/tail theorem statement fixed (tail(aS)=ε if aS=ε was malformed →
    tail(ε)=ε, tail(aS)=S); named "Head and Tail".
  - Double Substitution proof: dropped the false "(it is shorter than Y)"
    (X = Y is legal); now argues the scan never re-enters the inserted copy.
  - "Elimitation" typos, dead commented-out theorem block, ~15 grammar /
    transition fixes.
- **New verification**: `verify_total_rep.py` — the guarded-pattern total rep
  variant (above): 317,855 evaluations over |Σ| = 2 and 3 (rule sets n ≤ 3
  with ≥ 1 empty pattern, patterns ≤ 1, inputs ≤ 4), 0 failures against the
  skip-empty-patterns semantics.

## 9. Citations, Related Work, Conclusion (2026-09-19, evening)

- **Structure added**: `\subsection{Related Work}` closing the Introduction
  (4 run-in paragraphs: string rewriting / what is not covered / codes &
  transductions & stringology / growth of one-rule systems), a short
  `\section{Conclusion}`, and a 24-entry `references.bib` built with
  `splncs04`. Paper now 40 pages, 0 overfulls, 0 undefined refs, all 24
  entries cited.
- **Every entry verified online** before inclusion (DBLP blocked; used
  Springer meta tags, NASA NTRS, zbMATH, Cornell Nuprl bib, publisher pages).
  Notable exact data: Geser one-pair-of-overlaps = RTA 2003, LNCS 2706,
  pp. 410–423 (Springer's own recommended citation; the "p. 439" floating
  around search engines is wrong); Moczydłowski–Geser = RTA 2005, LNCS
  3467, pp. 338–352 (Nuprl bib GM05); Matiyasevich–Sénizergues = TCS
  330(1):145–169, 2005 (3-rule undecidability); McNaughton inhibitor = JAR
  26(4):409–431, 2001; Sénizergues RTA-96 = LNCS 1103, pp. 302–316.
- **FABRICATED REFERENCE AVOIDED**: the recent arXiv survey 2608.19397
  cites "Geser, Hofbauer, Waldmann, *The Termination Problem for One-Rule
  Leftmost String Rewriting is Decidable*, J. Symbolic Computation 38(5):
  1387–1411, 2004, DOI 10.1016/j.jsc.2004.06.002". The DOI resolves to an
  unrelated paper; no index (Springer, zbMATH, search engines, Waldmann's
  own one-rule bibliography) knows the title; GHW's real joint work is
  match-boundedness. Do NOT cite it; the claim "one-rule leftmost
  termination is decidable" rests on it and must be treated as
  unverified. Our open problem 5 (leftmost decidability) stays open as
  written.
- **New computation** (`$CLAUDE_JOB_DIR/tmp/leftmost_vs_general.py`): on
  all 930 binary rules |A|,|B| ≤ 4, rules diverging under the leftmost
  strategy = rules admitting ANY infinite derivation (closure computation,
  inputs ≤ 7; finite acyclic closure is an exact termination certificate
  by König's lemma). Also confirms (i)/(ii) hold unrestrictedly. This
  went into thm:termination's proof: "on this domain the strategy
  restriction costs nothing". The (i)–(iv) proofs were noted
  strategy-independent in the proof text (the weight argument is
  position-free), so the classical classification for |A| ≤ |B| falls out.
- **thm:termination(v) reworded**: the old "the problem embeds the
  one-rule semi-Thue termination problem" is now the precise "this is the
  termination problem for the single rule B→A under the leftmost strategy;
  its unrestricted-strategy form is a long-standing open problem,
  undecidable already for systems with three rules" + citations.
- **Other citation points**: borders/periodicity → Lothaire, Fine–Wilf;
  comma code = uniform prefix code → Berstel–Perrin (note: enc = [xb/b] is
  NOT a prefix code — x is a prefix of xb — only the length-2 comma code
  is; cite codes only there); thm:fp & thm:subsequential → KMP, Aho–Corasick,
  Berstel, Elgot–Mezei; §4 remark → Markov, Post, Book–Otto; cor:towers →
  both tower nodes are rules of the Zantema–Geser family 0^p1^q→1^r0^s
  (ab→baa and aa→ab both fit after renaming); §5.6 items 5–6 → the
  decidable-class cluster + Kurth's census tradition + Kobayashi et al.
  derivational complexity.

## 10. Recursion stage launched (2026-09-19, night)

Research program: recursive definitions over raw L (named first-order defs, call
nodes, macro-style as in meow), under eager vs lazy runtime semantics. Four
agents spawned (scratch: research/scratch/rec/{eager,lazy_args,lazy_pass,streams}):

- **eager** — conjecture: VACUITY. All L constructors are strict in all
  sub-expressions, so every call node in a body is evaluated on every
  invocation; the call tree is syntax-determined, any call-graph cycle makes it
  infinite (König), strictness propagates undefinedness to the root ⇒ every
  recursive definition diverges on every input ⇒ eager recursive L denotes
  exactly L's partial functions (plus ⊥). Nothing gained.
- **lazy_args** — conjecture: also inert, differently. Call-by-need arguments,
  strict constructors: a thunk is forced iff the parameter is live in the
  callee, and liveness is syntactic (transitive through call chains) ⇒
  termination is input-independent (all inputs or none), well-founded
  unfoldings prune+β back to plain L expressions ⇒ same class. Operational
  eager/lazy separation exists (dead-argument programs) but no denotational gain.
- **lazy_pass** — the payoff direction. Make the one operator-level
  non-strictness official: [R/P]E forces R only if P occurs in ⟦E⟧ (matches
  [A/B]S = S when B ⊄ S regardless of A). The replacement slot is the ONLY
  place a recursive call can be guarded (L's if splices both branches into a
  strict scrutinee, so it cannot guard). Conjectures: pattern-gated guarded
  recursion; universality (exactly the partial computable functions over Σ*,
  |Σ|≥2, self-recursion sufficing); consequences: rev computable (kills hinge
  2), X↦X^{2^{|X|}} computable (kills the §4 unreachable function), towers of
  growth for total defs, totality undecidable. Interpreter verification required.
- **streams** — coinductive lazy direction: infinite strings, passes as causal
  streaming processes (thm:subsequential's machine), productivity instead of
  termination, guardedness conditions, variable patterns on streams,
  conservativity over lazy_pass on finite strings.

Agents instructed: one problem per round, bounded turns (<128K output tokens,
<30 min thinking per turn), own scratch dirs, no edits to main.tex/Subst.lean.
Plan: collect reports, verify, then write the paper section (and only then
consider Lean formalization of the chosen semantics).

## 11. Lean: repC2_correct complete (2026-09-19, night)

The long-running Lean agent finished: `repC2_correct` (the paper's Multiple
Substitution theorem, unrestricted patterns) is fully proven in
lean/Subst.lean — 0 errors, 0 sorries, 0 warnings, all 36 #eval outputs
match. Independently re-verified by the coordinator (fresh
`lake env lean Subst.lean`: exit 0; grep: 0 `sorry`, 0 `axiom`/`native_decide`;
theorem statement byte-identical to git HEAD, only `:= sorry` → `:= by`).
Proof architecture: phase-locking via renLoop/insLoop over marked rounds
(markRounds/assemble), enc2/dec2 code layer, dec2Pass_enc2 finish; S = []
split. Header status comment updated (was stale: claimed the theorem unproven).
Section 2 of the paper is now fully machine-checked.

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

## 12. Recursion stage: eager + lazy_args COMPLETE (2026-09-19, late)

Both vacuity agents finished; suites independently re-run by the coordinator
(eager: 31,995 checks 0 failed; lazy_args: checks.py rerun byte-identical to
the agent's log, ALL CHECKS PASSED).

### eager (research/scratch/rec/eager/) — recursion is inert
- **Theorem G**: L_rec = L exactly, over every finite nonempty alphabet
  (incl. unary). LFP semantics (Φ monotone + continuous), operational
  trichotomy Halt/Err/Div with agreement theorem.
- Refinements over the conjecture: (i) the vacuous class is everything that
  can REACH a call-graph cycle, not just cycle members; (ii) "diverges" must
  read "never returns" (error-or-divergence, order-dependent which);
  (iii) my König sketch had a gap — the call tree is NOT syntax-determined
  (children need defined argument values; sibling errors preempt). König
  belongs to the converse (Div ⇒ j ∈ C via infinite path + pigeonhole).
- Acyclic never diverges (halt or error); "fails on all inputs" decidable in
  linear time (j ∈ C); stabilization bound φⁿ = lfp for n ≥ max D(j)+1.

### lazy_args (research/scratch/rec/lazy_args/) — inert, differently
- Liveness = LEAST fixpoint μF (greatest is wrong: f(x)=g(x), g(y)=f(y));
  polytime computable. Theorems: Confinement (forced ⊆ S*), Full Visitation,
  Adequacy (⟦M⟧ = ⟦E′⟧, ε-pattern partiality data-dependent as in L),
  class = exactly L's partial functions (all PTIME).
- Termination input-independent and polytime-decidable (live dependency
  graph acyclicity). 253-program corpus, 13,141 halting runs, 0 mismatches.
- Minimal operational separations (exhaustive search, 68,101 programs):
  size 4 (0-ary), size 6, size 7 = the dead-argument identity; Lemma 8.1:
  no 1-function strong separation. Hand-off note §8.5 for lazy_pass: under
  operator-level non-strictness everything becomes data-dependent
  (F(X)=[F(X)/b]X terminates exactly on b-free inputs).

### PAPER BUG found by the eager agent (P10) and FIXED in main.tex
- **Lemma β (§3) was FALSE as stated**: "both sides being undefined
  together" fails when some X_i does not occur in E and ⟦F_i⟧(T⃗) is
  undefined (E = W: LHS defined, RHS not). Naive β-inlining is call-by-name
  flavored; eager call nodes are strict in ALL arguments (dead ones too).
- Fix: β now states the equation for defined RHS + a strictness clause
  (undefinedness propagates exactly for OCCURRING variables), proof redone.
- cor:closure's proof now uses def:reachable's restriction clause
  explicitly; exact-composition witness added as a parenthetical (identity
  passes [E_hi·σ/E_hi·σ] force discarded arguments, by Identity Substitution).
- meow remark updated (expansion value-preserving; the gap is macro
  laziness). Rebuilt: 41 pages, 0 overfulls, 0 undefined.

## 13. Recursion stage: lazy_pass COMPLETE — TURING-COMPLETE (2026-09-19, late)

All four rounds re-run fresh by the coordinator: fails=0 everywhere.
REPORT.md (943 lines) in research/scratch/rec/lazy_pass/.

- **T4 (universality)**: lazy-pass recursive L computes exactly the PARTIAL
  COMPUTABLE functions (Sigma*)^n -> Sigma*, already over Sigma = {a,b}.
  Injective tally coding V (Horner + sentinel), DIGITS inverse via the raw-L
  halving pipeline [a/b][eps/a][b/aa], Minsky 2CM compiler into gated
  definitions, f = DIGITS(RUN(INIT(V(X)))). Executed: mu-sqrt (15 squares
  exact, 5 non-squares no-value), doubling + adder 2CMs.
  **Self-recursion suffices** (stratified; mutual recursion definable from
  self via tagged pairs — even/odd verified).
- **Finding D (headline)**: the paper's own §2 Selection
  if(C,X,Y)=dec([enc(Y)/bb]([enc(X)/TOP][bb/BOT]C)) puts the branches ONLY in
  replacement slots — so under lazy-pass **the paper's if is already a
  two-way pattern gate**: only the taken branch is ever forced
  (if(TOP,X,Omega)=X). Reversal runs through if alone, no gate machinery:
  revif(X)=if(isne X, cat(revif(tail X), head X), eps) — all 127 strings
  of length <= 6. This is the minimal repair of rem:total-rep's eager-if
  pain: the guarded rep can be written NAIVELY under lazy-pass.
- **Naive one-way gate UNSOUND** (D2 witness diverges on eps): the
  closed-gate base value may contain the gate pattern. The two-way gate
  sel (P=bbx, Q=xbb constant gate values, enc^2 transport) avoids it;
  Corollary: verbatim branch return (dec2.enc2 = id).
- **T5**: EXP(X)=X^{2^{|X|}} total recursive (exact on all 31 strings
  |X|<=4). §4's length/degree machinery dies: recursion is not a pipeline.
- **T9**: TWR a TOTAL definition with tower growth (4,6,14,254 by |S|,
  K_{n+1}=2^{K_n/2+1}-2; K_4=2^128-2), built from gated while-loop
  versions of the paper's own amplifier rules — AMP1/AMP2 cross-checked
  against restart() on 80 strings, BLOCK vs the cor:towers formula.
  Totality does not save the polynomial bound.
- **T8**: totality of a definition undecidable [SKETCH via 2CM compiler].
- T1 conservative extension (5475/5475 eager-defined agreement, 325
  strict extensions); small≡big-step equivalence on 400 random programs.

Landscape now settled on three of four semantics: eager = L (inert),
lazy-args = L (inert), lazy-pass = partial computable (universal).
Streams agent still running. Next: draft the paper's recursion section.

## 14. Recursion stage COMPLETE — all four semantics + §6 drafted (2026-09-19, night)

All suites re-run fresh by the coordinator (verify1/2/3.py etc.): ALL OK.
Streams REPORT.md in research/scratch/rec/streams/.

- **Streams (F1 fragment: one unary def, constants, cat, constant-pattern
  passes; coinductive values, causal pass = thm:subsequential process)**:
  - T1 adequacy machine iff Kleene least fixpoint (21/21 zoo); B1: 300
    random non-recursive exprs vs paper sub() composition, 0 mismatches.
  - **No syntactic guardedness** — semantic only. e(W) = pre-pull emission:
    T3 deadlock e(W)=eps => stall, no output (300/300); T4(a) |R|>=|P| ^
    |W|>=|P| => live (proved, length growth); T4(c) |P|=1 ^ e!=eps =>
    live (relay); T4(b) fresh char in e(W) outside alphabet(P) => live
    (560/560, flow proof only sketched). Refutations: deletion eats the
    junction buffer ([eps/ab](X.f(X)) on aab stalls after 'a'); geometric
    decay |R|<|P| (76 stall configs in the region); fresh-char-in-R alone
    fails (4 counterexamples). Grid 1890 configs, 0 violations.
  - **Least vs productive**: W=bab,P=bab,R=b: b^omega is a fixpoint but
    the LEAST is the partial 'b|' — semantics selects least, machine
    stalls. Guardedness must guarantee productivity OF THE LEAST.
  - **C2 beyond finite state**: f(X)=X.b.f(X.X) on a emits a b aa b aaaa
    b a^8 b... (non-ultimately-periodic, pigeonhole vs finite-state
    emitters; counter f(X)=X.b.f(X.a) same with linear runs). LIVE to 40+
    chars.
  - T5 replacement-slot trichotomy f(X)=[f(X)/a]X: no match => TERM
    scrutinee; first char => STALL; later => LIVE s^omega. T6 forcing
    frontier <= l+1 (l = longest pattern prefix occurring as a factor);
    infinite patterns never complete a match. T7 finite conservativity vs
    flat lazy-pass (146 + 120 programs, TERM/completed-LIVE agree, flat
    bottom splits stall/live).
- **Paper §6 "Recursive Definitions" DRAFTED** (main.tex, now 49 pages,
  0 overfull, 0 undefined): setup + def:recprog + 4 runtimes; 6.1 eager
  (thm:eager) + lazy-args (thm:lazyargs) inertness with the separation
  example (68,101 two-def programs size<=7, no 1-def separation); 6.2 lazy
  passes: prop:lpcons conservativity, def:gate sel (p=bbx,q=xbb),
  thm:gate, rem:ifgate (if was already a gate; rev; rem:total-rep naive
  guard now sound), ex:naivegate, thm:universal (Minsky 2CM, minsky67
  added to bib), cor:barriers (reversal, EXP, TWR towers K4=2^128-2,
  totality undecidable); 6.3 streams: prop:streamadeq, thm:guardedness,
  rem:leastfix, thm:beyondfinite, T5/T6 paragraph; 6.4 landscape table +
  4 open problems (borderline non-strictness, stream boundary O1,
  structural-recursion-only fragment, gates per variant — once-if splices
  branches into the scrutinee so is NOT a gate).
- Also: abstract + intro paragraph + §4/§5.6 reversal pointers + Related
  Work border sentence + Conclusion (now §7) extended.

FINAL LANDSCAPE: eager = L (inert); lazy args = L (inert, operationally
separated); lazy passes = partial computable (universal); streams =
beyond every finite-state emitter (characterization open). The whole
distance rides on one clause: [A/B]S = S when B not< S, regardless of A.

## 15. Prior-art stage COMPLETE — novelty confirmed (2026-09-21)

Agent: research/scratch/priorart/REPORT.md (4 rounds, 38 verification
entries). All citations below independently re-verified by the
coordinator (WebFetch/curl/search) before entering the paper.

VERDICT: Theorem 6.4 (lazy-pass recursion = exactly the partial computable
functions, over the single never-rescanning fixed-string pass) is NOT
proved or stated anywhere findable. Inertness (Thms 6.1-6.2) is new —
nothing similar exists anywhere. Closest relatives:
- Markov normal algorithms: exact characterization but iterate-to-NF
  (already cited, markov54).
- Rust macro_rules!: genuine tag-system proof with halt-equivalence
  (TLBORM, community book) — but token trees, rescan, no laziness rule,
  no inertness.
- Wehar's informal note: Sub(u,v,x) single sweep + assignment + universal
  program => TC — the nearest statement in spirit; already uses the
  occurrence-inertness equation as its if. Cited (wehar).
- /// esolang: repeated substitution on own text; TC via Johansen's BCT
  interpreter (2009). Cited (slashes, Swett 2006).
- C preprocessor: NO proof exists, only demonstrations (BF interpreter).
  Blue paint ("unavailable" bit) blocks self-reference; Fultz deferred
  expansion = the unformalized cousin of our lazy-pass clause; Mazières
  2021: "the real limit is how much time and memory we have for cpp, not
  the fact that cpp isn't turing complete". Cited (mazieres21).
- C++ templates (Veldhuizen 1995, proof sketch, "absence of formal
  semantics makes rigorous proof unlikely"). Cited (veldhuizen95tc).
- Huet-Levy 1979 (INRIA RR 359): our lazy-pass rule = a neededness
  criterion, never before instantiated for string substitution.
  Cited (huetlevy79).
- sed: TC via labels/branches, not s alone (Blaess turing.sed via
  Krumins). Cited (krumins-sed).
- Streams: Endrullis-Grabmayer-Hendriks-Isihara-Klop, "Productivity of
  Stream Definitions", TCS 411(4-5):765-782, 2010 — close prior art for
  §6.3 not previously cited. Cited (endrullis10).
- Alur-Cerny FSTTCS 2010 SSTs — the finite-state boundary our recursion
  escapes. Cited (alur10).

PAPER EDITS (coordinator): new Related Work paragraph "Substitution-based
programming" (11 new bib entries, all coordinator-verified online:
kernighan77m4, knuth84, veldhuizen95tc, tlborm, mazieres21, krumins-sed,
slashes, wehar, huetlevy79, alur10, endrullis10); SST sentence appended to
the transductions paragraph; productivity-analogue sentence appended to
§6.3's opening. Build: 50 pages, 0 overfull, 0 undefined. Bib 25 -> 36.
Not cited (unverifiable/incomplete): fischer68 (dropped, out of scope),
garrido06, sijtsma89, coquand94, Finch blue-paint post, Retina TC proof.
Collision check: "meow" collides only at name level (esolangs has five
unrelated Meow languages); nothing substitution-based.

## 16. last/init IN L + L+R and design-space stages launched (2026-09-21, later)

USER QUESTION: is last(X) reachable in plain L? ANSWER: YES — proved and
machine-verified by the coordinator on the spot (no agent needed):
- Construction (now Proposition prop:last, end of §2): T = enc²_x(X)·bb.
  The anchor bb never occurs in an enc²-image (Comma Code (ii)), so for
  each σ the CONSTANT pattern P_σ = xσbb occurs only at the junction, iff
  last(X)=σ. Occurrence of a constant is testable (eq of [c/P]T vs T);
  deleting the matching P_σ + dec² = init (drop last char). So
  last, init, rotate-right (cat(last,init)) ∈ L, all total. (Also
  swap-first-last = cat(last, tail(init), head) ∈ L.)
- Verified: research/scratch/… verify_last.py (in job tmp): 511 strings
  over {a,b} len ≤ 8, 1533 evaluations, 0 fails.
- CONSEQUENCE FOR THE REV HINGE: reading/editing the right end is NOT
  the obstruction — bounded anchored surgery is in L. Any rev ∉ L
  invariant must hold for last (output[0] = w[n-1]!) and init. Paper: prop
  added at end of §2; §4 open-problem-2 and §5.6 hinge-2 pointers now say
  "the question is whether the bounded calculus can REORDER, not read".
  Build 50pp, 0 overfull. The rev agent was messaged with the finding
  (positive controls for invariant testing + anchor trick as synthesis
  seed).

TWO NEW STAGES LAUNCHED (user request):
- L+R agent (research/scratch/lr/): the union calculus, L-passes and
  R-passes mixed, no recursion. Key texture: R-fns = rev∘f∘rev exactly;
  rev ∈ L ⟹ L+R = L; L+R ⊋ L ⟹ rev ∉ L; a mixed rev witness ⟹ (rev ∈ L
  or L+R ⊋ L) — either way new. Questions: mixed rev witness hunt (CEGIS
  over mixed pipelines), collapse-vs-strictness, commutation/normal forms
  for mixed pipelines (r2l-agree = unbordered case), what R is natively
  good at beyond L, place in the web.
- Systems/design-space agent (research/scratch/systems/): everything
  beyond one-at-a-time §5 and §6 recursion, EXCLUDING L+R and the
  is-rev-in-L problem. Candidates: pairwise variant combinations
  (once+restart, rescan+once, positional+restart...), new axes (anchored
  passes [A/^B],[A/B$] — connected to the anchor trick; k-th occurrence
  [A/B]_k (k=1 is once); wildcard patterns; native multi-pattern passes),
  inward fragments of L (delete-only, single-char patterns,
  length-preserving), the flat lazy-pass calculus (no recursion, §6
  conservativity ⟹ L + more-definedness — characterize it). Standard
  battery per system; final design-space map + which deserve a paper
  section.

TWO MORE STAGES LAUNCHED (user request, same day):
- lim agent (research/scratch/lim/): the user's lim operator — iterate a
  unary L-expression E from the input until the orbit reaches an exact
  fixed point E(w) = w, undefined otherwise; no recursion; nested lim
  nodes allowed. Distinct from the paper's restart variant (which
  iterates a single pass and stops at the first B-free string): lim(pass)
  = restart exactly (fixed points of a pass = B-free strings), so lim
  strictly generalizes the restart row, and the iterand can BRANCH
  (if/eq inside) — that is the new power source. Seeded conjecture:
  L+lim = partial computable via a FLAT-L 2CM step (fixed instruction
  template with the current instruction marker-wrapped, marker-delimited
  counters, constant-pattern dispatch/increment/decrement/zero-test; halt
  config = unique fixed point). Also: iteration hierarchy (where does
  universality kick in), convergence/totality undecidability, ω-limit
  reading as a second-stage extension (connects to §6.3 streams).
- ONCE agent (research/scratch/once/): hinge 1 — is the once-primitive
  L-reachable? Probe: "delete the leftmost b" ([eps/b]_1) in L. Seeded
  routes: shadowing as first-occurrence selector (leftmost-first greedy
  freezing shadows overlapping later occurrences — a built-in leftmost
  selector), mark-then-discriminate with rep_n rounds (leftmost-ness is
  locally checkable: no mark to the left), escalate the paper's failed
  searches, and the invariant hunt under the known constraints (not
  unary-domain, not subsequentiality — delete-leftmost-b is itself
  left-subsequential, not growth, not piece-count). Coordination: systems
  agent owns L_k (k>=2) ladder; rev agent owns hinge 2; no known
  implication between the two hinges.

ALSO (coordinator, this day): Corollary Inclusion Symmetry (cor:incl-symmetry
in main.tex): R ⊑ L iff L ⊑ R — the two inclusion questions are one, by
mirror algebra on thm:conjugation (R-class = m-image of L-class; mirroring
an inclusion flips it). Landscape note updated: the right-to-left row's two
open cells are one question. Build clean, 51 pages. R2 of the systems agent
verified by me (battery reproduces; measure lemma statement gap caught and
fixed: needs the MIRRORED split condition too — counterexample mu =
ends-with-a; all machine checks remain valid since the 8 tested measures
satisfy both directions; placement corollary survives).

L+R ARC COMPLETE AND INTEGRATED (four rounds, all verified by coordinator):
- R1: Collapse Criterion (L+R = L iff R<=L iff rho in L; rho = the R-pass as a
  3-ary function); minimal scan-direction witness (d,c^2,c^3) unique up to
  renaming; prop:r2l-agree sharpened to biconditional (agree iff unbordered).
- R2: Disjoint Commutation Lemma (alphabet-disjoint passes commute, every
  clause necessary; deletion-merging counterexample acb); one-alternation
  normal form refuted (156 tables need >=2 alternations; 4 sibling survivors
  robust against all two-block searches); thm:core transfers.
- R3: all witness hunts negative (rho: 1,841,923 tables + 300K randomized;
  [A/aa]^R: 592,447 + 1,574,748 + 74,525; rev in L+R: exhaustive + 400K +
  genetic 400x400 to depth 11 plateauing at the palindrome points 13/31);
  residue-routing obstruction analysis (R leaves run residues at run fronts,
  L computes them only at run ends); scope honest: pipeline templates only,
  DAG/junction-pattern expressions remain unexcluded.
- R4: COMPLETE two-block impossibility over the 4 cross-letter halvings
  (closures saturate: pure 15 tables, composites 69, the 4 siblings outside
  at ANY depth; 4 of 64 three-pass words are not two-blocks); Orientation
  Lemma (produced-block/residue order flips between directions); growth
  transfers; five invariant operationalizations all falsified output-shaped
  (the strongest, first-difference offset, falls only to input-computed
  patterns = the rep escape hatch) => the separation must be
  dependence-structural; bookkeeping reconciled (S1 = 156 passes).
- Paper: new section 5.6 "Both Directions at Once" (thm:union-collapse,
  lem:disjoint-comm, prop:no-2block, lem:orientation, conj:union with the
  fourfold evidence paragraph); prop:r2l-agree upgraded to the biconditional
  + rem:minwitness; landscape union row (three open cells in the r2l and
  union rows are ONE question); abstract/intro/conclusion clauses. 53 pages,
  0 errors, 0 overfull, no undefined refs. Files: research/scratch/lr/
  (REPORT.md sections 3,5,8,10-12; lrcore.py; verify_r1/r2/r4.py;
  search_r3.py; pilot_collapse.py).
- Standing cross-agent thread: the shared obstruction (junction-local
  bounded left-context / right-to-left flow of unbounded info) is confirmed
  from both the once side (tie obstruction, P = takeWhile) and the L+R side
  (residue routing, v5 boundary through computed needles); rev agent's
  conjectures A/B/C are reordering-specific (predicted NOT to separate P).

## Session 6 (continued): rev round 4 verified + integrated; lim R1 battery green

- rev agent round 4 (rev ∉ L program) -- ALL claims reproduced under my
  own runs (verify_round4_hinges.py, verify_round4_ladder.py,
  search_shaving.py; then my supplementary verify_round4_extra.py):
  * CROSS-HINGE: P = takeWhile≠b and f2 = [b/aa]^R both have χ = 0 on
    every binary input ≤ 12 (8,191 each) and prov width 1 at mult 1 --
    the A/B/C invariant family is rev-SPECIFIC; a crossing-count proof
    of rev ∉ L cannot double for either sibling (once / direction).
  * LADDER: revlast_k = cat(last∘init^j, init^k) built (320/2,498/
    17,689/123,971 nodes), exact on all binary inputs (≤10 for k≤2,
    ≤8 for k≤4); crossings at n=14 worst-of-56: 13/25/36/46, matching
    the closed form χ = k(n−k)+C(k,2) = C(n,2)−C(n−k,2); rev = 91.
    Barriers machine-checked: content-relabeling (canonical consistent
    labeling width ≤ #classes; brute-forced optimal ≤ 6) and faking
    (anchored rungs rebuild from constants: provLDS 0).
  * SHAVING v2 (the Conjecture-B piece): a copy's residual is a function
    of (entry offset, |B|−1 following chars) → ≤ |B|·|Σ|^{|B|−1}
    distinct residuals; verified as a function property + count bound,
    3,000 trials, 0 failures (v1 refuted: 318 same-offset trials).
    Constant-pattern case closed (prov LDS ≤ 1 outright); the remaining
    gap to B is exactly variable patterns -- same boundary as
    thm:subsequential. Genetic + hand attacks top out at LDS@mult1 = 2.
  * MY SUPPLEMENTARY (verify_round4_extra.py): rotR_k built for k ≤ 4,
    exact, crossings = k(n−k) exactly; cat(X,X) crossings 0 (all rows
    doubletons); 1,000 random pipelines at n=12: max χ = 3, top-5 flat
    at n=8..14. CAUGHT: swapfl expression duplicates on |w| ≤ 1 (last
    = head); exact on all 4,092 strings of lengths 2..11 -- the remark
    states the |w| ≥ 2 domain.
- PAPER: Remark rem:price "The Price of Reordering" in The Landscape
  (§5.7), right after the two-ropes enumerate: χ_f defined from flip
  influence, the ladder table (init/last/rotR/swap-fl/revlast_k/rev with
  closed forms), the c(E)·|w| suggestion with the full verification
  parenthetical, three delimitations recast without the provenance
  formalism (pair counts die on cat(X,X); content relabeling; tracing
  fakeable), and the rev-specificity paragraph (three obstructions:
  unbounded reordering / left-anchored region deletion / residue
  routing). Forward pointers added in §5.3 (direction) and the
  conclusion. 55 pages, 0 errors, 0 overfull, no undefined refs.
- lim R1 battery (verify_r1.py) ALL GREEN under my run: 65,788 checks,
  0 failures; 166 census agreement; 3,306 value mismatches / 290 verdict
  mismatches on exactly [baab/aba],[abba/bab]; unbordered-B slow-agree
  classification (17 raw → 0 true); towers carry through lim (t=3
  output length 65,556 = b^22·a^65,534). The script's stale "paper says
  170" note is now moot (paper fixed).

## Session 6 (continued): once arc COMPLETE + integrated (prop:del-leftmost)

- once agent final arc (R1-R4) -- the positive claim re-verified by me
  THREE ways: (a) my corrected independent inline check (W and guarded
  del1b, 2,047 strings <= 10 + 20,000 random <= 49, 0 failures -- my
  first attempt had two reference bugs of my own: a looping rep1b and
  an empty-string no-b case, caught and fixed); (b) my re-run of
  verify_r3.py (4095 + 400,000 random; AST-level 2047 + 20,000; del1b
  511 + 3,000; parity account 8 shapes; ternary lift 2,256/3,280 --
  all green); (c) the earlier session checks. W = [a/ab][ab/aa][b/ba]
  [ab/b][aa/a] = [a/b]_1 exactly; del1b = if(contains b, tail(W), X).
  Mechanism hand-re-verified by me on the stage table (gap arithmetic:
  2g+1 unique-odd pre-b gap; [aa->ab] pairing leaves the residue at
  the junction; [ab->a] consumes residue+b).
- PAPER INTEGRATED: prop:del-leftmost (The Leftmost Deletion, over Two
  Letters) in 5.1 with the gap-parity proof + verification note; the
  mirror remark gains the conjugation corollary (rightmost deletion
  R-reachable over binary) and its central-problem paragraph REWRITTEN
  (old searches explained: witness needs depth 5, random search
  sampled 0.08%; closest misses = the junction; what remains: constant
  needle over |Sigma|>=3 with the homogeneity obstruction, computed
  needle over every alphabet); Landscape rope 1 updated; conclusion
  once-clause updated; price remark's third obstruction relabeled
  "the computed needle". 56 pages, 0 errors, 0 overfull.
- Ternary boundary (agent's R4, search-negative, recorded not
  integrated): parity cascade vs fresh-block-encoding have
  COMPLEMENTARY alphabet requirements; every repair scheme re-creates
  first-site selection; W fails 2,256/3,280 abc-strings <= 7, 3,402/
  5,461 abcd <= 6. R5 lead if resumed: anchored needle (P => D,
  verified over ternary) reduces the lift to the prefix-tally/P
  question; first-b index preserved by pi = [eps/c]X.
- design-space: verify_r3c GREEN under my run (rank-1 == rank-0
  collapse: 146/12/4 identical; amplifier rank-1 lens [2,5,10,19,36,
  69,134,263] vs rank-0 doubling; rank-2 cures fail at length 24;
  rank-1 robustness 0 flagged). verify_r3.py timed out at 900s on the
  first attempt (exit 124, output lost to buffering) -- re-running
  unbuffered at 5400s.

## Session 6 (continued): rev round 5 verified (proof fragment); systems D-battery green

- rev round 5 (the user-directed rev-not-in-L proof attempt, first round):
  verified by me, ALL GREEN — but the crux had NO verification code
  (verify_round5_phases.py covers parts 1-4 only; the 1.15M-text
  Left-Move run was unreproducible). I wrote verify_round5_leftmove.py
  myself: 1,152,480 texts, max strictly-decreasing position chain
  through pairwise-disjoint residuals = EXACTLY 2, no chain of 3
  anywhere; 40,000 random (|A|<=7, |B|<=6, 6 copies): max 2. Bookkeeping
  note: my qualifying-text count 23,368 ("any pair disjoint") vs their
  4,730 (likely "all disjoint") — check is a superset, a fortiori.
  Round 5 substance: Lemma Phases (residual = f(entry straddle o, exit
  straddle j), #(1+|O|)(1+|J|)+1 — overlap sets, superseding |B|*s^|B-1|
  (3 <= 4 vs 12 on the validated construction)); Lemma Overlap-
  Periodicity (border-chain structure; AP phases => repetition; density
  bound FALSE: A=aabaabaa, B=xaabaa, O={1,2,5}, p=3); Left-Move Wall
  (verified fact, proof open); Base Case Proposition LDS <= 2*LDS
  (prov_A)+1 for [A/sigma][eps/B] at mult 1 (205,585 instances; max 1
  constant A, 3 = 1+2*2 variable). Full-proof gap list: faking caveat
  (both routes needed), prove the wall, value recursion at intermediate
  multiplicity, multi-pass composition. NOT integrated (fragment in
  research record; holds until the wall is proved or arc ceiling).
  Round 6 resumed: prove the wall, value recursion, LINE 2 crossings.
- systems R3 now FULLY verified: my verify_r3d.py (occ_fast
  equivalence-proven, D1 = 8,000 rank-0 == restart agreements; D2 census
  at adequate caps (5000/8000): rank 0 = 166 = 162 + the four; rank 1 =
  166 SAME SET; rank 2 = 148 with the 18 cures exactly 16 A=B |A|=4 +
  [abba/bab],[baab/aba]; no creations) + verify_r3c green earlier +
  parts A-C green in the truncated run. Systems agent resumed for R4
  (flat lazy-pass calculus).

## Session 6 (continued): lim round 3 verified (all four steers green)

- lim R3 verified by me: verify_r3.py = 964,604 checks, 0 failures
  (occurrence census: edge lengths {0,1,2} at every pc + systematic
  0..40 + 400 random <= 1000, offsets 2/3/7 + empirical offset-1;
  the three normalization lemmas B1/B2i/B2ii with raw failures
  demonstrated; containment driver 135 conv + 29 div at BOTH toolkit
  roles + the 2CM steps themselves + selfloop diverging both sides);
  verify_r2.py re-run after the agent's mk_contains fix (mask must
  differ from pattern; R2 was immune -- all long frame patterns):
  50,744/0 unchanged. Occurrence lemma hand-checked by me (Steps 1-3
  sound: gap sequences (2;1^k-1;3), pattern gaps only {1,3,5} never
  0/2, tau-to-consecutive-tau mapping, three-step pinning).
  occurrence_lemma.tex is paper-grade.
- Round substance: the general occurrence lemma (ALL pc,x,y -- proof
  by gap calculus); fix_selfjump / swap_counters / add_cleanup as
  verified lemmas (complete normalization pipeline); lim(L) <=>
  lazy-pass recursion via the RUN driver; convergence undecidability
  (Sigma01 convergence, Pi02 totality). NEW growth finding: [aabb/ba]
  and [bbaa/ab] grow exponentially under lim sweeps (len 8 -> 204 in
  10 sweeps) -- ONE pass + one lim node doubles per iteration vs
  cor:towers needing 2t-1 nested nodes.
- R4 resumed: the paper-form assembly (variant subsection after
  "Restarting from Zero": syntax/denotation, fixed-point-set lemma,
  compilation theorem with preprocessing, occurrence lemma, partiality,
  containment, the punchline corollary flat-L+one-lim = lazy-pass
  recursion = partial computable, undecidability corollaries, growth
  proposition, landscape row).

## Session 6 (continued): systems round 4 verified (flat lazy-pass collapses into L)

- systems R4 verified by me, ALL THREE BATTERIES GREEN:
  verify_r4.py (A1 cross-check: 1,500 exprs x 15 inputs x 2 runtimes =
  0 mismatches; A2 lpcons over the FULL depth<=2 space: 599,844
  expressions x 31 inputs, eager-defined 7,242,300 points all in exact
  agreement, 10,211,456 undefined-both, 1,141,408 LAZY-ONLY
  definedness points, all with the discarded-replacement mechanism --
  undefined node inside a subtree the sweep discards; no R-slot
  mechanisms); verify_r4b.py (hand cases 4x31; TR vs the paper's own
  run_eager 25x31; ALL 193 lazy-only witnesses x 31 inputs; 250 random
  depth<=2; escalation 25 witnesses x 127 inputs |S|<=6 -- all 0
  mismatches, 0 Phi-undefinedness); verify_r4c.py (O unit test 15^2
  pairs 0 undefined / 0 wrong; 120 random depth-3 x 31 inputs 0
  mismatches; TR sizes to 31,036 nodes).
- The theorem: the flat lazy-pass calculus COLLAPSES into L as partial
  functions. TR(E) = [a/if(F(E),a,eps)]Phi(E) is an explicit eager
  pipeline with Phi([R/P]T) = [PhiR/g(PhiP)]PhiT (patterns eps-coerced
  via g(X)=if(eq(X,eps),a,X); scrutinees uncoerced), occurrence test
  O(u,v) = if(eq(u,b), [bb/b]v != v, [b/g(u)]v != v) (mask-must-differ
  trick), and the guard gate uses [a/a]=identity vs [a/eps]=undefined.
  Punchline: laziness adds DEFINEDNESS, not power -- every lazy-only
  point is a defined-elsewhere-identical node hidden inside a subtree
  the leftmost sweep discards; and the paper's S6 universality is
  genuinely a RECURSION phenomenon (the gate), not an evaluation-order
  phenomenon.
- Construction scrutiny: sound. ONE write-up bug found: REPORT S9.4's
  typeset F-formula has an antecedent-scope error -- "(F_T and F_P and
  isne) => (not-O or F_R)" as written makes eps-pattern nodes DEFINED;
  the code (verify_r4b.py: cond = and3(F(T), F(P), isne(sg, PHI(P)));
  rest = or2(notb(O(...)), F(R)); tk.if_(sg, cond, rest, K(BOT))) is
  CORRECT: F = F_T and F_P and isne and (not-O or F_R), the isne is a
  CONJUNCT. Flagged to the agent for the report fix; load-bearing for
  any paper version.
- Agent resumed for R5 (final): the two paper-ready drafts (flat-lazy
  collapse as a S6 theorem; L_k mosaic as a landscape addition), the
  final design-space map, and remaining survey rows as budget allows.
  Integration queue: this is the second S6-theorem candidate behind
  the lim arc's universality subsection.

## Session 6 (continued): systems R5 verified + lim R4 verified -- BOTH INTEGRATED; paper 67 pages

- systems R5 (final) verified by me: verify_r5.py rows 1 and 3
  (once+rescan = ONCE: 2,646/0; once+restart(node) = MARKOV: 2,646/0 --
  both by airtight arguments + machine) and verify_r5b.py for ROW 2
  CORRECTED: pass-granularity restart (iterate the full unsafe pass) is
  NOT Markov -- 9,322 agreements, 2 differences; witness [aba/bab] on
  'bbabb': pass-iter 'baaba' vs Markov 'abaab'; I hand-checked the
  witness against the paper's own def:rescan (freeze b, freeze a, T =
  aba -> 'baaba') -- CORRECT. NOTE: verify_r5.py's internal
  unsafe_pass re-implementation failed its own sanity check (46
  mismatches vs systems.rescan) and its [ba/ab] "witness" prints same;
  dead code superseded by verify_r5b. The S9.4 F-formula scoping typo
  was fixed by the agent (isne now a conjunct).
- systems R5 integration (my fixes to the drafts): (1) thm:flatlazy
  "Flat lazy passes denote L" after cor:barriers -- relabeled
  sigma/sigma_1/sigma_2 to the paper's b/x convention; juxtaposition
  for concatenation; isnе referenced from rem:ifgate; FIXED THE SIZE
  ARGUMENT (draft said "each level multiplies by a constant" = c^depth
  exponential on spines; true accounting: F adds a copy of Phi of each
  node's pattern and scrutinee -> |E^+| = O(|E|^2), a sum over nodes);
  tightened the occ verification note to "the load-bearing branch"; all
  numbers confirmed against my r4/r4b/r4c runs (the 193 are distinct
  lazy denotation tuples no depth-2 eager expression has, verified via
  smallest witnesses). (2) prop:kth "The k-th-occurrence family" after
  the eq-conjecture paragraph: fixed the test set to 63 strings
  (includes epsilon; the draft said 62); DROPPED the 688,499 claim (it
  is the ANCHORED reduced-vocab space from verify_r2.py part E, whose
  target battery never tested [a/b]_2-type functions -- the REPORT's
  8.5 verdict line conflated it in; only 969,321 and 3,773 were
  [a/b]_2-tested); softened "each [A/B]_j" to the verified instances
  ([a/b]_j diagonal + [aa/b]_2); marker-freshness stated as
  thm:pos-hinge(ii)'s hypothesis (fresh for B, A AND the input); the
  opening's "none collapses into ONCE" qualified (over |Sigma|>=3 the
  constant fragments DO collapse by marking). (3) Landscape table rows
  for L_k and lim; walking-paragraph clauses; intro/abstract/conclusion
  touch-points. Re-established verify_r3 parts A-C with visible output
  (my earlier r3 run's output was lost to the timeout): 135,136/0 + 0
  classical violations; 38,959/28,090/2,307 with the diagonal matrix;
  18,522; 969,321 + absences + depth-1 sanity; 3,773 + absences. ALL
  GREEN. Systems ARC CLOSED.
- lim R4 verified by me: verify_r4.py re-run = 364,693 checks, 0
  failures, ALL GREEN (fp-set 930x255; census <=6 114,300 pairs
  126/20/0; all draft witnesses incl. [ab/bb] on bbbb lim 'abab' vs
  restart 'aaab' -- MY hand-check initially disagreed; found MY error:
  'abbb'.find('bb') = 1, not 2, so restart goes bbbb->abbb->aabb->aaab;
  the agent's witness is correct; amplifier law on 8,391+200 inputs +
  50 traces + n<=14; towers t<=3 (65,556 at n=4); Fibonacci |s_k| =
  2F_{k+1}+2k+6 through k=28 (|s_28| = 1,028,520 = 2*514229+62 -- I
  checked against F_29 = 514,229), bbaa law +2, mirror, sort). The <=9
  census numbers (3,306/290/0) confirmed present in MY earlier
  lim_verify_r1.out run. sanity_lim.tex compiles clean under my run.
  I hand-verified V(k) arithmetic (length 2k+4, gaps (2;1^{k-1};3)),
  the half-node/amplifier closed form (v after (ab)^j = 2^{j+1}-2), the
  driver, and the undecidability reductions.
- lim R4 integration: lim_section.tex (605 lines) inserted after the
  sort remark, before "Both Directions at Once", as \subsection
  {Converging to the Fixed Point} (ssec:lim): def:lim, lem:fpsweep +
  eq:contains, prop:limtotal, rem:limstrategies, thm:lim2cm
  (construction + correctness via lem:occurrence's gap calculus),
  thm:limpartial, prop:limcontain (the RUN driver), cor:limclass (flat
  L + one lim node = lazy-pass recursion = partial computable),
  cor:limundec (Sigma01/Pi02-complete), prop:limgrowth (amplifier with
  complete potential proof; towers 2t-1 nodes), rem:fiborbit (Fibonacci
  divergent orbits, the R1 "doubling" corrected to golden-ratio growth;
  witnesses corrected to paper notation [babb/bbbb],[ab/abba],
  [baab/aba]). The draft's mini landscape table folded into the real
  table (lim row: trivially / refuted / verbatim / unbounded; I changed
  the toolkit cell "flat" -> "verbatim" to match the table's vocabulary
  and the draft's own explanation). Touch-points: the flatlazy closing
  paragraph gains the bookend sentence (the loop, with no recursion to
  unwind, is the whole of it); intro variants paragraph, abstract,
  conclusion. All cross-references verified to exist (def:markov,
  thm:termination items (i),(ii),(iii),(v) -- the paper's own proof
  states the position-independence prop:limtotal leans on; thm:
  amplifier, cor:towers, minsky67, geser01; mathpartir's mathpar).
  BUILD: 67 pages, 0 errors, 0 undefined references, 0 overfull.
- Paper now 56 -> 67 pages this session: rem:price, prop:del-leftmost,
  thm:flatlazy, prop:kth, the lim subsection, 3 new landscape rows
  (L_k, lim; once row context), and touch-points in abstract, intro,
  open problems, and conclusion. Nothing committed (user commits
  externally).

## Session 6 (continued): rev round 6 verified -- a NEGATIVE round, honestly reported; HOLD continues

- rev round 6 (the user-directed rev-not-in-L proof attempt) verified by
  me, all four batteries green under my runs:
  verify_round6_witness.py (the staircase family table: mult=3 pinned,
  LDS=j exactly, content==den every row; the B2 triple standalone;
  the staircase provs), verify_round6_conjAB.py (d=2..6 family sweep
  j=2..40 with den_ok; the mod-3 rows; the d=4 extension),
  verify_round6_mult1_sweep.py (25 constructions x 7 patterns x 6
  sigmas: NO row with mult=1 and LDS>=4; top rows all mult>=2),
  verify_round6_leftmove.py (PART A: the round-5 domain re-run, 0
  triples, 4,730 vs 23,368 = pure counting conventions; PART B1: the
  B^inf skeleton solver finds the triple deterministically; PART B2:
  300K structured randoms, histogram {0:35235, 1:258135, 2:6629, 3:1}).
- MY OWN HAND-TRACE of the headline witness settles the prov machinery:
  E2 = [eps/init^2 X][X/b]X on w=b(ab)^2='babab': inner [w/b]w gives
  T = X a X a X (17 chars, labels [0,1,2,3,4,1,0,1,2,3,4,3,0,1,2,3,4]),
  outer deletes init^2w='bab' greedily at spans 0-2,4-6,8-10,12-14,
  survivors at T-positions 3,7,11,15,16 -> prov = (3,1,3,3,4) -- the
  staircase (n-2, n-4, ..., 1, n-2, n-2, n-1), mult 3 (label 3 thrice),
  LDS 2, output 'aaaab'. Machine matches at every j. I also probed
  independently: initd(2)('babab') = 'bab' (true init^2) and
  L.den(E2)('babab') = 'aaaab' -- so the conjAB SANITY block's "INIT
  BAD" flags are label-convention artifacts exactly as the agent said
  (content correct; the family rows all content==den).
- THE RESULTS: (1) the Left-Move Wall (round 5's max-chain-2) is
  FALSE -- a small-domain artifact; refuted twice (the B2 triple:
  B='ababa', A='bababab', gaps aa,a,a,a, residuals {4},{2},{0,6},
  picks 4>2>0; and the staircase family: chains of length ~|w|/2
  through pairwise-disjoint singleton residuals). (2) HEADLINE:
  Conjecture A (LDS <= C(E)*mult) is REFUTED -- the fixed two-pass
  expression [eps/init^2 X][X/b]X on b(ab)^j has LDS=j exactly, mult=3
  exactly, j=2..40 (ratio 13.3 at j=40); init^4 gives LDS=j/2+1 at
  mult 4-5. Mechanism: the MODULAR STAIRCASE (odd-length needle from
  the same alternating stream; greedy scan emits one atom per match at
  offsets (m+pi/2)c mod (n+g), descending by constant step; boundary
  emissions contribute only the pinned constant duplications). This
  also kills the round-5 base-case DERIVATION. (3) Conjecture B
  (mult 1 => LDS <= C(E)) SURVIVES every attack (no mult-1 row with
  LDS >= 4 anywhere swept) and is now THE single live atom-route
  invariant -- rev's prov has mult exactly 1 with LDS = n. (4)
  Conjecture C: vacuous on the staircase families (they change output
  length under input flips) -- the length-discard rule is load-bearing
  wherever C is used.
- phase_leftmove_fragment.tex honestly revised: the wall struck
  through and marked REFUTED with both counterexamples; the staircase
  remark added; the base case withdrawn as a derivation and restated
  as a conjecture with its evidence. HOLD CONTINUES: nothing enters
  the paper this round (the wall fell; the atom route runs through the
  unproven mult-1 theorem). The paper's rem:price conjecture
  (chi <= c(E)|w|) is NOT affected -- the staircase's LDS is linear
  in |w|, consistent with a linear bound; different measure, different
  claim. One cosmetic for the record: the staircase's descent is
  always odd labels (n-2, n-4, ..., 1), so the fragment's "..., 2, 1"
  should read "..., 3, 1".
- Round 7 resumed: prove the mult-1 theorem (the duplication argument:
  long chain needs the staircase; the staircase's wrap and the
  end-of-text dump both duplicate labels, forcing mult >= 2).

## Session 6 (continued): rev round 7 verified -- the Phase Bound, the atom route's first theorem

- rev round 7 verified by me: verify_round7_mult1.py = ALL GREEN under
  my run. PART 1: 1,157,184 exhaustive realizable pipelines (|A|<=4
  x prov variants of LDS 1-3 x |B|<=3 x 8 sigmas x |w|<=6; 591,315 at
  mult 1): 0 violations of Theorem A(i) (#surviving copies <= phases),
  0 of A(ii+iii), 0 of the base-case conjecture; content cross-checked
  vs L.den; + 20,000 random larger (A<=8, B<=6, |w|<=10): 0/0/0.
  PART 2a: the text-level witness confirmed -- and I HAND-TRACED it:
  T = (babababab.a)^5.babababab, B = abababa: the greedy deletion eats
  spans at 1,9,17,25,33,41,49 (spacing 8), per-copy residuals {0,8},
  {6}, {4}, {2}, {0,8} -- copies 2-5 give the strictly decreasing
  chain 6>4>2>0 with distinct labels. The hunt: chains up to 6 (m=11,
  n=13, 6 copies, residuals {0,12},{10},{8},{6},{4},{2}). PART 2b:
  realizable pipeline hunt (variable needles): 0 mult-1 rows with
  LDS>=3, max 1. PART 3: E2's chi = 0 vacuously (all rows
  length-changing, discarded) -- the crossing measure does not see
  the staircase; rem:price untouched, as predicted.
- THE RESULT: PROPOSITION (Phase Bound at mult 1) PROVED: for the
  two-pass fragment [A/sigma][eps/B], at output multiplicity 1,
  LDS(prov) <= ((1+|O|)(1+|J|)+1) LDS(prov_A) + 1. Proof structure
  (I checked each step): mult 1 is used exactly once (two surviving
  copies of equal phase have identical residuals by round-5's proved
  Lemma Phase, so a nonempty shared offset forces mult >= 2 -- at most
  one surviving copy per realized phase); within a copy the picks are
  a decreasing subsequence of prov_A (text order = ascending offsets);
  gap survivors' labels strictly increase (<= 1 per chain). The
  staircase (mult 3) is exactly what the mult-1 hypothesis excludes.
- THE REFUTATION: the TEXT-level statement (2 LDS(prov_A)+1 for free
  texts) is FALSE -- deterministic chain-4 witness + chains to 6 in
  aligned alternating texts, all at mult 1. Realizability is
  load-bearing: the supply pigeonhole (an alternating A of odd length
  n needs (n+1)/2 input positions of one parity; any realizing w
  supplies only (n-1)/2 sigma-sites; a nondecreasing prov_A cannot
  bridge) -- sketched, machine-consistent, not yet proved. So any
  correct proof of the uniform bound MUST use realizability.
- REMAINING GAP: Theorem B -- mult 1 => #realized phases <= C(E)
  alone (the Phase Bound's constant is value-dependent via |O|,|J|).
  The two test cases any proof must kill: the length-6 text-level
  chain and the staircase family. The C-caveat: C's crossings live on
  length-preserving rows; [X/sigma]-style pipelines discard all rows
  (flips change output length) so C holds vacuously there; the discard
  rule is load-bearing wherever C is invoked.
- Fragment updated honestly: Proposition (Phase Bound, proved) +
  Remark (text-level refutation, realizability load-bearing) + the
  corrected staircase "..., 3, 1" + revised next-steps. HOLD CONTINUES
  (nothing enters the paper until the arc lands or hits a ceiling --
  the paper has no prov/LDS machinery yet; partial integration would
  fragment the narrative). Round 8 resumed: Theorem B via periodicity
  + supply.

## Session 6 (continued): rev round 8 verified -- Theorem B machine-complete over the hunted habitat

- rev round 8 verified by me: verify_round8_theoremB.py = ALL GREEN
  under my run. PART 1: 355,928 direct pipelines (R in {X, ten
  constant deletions, init, tail} -- all LDS(prov_A)=1, the hardest
  case for 2*1+1=3 -- x 25 needles x 4 sigma x 331 inputs), 70,212 at
  mult 1, LDS histogram {0:9108, 1:59785, 2:1319}: MAX LDS AT MULT 1
  = 2. The max instance re-verified END-TO-END BY MY OWN HAND-TRACE:
  E = [eps/tail^3 X][X/ab]X on w='baabaaba': inner [X/ab]w matches at
  positions 2 and 5, giving T = 'ba'.X.'a'.X.'a' (20 chars, labels
  [0,1, 0..7, 4, 0..7, 7]); outer deletes tail^3 w='baaba' greedily
  at spans 2-6, 8-12, 14-18; survivors at T-positions 0,1,7,13,19 ->
  prov (0,1,5,2,7), mult 1, LDS 2, output 'baaaa'. (My first two
  hand-traces were wrong -- I misread the inner match positions;
  the agent's instance is exactly right. Third trace confirmed.)
  PART 2: 60,180 chain-rich structures, 147 with disjoint-chain >= 3,
  48 pairwise-disjoint mult-1 candidates, 0 feasible embeddings (the
  realizability CSP in its most permissive form: nondecreasing
  embedding of A into w, injective on surviving offsets, avoiding
  surviving gaps, six sigma options each). PART 3: border-period
  lemma EXHAUSTIVE over all binary strings <= 11 (worst ratio 2.667,
  inequality p(t-1) <= |x|-1 holds everywhere) -- and the lemma is a
  classical Fine-Wilf consequence (all periods d <= n-p of a string
  with minimal period p are multiples of p), so the write-up can cite
  lothaire97, which the paper already cites for periodicity steps.
- THE STATE: the meeting is machine-complete over the hunted habitat.
  The chain: mult 1 + K realized phases => max(|O|,|J|) >= sqrt(K)-1
  (Lemma Phase) => A has >= sqrt(K)-1 borders at one end => that end
  of A has period <= (|A|-1)/(sqrt(K)-2) (Border-Period) -- few
  phases or periodic is now a THEOREM; and every chain-rich periodic
  candidate dies on supply (0/48), with the direct sweep never
  exceeding LDS 2 at mult 1. What remains: the WRITTEN general proof
  of the supply half for periodic-at-one-end A (the cycle/disjointness
  tension). Fragment updated with Lemma (Border-Period) + the two
  machine facts; compiles cleanly.
- HOLD CONTINUES. Round 9 resumed: formalize the supply half -- the
  cycle/disjointness tension for periodic A, leaning on the two
  machine facts (max |S| = 2 at mult 1; 0/48 lifts).

## 2026-09-21: lim agent R5 verified + integrated (paper 69 pages)

- MY BATTERY: verify_r5.py rerun from scratch, ALL GREEN -- 1,224
  checks, 0 failures. (A) freshness/branching/drift on 203,126
  convergent orbits of the 930 rules x inputs <= 7: 0 failures.
  (B) all 148 growing rules (|A|>|B|, B not-in A, |A|<=4) on inputs
  <= 9, caps 6000 sweeps/2^16 chars: law f,K,R <= (|A|-|B|+1)^n + n
  per rule holds; max fires/sweep 9; longest strictly-growing fire
  run 4 sweeps. (C) base-m family S1/S2/T1/T2 x m=1..5: 1,169 grid
  cells exact; champions at n=9 are the two-block Horner inputs
  ([baa/ab] f(9)=264=2^8+8, [baaa/ab] f(9)=6569=3^8+8). (D) the
  omega-reading: amplifier dwell 2^(v-1)+1 and k_j=2^j+j exact
  (v<=10, slack-certified at M doubled); [aa/a] non-commutation
  (finite 'a' for all 1<=n<=60 vs coinductive a^omega, window-
  verified); omega-census 1,222 stabilized / 18 churning; [eps/ab]
  erases (ab)^omega in one sweep (truncations 17/34/71).
- HAND CHECKS: S1(3) on 'ab' -> 'baaa' one sweep one fire; the m=2
  row matches prop:limgrowth's table; K = i*m^(j-1)+j-1 traced on
  (i,j)=(1,2),(2,1),(3,2); [a/aa] halving (pattern 'aa' is the
  SECOND argument) a^5 -> a^3 -> a^2 -> a confirmed by hand -- the
  remark's lim([a/aa])(a^n) = a is the halving cascade, correct.
  Branching lemma proof checked: an occurrence of B in s_{k+1}
  clear of every emission lies in surviving text, where sweep k's
  cursor would have fired on it; one emission admits <= |A|+|B|-1
  occurrence starts. Honest one-line proof -- stated inline in the
  paper with the argument as a parenthetical.
- INTEGRATED INTO PAPER (main.tex, build 69 pages, 0 errors / 0
  undefined refs / 0 overfull):
  1. Lim subsection closing UPGRADED: the open "no argument is known
     in either direction" replaced by the single-exponential
     conjecture |lim([A/B])(w)| <= (|A|-|B|+1)^{|w|}+|w| on
     convergent orbits -- with the branching bound + its proof
     parenthetical, the census numbers (9 rules -> max 9 fires/sweep,
     growing runs <= 4), the four base-m shapes (1,169 cells,
     m=1 = insertion sort), tight-in-the-base note (family attains
     m^{n-1}), the separation consequence vs cor:limclass/cor:towers,
     and the missing step (the same bound on sweeps; lem:fpsweep's
     B-free fixed points as where it must bite).
  2. rem:omega (the agent's omega_remark.tex, verbatim modulo comment
     header and cf->plain ref) placed at the end of the streams
     subsection, after the "Two further phenomena" paragraph: pointwise
     convergence of the amplifier orbit at 2^j+j sweeps per position,
     [a/aa] least-vs-greatest split compressed into one rule (the
     rem:leastfix theme), [eps/ab] erasing (ab)^omega as thm:
     guardedness's edge case.
  3. Touch-points: conclusion clause on the conjecture (base |A|-|B|+1
     exact by four shapes); conclusion sentence on the two fixpoint
     readings; intro recursion-paragraph clause (least vs greatest
     fixpoint in a single rule).
- LITERATURE: the flagged items (Kobayashi TCS 262; Geser-Hofbauer-
  Waldmann match-bounded; Kurth) are ALL already in references.bib
  (kobayashi01, geser04, kurth90/96) -- no new citations, no new
  vetting needed. The lim subsection cites kobayashi01/geser01 already.
- AGENT CORRECTIONS CARRIED: base-3 quartet cap artifact (K=2194 >
  2000 hid f(9)=6569) -- my rerun with caps 6000/2^16 confirms
  f(9)=6569=3^8+8; the R4-era "140 of 148" was the agent's sweep
  census, not the paper's restart census (no paper erratum).
- NEXT (lim arc): the missing step -- bound sweeps K by single-
  exponential under convergence -- or close the arc. Decision
  deferred to the user report; the conjecture is now stated in the
  paper, so the arc has a precise target.

## 2026-09-21: rev round 9 verified -- THEOREM B REFUTED (the period-3 family)

- MY BATTERY: both scripts rerun from scratch, green, exit 0.
  verify_round9_witness.py: the family E = [eps/tail^4 X].[tail(X)/ab]X
  on w = (bba)^k, k = 5..16 -- mult EXACTLY 1, LDS = k-1, len(prov) =
  k+3, prov = (0,1,n-3,n-6,...,3,n-2,n-1), den_ok (content vs the
  independent denotation) True on EVERY row. Probe: 1,157,184
  text-level instances -> 318 descending-bijection hits, 110 essential
  families, longest |w| = 4. verify_round9_supply.py: 581,856
  pipelines / 221,579 at mult 1 / LDS hist {0:9635, 1:210988, 2:941,
  3:11, 4:1, 5:1, 6:1, 7:1} -- the 4..7 singles ARE the period-3
  family; max (7, ('tail','tail^4','ab',(bba)^8)). Part 2: 0 of
  80,000 random periodic structures reach even the candidate stage
  (all die at chain<3 / <3 residuals) -- consistent with round 8's
  147 all coming from the aligned family. Part 3 residue check:
  4,666/5,784 constant-descent.
- MY HAND-TRACE of the k=5 witness, full: w = bbabbabbabbabba; inner
  [tail(w)/ab] fires at sites 2,5,8,11 -> T = bb.A.b.A.b.A.b.A.ba with
  A = babbabbabbabba = B.bba, B = tail^4(w) = babbabbabba (11); outer
  [eps/B] deletes greedily at T 2,14,26,38,50 (spacing |B|+1 = 12,
  each match straddling a copy boundary), survivors at T 0,1,13,25,
  37,49,61,62 -> w-labels (0,1,12,9,6,3,13,14) -- the agent's prov
  EXACTLY; all labels distinct (mult 1), LDS 4 = k-1, output
  bbbbbbba, |out| = 8 = k+3. Mechanism confirmed: one 'b' survivor per
  copy at labels descending by 3 (the 0-mod-3 class), pre (0,1) and
  post (13,14) outside the staircase.
- COSMETIC (on record, no impact): the report's "matches at spacing
  23" (k=8) and the script docstring's "spacing |B|+3" are both off by
  2 -- the verified spacing is |B|+1 (k=5: 11+1 = 12, confirmed by
  hand). The prov/LDS/mult numbers -- what the scripts actually check
  -- are exact.
- CONSEQUENCES (agent's ledger, confirmed by my runs): Conjecture A
  refuted (R6); Conjecture B / "Theorem B" refuted (R9 -- it was
  never in the paper, fragment-internal only, so no paper erratum);
  base-case conjecture (mult 1 => LDS <= 2 LDS(A)+1) refuted (here
  LDS(A) = 1, LDS = k-1); Theorem A / Phase Bound still TRUE but a
  structure theorem (one atom per realized phase), its constant
  value-dependent -- NOT a complexity bound; the (mult, LDS)-separating
  invariant route is DEAD: L realizes mult 1 with LDS linear in |w|.
- FRAGMENT state: honestly revised (basecase marked REFUTED with the
  witness; rem:period3 new; supply pigeonhole marked non-generalizing;
  "What Remains" rewritten around the two live routes). Compiles clean
  in a main.tex-preamble host (amsthm + stmaryrd; 5 pages). HOLD
  CONTINUES.
- LIVE ROUTES: (1) influence-crossing (Conjecture C) -- untouched:
  the period-3 family is length-changing (|w|=3k, |out|=k+3), the
  length-discard rule stays load-bearing; (2) NEW: the descending-
  bijection invariant -- rev's prov is a descending bijection (mult 1,
  |prov| = |w|, all labels, LDS = |prov|); the two-pass fragment
  "provably cannot" (sketch has a gap I see: it presumes copies can't
  keep 2 descending atoms -- prov_A itself descending is the loophole
  the text-level probe already closes at |w|<=6 via arbitrary
  injective labelings, longest hit |w| = 4). Round 10: tighten the
  impossibility to a real proof + probe depth 3.

## 2026-09-21: user's cat observation -- expository fix at thm:cat (paper rebuilt clean)

- THE USER'S POINT (correct): in the calculus, XY is a term, so the
  function (X,Y) -> XY is realized trivially by the expression XY;
  thm:cat is not needed for REACHABILITY, and the paper never said
  so explicitly -- a reader naturally reads the construction as
  ceremony.
- THE CONSTRUCTION IS LOAD-BEARING (three ways, now stated in the
  paper at the close of thm:cat): (1) thm:core's eliminator is
  (E1E2)-deg = cat-deg[E1-deg/X1, E2-deg/X2] -- the cat construction
  IS the eliminability of the concatenation constructor (conservative
  sugar; pure pipelines suffice); (2) the naive [X/a][Y/b](ab) fails
  under replace-all ([X/a] corrupts every a of Y; no bare marker
  choice helps, any fixed marker word occurring in some Y) -- the
  escape is the repair, and the escape engine carries rep_n/eq/if;
  (3) each variant re-earns cat under its own semantics -- the
  once-calculus's [X/a]_1[Y/b]_1(ab) needs no escape at all
  (leftmost-only fires at the marker, never inside Y), a sharp probe
  of what replace-all costs.
- EDIT: the paragraph after thm:cat's proof ("Concatenation of
  arbitrary strings is therefore itself a substitution expression...")
  now says the trivial term realization explicitly, names thm:cat's
  content as core-expressibility, records the naive failure + why no
  bare marker repairs it, and points to thm:core and
  thm:once-toolkit(i). Abstract unchanged (its cat display is the
  primitive-power emblem, not a reachability claim). Build: 69 pages,
  0 errors / 0 undefined refs / 0 overfull.

## 2026-09-21: lim agent R6 verified + integrated -- THE SWEEP BOUND IS A THEOREM FOR THE EXPONENTIAL TIER; lim arc CLOSED (paper 70 pages)

- MY BATTERY: verify_r6.py rerun from scratch, ALL GREEN -- 111
  checks, 0 failures, exit 0. (A) 148 growing rules: 144 convergent /
  4 divergent; 114 with an affine potential; 0 divergent rules admit
  a potential (theorem consistency). (B) per-orbit theorem
  verification on all 114 x inputs <= 7 = 29,070 orbits (v invariant
  every sweep, Phi >= 0, K*delta <= Phi_0, limit B-free) + random
  positivity/Phi_0-bound checks. (C) the 30 non-admitters' (f,K,R)
  tables -- all slow, worst K(9) = 14, f(9) = 34. (D) 372/400
  random larger rules convergent, 149 without potentials --
  phenomenon robust beyond census. (E) shrinking K <= n/(beta-alpha);
  length-preserving K <= 2^n (states distinct). (F) all 16 base-m
  family instances: Phi_0 = i*m^j - i EXACT, R = Phi_0/(m-1) EXACT.
  (G) k-gram potentials: 18 of 30 covered (K <= n^k), the 12-rule
  obstruction list exact.
- HAND CHECKS: (1) the amplifier [baa/ab] as the m=2 instance --
  L-fold a:+1, b:x2: v(baa) = v(ab) = 2 (inv), delta = 1, Phi_0 =
  i*2^j - i, R = Phi_0/(m-1) = i(2^j - 1) = the paper's prop:limgrowth
  fire count EXACTLY -- the potential counts remaining fires; (2)
  k-gram: [aba/aa] by overlapping #aa, 'aaa' -> 'abaa' Delta = 2->1,
  'aaaa' -> 'abaaba' 3->1; (3) the obstruction's hardest
  representative [aaab/baa] BY HAND: map equality forces
  mult(a)^3*mult(b) = mult(a)^2*mult(b) => mult(a) = 1, then
  3*off(a) + off(b) = 2*off(a) + off(b) => off(a) = 0, killing the
  only delta >= 1 letter. Proof of the theorem checked line by line:
  (inv) is per-fire and composes over the sweep; Phi >= 0 by the
  off-weighted sum; Phi(B) = Phi(A) + delta; Phi(uv) = M(v)Phi(u) +
  (M(v)-1)#c(u) + Phi(v) >= Phi(u); leftmost occurrence fires while B
  occurs; K <= Phi(s_0)/delta; lem:fpsweep closes.
- AGENT CORRECTIONS (all machine-caught, none touch the paper):
  off-equation primitive solution sign (71 -> 114 admitters);
  str.count non-overlapping (0/30 -> 18/30 after overlapping fix);
  partF family definitions garbled in the script (the PAPER's family
  statement came from my R5 battery, unaffected); Phi(final) = 0 is
  family-special not theorem-general.
- INTEGRATED (main.tex, 70 pages, 0/0/0): thm:affine (Affine
  Potentials) + proof placed at the end of the lim subsection after
  the conjecture paragraph (now "the sweep half is no longer missing
  for the exponential tier"); the classification paragraph (114/18/12
  split, the [aaab/baa] forcing argument, measured K <= 2n, the
  conjecture's new status: proved up to a polynomial factor on every
  exponential-tier rule, open on the 12-rule family where it is
  expected loose); the termination-passage clause (affine potentials
  as a decidable sufficient condition for the strategic case);
  conclusion clause upgraded ("proved for the entire exponential
  tier by affine potentials, each sweep draining a nonnegative
  potential by a fixed amount").
- ARC DECISION: CLOSED. The charter was proof-or-obstruction and R6
  delivered both: the theorem for the affine class (the entire
  exponential tier, where the conjecture's tightness and its
  separation consequence live) and the precise 12-rule obstruction
  where the potential method fails but the measured sweeps are
  linear. The subsection is complete (def:lim, limtotal, strategies,
  2CM, occurrence, partial, contain, limclass, limundec, limgrowth,
  fiborbit, now affine). A future round could chase the 12-rule
  family for the exact-form conjecture, but the data says the bound
  is loose there -- low value; reopen only if the user asks.

## 2026-09-21: dynamics rules for the three runtimes -- user request, integrated (paper 71 pages)

- USER REQUEST: define the eager and two lazy evaluation modes formally
  with dynamics rules. DONE: def:dynamics (Definition 6.2, p. 58) +
  rem:dynamics in sec:recursion, right after the four-runtimes list.
- THE RULES: values are strings; shared axioms (cat), (fire); eager/
  lazy-args rules (inert_=, strict -- all slots values) with
  (call_v) by value for eager / (call_n) by name for lazy args; lazy-
  pass rules (inert_eps -- R an arbitrary DISCARDED expression, the
  operator equation made operational) + (call_n). The three context
  grammars are the whole difference: eager = hole anywhere (cat
  children, pass slots, call arguments); lazy args = cat children and
  pass slots only (thunks); lazy passes = cat children, pattern/
  scrutinee slots, and the replacement slot ONLY under the guard
  (other slots values + pattern occurs -- Huet-Levy neededness, cited).
  Outcomes: halting value / stuck / divergent; defined exactly on
  halting.
- rem:dynamics records the agreement: eager relation = thm:eager's
  least-fixpoint denotation; lazy-args = thm:lazyargs' liveness
  (by-name vs shared thunks force the same live positions); lazy-pass
  = prop:lpcons' machine. Order-independence of value/definedness on
  record; stuck-vs-divergent split order-dependent (thm:eager).
- VERIFICATION (scoped per the user's scale directive -- no large
  search; definitional addition): dynamics.cpp (C++ per the user's
  rule; batch tool implementing the rules as its only specification)
  run on the NINE canonical programs with hand-computed outcomes --
  gate [g(X)/b]X open (val) and closed (stuck), dead-argument
  separator under all three runtimes (eager und by growth, la/lp val),
  mutual ping-pong (und), empty pattern (stuck), constant-scrutinee
  fire (val), plus the basic cat/call cases -- 9/9 correct, sub-
  second. A full random cross-check against the three reference
  evaluators was started and ABORTED at the user's direction (by-name
  blowup cases defeat small work caps; a definitional addition does
  not need it -- the reference machines already agree with the prose
  semantics these rules formalize, per the existing record). The tool
  stays in research/scratch/rec/ with the driver.
- NEW STANDING RULES (saved to memory, relayed to both agents): C/C++
  for CPU-heavy tests (never Python); no verification job longer than
  1 minute; ask first whether a task needs code at all.

## Alphabet invariance: round 1 VERIFIED + INTEGRATED (2026-09-21)

Agent: research/scratch/alphabet/ (the user's question: is the reachable
class invariant under alphabet size? intuition: reduce any size to 2).

VERDICT: the agent's result is correct and is now in the paper. My own
verification, all runs within the 1-minute rule, C++ for everything
compute-bound:

- verify_hot.cpp REBUILT FROM SOURCE by me and run: ALL OK, 13.3 s --
  HA1/HA2/HA3L/HA3v (dictionary family + Fib sizes, alignment 14,196,
  pass transfer 188,760 + 31,200 for once/R/kth), HT1 x3 (Direction 1
  at the expression level: 357,434 L-mode + 118,160 once + 118,160 R,
  0 mismatches, definedness matching), HU1 (exhaustive unary size<=7,
  36,978 expressions; targets: id/2n/n^2/n+1/ceil/parity FOUND,
  floor(n/2)/max(n-1,0)/n^4/2^n NOT FOUND; n^4 witness at size 10
  exact), HU3, HP (middle-marker family + binary palindromic maxima
  1,1,3,2,7,14). Every deterministic count matches the agent's Python
  logs exactly.
- Python glue batteries re-run by me from copies in the job tmp dir
  (heavy T1/T2 stubbed in my copy -- covered bit-exactly by the C++):
  verify_palindromes.py ALL OK 28.8 s (P1-P4); verify_transfer_light.py
  ALL OK 1.3 s (T0, T1b live at 48,000/0, T3/T3b unary->binary 6,450 +
  12,000, T4a/T4 roundtrip 6,200/0 with 1,025 undefined matching,
  T5a/T5b reversal retraction 63/0, T5c 1,176, T6a/T6b-0/T6b payoff
  31 + 1,176 + 294 + 882, T7/T7b deg/safe/node-count); verify_alignment.py
  ALL OK 6.7 s (A1-A6 incl. the full A3L 188,760; A5b's 24 R-mode
  mismatches are the paper-comma-code's known non-Golomb behavior,
  consistent with thm:r2l-rep -- the battery discriminates);
  verify_unary.py ALL OK 3.2 s (U1a/U1b/U1b'/U2/U3). Total ~53 s.
- HAND-CHECKS (mine): alignment lemma (straddle => comma-free
  violation) sound; pass-transfer induction along the scan sound
  (greedy fires exactly at ell*occ, resume aligned, never rescan);
  double-a family ('aa' only at 0 and ell in u.v, Fib count -- spot
  checked ell=6 = 3 codewords, minimal for ternary); middle-marker
  comma-freeness (mu only at exact middles); BOTH binary size-3
  dictionaries comma-free verified by full enumeration of the 9 pairs
  x 4 offsets by hand; composition lemma; retraction by rep (freezing
  protects inserted codewords); Direction-2 composite equation
  traced; reversal route (palindromic e gives rev(e(T)) = e(rev T);
  q = c.e always lands on image points => composite total); unary
  obstruction h(ab) = h(ba) airtight; unary pass law
  [a^i/a^j]a^m = a^{i*floor(m/j) + m mod j}.
- ERRORS CAUGHT IN THE AGENT'S transfer.tex (fixed at integration):
  (a) the gamma-wrapper for totalizing the Direction-1 witness was
  stated as a single top-level wrap -- correct only as a SIMULTANEOUS
  wrap of every pattern sub-expression (fixed; the reversal theorem
  does not need it: q(T) is always an image point, so the composite
  is total anyway); (b) "Gamma-witness of Direction 2" -> Sigma-
  witness; (c) E' in the Direction-2 construction is the GIVEN
  Gamma-witness of f^c, not E^c (a roundtrip-specific leftover that
  had leaked into the theorem statement); (d) the section's open
  problem is the fourth of sec:limits, not sec:calculus.

INTEGRATED into main.tex as Section "Alphabet Invariance"
(sec:alphabet), between the variants and recursion sections: def:code
(good codings, Golomb comma-free, cites golomb58 -- NEW bib entry,
verified online: Golomb-Gordon-Welch, Canadian J. Math. 10 (1958)
202-209, doi 10.4153/CJM-1958-023), lem:dict (double-a family, Fib
sizes), lem:selfsync, lem:pass-transfer (all four semantics), def:conjugate,
thm:transfer-forward (Direction 1 + node/deg/safe invariants + the
corrected totalization clause), lem:compose, lem:retract, thm:transfer
(both directions, with the corrected witness description), cor:uniform
(alphabet-uniform questions: r, the once node, every k-th node, rev;
negative answers transfer across alphabets), lem:palindrome, thm:rev-uniform
(rev in L over one alphabet iff over every; binary sources via the
size-3 dictionary -> ternary -> middle-marker), rem:native (no
contradiction with prop:del-leftmost/prop:kth: conjugate vs native
conjugacy classes, the ell=1 sub-alphabet subtlety), prop:unary-edge
(the |Sigma|=1 boundary: holds one way, h(ab)=h(ba) obstruction the
other way, unary class eventually polynomially bounded, floor(n/2)
absent from all 36,978 size<=7 expressions -- bounded-search, stated
as such). Touch-points: open problem 4 (sec:limits closing remark),
both landscape ropes (once hinge and reversal are single questions
across alphabets), intro paragraph, abstract clause, conclusion x2.
Build: 0 errors / 0 undefined / 0 overfull, 78 pages (was 71).

ANSWER TO THE USER'S QUESTION: the intuition is right in the strong
form. Every reachable function conjugates along a good (comma-free)
coding to a reachable function over ANY other alphabet of >= 2
letters, both directions -- so no larger alphabet adds power up to
conjugation, and every negative result proved over one alphabet
excludes the conjugate over all. The reduction to TWO letters is
genuine. Two qualifications: (1) what transfers is the CONJUGATE
(block-level) function, not the native one -- which is exactly why
the binary once-witness and the ternary resistance coexist; (2) the
unary alphabet is a real edge: reachable from below, structurally
not from above, and its class is eventually polynomially bounded.
Open threads left deliberately un-chartered (user's scale rules):
binary palindromic comma-free maxima (1,1,3,2,7,14 at ell=3..9) --
unbounded?; floor(n/2) over unary beyond size 7 -- residue-leak
proof or witness.

## Rev agent round 10 CANCELLED by the user (2026-09-21)

The user stopped the rev agent directly. Its mode-3 brute-force hunt
(killed at 17 min, 0-byte log) was the last thing it ran; round 10
produced no result. The no-brute-force / 1-minute rules were relayed
before the stop. Standing state: rounds 1-9 verified and on record;
phase_leftmove_fragment.tex still on HOLD; the descending-bijection
invariant route (gap: prov_A itself descending is the two-pass
loophole) remains the live proof question, unchartered. Do not
restart the arc unless the user asks.

Continuation (same day): at the user's request the rev arc was
re-chartered as a NEW agent continuing round 10 in research/scratch/rev/
(same state: descending-bijection invariant, two-pass gap), under the
hard rules: no brute force, 1-minute cap per run, C/C++ only for
compute-bound work. Old agent stays cancelled; the kill of its
mode-3 hunt stands.

## Rev agent round 10: VERIFIED with ledger corrections (2026-09-21)

Deliverables (research/scratch/rev/): REPORT.md sec 10 (the descending-
bijection invariant, part I: the two-pass bound), round10b_db.c (four-mode
DB/FDI hunter, replacing the killed round10_hunt), verify_round10_lemmas.py,
round10_mode1..4.log, descending_bijection.tex (4pp paper-voice fragment).

THE RESULT: T1 (last-pass: c>=2 + labeled replacement forces mult>=2;
c=1 chains the blocks t^- y t^+; c=0 vacuous). Theorem 1 (S-depth<=1 +
FDI => |prov| <= #V(E), so DB only for n <= #V(E)). Lemma chain Pick /
Slice / Sandwich / Transport. Theorem 2 (S-depth<=2 DB => n <= beta +
2 rho + nu, all shapes, no periodicity; beta = final pattern value
length, rho = #V(F1), nu = #V(final replacement)). Corollary: constant
final pattern => {w : DB(w)} finite (n <= size(E) + 2 #V(E)). Pinch: in
the escaping regime (beta >= n) w is constant on all but <= 2 rho + 4
positions. First pure-chain DBs at depth 3, n = 3 (w = bab, w = abb),
hand-dissected; nothing at n = 4 up to depth 4 on the swept domains.
Budget conjecture (chains: DB only n <= depth+1) clearly labeled open.

MY VERIFICATION (all runs < 60 s each):
- round10b_db.c read in full and checked faithful (greedy never-rescan
  pass at atom level; T1-justified pool restrictions sound); rebuilt
  from source, all four modes reproduce the agent's logs bit-identically
  (mode 1: 162 inputs / 9.95M sims, DB 38,442 all n=2; mode 2: 379 /
  772.9M, max n=2; mode 3: 130 / 389.5M, 29 C(3,1) n=3 + 2 chain3 n=3;
  mode 4: 136 / 537.5M, max n=3, zero n=4). 0.9/10.2/4.5/5.8 s.
- verify_round10_db.py parts 1-2 green (T1(a): 41,850 sims 0 violations;
  depth<=1 FDI singletons). Part 3 superseded by the C program.
- Both n=3 chain witnesses hand-traced atom-by-atom, twice (t1/t2/t3
  match the report's dissection exactly; prov (2,1,0) both).
- Independent t-based checker (my sandwich_t.py): the agent's Sandwich
  check reads the window from the OUTPUT, and its out-adjacency
  precondition never fires -- VACUOUS. My t-based version (window
  t[q-mF:q] at the pick's t-position) fires 22,957 times on the same
  domain: Pick 0, Slice 0, Sandwich 0 violations.
- Checker v2 (my sandwich_t2.py, same domain): MIRROR sandwich (the
  X-first-char input of Pinch, previously unexercised) 21,514 firings,
  0 violations; TRANSPORT pairs (surviving copy-picks at offsets o+beta
  earlier / o later) 0 found across 59,300 FDI outputs.
- Proof scrutiny, line by line: T1, Theorem 1, Pick, Slice, Sandwich,
  Transport, Theorem 2 case (i), corollary, Pinch counting, witnesses,
  round-9 consistency -- all sound except the items below.

DEFECTS FOUND (3):
1. Theorem 2 case (ii) (labeled final replacement, c=1) has a GAP in
   both the report and the fragment: "t^-/t^+ contain only run-pieces,
   <= rho picks each (Slice)" -- Slice bounds picks per F1 ORIGINAL
   run; t^-/t^+ also contain COPY-run pieces, which Slice does not
   cover. REPAIR (mine, hand-proof): every copy meets the site (a
   disjoint copy survives whole, giving >= n >= 2 same-instance picks
   against Pick); each copy yields <= 1 pick (instance-ascending vs
   block chaining t^- > y > t^+); #site-meeting copies <= beta (each
   holds >= 1 of the beta site atoms, copies disjoint); and the label
   count c' rho_Y n <= n + beta caps c' when beta < n. Hence copy-picks
   <= min(c', beta) <= beta and n <= rho + nu + beta, which still
   implies the THEOREM'S STATED BOUND n <= beta + 2 rho + nu. So
   Theorem 2 as stated is TRUE and provable; the write-up needs this
   repair.
2. The sharper ledger item "single labeled final site => n <= 2 rho +
   nu" is NOT proved as written (listed PROVED in sec 10.9). It holds
   when Y is label-free (n <= rho + nu) or rho >= 2, but at rho in
   {0,1} with Y labeled the repair yields only rho + nu + 1 (beta < n)
   or rho + nu + 2 (beta >= n). No witness refutes it (zero depth-2
   DB at n >= 2 on the swept domain), but it must be dropped or
   re-proved; Theorem 2 does not need it.
3. Pinch's final clause "the deviations sit at instance boundaries" is
   asserted, not proved (report sec 10.5, fragment lem:pinch). The
   counting part of Pinch is valid (conservative). The clause must be
   cut or proved before any paper use.
Minor: Transport is stated for [eps/X] but its proof never uses the
eps form (works for any label-free replacement -- understatement,
harmless); sec 10.7's "n <= beta - 1 + 2G reads 3 <= 3 + 2" arithmetic
is muddled (commentary line, not load-bearing); the fragment's
"Verified" parenthetical for Pick/Slice/Sandwich must cite the
t-based check, not the agent's (vacuous on Sandwich).

DISPOSITION: HOLD (not integrated). The DB framework (provenance,
instances, picks, S-depth) is not in the paper; the arc is mid-flight
(depth >= 3 open, budget conjecture open, residual endgame partially
proved), and the fragment needs the case-(ii) repair and the Pinch
clause cut before it is paper-ready. Next round should carry the
repairs plus the residual endgame / budget conjecture. Round-10 core
(Theorem 1, the lemma chain, Transport, Theorem 2 with repair, both
n=3 witnesses) is verified and on record.

## Rev agent round 11: VERIFIED with a framing correction (2026-09-21)

Deliverables (research/scratch/rev/): REPORT.md sec 10 corrections + new
sec 11; descending_bijection.tex updated (516 lines, Theorem 3 in paper
voice); verify_round11.py (4 parts); round11_hunt.c/.log; verify_round10_
lemmas.py v2.

THE RESULT: Theorem 3 -- for every S-depth<=2 E an explicit C(E) bounds
n on DB realizations. Depth 2 of the finiteness program closed by proof
(Frames + Breaks + B-rigidity + residue count), not sweep. Plus four
n=2 chain2 witnesses (the first non-C depth-2 DBs; round 10's mode-2
pool lacked w.b.w-type final patterns -- domain gap, third occurrence).

MY VERIFICATION (all runs < 60 s):
- verify_round11.py parts 1-4 reproduced green (38.1/2.2/2.6/3.9 s):
  elimination 6,831,200 sims, 0; frames 3,545 FDI / 83 firings / 0
  adjacent pairs; B-rigidity 1,184 / 41; kills 5,665 / 41.
- round11_hunt.c read faithful, rebuilt from source, rerun:
  bit-identical (232 inputs / 22,281,480 sims / 345,448 FDI / 4 hits,
  8.85 s).
- All four n=2 witnesses hand-traced atom-by-atom (each prov (1,0));
  sec 11.5's dissection of witness 1 matches my trace exactly.
- verify_round10_lemmas.py v2 reproduced (per-run 22,938/21,498, per-copy
  22,957/21,514 -- my checker's numbers; 0 violations, 0 transport pairs).
- Proof scrutiny line by line: Elimination, Frames, Break, Dichotomy,
  the reductions, uniform-Z tiling, the three kills, B-rigidity, the
  residue count, deep shapes, top-level C-nodes -- all check.
- The five round-10 corrections verified as applied (the case-(ii)
  three-way closure is correct -- Elimination is the clean resolution;
  Pinch's replacement clause hand-checked; Transport widened; v2 real).

DEFECTS FOUND (4):
1. (minor) part 1's "label-free c=1" control is dead code (yf drawn only
   from labeled forms). My probe with the full library on a reduced
   domain: 233,355 FDI outputs with c=1 and label-free replacement vs 0
   labeled -- the c=1-labeled check is LIVE and its 0 is genuine; fix the
   control, fix the "controls behave" citation.
2. (minor) sec 11.2 says 33 inputs, sec 11.6 says 32 for part 1; actual 33.
3. (moderate, repairable) the corner analysis is written for PURE chain2
   t = [Y/Z]f. The in-scope S-depth-2 shapes [R2/P2](g1.[Y/Z]f.g2) with
   pass-free flanking pieces g_i carrying runs are waved at as "chain2
   after flattening" -- flattening is not an equality (the inner pass does
   not scan the flanking material), and there a tau-run can span the
   junctions, so the gap bound s_p <= (j'_p+1)c_Y misses junction gaps
   (g-constants <= c_F, tiling tails < beta'). The analysis SURVIVES with
   each gap bounded by 2c_Y + c_F + beta' - 1, so Theorem 3 is true but
   the write-up and the stated C(E) need the repair. NOTE: neither round
   10's mode 2 nor round 11's hunt swept these mixed-scrutinee shapes
   either -- the machine record "no depth-2 DB at n >= 3" is on pure
   shapes only.
4. (major, framing) the finiteness program's rev payoff is overstated
   for the paper's setting. Over a FIXED FINITE alphabet, distinct-char
   inputs have length <= |Sigma| (bounded), and even on them DB is not
   forced (constant-supplied characters), so "{w : DB(w)} finite" does
   NOT imply rev not in L. Round 2 had this exactly right ("not enough
   for finite Sigma"; "content-level relabeling invariants CANNOT
   exclude rev over any fixed finite alphabet"); rounds 10-11 slid to
   "excludes rev in L outright" and Theorem 3's closing clause (vacuous
   over fixed Sigma). What IS proved, once spelled out: over UNBOUNDED
   alphabets, for any E and any n there is a distinct-character w
   AVOIDING E's constant alphabet, and on such w a rev-computing E must
   realize DB exactly (no output atom can be constant-supplied since
   rev(w) avoids E's constants) -- so Theorem 3 excludes rev at depth
   <= 2 over unbounded alphabets for ALL E, constant-bearing included.
   This avoiding-inputs argument is written NOWHERE in the report; it
   must be added and the finite-alphabet framing corrected.

DISPOSITION: HOLD. The fragment's motivation must be rewritten per
defect 4 (honest headline: depth-<=2 rev-exclusion over unbounded
alphabets; over finite alphabets the prov route has no known forcing
family), the junction-gap repair folded in, both checker controls fixed.
Next round: those repairs first, then the open targets -- the FDI
analogue (sec 11.7), a finite-Sigma forcing idea (the real open problem),
or depth 3 / the budget conjecture.

## Rev agent round 12: VERIFIED, zero defects (2026-09-21)

Deliverables: REPORT.md sec 12 (+ repairs in 10/11), descending_bijection.tex
(653 lines: lem:forcing, thm:laundering, "What DB can and cannot exclude"
motivation, mixed-scrutinee corner), verify_round12.py (3 parts),
verify_round12_mixed.py, round11_hunt.c phase 2, verify_round11.py mode 1c.

THE RESULT: the alphabet-scope theorem, closing the round-11 framing gap in
BOTH directions.
- Lemma DB-forcing (unbounded alphabets): rev-correct on w with pairwise
  distinct characters avoiding Gamma(E) (E's constant letters) forces
  prov = DB exactly. So Theorem 3 excludes rev at depth <= 2 over every
  unbounded alphabet, for ALL expressions, constants included.
- Theorem laundering (fixed alphabets): L_sigma = [sigma/sigma-sigma]
  [sigma-sigma/sigma] (doubling then halving) is a text-level identity
  killing every sigma-label; L_Sigma o E computes exactly what E computes
  with prov == () everywhere. COROLLARY: over any fixed finite alphabet,
  NO nontrivial prov-level property is forced by rev-correctness on ANY
  family -- the finite-Sigma forcing question is answered definitively in
  the negative, by proof (the atoms-level sharpening of round 2's
  content-level negative result).
- The split problem: the two-sided one-b family {a^i b a^j} reduces to
  left-run computability (reduction lemma, explicit construction); the
  split CONJECTURE (no E computes left-run on F -- "can substitution
  subtract?") is the sharpest remaining content-level open problem over
  fixed alphabets. Plus dead-prov rev witnesses W1-W6, incl. the single
  pass [ba/ab] computing rev on {(ab)^k} with prov == ().

MY VERIFICATION (all runs < 60 s):
- verify_round12.py all: reproduced exactly (24.4 s) -- 440,000 laundering
  trials 0 failures; 111 witness checks 0 failures; forcing crux
  1,397,644 atoms 0 violations, degenerate firings exactly as classified
  (15,116 palindromes / 8,391 single letters, all DB).
- round11_hunt.c rebuilt from source, both phases rerun: BIT-IDENTICAL
  (phase 1 = round 11's log; phase 2 mixed shapes 39,628,160 sims, 36
  hits all n=2; 18.1 s).
- verify_round12_mixed.py: 36/36 phase-2 hits re-verified as DB through
  prov.py's independent evaluator; I also hand-traced one mixed hit
  ([eps/'abaa'](ab.[(a.w)/'a'].w.(b.w)) on w=aa, prov (1,0)).
- verify_round11.py 1c: reproduced (16.1M sims, 52.8 s; 673,290 live vs
  0 labeled -- the c=1 channel demonstrably live).
- Hand-proofs checked line by line: the laundering theorem (doubler/
  halver run arithmetic, non-sigma pass-through, per-letter composition
  non-interaction -- the chain order notation is correct: [sigma-sigma/
  sigma] is the DOUBLER, applied first); the forcing lemma (my own
  avoiding-inputs construction from round-11 verification, now proved in
  the arc); the reduction lemma construction; all witnesses W1-W6; the
  junction-gap repair (I re-derived s_p <= (j'_p+1)c_Y + c_F + beta'-1
  independently -- a run-prefix crosses at most one junction and at most
  one interior tail -- and the arithmetic to the restated C(E)).
- No substantive defects. Two notes: part 3's crux check is
  near-definitional (constants cannot supply non-Gamma letters by the
  atom model -- it validates the implementation; the lemma's content is
  the hand-proved counting argument, and the report does not overclaim);
  the n=2 mixed hits sit below every threshold exactly as the pure ones
  do.

DISPOSITION: the DB chapter now has its complete two-sided shape
(unbounded: exact and depth <= 2 closed; fixed: prov route dead by
theorem, content-level split problem open). Integration is now a live
option: the chapter is verified end to end. Recommended next round: the
split conjecture (left-run on {a^i b a^j}) -- if it resolves, the chapter
integrates complete; if it resists after genuine effort, integrate as-is
with the split problem as the paper's new open problem. Budget conjecture
and depth >= 3 (unbounded) also still open.

## Round 13 verification (E_swap; verified 2026-09-21)

Agent: aaadbf445d0648586 (round 13, one-b family). Verdict: VERIFIED in
full. This round produced the arc's first POSITIVE headline result.

- verify_round13.py (parts A/B/C): read line by line first. The
  expression encodings match the paper's [replacement/pattern] order
  throughout (I hand-derived the piecewise diff = [eps/merge]dbl over
  all three regimes incl. the i=j both-runs-fire boundary before
  running). My run (4.7 s) reproduces round13_verify.log byte-identically;
  case counts match the report exactly (A1 13,246 / A2 13,291 / A3 3,653
  / A4 4,424 / A5 13,246). Two minor notes, non-blocking: A4 does not
  test the non-firing converse (implied by A2 anchoring); A5's
  consecutive-b condition is implied by the window-b count (sound --
  windows are contiguous).
- round13_sweep.c: read in full; rebuilt from source (-Wall -Wextra,
  clean), rerun (0.5 s), diff against round13_sweep.log: IDENTICAL. The
  reported const-table bug (consts[idx-NCONST] vs consts[idx-NLIB]) is
  fixed in all three lookups (evalPR, prname, eval2). Chain semantics
  correct (both passes' P/R values evaluated at the original input, as
  lcore requires). Buffers bounded (max library value 42 < MAXS; pass-1
  output <= 441 < CAP); caps = 0 in the log, so the cap-soundness
  caveat never engaged -- the sweep was exhaustive.
- THE CONSTRUCTION, hand-verified by me before any machine run:
  E_swap = [b/w]bigsym, bigsym = C([eps/b]X, b, [eps/b]X). By match
  anchoring the one-b pattern w = a^i b a^j can only match bigsym's
  unique b, at start j; remnants are the first j atoms of the left
  merge copy and the last i of the right copy; the constant b
  replacement gives a^j b a^i = rev(w). Traced concretely: (2,3) ->
  aabaaa, bigsym a^5 b a^5, match at 3, out aaabaa; boundaries (0,2)
  -> aab, (3,0) -> baaa, (0,0) -> b. prov derivation done by hand:
  the surviving a-atoms are exactly merge's label sequence
  (ascending, n-1 labels, all distinct -- first-j + last-i partition),
  so prov = (0..n-1) minus {i}: ascending, injective, length n-1,
  never DB on any input. Machine agrees (C3). The involution I also
  derived by hand (pattern a^j b a^i, same bigsym, match at i,
  remnants (i,j)) before C5 confirmed it. First nontrivial rev
  computation in L; on the FULL one-b language {a^* b a^*}.
- Sweep results cross-checked against the report: unique non-circular
  SWAP at depth 1 is F=bigsym P=w R=b (the construction itself); the 3
  non-circular half-swap seeds ([ba/w]bigsym, [b/shrinkR]bigsym,
  [ba/shrinkR]bigsym); all other swap hits (215+244) circular on
  swapv; SPLIT-i/j = 0 over the enriched 15-value library incl. the
  swap values (720,280 sims); two-b frontier clean (143,388 sims: rev
  0, splits 0, flank-progress 0).
- The 13.7 wall argument read line by line and re-derived by me: for
  w2 = (i,j,k) to fire, the text needs two consecutive b's with
  interior run EXACTLY j (interior exactness), the match consumes the
  whole interior (middle remnant always 0), so the output's leading k
  forces the text's left run = i+k (merge minus middle = middle
  knowledge) and the output's middle j must be resupplied by the
  replacement (interior run exactly j = middle knowledge again). Every
  branch of the complement route needs middle-run isolation -- the
  two-b analogue of the split. One-b is free because it has no
  interior runs at all. The honest hedge (strategy class + depth <= 2
  sweep, not an impossibility proof) is correctly stated.
- The tex addendum (descending_bijection.tex, round-13 paragraph) is
  accurate: S-depth 2 (#S=3, #C=2), no one-separator family can
  exclude rev at any level (12.2 prov + 13.4 content), laundered
  L_Sigma.E_swap = rev with prov = () on the one-b language.
- No defects found this round. Discovery path (C bug surfacing the
  'ba' half-swap seed, then hand analysis) recorded honestly and the
  final construction verified independently of how it was found.

DISPOSITION: the campaign's target moved. rev is now COMPUTED on an
infinite two-sided family; "prove rev not in L" can no longer run
through one-separator families at any level, and the fixed-alphabet
content question lives entirely at >= 2 separators. Round 14 chartered
on the two-b frontier {a^i b a^j b a^k} / {a^i b a^j c a^k}: either the
interior-exactness invariant induction (run-vector reachability under
passes AND concatenations) or a construction that breaks it. Integration
of the DB chapter remains on hold while the arc is producing major
results per round.

ADDENDUM (same day, during verification): I found a MISSED POSITIVE
STRATUM while scrutinizing 13.7 line by line. 13.7's interior-exactness
wall concerns the ALL-VARYING family (i,j,k all vary).  If the middle
run is FIXED, exactness is free: the interior can be baked into the
scrutinee as a constant.  Construction (mine, machine-verified with
prov.py before writing it anywhere):
  E_M = [a^c M^R a^c / w] . C(shave_M, M, shave_M)
computes rev on {a^i M a^k : i,k >= c(M)} for fixed middle M, where
shave_M = a^{i+k-c} via junction-anchored deletion passes.  Verified
instances: M='bab' c=1, M='baab' c=2, M='babab' c=1 (THREE separators),
M='baac' c=2 (mixed letters, the b and c swap in the output), M='bb' c=2
(adjacent).  Round 13's E_swap is the degenerate case M='b', c=0 (shave
= merge).  Script: seed_round14_fixed_middle.py in the rev dir (grids +
random, prov never DB, always injective).  My own hand-derivation slip
on the way (M='bb': [e/(ba)] eats the b plus one right-flank a, so c=2
not 1) was caught by the machine immediately -- recorded as a lesson.
Impact: 13.7's program statement "the content question lives entirely
at >= 2 separators" must be refined to ">= 2 separators WITH VARYING
interior runs"; no proved statement of round 13 is contradicted (the
honest caveat in 13.7 anticipated exactly this).  Also derived (to be
proved in round 14): b-free/b-free passes give psi(u) = r*floor(u/p) +
(u mod p), and psi(u) = u - c forces c = 0 -- a constant can never be
shaved off a b-free run without a junction b.  And a new reduction
question: does rev on the all-varying two-b family imply the split?
Round 14 chartered accordingly (see agent charter).

PARALLEL CAMPAIGN (2026-09-22, user-directed): five lanes at once.
- Lane A (rev agent, round 14, re-scoped): general fixed-middle theorem +
  no-constant-shaving calculus fact + 13.7 refinement + the REDUCTION
  (rev-on-all-varying-two-b => split?) + section 14 write-up.
- Lane B (rev-split): the split head-on, both directions (construction
  candidates from the catalogue; obstruction lemmas for each failure).
- Lane C (rev-try): constructions against the wall -- mixed-letter
  {a^i b a^j c a^k} all varying (asymmetric anchors), same-letter
  all-varying, the correlation spectrum ({j=i}, {j=k}, {j=i+k}, ...),
  toward uniform rev. C-shaped scrutinees mandatory (the round-13 sweep
  blind spot that missed my fixed-middle family).
- Lane D (rev-wall): the run-vector impossibility invariant; Lemma 0 =
  my no-constant-shaving derivation; strongest line: the symmetry
  question (every constructible b-free value of a one-b input a function
  of i+j alone?). Adversarial to B/C.
- Lane E (rev-db): the unbounded-alphabet program -- budget conjecture
  for depth >= 3, or a depth-3 DB realization. The direct route to
  'rev not in L'.
Verification discipline unchanged: every lane reports to its own
scratch dir with REPORT.md + scripts + honest ledger; I re-verify
everything independently before anything enters the paper.

T-DIAGONALITY RELAY (2026-09-22, mid-round): Lane A derived, while
answering the reduction question, a T-diagonality lemma: on every
full-dimensional cell of an expression's firing arrangement over
w2 = a^i b a^j b a^k, the a-run type-triples sum to Lambda(1,1,1) + O(1)
(syntax induction; per-firing accounting exact by never-rescan; firing
counts affine on cells). Corollary (split toll): b-free pure types
a^i, a^j, a^k, a^{i+k} are unconstructible -- the SPLIT IS IMPOSSIBLE,
on the all-varying two-b family and on one-b alike. rev itself is NOT
excluded (its type-sum (1,1,1) is diagonal) -- the wall against
all-varying rev is RUN-LEVEL (positional), not total-level. The
fixed-middle family is exempt coherently (in (i,k)-space a^{i+k} IS
the diagonal -- my seed constructions are exactly outside the lemma's
scope; nontrivial cross-check, passes).
My verification BEFORE relaying (the lemma is not yet writeup-verified):
independent probe of the falsifiable signature -- on the line i+j = S
a piecewise-diagonal a-count takes C(E) distinct values independent of
S, a split-like value ~S -- 3368 random E's (S-depth <= 3), zero
growth, catalogue sanity exact (diff: 2 sign-piece clusters; merge/
half/E_swap: 1). Lane A's own machine: tdiag_check.py, 1358 groups,
one flagged b-count grouping artifact (claimed hand-verified), 0
non-diagonal b-free. Its run self-reported 62.55 s -- over the 60 s
cap; flagged.
Relayed to all lanes with instructions: B pivoted from split
construction to adversarial proof scrutiny (three attack points: cell
affinity of floor/mod jitter; greedy boundary interactions; the
unstated piecewise-affinity structure lemma); C got the type-sum
pre-filter ((2,1,2) slack-flank texts unconstructible if the lemma
holds; ww = C(X,X) legal with exact-j interior but slack-free; hunt
asymmetric diagonal decompositions); D got the run-level tier framing
(ww seed; the positional invariant is now the campaign's fixed-alphabet
impossibility target). A asked to: prove the structure lemma
explicitly, write out the coefficient-mismatch step, enumerate which
converse routes the lemma blocks, and respect the 60 s cap.

## Round 14 verification (Lane A; verified 2026-09-22)

Agent: aaadbf445d0648586 (round 14, re-scoped mid-round when the
campaign went parallel). Verdict: VERIFIED IN FULL. Headline: THE SPLIT
IS IMPOSSIBLE -- the campaign's first fixed-alphabet content lower
bounds.

- verify_round14.py: read line by line, ran: ALL VERIFIED (23.3 s;
  reproduces round14_verify.log up to the timing line). Parts A (my
  five junction-shave seed instances, their c's), B (the OPTIMAL
  fixed-middle theorem: E_M = [M^R/X].C([eps/M]X, M, [eps/M]X), c = 0,
  FULL family i,k >= 0, boundaries included, 29 middles incl. 'aabbcc'
  and 'cbabc'; M='b' reproduces E_swap), B3 (junction-shave c-formula,
  2,045 in-region trials), C (self-anchoring, 20,000 trials), D (psi +
  15,625 depth-3 compositions, no tail-translation with c != 0), E
  (the palindrome-middle reduction engine on fixed-j slices +
  laundered L_a.L_b.E_bab).
- Hand-verification by me: the self-anchoring counting argument ({p+s_r}
  subset {i+s_r}, equal sizes, p = i); the c=0 engine end to end (unique
  occurrence -> shave = merge; unique match at L-i; remnants a^k, a^i;
  replacement M^R); the Pi-progression proof of 14.4 (exactness at
  u = Pi*t forces Lambda = 1, c = 0); the quadratic counterexample
  [merge/'bb'].[b/a]X (b^{S+2} tiled by 'bb' windows each inserting
  merge = a^S -> a-count S*floor((S+2)/2) -- verified by my own
  derivation); Corollary 1's slice argument (constant-S plane is
  2-dimensional, finite piece-traces can't cover it, N_E constant on a
  2-d trace while j varies); the 14.5.3 route enumeration.
- tdiag_check.py (rewritten, 2.1 s): reproduces exactly (811 groups /
  1 flagged / 13,815 skipped / 4,516 dead). I hand-verified the flagged
  group's resolution MYSELF -- the combo [onbA/onbB]onbA's b=2 output
  group glues three sub-regions (the j=1 plane: pattern dead ->
  identity, a-count i+k+1, diagonal in (i,k); the (i,j)=(2,2), k>=2
  line: onbA = b a^k, onbB = a^k, pass fires at 1, output bb a^k,
  a-count k; the point (1,2,2)) -- each genuinely diagonal in its own
  varying space; the (1,-3,1) fit is a gluing artifact. 0 genuine
  violations, confirmed independently.
- round14_sweep.c: rebuilt (-Wall -Wextra; two harmless
  misleading-indentation warnings in parse2b -- behavior correct),
  1.29 s, output identical modulo the agent's appended wall-time line.
  12,787,938 sims; rev 0 (best partial 25/125 = [w2/w2]w2, exactly the
  i=k palindrome diagonal); splits/sums 0 (partials 36-44, firing-cone
  artifacts as Lemma S predicts); flank-progress 0 (nothing crosses the
  flanks at depth <= 2); midstr ABUNDANT (the middle is the cheap
  direction). Completeness cuts documented (depth <= 2, 18-value short
  pool, first-pass <= 200 chars, 6 skipped).
- THE CORRECTION HISTORY, verified as honest: the affine-diagonal form
  of the total-type lemma was refuted by the agent's own machine
  BEFORE landing (the quadratic example); the landed form is Lemma S
  (piecewise S-function totals); affine-diagonal survives on the
  non-explosive stratum and was validated on two independent batteries
  (the agent's 811 groups + my 3,368-E line battery). My earlier relays
  to lanes B/C/D carried the dead affine form; corrections were sent
  the moment round 14 landed (before that: mid-flight correction when
  the agent's message arrived).
- One looseness noted (not a defect): 14.3's parenthetical lists 'bb'
  with (x,y) = (0,1) or (1,0), c = 2 -- but 'bb' has mu_1 = 0 < x+y,
  outside the single-pass proposition's firing region; the actual c = 2
  comes from the TWO-PASS composition (correctly machine-verified in
  part A). Wording only.
- Cap compliance: 23.3 + 2.1 + 1.3 s (the 62.6 s violation was
  rewritten as instructed). Nothing committed (HEAD e80848e).

DISPOSITION: round 14's theorems are verified and paper-grade: 14.1
(self-anchoring), 14.2 (fixed middles c=0 -- the optimal form,
unifying round 13's E_swap as the M='b' point), 14.4 (no constant
shave), 14.5a (vacuous forward reduction), 14.5b (exact per-pass
accounting), Lemma S + Corollaries 1-2 (THE SPLIT IS IMPOSSIBLE on W2
and one-b; the extraction toll; the two-b question stands alone at run
level). Lemma S stands at report rigor with its formalization gap
precisely named -- lane B is attacking it adversarially; lanes C (two-b
constructions), D (run-level invariant), E (unbounded DB) continue.
The DB chapter's integration case strengthened again: rounds 12-14 now
form a coherent fixed-alphabet story (laundering kills prov; totals
kill splits; rev computable on every fixed-middle family; the open
question is exactly all-varying interiors at run level).

## Lane E verification (Separable Rigidity; verified 2026-09-22)

Agent: a0393f9041c41a02d (rev-db dir). Verdict: VERIFIED IN FULL.
THIS IS THE CAMPAIGN'S HEADLINE THEOREM: rev is not computable in L
over unbounded alphabets, at any S-depth.

- The theorem: for w SEPARABLE (letters pairwise distinct, disjoint
  from Gamma(E)), every defined value is v_0 W v_1 ... W v_M (constants
  interleaved with full FORWARD copies of w) and prov = (0..n-1)^M.
  Corollaries: no DB and no FDI of length >= 2 at n >= 2, any depth
  (the budget conjecture in the separable regime, C(E) = 1); E(w) !=
  rev(w) on every separable input; rev not computable in L over
  unbounded alphabets at any depth (via DB-forcing 12.1 or directly at
  content level); any fixed-Sigma rev witness has |Sigma \ Gamma(E)|
  <= 1 (a constraint, not an obstruction -- laundering can raise
  Gamma).
- Hand-verified by me BEFORE the machine: the copy-alignment core (a
  length-n stretch spelling w must be a whole instance: constants
  can't appear, and suffix+prefix across a copy boundary forces
  alignment on distinct letters); the gap induction forcing
  |u_i| = |v_{a+i-1}|; preservation under the greedy never-rescan
  scan; the corollary arguments incl. rev(w) = w forcing n <= 1 on
  distinct letters, and the |Sigma \ Gamma| <= 1 count. The proof
  engine is a SELF-MAINTAINING form invariant closed under the
  semantics -- a genuinely new technique for the paper.
- Machine: verify_separable.py byte-identical (parts A/A2/A3/B/C: 9.3k
  trials, 1,170 instrumented windows, 0 instance cuts, 0 lden
  cross-mismatches); separable_hunt.c rebuilt (-Wall: one harmless
  unused-variable warning; the empty-deep-pattern infinite-loop fix
  confirmed at the pn<=0 guard), all FIVE modes byte-identical (22.2 +
  15.8 + 3.5 + 4.5 + 10.9 s, all under the cap; 122,935,396 defined
  pipelines, ZERO violations); verify_hunt_cross.py byte-identical
  (1,874/1,874 CROSS lines ok; the chain-order fix verified in source:
  run-order first = innermost S-node). The fdihits diagnostic in the C
  only compares text-adjacent labeled atoms -- immaterial: the exact
  badprov block check catches any FDI prov anyway.
- Consistency section checked against my knowledge of rounds 10-13:
  every DB realization on record sits on non-separable w (incl. round
  11's w='ab' with Gamma meeting w); E_swap collapses on separable
  inputs to prov = () exactly as the theorem predicts; n=1 degenerate
  matches round 12's single-letter firings.
- Honest scope: C coverage bounded by the 24-form library and depth 4;
  2.0M explosive pipelines capped (documented); depth 5-8 by sampling.
  None of this weakens the hand proof. The tex fragment
  (separable_rigidity.tex) matches the proved statements.
- PROGRAM STATUS: the unbounded-alphabet program is CLOSED (rev not in
  L, all depths). Theorems 1-3 (rounds 10-11) remain the record for
  the all-w statement at depth <= 2; the arbitrary-w budget at depth
  >= 3 stays open but is no longer needed for rev. The FIXED-alphabet
  question is now the only residual: does any E compute rev on Sigma*
  (e.g. binary with Gamma >= {a,b})? By Corollary 4 + laundering that
  is exactly the lanes C/D battleground.

## Lane B verification (Lemma S scrutiny; verified 2026-09-22)

Agent: a679666dbc05c720e (rev-split dir; its REPORT.md write was
blocked in its session -- I transcribed its text deliverable verbatim
into rev-split/REPORT.md, marked). Verdict: VERIFIED IN FULL.

- B's verdict: Lemma S STANDS; the writeup needs five repairs (R1
  locally-finite not finite; R2 the explosive-stratum count analysis
  reorganized in three cases -- counts never need run-level
  S-functionality -- with the pinned-polynomial run-length auxiliary
  still unowned; R3 ordered refinement slabs->residues->coincidence
  with pinned-POLYNOMIAL conditions; R4 missing single-b
  zero-interior-run pattern case; R5 two slice-step caveats). I
  assessed all five independently: every one is sound (R2's integer-
  polynomial residue determinism and R3's nonzero-polynomial-open-set
  argument both check). None kills the corollary.
- B independently derived the non-explosive obstruction (the
  flank-antisymmetry coefficient invariant) BEFORE my relay; priority
  for the general form stays with Lane A, recorded honestly.
- Machine (all reproduced): verify_grid.py ALL VERIFIED (3.4 s, near-
  miss catalogue A1-A10 incl. the 2,184-firing two-b engine check);
  lemma_stress.c rebuilt + default seed byte-identical (5.1 s) + my
  second seed confirms the fixed box-stream flags idx 455 again, zero
  split hits; growth.c + w2support.c rebuilt, default seeds
  byte-identical (3.2 s, 1.4 s); growth2.log reproduced byte-identical
  after I recovered the unrecorded seed (24681357, hardcoded in the
  dissect tools); dump455 confirms the mod-3 sawtooth (fixed stream,
  reproducible); w2dissect2/w2path on idx 3372 reproduce the report
  verbatim (non-monotone supports; the S=27 k=1 period-4 step function,
  3 distinct values, never a ramp).
- B's methodological caveat about MY 3,368-E line battery: the
  cluster-flat signature is a valid falsifier only on the
  non-explosive stratum (locally-finite Lemma S permits ~S support
  growth on explosive strata legitimately); explosive E's need the
  path/step test. Accepted -- noted here for the record; my battery
  stands as a non-explosive smoke test.
- The split-corollary is now: PROVED on the non-explosive stratum;
  conditional on the unowned pinned-polynomial schema induction (R2)
  beyond it. That induction is the campaign's most load-bearing open
  writeup task; relayed to lane D as its machinery.

PARALLEL STATUS after this wave: A (round 14) verified; B verified;
E verified (headline theorem); C and D still running. When they
report: verify both, then charter the consolidation round (Lane A
resumes: fold R1-R5 into the Lemma S writeup, own or assign the
pinned-polynomial induction, integrate the separable-rigidity tex).

## Lane C verification (round 15: mixed-letter family falls, T3* spectrum, V_h reduction; verified 2026-09-22)

Agent: a03621548e520da79 (rev-try dir; its REPORT.md write was blocked
-- I transcribed its final report verbatim into rev-try/REPORT.md, with
my verification note on top). Verdict: VERIFIED with artifact
corrections (below). This is the round that moves the fixed-alphabet
frontier.

- THEOREM T1 (hand-verified by me in full, incl. all boundaries): over
  Sigma={a,b,c}, E_mix = [b/(mrg.b)](Cc.Bb) computes rev on the
  ALL-VARYING mixed family {a^i b a^j c a^k}. Mechanism: b!=c makes
  each letter's deletion a uniquely-firing projection ([e/c]X and
  [e/b]X are one-separator texts); each box (Cc, Bb) is the
  fixed-middle complement engine on a projection; T = a^k c a^{i+2j+k}
  b a^i; the final merge-flavored shave [b/(mrg.b)]T fires at T's
  unique b and leaves exactly a^j (i+2j+k - S = j). NO middle-run
  isolation -- evades 13.7(c); REFUTES 13.7's "distinct rare letters =
  same wall". 15 S-nodes, S-depth 4, size 58 (my counts). Consequence:
  no fixed-alphabet content obstruction exists at 2 distinct
  separators.
- THEOREM T3* (hand-verified): E_{c,d} = [b.M.b/X](F.b.M.b.F) computes
  rev on {a^i b a^{c(i+k)/d} b a^k} for every coprime c>=0,d>=1. The
  family's integrality (d | i+k) makes the b-free floor-division run
  maps exact: F = a^{i+k}, M = a^j with no leftover. Consistent with
  Lemma S: on-family, a^j = a^{cS/(c+d)} IS a function of S. Includes
  the m-family j=(m-1)(i+k) and the M='bb' fixed-middle point (0,1).
- V_h-EQUIVALENCE (hand-verified both directions): rev on same-letter
  all-varying {a^i b a^j b a^k} IFF V_h = a^k b a^{j+h} b a^{i+h} is
  constructible for some constant h. V_h is INVISIBLE to the
  total-content calculus (total S+2h, exact S-function) -- it is the
  precise reduced target, relayed to Lane D mid-flight.
- Wall analysis: every two-b one-firing final pass forces R's middle
  run = j exactly; the only j-suppliers are X-family flanks (=> slack
  => V_h route), merge-powers (=> exactly the T3* families), and the
  dead split (round 14 Cor 1). Transplant lemma: P1 (a^i b a^{j+k})
  and P2 (a^{i+j} b a^k) constructible => rev; P1&P2 <=> V_h.
- MY BATTERY (rev/verify_round15.py, ~10 s, ALL VERIFIED): fresh
  re-encodings of E_mix (13^3 grid + 500 random) and E_{c,d} (12 pairs
  incl. 7/3 and 5/6 beyond the agent's list); the four checks the
  agent's overwritten scripts dropped (slack calculus, size counts,
  A7-convergence, slack-class closure), all re-established; slack
  class closed under one-b constant passes with affine action
  (d1,c,d2) -> (d1-r0+x, c+x+y-r1-r0, d2+y-r1).
- CORRECTIONS (artifacts only, claims stand): (1) the report's
  rev-slack pass formula is a sign slip -- as written it yields
  a^{k+2d1} b a^{j+2h} b a^{i+2d2}; correct forms are PAD
  [a^{r0+d1} b a^{r1+d2}/a^{r0} b a^{r1}] on rev and STRIP
  [a^{r0-d1} b a^{r1-d2}/...] on slack, both machine-verified by me.
  (2) t3star.log/t4_reductions.log are narrative concatenations, not
  single-run outputs (t1/t2 reproduce byte-identically; t3/t4 do not)
  -- stale REFUTED lines are from earlier fixed script versions.
  (3) ST2's "[aa/a]X" is a label typo for [a/aa]X (the halver).
  (4) ST2 does NOT refute the landed per-piece Lemma S: my part G
  shows the halver total is (S+#odd)/2 on each mod-2 cell -- an
  S-function per cell; only the residue-less S-exact reading dies
  (consistent with B's R3).
- Consistency: Gamma(E_mix) = Sigma (Cor 4 tight); E_2's off-family
  near-miss (flanks +1 on j=i+k+1) is the halver's O(1) jitter -- the
  same mechanism ST2 isolates.
- PROGRAM STATUS: unbounded program CLOSED (Lane E). Fixed-alphabet
  program now: 2+ distinct separators CLOSED (T1); rational symmetric
  correlations CLOSED (T3*); same-letter all-varying = exactly the V_h
  question (Lane D running). 3+ distinct-separator families left OPEN
  by C (unclaimed) -- natural next construction round if D proves V_h
  unconstructible.


## Round 15B (my own construction): general distinct-separator theorem (verified 2026-09-22)

Lane C's OPEN item (3+ distinct-separator families, unclaimed) closed
by me: for every k >= 1, distinct separators s_1..s_k, all runs varying,
rev is computable on {a^{r_0} s_1 a^{r_1} ... s_k a^{r_k}} by
E_k = [s_1/(mrg.s_1)]...[s_{k-1}/(mrg.s_{k-1})] . (D_k ... D_1), where
D_m = [s_m/L_m](mrg.s_m.mrg) is the complement engine on the keep-only-
s_m projection (inter-separator runs of the concatenation are exactly
S + r_m; each shave removes S leaving r_m). k=1 unifies with the
round-14 complement engine; k=2 IS E_mix (my E_2 reproduces T1's counts
58/15/4). Verified: rev/verify_round15b.py + round15b_verify.log
(k=1..k=4, grids incl. boundaries + randoms, 25 s, ALL VERIFIED);
4k^2-1 S-nodes, S-depth 2k. CONSEQUENCE: every distinct-separator
all-varying family falls, any k; a fixed-alphabet obstruction for rev
can live ONLY where separators collide = the same-letter question =
exactly V_h. Lane E Cor 4 tight (Gamma(E_k) = Sigma_k).

PROGRAM STATUS after 15B: unbounded CLOSED (E); distinct-separator
families CLOSED at every k (15B); rational symmetric same-letter
correlations CLOSED (T3*); same-letter all-varying = the V_h question
(D running). Consolidation round (Lane A) chartered next: fold
R1-R5 + ST2-per-cell into Lemma S, integrate rounds 13-15B +
separable rigidity into the paper record.

## Lane D verification (round 1: prefix-dominance + split-toll scrutiny; verified 2026-09-22)

Agent: a02db52e865864df1 (rev-wall/; its REPORT.md wrote fine, 481
lines). Verdict: VERIFIED with two artifact notes. The machine battery
reproduces EXACTLY, number for number.

- E_asym (sign-gate): hand-verified by me in full (every firing in all
  three regimes; [aa/a]X is the DOUBLER here, correct convention; the
  i<j case fires once at the first b leaving a^{2i} b a^{j-i}; i=j and
  i>j never fire; final [eps/b] gives i+j vs 2(i+j)). Machine: 1025
  checks 0 mismatches, reproduced. Significance: sign(j-i) extractable
  as a GATE, not a length; b-free lengths are piecewise-in-s with
  sign-keyed pieces.
- Scrutiny of the split toll (Corollary 1 / Lemma S induction):
  V1 CONFIRMED -- "every run is O_E(S)" is an invalid inference and
  false in fact ([merge/'bb'].[b/a]X single Theta(S^2) run, the ST1
  exhibit I verified in round 14); the bounded-tile-count route to case
  (i) is dead on the explosive stratum. V3 CONFIRMED -- the covering
  step is invalid on the integer lattice (finitely many j-levels DO
  cover the triangle); Lane D's counting repair verified by me by hand:
  N diagonal traces cover <= N*S_0 < (S_0-1)(S_0-2)/2 for S_0 >= 2N+3;
  finiteness of the partition is load-bearing. V2 = the salvage
  (dangerous configs need multi-run non-S-functional scrutinee AND
  sublinear-unbounded/non-affine computed modulus; all attempts
  collapsed: p3 = S mod ceil(S/2) is affine-on-parity) -- honest
  conjecture, unowned. NET: the split toll is CONDITIONAL on R2 --
  book Corollary 1 as conjectured-until-Schema-P.
- PREFIX-DOMINANCE (the run-level invariant, CONJECTURED by the lane):
  run-boundary prefix a-counts i-dominant, suffixes k-dominant. I
  hand-verified the selectivity matrix: V_h lead (0,0,1) EXCLUDED;
  rev(w2) EXCLUDED; P1 prefixes (1,0,0),(1,1,1), suffix (0,1,1) LEGAL;
  P2 lead (1,1,0), tail (0,0,1) LEGAL -- exactly the required
  selectivity (admits the transplant building blocks, excludes the
  target). Conditional theorem (invariant => rev impossible on W2):
  sound, one line. Complement-text obstruction honestly marked
  conditional (2S-j not an S-function -- the round-14 (2,1,2) filter).
  Induction closes at K/V/C (cone argument) and depth-1 passes
  (absorption); the ONE open case is localized to the L-family window
  cut (pattern-lead with d_j > d_i eating the middle run anchored at
  the second b) -- coherent, and itself circular on the toll.
- Machine battery: ALL REPRODUCED EXACTLY. wall_verify A 1025/0; part C
  sweep-1 1500/884 with 9 FLAG INSTANCES on 6 DISTINCT expressions (the
  report says "9 flagged expressions" -- wording slip, noted), all 6
  autopsied by dissect.py (cell crossings + residue sawtooths);
  controls: E_swap flagged 5/5 (positive control), E_asym clean,
  catalogue passes; sweeps 800/443, 800/463, 250/56 (depth 4),
  700/402, 1200/670 (the unlogged 424242 run), chain 800/627 -- total
  4550/2661 ZERO violations, each run < 60 s (my re-runs 9-53 s);
  seed-222 timeout reproduced (exit 124 at 55 s).
- Artifact notes (mine): (a) the 9-flags/6-expressions wording above;
  (b) the C-split classification's b-free branch silently assumes the
  prefix length "tracks k" -- i.e. the piecewise-affine/partition
  structure -- so that branch inherits the R2/Schema-P condition like
  its neighbors (the b-bearing branch IS unconditional: A's lead run =
  k exactly, type (0,0,1)). Marked for Lane A's next integration pass.
- PROGRAM IMPACT: the wall (prefix-dominance) and the toll have
  converged on the same load-bearing stone -- R2/Schema P. Lane A's
  consolidation (just delivered, verification next) owns Schema P with
  P0-P3 proved and the residual precisely specified. The endgame
  structure: Schema P => Lemma S finite-partition form => Corollary 1
  (with the counting repair) => L-family window cut closed =>
  prefix-dominance => V_h unconstructible => rev impossible on W2 =>
  (laundering + rounds 10-15B + separable rigidity) rev not L-reachable
  over any fixed alphabet with >= 2 letters. Every arrow now has an
  owner except Schema P's residual transformer table.

## Lane A consolidation verification (§15 + Lemma S repairs + Schema P + main.tex; verified 2026-09-22)

Agent: aaadbf445d0648586, resumed with the consolidation charter.
Verdict: VERIFIED with three patches required (relayed back for a
follow-up pass).

- BUILD (independent): pdflatex twice from clean logs -- 84 pages,
  0 errors, 0 overfull, 0 undefined references (the 10 "undefined"
  grep hits are font-shape substitutions, cosmetic; 12 underfulls
  benign). Git: nothing staged or committed; only working-tree
  modifications. Wire-ins present at the intro (limits item), the
  alphabet section, and the conclusion.
- The frontier subsection (ssec:frontier) scrutinized in full:
  separable rigidity reproduces Lane E's verified proofs faithfully
  (copy alignment induction, preservation, rigidity, no-rev, witness
  shape with the exact machine-domain numbers from my Lane E battery);
  the positive half is correct (self-anchoring = round-14 lemma 14.1;
  fixed middles with c=0 and no boundary restriction; the distinct-
  separators theorem is my 15B with a faithful proof -- I re-checked
  the anchoring inequality L=S >= max(...), the inter-separator run
  S+r_m, and the flank-starved first separator in the transplant
  note, which is a correct sharpening); V_h uses the CORRECTED STRIP
  form; the wall analysis and three-supplier reduction are as
  verified in round 15. Honest status marking throughout: the
  structure lemma carries its explicit conditional block; the toll is
  marked conditional; two overclaims caught pre-landing by the agent
  itself.
- PATCH 1 (rigor gap, prop:toll's covering step): "every at-most-one-
  dimensional cell meets the plane in a finite set" is FALSE for
  curved coincidence cells (a pinned-polynomial coincidence j = i^2
  has an infinite lattice trace on the plane). Correct completion
  (mine, simplest): the LEVEL PIGEONHOLE -- N cells each confined to
  a single j-level cover at most N of the plane's S_0-2 j-levels, so
  for S_0 > N+2 some cell meets two levels, and two same-cell,
  same-S_0 points with different j already contradict the pinned
  a-count (h_r(S_0) fixed, output length j varies). All six toll
  targets work via the corresponding coordinate's levels; Lane D's
  diagonal-counting repair covers the general non-S-functional
  targets. Both must replace the segment phrasing.
- PATCH 2 (label slip, thm:separators parenthetical): "14/2, 58/4,
  126/6, 218/8 (pass nodes / pass depth)" -- those are TREE node
  counts; the pass-node counts are 3/2, 15/4, 35/6, 63/8 (the
  theorem's own 4k^2-1). One-line fix.
- PATCH 3 (Schema P residual under-specified, 14.5.2 + lem:structure
  status): the residual names computed replacements at anchored/
  coincidence sites and nested computed patterns on periodic regions,
  but NOT the explosive-tiling class -- b-bearing constant patterns
  tiling uniform b-blocks with computed replacements
  ([merge/'bb'].[b/a]X, the round-14 exhibit itself, exactly V1's
  stratum). The consistency check verifies the one known exhibit;
  the class must be an explicit residual entry (a T5) or the
  "precise statement another agent could attack" is incomplete.
  Everything else in Schema P checks: the group-total design is
  exactly right (the halver is its canonical instance -- per-run
  multiplicities floor(i/2) are not S-functions, the group total
  (S-#odd)/2 is, per cell); P0/P1/P2 proofs scrutinized and sound
  (P2 = periodicity + single-fixed-pattern; P1's boundary-correction
  accounting credible); T1's product-form closure verified against
  ST1/ST2.
- 13.7's correction of record: in place, exemplary (bracketed at the
  section head, the refuted clause marked in situ, the surviving
  same-separator wall identified, the evasion mechanism named).
- Follow-up chartered: integrate Lane D's round as §16 (prefix-
  dominance with its selectivity matrix, E_asym, V1/V2/V3 with the
  counting repair folded into Corollary 1's proof, the C-split
  classification with the b-free branch's inherited conditionality,
  and the 9-flag-instances/6-distinct-expressions wording note),
  plus the three patches above.

## Lane A follow-up verification (patches 1-3 + P4 + §16; verified 2026-09-22)

Verdict: VERIFIED. Build reproduces independently (85 pages, 0 errors,
0 overfull, 0 undefined refs); git clean.

- PATCH 1 verified and IMPROVED over my spec: the level pigeonhole as
  written is tighter -- a cell on which the a-count is h_r(S) meets a
  j-level {j = c} only with h_r(S_0) = c (outputs there have length c),
  so 'each cell meets at most one level' is immediate; the diagonal
  count is unified with it as the same repair (coordinate vs general
  affine targets), credits in place; the load-bearing-finiteness note
  (countable j-pinning cover) in place. IMPORTANT: Lane A caught a
  genuine circularity in MY pigeonhole spec that my own verification
  missed -- with only local finiteness the cell count N depends on
  S_0, so 'choose S_0 > N+2' is circular. Mutual scrutiny working as
  designed; recorded.
- The circularity repair is P4 (degree separation => FINITE partition),
  scrutinized by me: run lengths decompose as affine (coefficients
  bounded by node count -- anchored glueings) + pinned S-polynomial;
  slab indices bounded (affine <= C_E*S vs Omega(S) moduli => quotients
  O(1); S-parts by polynomial division; constant moduli = residues).
  The one subtle case -- merged product runs f.m from tiling with
  b-free computed replacements -- closes NON-circularly: non-b-free
  templates carry affine parts INSIDE, separated by b's, never merging
  across copies; b-free templates merge, and their lengths are
  cell-wise S-functions by the TOTALS-IH (Lemma S's conclusion at
  smaller depth), a well-founded simultaneous induction. PRECISION
  NOTE (relayed for the record): the writeup cites P1 for 'template
  contents are S-functions'; the correct citation is the totals-IH --
  P1 covers multiplicity group sums, not template run lengths.
- PATCH 2 verified (3/2, 15/4, 35/6, 63/8 pass nodes + tree sizes
  separate). PATCH 3 verified: T5 (explosive tilings) added as the
  residual's third entry, correctly scoped (single-pass mechanism =
  T1-with-letter-swapped, proved; nestings unwritten -- now Lane B's
  charter), the attackable statement now complete in scope.
- §16 verified: E_asym with the full proof, V1/V2/V3 as the
  correction of record (R5b retired, R5a survives), prefix-dominance
  with the selectivity matrix and the C-split b-free branch marked
  Schema-P-conditional (my note), the 9-flag-instances/6-distinct-
  expressions correction, machine verdicts marked
  coordinator-reproduced.
- The toll's status is now exactly: PROVED on the non-explosive
  stratum; conditional on Schema P (P0-P4 + the residual table) in
  general -- and the conditional delivers the FINITE-partition form,
  which is what the pigeonhole needs.

## Lane C round 15C + Lane B round 2 verification (THE SAME-LETTER WALL FALLS; verified 2026-09-22)

The campaign's decisive round. Both lanes verified in full.

### Lane C (rev-try, round 15C): E_rev and the general engine — VERIFIED

- HEADLINE: rev is computable in L on W2 = {a^i b a^j b a^k : i,j,k >= 0}
  over Sigma={a,b} — the same-letter all-varying family, the last
  fixed-structure family. By the general engine: on EVERY fixed
  separator structure {a^{r_0} s_1 a^{r_1} ... s_k a^{r_k}} over any
  finite alphabet (any letters, repeats allowed, all runs varying).
  The fixed-alphabet question's only remaining refuge is VARYING
  separator count (one expression for all of Sigma*).
- MECHANISM (merge-catalyzed selective deletion): concatenating the
  merge next to the input gives one separator an unbounded adjacent
  run, so a merge-flavored pattern fires there unconditionally and at
  the other separator never. P1 = [eps/(b.mrg.a)](X.mrg.a) = a^i b
  a^{j+k}; P2 = [eps/(a.mrg.b)](a.mrg.X) = a^{i+j} b a^k. Then the
  transplant skeleton: Cc = [b/P2](mrg.b.mrg) = a^k b a^{i+j}, Bb =
  [b/P1](mrg.b.mrg) = a^{j+k} b a^i, T2 = Cc.a.Bb, final shave
  [b/(a.mrg.b)] leaves exactly j (the K('a') pad and the +1 are
  paired edge-guards). NO middle-run isolation — the 13.7 wall is
  bypassed, not broken.
- MY VERIFICATION (rev/verify_round17.py, 33 s, ALL VERIFIED): fresh
  encoding from my own hand derivation (every firing hand-verified
  BEFORE reading either lane's scripts, incl. all boundary cases);
  12^3 grid + 500 random + 300 adversarial scales; intermediates; prov
  never DB + injective; laundered L_a.L_b.E_rev = rev with prov == ();
  V_0 = E_rev and V_1 = [b.a/b]E_rev constructible (prefix-dominance
  concretely refuted); the general engine on 11 separator words (k=1
  cross-check = round-14 engine; k=2 'bb' = E_rev; 'cb'/'bc' = E_mix;
  k=3/k=4 same-letter; mixed with repeats 'cbb','bcb','bcc','cbc';
  k=5 'cbccb') — 800 cases each. Lane C's own scripts (verify_t5_rev,
  verify_t6_general) re-run: all VERIFIED (logs carry appended
  narrative blocks beyond script output, as in round 15). Lane B's
  independent rebuild (rev-split/verify_lc_rev.py) re-run: VERIFIED,
  13.5 s.
- SIZES (my counts): E_rev tree 75 nodes, 14 S-nodes, S-depth 4 (Lane
  C's "75 nodes, 6 S-nodes" mixes tree size with DAG S-count — noted
  for the record; syntactic size is the tree).
- CONSEQUENCES: (1) V_h-equivalence intact with witness h=0 (V_0 IS
  E_rev's value); every universal V_h/projection-exclusion claim is
  refuted; (2) Lane D's PREFIX-DOMINANCE refuted as a universal
  invariant (V_0's lead run is k-typed (0,0,1)); the escapes: (a)
  merge-padded concatenated scrutinees (X.mrg.a, a.mrg.X) — enabling
  windows at the first/last separator, the merge absorbing the
  deletion; (b) complement boxes [s/L_m](mrg.s.mrg) whose output lead
  is S minus the pattern's trail — invariant programs closing over
  X-structured texts see neither step; (3) Lemma S / Schema P
  UNTOUCHED (all intermediates S-total: S, S, S, S, S, 2S+1, S+2; the
  engine is a positive specimen of B's entry-(i) classes); Lane E
  consistent (Gamma(E_rev) = {a,b} = Sigma, Cor 4 tight); (4) the
  b-free splits (a^i, a^{i+j}, a^{j+k}) remain toll-excluded — and
  are never needed.
- NEW FRONTIER: varying separator count — rev on all of Sigma*. Lane
  C notes del_first/del_last and the shaves are already count-adaptive;
  only the positional middle projections L_m are k-dependent.

### Lane B (rev-split, round 2): residual table closed at skeleton level; P4 REFUTED and repaired — VERIFIED

- All three residual entries close via the TELESCOPE LEMMA: every
  window count is an S-function on each cell of a finitely
  parameterized arrangement, because multiplicities enter only through
  template-group sums (P1) and every per-run count telescopes to a
  letter-total, a prior window count, or a pinned constant. Entries:
  (iii) T5 explosive tilings + nestings (c_w = (T_c - Lambda)/p
  exactly; CH3: T5^3 = a^{S+2S^3} exact); (i) computed replacements at
  anchored sites (site types: O(1) singular + per-template kappa_U;
  c_w = Sum kappa_U n_U + O(#segments)); (ii) nested computed patterns
  on periodic regions (Sum floor(m/g) = (n_U - Lambda_g)/g); the
  b-free-length closure uses the totals-IH at smaller depth (my
  addendum's point — load-bearing, non-circular).
- P4 REFUTED AS STATED (CH2 = [merge/'bb'].[bb/aa]X): on the all-odd
  cell the output contains the singular run a^{S(i+j-2)/2+1}, whose
  k-slope on a fixed-S plane is -S/2 — unbounded — hence not
  A(i,j,k)+P(S). Root cause: the run absorbed a PARTIAL group sum
  (individual block mults are pinned polynomials, only P1's group
  sums are S-functions). I verified the algebra by hand and by
  machine (my part D). My precision note fixed the template-length
  direction; this is the multiplicity direction — three writeup sites
  conflated them (P4's parenthetical, profile (B), T5's parenthetical).
  REPAIR (P4'): run lengths live in the closure of {affine junction
  parts; S-function template lengths} under sums, products
  (S-function) x (pinned polynomial), and exact division — affine x
  affine never arises; finiteness via exact polynomial division +
  cones + finite arrangements. The toll SURVIVES (the writeup must
  replace P4's proof, not its conclusion); Lemma S untouched (CH2's
  totals still telescope — N = S(S-3)/2+3 on the odd cell
  [CORRECTED 2026-09-22: this entry originally transcribed Lane B's
  number as 3 + S(S-4)/2; Lane A caught it, I machine-verified the
  corrected form — grid i,j,k odd 1..9 — and my original form is
  REFUTED; spots: (1,1,1)->3, (3,1,1)->8]).
- MY VERIFICATION: schema_p.c rebuilt from source; mode t5 reproduces
  BYTE-IDENTICALLY (4,192 checks, 0 failures, wrong-formula control
  FLAGGED); mode cells run 1 = the default invocation (777111/1000)
  reproduces byte-identically (765 exprs, 293,507 cells [CORRECTED 2026-09-22: I transcribed 293,307; Lane B's drift check caught it — the log reads 293,507], unexplained
  0); runs 2-3's seeds unrecorded (bookkeeping slip) but 20+ fresh
  seed probes ALL return unexplained 0 — the claim is over-reproduced.
  CH2 hand-verified (see above). The Telescope Lemma scrutinized at
  skeleton level: the mechanism is sound; the write-out (provenance
  recursion, quasi-polynomial closure) is the remaining writing task.
- STATUS: the residual table is CLOSED AT SKELETON LEVEL — Lemma S's
  full proof (finite partition + S-functional totals) is one write-out
  away; the toll inherits that status.

### PROGRAM STATUS after these rounds

rev is computable on every fixed separator-structure family over any
finite alphabet. The unbounded-alphabet negative (Lane E) stands. The
fixed-alphabet question now lives EXACTLY at varying separator count:
one expression for all of Sigma* — or an obstruction there. The
endgame chain is re-routed: the toll (Lemma S write-out) is no longer
on the path to the main question (it constrains the b-free splits,
which are no longer needed) — it is now a self-contained structural
theorem. Next charters: the unification construction (varying k) and
the varying-k invariant hunt.

### Correction + exact engine sizes (coordinator, 2026-09-22)

My round-17 battery verified the general engine's VALUES (rev on 11
separator words). While producing size counts for the paper I caught
an error in my own relay prose: I had generalized E_rev's S-depth 4
(the hand-optimized k=2 case) to "S-depth 4 for every k" — FALSE.
Machine counts for my gen_engine encoding (same-letter words,
k=1..5): DAG nodes 9k^2+2k+4 (15/44/91/156/239), S-nodes k^2+k+1
(3/7/13/21/31), S-DEPTH 2k+1 (3/5/7/9/11) — the del_first/del_last
chains stack. Mixed-letter words are within O(k) of these (cbb k=3:
97/14/8; cbccb k=5: 245/32/12; cbccbcc k=7: 465/58/16). Also a
wording fix: in the entry above, "k=2 'bb' = E_rev" means the engine
AGREES WITH E_rev's function on W2 — gen_engine('bb') is a second,
systematic encoding (44/7/depth 5), not the hand-built E_rev
(41/6/depth 4, tree 75/14). Bottom line for the paper: for every
fixed k, rev on the k-separator family is computable with S-depth
2k+O(1) and size Theta(k^2) — depth is Theta(k), NOT constant. This
supersedes round 15B's distinct-separator bounds (4k^2-1 S-nodes,
S-depth 2k) as the general statement (repeats included). Charters
for lanes C/D/B were corrected before dispatch; no false claim
reached an agent.

## Lane D round 2, Lane A round 4, Lane C round 16 verification (verified 2026-09-22)

### Lane D (rev-wall, round 2): refutation recorded + varying-k hunt — VERIFIED

- Prefix-dominance refutation recorded with a precise autopsy
  (R2.1.1): the sweep missed (a) merge-padded concatenated
  scrutinees, (b) computed b-bearing patterns, (c) complement boxes'
  S-typed leads; the invariant survives only on the non-merge-padded,
  constant-pattern stratum. My check: the record matches the
  verified facts exactly.
- SNF (Sweep Normal Form): out = q_0 R q_1 ... R q_t, same R at
  every firing, remnants in input order — PROVED (3 lines from the
  semantics; it is the firing-uniformity fact). MY ADDITION: I
  verified the decomposition DIRECTLY against the campaign
  evaluator (rev-wall/verify_r2_wall.py part 4: 765/765), not just
  against D's reimplementation (D's 990/990 cross-check).
- Diagonal census: a.b^k |-> b^k.a computable uniformly in k
  (E_abk = [R/X](X.a), R = [eps/a]X; fails only at k=0); (ab)^k |->
  (ba)^k by the constant pass [ba/ab]X; b^k and palindrome profiles
  = identity. My fresh encodings: 60 k-values + boundary + off-
  family honesty — VERIFIED. Lesson: the obstruction must live on
  asymmetric all-distinct-run profiles (the increasing diagonals).
- The arithmetic fixed point (r_k <=> S - r_k; at k=2 the circle is
  broken by the ADJACENT MERGE, at k >= 3 the sum spans k runs and
  recurses): hand-scrutinized — sound as architecture, correctly
  labeled conjecture (V1/V2/V3 + the conditional target).
- Battery reproduction: varyingk.log BYTE-IDENTICAL on re-run.
  Dissection replay (my battery): the single k=2 SUM-MINUS-MAX hit
  is a CONSTANT a^4 at every k=1..6 — coincidence confirmed.
- MY FINDING (new, machine-verified): the naive dec-capacity
  program is FALSE on the explosive stratum — [X/a]X has
  dec(output) = 2,3,5,6 growing with k (sizes 21,197,1723,15129).
  D's probe cap (len <= 600) silently excluded exactly this class;
  its "max dec = 3" is an artifact of the cap on the non-explosive
  sample. Lane C INDEPENDENTLY found the same class ([X/'b']X,
  LDS ~ k at depth 2) from the construction side. Convergent
  discovery: any dec/LDS-type invariant must carry VALUE-
  STRATIFICATION (disjoint value ranges across copies), not
  subsequence counts alone. Also: D's part-C label prints "B=4"
  while the code uses B=3 (cosmetic; the report says B=3 correctly).

### Lane A (rev, round 4): the major integration — VERIFIED

- Build reproduced: 87 pages, 0 errors, 0 overfull; the 10
  "undefined" log lines are all pre-existing font-shape warnings.
- Provenance deviation CORRECT: my charter's pointer file
  (tmp/laneC_report.md) contains the ROUND-15 report, not 15C — I
  extracted the wrong message. Lane A detected it, reconstructed 15C
  from the primary sources (verify_t5/t6 docstrings, logs, my
  OVERVIEW entries), re-deriving by hand E_rev's every firing and
  the engine arithmetic before writing. §17.0 records this.
- §17.1-17.9 checked against my verified record: E_rev mechanism
  (matches my hand-verification exactly), the general engine
  (firing analysis sound; the value-batteries subsume it), the size
  table (my corrected counts + Lane C's own tree counts re-run by
  me: 75/160/279 nodes, S-depth 4/5/6 = k+2 — a THIRD encoding,
  tighter than my 2k+1; both Theta(k)), P4'/Telescope statuses,
  consequences 1-5, and the in-place corrections (15.4, 15.5 status
  block, 16.3 addendum, 16.4 chain re-route).
- Lane A's correction of my OVERVIEW entry ACCEPTED and machine-
  verified by me: CH2's all-odd total is S(S-3)/2+3, not my
  transcribed 3+S(S-4)/2 (my entry now corrected in place).
- main.tex frontier (ssec:frontier) hand-checked: the refuted
  scoping claim is GONE; thm:separators now the general engine
  (repeats allowed, edge-guards, supersession of 15B), the E_rev
  mechanism paragraph, prop:vh resolved at h=0 with the winning
  engine correctly placed OUTSIDE the two-b-pattern class
  (Lane A's own self-caught over-claim, corrected), lem:structure
  with P4-refutation + P4' + skeleton status + finiteness note,
  prop:toll repositioned, and the closing paragraph relocating the
  frontier to varying separator count.
- ONE PRECISION ISSUE FOUND (not yet fixed by me at verification
  time): prop:toll's tail clause "no value whose length is not a
  function of S alone" overshoots its proof, which handles the six
  coordinate targets + affine L (the diagonal-counting paragraph
  scopes to affine). The partition's residue classes can in
  principle compute mod-constant values, so the universal reading
  is unproven and possibly false. FIX APPLIED BY ME: the tail now
  reads "no affine target whose length is not a function of S
  alone" (see below).

### Lane C (rev-try, round 16): THE UNIFICATION IS ARCHITECTURALLY IMPOSSIBLE — VERIFIED (architecture + positives; the two closing lemmas remain open)

- HEADLINE: no fixed expression computes rev on all of {a,b}* —
  delivered as a conditional architecture: Final-Pass Lemma PROVED
  by hand, the descent formulated with both escape routes killed
  on analysis, and exactly TWO formalization lemmas remaining (both
  assigned to Lane B's program): (1) the pinned-schema at varying k
  in its sharp form (every a-run of V(w^(k)) is an extraction
  tweak or a pinned affine alpha*S+beta from a finite V-fixed set,
  at top-O(depth) run-sizes only); (2) the tuning/deletion-rate
  lemma (each distinct deep run-size needs a flank tuned to that
  size; ~k depths need Omega(k) S-nodes). If both land, the
  conclusion is the full negative: rev not in L over ANY alphabet
  >= 2 — combined with Lane E's unbounded negative and the
  fixed-structure positives, the paper's open problem 2 closes as
  a DICHOTOMY theorem (C's proposed statement, §7 of its report).
- THE REFORMULATION: rev on {a,b}* = the MIRROR-PLANT — plant each
  b into the merge a^S at depth = its right-a-count. Every known
  reversing mechanism (E_rev, the engine, block-swap, phase-swap)
  buys plants; the question is whether a fixed DAG can buy
  unboundedly many.
- FINAL-PASS LEMMA (hand proof, scrutinized by me line by line):
  multi-fire (t >= 2) forces R single-b-or-pure (interior a-runs
  repeat at every firing vs the distinct powers-of-2 output runs);
  t <= 1 is a single splice the descent absorbs; so the reversal
  pre-exists in the scrutinee as an IN-ORDER EXTRACTION with
  uniform tweaks (same bites p0,p1 at every site — one pattern,
  one greedy). My scrutiny notes: (i) the proof is correct,
  including the b^m (m >= 2) exclusion by consecutive-b's;
  (ii) WRITEUP PRECISION: the tweaks include ADDITIVE contributions
  from R's flanks (a^{m1} b a^{m2} merges its flanks into adjacent
  remnant runs), not only subtractions — the finite tweak set is
  {-p0, -p1, +m1, +m2}; (iii) q_0 and q_t have only one bite each.
- ESCAPE A (stratified picks across copies) — real (C's own
  counterexample killed its first LDS invariant — the SAME class as
  my Lane-D finding; convergent discovery), but cannot build the
  reversal: kept pieces from different copies need pairwise
  disjoint value ranges, forcing R'-interior to contain deep
  distinct values as contiguous decreasing stretches — the descent
  recurses unchanged. ESCAPE B (phase carving) — killed by the
  deletion-rate/tuning argument (lemma 2). Both correctly labeled
  analysis, not proof; the quantitative conclusion (Omega(k)
  S-nodes on the super-increasing family) is CONJECTURE-GRADE
  pending lemma 2 — consistent with the engine's Theta(k) depth and
  Theta(k^2) size.
- POSITIVE BYPRODUCTS (my fresh encodings, hand-derived before
  reading C's script): E_block = [B/(X.b)]((X.b).mrg) computes rev
  on {a^i b^k} (skeleton separation — scrutinee literally begins
  with the pattern value; 15^2 grid + 500 random, all boundaries)
  VERIFIED; E_alt = [R/P]X with R = [eps/aa]X, P = [eps/aa][ba/ab]X
  computes rev on {(ab)^k aa, k >= 1} (phase swap; k=1..69 +
  pattern uniqueness) VERIFIED; L1/L2 collapse facts VERIFIED; the
  [X/'b']X and [X/a]X counterexample class VERIFIED (dec >= k at
  S-depth 2); FP uniform-bite spot-check [bab/aa]X VERIFIED.
- Battery reproduction: r16.log's script output BYTE-IDENTICAL
  (lines 9-27 are the appended think-pass narrative, recorded
  before machine work per the charter — the think-pass is genuine).
- Three letters do not help: the argument is alphabet-blind
  (run values + greedy mechanics); the dichotomy is by structure,
  not alphabet size.

## Lane B round 3 verification (verified 2026-09-22)

### Lane B (rev-split, round 3): the Telescope at varying k — VERIFIED

- THE CONVERGENCE: B independently PROVED the Final-Pass
  constraint (its Theorem FP: multi-fire t >= 2 + distinct
  positive runs => R has at most one b) from the counting side,
  machine-checking 4000 forced cases plus Lane C's E_rev (343/343
  correct reversals, top pass exactly t=1, R='b' — consistent with
  both proofs). Lane C's hand proof (round 16) and B's proof agree.
- THE MULTIVARIATE TELESCOPE (Theorem MT): (a) per-pass accounting
  N_out = N_F + c_w(N_R - N_P), M_out = M_F + c_w(M_R - M_P) is
  k-free; at each fixed k the ordered refinement is locally finite
  — the fixed-k machinery carries over with (S_a, k) in place of S.
  (b) MY CHARTER'S GUESS WAS FALSE as stated: totals are NOT
  functions of (S_a, k) — the ceiling-halver witness N =
  (S_a + nu)/2, nu = #odd runs, takes Theta(k) values at fixed
  (S_a, k) (census law machine-verified exact for k=1..7: ceil
  parity). The correct pinning is the RESIDUE-VECTOR; no
  k-uniformly-bounded finite partition exists. NOTE (my bridge to
  Lane C's lemma 1): the halver degeneration does NOT kill the
  pinned-schema on C's super-increasing family w^(k), where the
  residues are pinned by the family itself (one odd run, distinct
  powers) — the lemma must EXPLOIT the family's residue
  structure, not assert a general (S_a,k)-granularity.
- LEMMA SD (site distinctness): q >= 2 b's + positive interior =>
  at most one firing on distinct-run scrutinees (two windows would
  repeat the interior run sequence at two skeleton positions;
  distinctness forces coincidence, contradicting disjointness).
  Machine: 0 violations; controls show multi-firing is real off
  the hypothesis. Sharp both ways.
- THEOREM SB (SEPARATION BUDGET — the no-progress lemma,
  merge-free regime): Phi'(rev(w)) = k for every w in W_k;
  merge-free derivations satisfy Phi'(S(R,P,F)) <= Phi'(F) +
  Phi'(R) + 4 and Phi'(C) <= sum + 2 — the t firing junctions
  contribute at most 4 DISTINCT pairs (each pinned by one of R's
  four boundary-adjacent run labels) regardless of t; hence
  Phi'(E) <= 4#S(E) + 2#C(E). NO MERGE-FREE E COMPUTES rev FOR k
  BEYOND ITS SIZE. Machine: 2112/2112 (their run) + my re-runs all
  hold. Hand-scrutinized: the pinned-by-boundary-labels argument
  is sound; the tight constant is open (2#S+2#C held on all
  samples).
- POLLUTION WITNESS: E_poll = [(merge.b)/'aa']merge has Phi' = k
  with budget 8 (verified k=9,10) — merging is the unbounded
  flip-creating resource; flip-counting alone can NEVER prove the
  no-go. The obstruction must live in RUN-LENGTH EXACTNESS.
- LEMMA DECOMP: C-nodes partition the reversal into leaf intervals
  in reverse order; some leaf's subtree reverses an unbounded-
  separator interval with an S-node on top (X cannot). The
  unification question reduces to S-topped trees — where SD/FP/SB
  apply.
- TOLL AT VARYING k: the exclusions STRENGTHEN — per-k thresholds
  (S_a > N(k), N(k) finite per k) kill the union statement
  outright; the k-dependence enters only through the threshold.
  Conditional on the general-k profile write-out (skeleton status,
  same as round 2).
- TASK 4: Lane C's k-adaptive ops (D_last/D_first q=1 zero-
  interior; the S-domination flank pins single firing whatever k)
  verified IN CLOSED FORM on all 349,524 run-vectors for k=1..8
  including zero runs; concatenated scrutinees covered by P0; no
  new profile entry needed (one write-up action: F may be a
  concatenation node, stated explicitly).
- MY BATTERY (rev-split): rebuilt varying_k.c from source (cc
  -O2 -w), re-ran. OPS/CEN/FP modes: EXACT (deterministic; FP 4000
  cases 0 violations, E_rev 343/343). SD/SB case counts are
  seed-dependent: the default invocation (tr=400) gives 203/197/
  400/214; tr=4000 with fresh seeds gives their exact TOTAL
  1,755,621 checks 0 failures (5 seeds probed: 777111, 4242,
  20260922, 12345, 99991 — all 1,755,621/0). Their log's seed is
  unrecorded (bookkeeping slip #3 — same class as round 2's cells
  runs 2-3): per-mode counts differ slightly (2007 vs 2024 at
  seed 314159). VERDICT: VERIFIED with the invocation-unrecorded
  caveat; the 0-failure claim is over-reproduced. Told B to log
  the full invocation in the log header.
- OPEN CORE (now precise): can merging + q <= 1 patterns (the
  k-adaptive class) reverse unbounded k at fixed size/depth? Any
  unifier must merge input-run material on every input with
  k > 4#S + 2#C; order-inversion is cheap in the mergey regime
  (E_poll) — the obstruction must be merge-sensitive and live in
  run-length exactness. This is the merge-sensitive budget
  program (B's next round) + the tuning lemma (Lane C's lemma 2 /
  Lane D's selectivity).

### Program status after round 3 of all lanes

The endgame is now sharply located. PROVED: FP (two independent
proofs + machines), SD, SB (merge-free no-go), DECOMP, MT(a), the
toll's strengthening at varying k (skeleton), the positive
byproducts (E_block, E_alt), and the fixed-structure dichotomy
positive half. CONDITIONAL ARCHITECTURE: the full unification
impossibility (Lane C round 16) rests on exactly two lemmas: the
pinned-schema at varying k in sharp form (on w^(k), exploiting the
family's residue structure per my bridge note above) and the
tuning/deletion-rate lemma (merge-sensitive per B's finding). The
mergey regime is where E_rev itself lives — the no-go must work
THERE, which is why SB alone cannot finish it. Next round: B takes
the merge-sensitive budget; D takes the tuning lemma from the
selectivity side; C writes the FP/descent LaTeX + illustrates; A
integrates rounds 16-18 (C16, B3, D2) with the conditional status
labeled.

## Lane A round 5 verification (verified 2026-09-22)

- Build reproduced: 89 pages, 0 errors, 0 overfull, 0 non-font
  undefined mentions. thm:dichotomy ("The Reversal Dichotomy",
  p. 74) hand-checked: part (i) fixed-structure positive, part (ii)
  "Conditional on the two structure lemmas of the paragraph below"
  with the effective bound k > f(|E|) — the conditionality is
  unmistakable and part of the statement; part (iii) unbounded
  negative. The proof cites parts and states the conditional
  status; the machine-backdrop parenthetical's numbers all match
  the record (990/990 + 765/765 SNF; 4000 + 343/343 FP; 2112 +
  pollution SB; 1,747,600 / 349,524 task 4).
- The architecture paragraph is accurate: SNF -> Final-Pass Lemma
  (proved twice, attributed to both sides) -> descent with both
  escape kills marked at their analysis grade -> separation budget
  closing the merge-free regime -> pollution witness -> the
  obstruction located in the mergey regime + run-length
  exactness. Both named lemmas stated exactly, with my residue-
  bridge note folded in correctly.
- The integration hook for Lane C's dichotomy.tex is a comment
  (not \input, not referenced) — correct per charter. My toll
  patch survives verbatim. The 293,307 -> 293,507 fix applied at
  17.2/17.6. Wire-ins (landscape 2196, alphabet intro 2251,
  conclusion 3004) all carry the sharpened status accurately.
- ONE CLAIM EXTENDED BY MY VERIFICATION: part (i) says the
  laundering is "verified with the engine, k <= 5" — the record
  had laundering at k=2 (my round-17 battery) and k=3 (t6). I
  machine-verified the FULL-ALPHABET laundering composition at
  k=3 ('bbb', 'bcb'), k=4 ('bbbb'), k=5 ('cbccb'): value = rev
  and prov == () on 100 cases each — ALL VERIFIED. The claim now
  stands with a complete verification basis. (Note for the
  record: my first attempt REFUTED because I laundered only the
  separator letters — the filler 'a' atoms carry input
  provenance too; the laundering must cover every letter of the
  alphabet. My test bug, not the paper's.)

## Lane B round 4, Lane C round 17, Lane D round 3 verification (verified 2026-09-22)

### Lane B (rev-split, round 4): L1 REFUTED as stated, repaired to L1''; the merge-sensitive budget — VERIFIED

- L1-as-stated (tweak-or-finite-affine) is REFUTED by two fixed
  expressions from the engine's own mechanisms: E_leak =
  [(mrg.b)/'b']X with runs exactly (S+2^0, ..., S+2^{k-1}, 2^k), and
  E_prod = [mrg/'aa']X with runs exactly (1, S, 2S, ..., S*2^{k-1}).
  MY FRESH-ENCODING VERIFICATION: exact run equalities k=1..10 both;
  non-classification reasoned and checked (tweak-distance 2^j-1
  grows; affine fails since alpha=1 forces beta=2^j).
- THE REPAIR (L1''): the P4'-closure form on w^(k) — every a-run is
  in the closure of {site terms 2^t, S, constants} under +, -, x by
  pinned counts, with the TERM LEDGER M_V <= #S(E)+O(1) (skeleton:
  consecutive-complete supports collapse; S-nodes add O(1) irregular
  references via SD; replication copies supports but per-run
  multisets stay bounded). Residue bridge confirmed (the family pins
  its own residues; MT(b) does not bite). Machine: 9-expression
  exact battery + 40,896/40,896 random compositions fully classified
  (100%, bounded-output cap disclosed). Skeleton status for the
  write-out, honestly labeled.
- MERGE-SENSITIVE BUDGET delivered: stratum-1 (SB reinforced:
  7,381 more merge-free derivations, zero violations of even
  2#S+2#C); stratum-2 per-node identity Phi' <= Phi'(F)+Phi'(R)+4+MJ
  (4359+4436 node identities, 2686+2668 tree totals, E_poll's MJ
  values); the PAYMENT THEOREM (surviving mergey flips must be
  stripped by downstream exact deep cuts priced by the tuning
  constraint; the replication deferral closed by C's Escape-A kill).
  COROLLARY (conditional on L2): k <= 4#S+2#C+C'(#tuned deep cuts)
  = O(|E|). The architecture now interfaces through ONE quantity:
  THE DEEP-CUT COUNT.
- Battery reproduction: rebuilt from source; all logged invocations
  reproduce (104 checks/0 failures both seeds; class modes 17,792 +
  17,753 at seeds 12345/99991, trials 20000; the four seeds' counts
  sum EXACTLY to 40,896). The 512-array overrun harness bug was
  disclosed and fixed pre-delivery (the "58 unclassified explosive
  nestings" were ASLR stack garbage; print-only path; no ck() check
  affected) — my reproduction confirms 100% classification.
  INVOCATION DISCIPLINE now applied (first line of every log).
- CONSEQUENCE FOR THE PAPER: the two-lemma paragraph after
  thm:dichotomy stated L1 in the refuted form — conditioning on a
  falsehood. I PATCHED main.tex MYSELF (the closure form + term
  ledger + the two witnesses + the site-term refinement of L2),
  sourced from B's verified report; build re-verified 89 pages,
  0 errors, 0 overfull.

### Lane C (rev-try, round 17): the dichotomy fragment + tuning illustration — VERIFIED (fragment needs revision)

- dichotomy.tex (12 dich:-labels) checked: SNF, FP merged with BOTH
  proofs credited, the FP(ii) STRENGTHENING (termwise per-gap
  accounting with single-b pattern AND replacement — separator count
  preserved; shift set {0, -p0+a1, -p1+a2, -p0-p1+a1+a2}) — I
  hand-scrutinized the per-gap argument and it is sound, and the
  battery anchors EVERY case (8 inputs x 256 passes + 384 pure-a
  passes: reconstruction == evaluator). SD/SB/DECOMP restated with
  attribution; escapeA/escapeB as Status: analysis propositions;
  dich:thm:main with the LINEAR effective bound k+1 <= c#S + c'
  (tight against the engine's Theta(k)); dich:thm:dichotomy with
  (ii) conditional.
- verify_r17_tuning.py reproduces (r17.log script output identical;
  diff = appended narrative only; the honest 60s-overrun-then-fixed
  note and the stale-k artifact note are in the log). Part B is a
  GENUINE STRENGTHENING: fully-consumed values are always a subset of
  {p0, p1, p0+p1} — at most TWO deep sizes per flank pattern on the
  powers; part C isolates the engine's catalysis (pinned flanks fire
  only at merge-flanked/top separators, 12/12, zero deep); part D:
  (2^j,2^j) covers {2^j,2^{j+1}} so >= ceil((k-1)/2) patterns.
- BUT the fragment's dich:L1 is the REFUTED form (B's round 4 landed
  mid-round), and its staging family is B=2 (D's round 3 finding,
  below). REVISION REQUIRED — charter sent.

### Lane D (rev-wall, round 3): the B=2 DEGENERACY + L2's proved core — VERIFIED

- THE B=2 DEGENERACY (major, machine-verified 65 checks 0 failures;
  all six re-verified by me with fresh encodings, k=0..11): the
  staging family w^(k) (base 2) is the BOUNDARY of super-increase
  (2^j = Sum_{i<j} 2^i + 1) and TELESCOPES: E_last = [eps/b][a/aa]X
  = a^{2^k} (THE LAST RUN, b-free, S-depth 2!); E_cbox =
  [b/(E_last.b)](mrg.b.mrg) = a^{2^k-1} b a^S; E_smm =
  [eps/(b.mrg)]E_cbox = a^{2^k-1} (B-FREE SUM-MINUS-MAX); E_h2 =
  [a/aa]E_smm = a^{2^{k-1}}; [eps/b][aa/a]X = a^{2^{k+2}-2};
  del_last glues 2^{k-1}+2^k. Consequences: V1/V2 REFUTED on B=2
  (they STAND on B >= 3 — gap verified by me for k=5..14, past the
  documented small-k coincidences); the arithmetic fixed point is
  FALSE on B=2 (both r_k and S-r_k reachable in O(1) depth); C's
  pinned-schema ask survives IN FORM (E_last hits each fixed depth j
  only once) but no extraction-impossibility argument is available
  on B=2. RECOMMENDATION (adopted): migrate the staging family to
  B >= 3. Uniform rev on the B=2 family: still NOT found (4
  structured attempts fail at k=2,3,4).
- L2's PROVED CORE: L2.1 SLOPE-PINNING (exact re-separations need
  interval sums Sum_[u..v] B^i = alpha*S + err, alpha = B^{v-k},
  |err| <= (B^u-1)/(B-1) — exact cuts at top-offset d require dyadic
  slope B^{-d}; tweak channel covers only O(1) offsets from an end;
  pairwise distinct, power-separated on B >= 3) — arithmetic
  hand-checked by me. L2.2 PER-NODE SUPPLY <= 4, UNCONDITIONAL
  (each firing cuts only at its window's two ends with the SAME
  amounts; interior pattern runs are DEMANDS by Match Anchoring) —
  the argument I independently sketched earlier; sound. L2.3 demand
  interface: the [X/a]X class supplies VALUES cheaply but not
  DELETIONS; exactness forces the deletion work — where the tuned
  cuts are demanded. Composition #S = Omega(k) conditional on the
  same two lemmas.
- Battery: tuning_fixA.py BYTE-IDENTICAL; tuning_check.py
  reproduces (timing jitter only). Part C: 168 instrumented
  expressions, 56 exactness events all tweak-class, zero
  middle-interval bites, 0 evaluator mismatches. Honest ledger
  accurate throughout (including the process note: three wrong hand
  derivations machine-falsified before being written anywhere).
- MY DIAGNOSTIC NOTES (recorded for honesty): my first B=3 battery
  had two REFUTED results — both MY bugs: (i) the gap check demanded
  no hits at k=1, where the documented coincidence sits (E_last on
  B=3, k=1: (S+2)/2 = 3 = 3^1); (ii) I generalized E_prod's B=2
  formula to B=3 naively (odd runs tile as (aa)^{(3^j-1)/2}a, giving
  runs S*(3^j-1)/2+1 — my derived closed form then VERIFIED k=1..7,
  still refuting L1-as-stated on B=3). Also: I nearly flagged D's
  message as having a pattern typo — MY convention slip ([a/aa] is
  the halver: left = replacement, right = pattern; D was correct).
  E_leak verified by me on B=3 too (runs (S+3^j, ..., 3^k), k=1..8):
  B's witnesses refute L1-as-stated on BOTH staging families.

### Program status (updated)

The staging family migrates to B >= 3 (strongly super-increasing;
nothing is lost — it is still a subfamily of {a,b}*). On B >= 3:
FP PROVED (twice), SD/SB/DECOMP PROVED, L2.1+L2.2 PROVED (supply
side), L1'' machine-supported (write-out pending = B's term ledger),
the Payment theorem hand-proved (B), the descent/demand composition
analysis-grade (C+D). The two lemmas of the conditional theorem are
now: (1) L1'' write-out (term ledger on B >= 3); (2) the demand-side
descent formalization. The B=2 family becomes a recorded curiosity
(the telescoping boundary: extraction is free there) and an open
positive question (uniform rev on it: unknown, 4 attempts failed).

## Lane C round 18 verification — the fragment revision (B>=3, L1'', L2 restructure) (verified 2026-09-22)

VERDICT: ACCEPTED. The revision is complete and integration-ready; my
verification found nothing needing correction.

- Battery: verify_r18_migration.py re-run by me (exit 0), script
  output BYTE-IDENTICAL (diff = invocation first line + appended
  narrative only). All five sections VERIFIED: A3 FP tweak sets on
  D(k;3) k=4..6; B3 exact tuning (fully-consumed subset of
  {p0,p1,p0+p1}, caps 2 on the powers); C3 pinned flanks (12/12 top
  firings, zero deep); D3 counting corollary (>= ceil((k-1)/2)
  patterns, k=4..8); E2 the seven B=2 witnesses re-anchored.
- dich:lem:flankcap hand-scrutinized: flank pattern a^{p0} b a^{p1}
  fully consumes only gaps in {p0, p1, p0+p1} (FP window accounting:
  a gap is bitten only by its two adjacent windows, in amounts p1 and
  p0); at most two of the three are powers of 3 (3^a+3^b =
  3^a(1+3^{b-a}), 1+3^d not divisible by 3). Sound; the B3 section
  is its machine core.
- dich:prop:boundary: all five B=2 constructions re-derived BY HAND
  by me ([eps/b][aa/a]X = a^{2S} = a^{2^{k+2}-2}; E_cbox's window at
  the lone b of mrg b mrg leaves a^{S-2^k} b a^S = a^{2^k-1} b a^S;
  E_smm; E_h2 = halver on 2^k-1 gives ceil = 2^{k-1}) — all match
  the verified round-3 record; k=5..14 gap check is mine; the four
  failed B=2 uniform attempts and attribution lines accurate.
- dich:L1 = the closure form L1'' + term ledger, statuses accurate
  (machine-supported; write-out in flight). E_leak/E_prod constants
  match my verified closed forms exactly, including E_prod's B=3
  form S*(3^j-1)/2+1 and E_leak's B=3 runs (S+3^j, ..., 3^k).
- dich:L2 = restructured per the charter: proved supply lemmas
  (L2.1, L2.2, flankcap) restated with correct attribution; the
  demand side is the one remaining assumption (Lane D, in flight).
- Escape A/B and dich:thm:main's sketch re-derived WITHOUT
  extraction-impossibility, exactly the charter's route: FP -> SD
  -> SB -> PAYMENT -> slope-pinned supply (<= 4 per node, <= 2 deep
  sizes per flank pattern, dyadic slope 3^{-d}) -> demand. Escape B
  now uses L1'' (padded and degree->=2 product flanks are top-scale,
  cannot partially carve a deep run; partial carving confined to
  constant/tweak flanks, off-target by the mod-3 argument; the
  tuning unit is the site term, ledger M_V per run). The merge-
  catalyzed deletion disclosure retained. The final count k <=
  4#S+2#C+C'c#S is linear in the pass count; the tightness remark
  matches the engine (Theta(k) pass depth, Theta(k^2) size).
- PAYMENT restatement: machine stats correct (4,359+4,436 nodes,
  2,686+2,668 derivations, MJ non-vacuous); the final inequality is
  honestly marked conditional on the demand assumption.
- COMPILE CLAIM REPRODUCED BY ME: wrapper in the paper's exact class
  preamble (llncs, amsmath, amssymb, enumerate, mathpartir,
  stmaryrd, hyperref, the remark/proof patches) built twice with
  pdflatex: 0 errors, 0 undefined references, 0 overfull boxes,
  0 warnings, 9 pages — exactly as claimed.

## Lane D round 4 verification — the demand-side composition (verified 2026-09-22)

VERDICT: ACCEPTED WITH ONE CORRECTION — D1''s status is downgraded
from "PROVED" to "machine-supported, proof incomplete" (the gap is
precise and does not sink the round; the composition uses D1''
only supportively — the plant counting carries Omega(m)).

- Battery: demand_check.py re-run by me, exit 0, output identical
  except timing jitter (0.1s marks). DISCIPLINE SLIP (mild): the
  log's first line is NOT the full invocation (the rule instituted
  after B's round-3 bookkeeping). Recovered by me: default
  invocation, cwd rev-wall/, reproduces. Required going forward.
- My fresh tagged evaluator (route-list + leaf encoding, distinct
  from D's head-prepend encoding): coord_r4_check.py /
  coord_r4_check.log.
- D1: proof sound (FU position-flow induction over the tree; SNF
  remnant order + C concatenation + X identity + K fresh). Machine
  replay with MY evaluator: 300 exprs, 1594 node-checks, 0
  violations — exact match. Skip classification: all 98 skips are
  Undefined-class (empty patterns), 0 Bail, 0 top-mismatches, 0
  PER-NODE mismatches (D's code silently skipped node mismatches,
  so their "0 mismatches" claim was not directly evidenced by the
  log; my instrumentation confirms it).
- Engine autopsy: every constant recomputed by hand AND by my fresh
  evaluator — tree S-nodes 50 (k=4) / 77 (k=5) (my hand count: each
  del = 3 S-nodes with the inlined mrg, D_m = 12/15, T = 48/75,
  +2 wrap; NOTE these are TREE counts with mrg inlined — my 15C
  k^2+k+1 was the DAG count, no contradiction); walks [9,9,9,9] /
  [12 x5] = 3(k-1) per junction; plants [81,108,117,120] =
  top-anchored sums (hand: 81, 108=81+27, 117=+9, 120=+3; S=121);
  routing depths [1,1,1,1]; T1 labels = [k], T2=0, T3=1 at k=2..5;
  S - prefix-sum = 3^k (121-40=81 at k=4).
- D1'': THE CORRECTION. D's two-line proof is INCOMPLETE: D1 gives
  NON-DECREASING labels along the output; with the slice bound
  lambda_m >= k-m (output run m has value 3^{k-m} <= 3^lambda_m)
  and per-label exhaustion (total slice length at one label <=
  3^lambda), multi-label assignments remain possible — e.g. at
  k=4: run 1 = full input run 3 (27=3^3), runs 2-4 = slices of run
  4 (9+3+1 <= 81) gives labels {3,4}, consistent with every
  constraint I can derive. My probe: 4000 single-constant mutants
  of the k=2 engine, 537 rev-true, ZERO multi-label; engine
  one-label at k=2..4; 20000 random vocabulary compositions, 0
  rev-true (space too hard to hit randomly — the probe has limited
  power). No counterexample, no proof: status = machine-supported,
  proof open. What IS proved: non-decreasing labels + slice bound
  + exhaustion ("D1''-weak").
- OL-1 (match-exactness) and OL-2 (interior-anchor supply): well-
  formed, correctly located; OL-2 rightly identified as the piece
  that is FALSE on B=2 (where the family distinction enters).
- The conditional theorem's shape is unchanged: #S = Omega(m) on
  D(k;3) conditional on OL-1 + OL-2 (+ B's TL and Payment as
  inputs). D1''-weak suffices for the T1-channel role in the
  composition as far as I can trace it (the plants carry the
  count), but the honest record states D1'' as open.

## Lane B round 5 verification — the term-ledger write-out (TL) (verified 2026-09-22)

VERDICT: ACCEPTED. TL is delivered at proof altitude conditional on
ONE precisely-located piece (Lemma PO's general case); the two
corrections are real, machine-witnessed, and independently
hand-derived and re-verified by me.

- Machine: ledger3.c rebuilt by me (cc -O2), all four invocations
  reproduced — seed 271828 (all) BYTE-IDENTICAL (293 checks, 0
  failures), seed 314159 (all) byte-identical, plus the two extended
  runs (ledger 3000, ba3 3000) reproduced. Invocation lines present
  in every log (discipline held).
- C1 (k-affine junk stratum): hand-derived by me BEFORE reading the
  machine (halver on odd 3^j gives ceil = (3^j+1)/2; sum = (S+k+1)/2)
  and fresh-encoded: [eps/b][a/aa]X on D(k;3) = a^{(S+k+1)/2},
  k=1..8 ALL OK. The B=2 side: [a/'aaa']X runs = (2^j+2)/3 [j even],
  (2^j+4)/3 [j odd] — my own derivation matched the report exactly;
  fresh-encoded j=0..12 ALL OK. These values are non-dyadic and
  outside round 4's alpha-family: the correction is genuine, and the
  disclosure that round 4's battery let them through its junk window
  at k <= 9 is honest.
- C2 (rational slopes): the /3-denominator instances machine-checked
  (my battery); the strengthened supply/demand mismatch (non-dyadic
  supply never equals dyadic demand, s nmid 3^Delta * 2^d) is a sound
  cross-multiplication argument.
- BA correction: E_prod's last run on B=3 = 1 + floor(3^k/2)*S
  fresh-encoded k=1..6 OK (with interior runs S*(3^j-1)/2+1 re-
  confirmed) — the count-times-S product class is genuinely missing
  from round 4's three classes; the corrected boundary statement
  (<= 2 anchored terms, never middle-depth) is the right form.
- E_cbox/E_smm on B=3 = (S-k-1)/2 family: fresh-encoded k=1..6 OK;
  E_last on B=2 = a^{2^k} = (S+1)/2 re-confirmed k=0..8 (the six
  constructions classify on B=2 in the closure).
- My fresh-encoding battery: coord_b5_check.py / coord_b5_check.log
  (54 checks, 0 failures).
- Proof scrutiny (report section 2): GLUE's case split is the
  verified FU-calculus run algebra; the interval-sum invariant
  (INV1/INV2, budgets add over disjoint subtrees, C-seams/bites/
  remainders collecting into one V-fixed junk element) is clean and
  the disjointness accounting is the right shape; COLLECT generates
  both corrections (I verified its instances); the honest c <= 8
  coefficient note is correct to surface (O(#S) suffices for the
  Omega(k) application). PO's gap is precisely located (position
  pinning vs count pinning for multi-b patterns on replicated
  scrutinees).
- Disclosures verified as accurate: the [spec] caveat (no
  classifier specificity at k <= 8; the load-bearing verification
  is forms + identities + proof), the atoms-vs-terms lesson, the
  [b/ab] hand-form catch, the two discarded classifier designs.

### Program status (updated)

The pinned schema on B >= 3: TL (B5, conditional on PO) + L2.1/L2.2
(proved) + flankcap (proved) + Payment (proved) + SB/DECOMP (proved).
The dichotomy's part (ii) residue is now THREE named pieces, all
located: PO (B's lane — the write-out; B round 6 chartered), OL-1
match-exactness (Lane C's part-B machinery — after C19 lands), OL-2
interior-anchor supply (Lane D round 5, in flight). The paper's
two-lemma paragraph needs the B5 corrections at integration: the
k-affine junk stratum, the rational denominators, the c*#S+O(1)
coefficient, and the BA count-times-S class.

## Lane C round 19 verification — the B=2 uniform-rev side quest (verified 2026-09-22)

VERDICT: ACCEPTED. NEGATIVE (architectural): the offset-cost
ceiling. The boundary family does not cross the no-go.

- Battery: verify_r19_b2rev.py re-run by me from rev/ (exit 0); the
  final run's content lines byte-identical (diff = the narrative
  re-run header + the timing footer format; wall 2.05 s exact). The
  delivered r19.log honestly contains the two intermediate REFUTED
  runs (the jumpdown hand-derivation corrected; the depth-list
  comparison fixed to order-reversing) — good process.
- My charter's plant-depth identity: substance correct, my INDEXING
  SLIP caught by Lane C (separator m sits at left-depth 2^{m+1}-1 =
  the run it PRECEDES minus one; the mirror is ORDER-REVERSING:
  rev's separator j at right-depth 2^{k-j}-1 = w's separator k-1-j
  left-depth). Their restatement is right; my fresh encoding
  confirms it (after I fixed MY OWN mirror check, which repeated
  their first bug exactly — left-depths of the reversed string
  instead of right-depths; the fix rd = S - left-count).
- JUMPDOWN closed form independently re-derived by me from first
  principles BEFORE reading their correction: each interior run j
  (i<j<k) is DOUBLE-BITTEN (2^i at each end), so T = Sum_{j=i+1}^{k-1}
  (2^j - 2^{i+1}) + (2^k - 2^i) = 2^{k+1} - 2^i - (k-i)*2^{i+1} —
  matches their corrected form exactly; and the two forms coincide
  at k=i+2 (both 3*2^i), confirming their small-k-coincidence
  explanation for the initial error.
- My fresh-encoding battery coord_r19_check.py / coord_r19_check.log
  (0 failures): halver self-similarity [a/aa]X = 'ab'.w^{k-1};
  STEPDOWN + chains (w^{k-1}/w^{k-2}/w^{k-3}); JUMPDOWN i=0..3,
  k=i+1..10; SCALER (one-pass gap scaling by 2^k via computed
  replacement — the round's surprise, verified k=0..7); DIVIDER
  (threshold division, k=1..10); LADDER (1,3,...,2^k-1,2^{k+1} in
  two passes) + the bonus identity halver(ladder) = w^k; BOTH +/-S
  round trips back to w^k (padding is order-preserving — the
  pad-then-strip route is dead); the recursion facts both
  directions k=1..8; the mirror; the rotation threshold k<=2.
- The autopsy of the four attempts and the two analysis-grade halves
  (the order/stream barrier; the offset-cost ceiling) read and
  hand-scrutinized: the stream argument (remnant order + one gap per
  in-order stream + the descending middle forces isolation) and the
  census (deepest lone near-power at end-distance 2 in a 27-expression
  depth<=6 battery) are coherent and correctly graded as analysis.
  The formalization target (B=2 offset-cost lemma: a lone gap 2^j+O(1)
  costs Theta(min(j,k-j)) passes) is well-posed via the B=2 ledger
  instance.
- Bottom line verified: at B=2 every VALUE is cheap (the degeneracy)
  but the ORDER is priced — the reversal needs the middle offsets,
  Theta(k) from both free ends. The dichotomy's linear f(|E|)
  survives the boundary intact; the B=2 family remains open but is
  now census-backed as obstructed.

## Lane D round 5 verification — D1'' resolved + OL-2 (verified 2026-09-22)

VERDICT: ACCEPTED WITH ONE CORRECTION — the fired-set lemma's part
(i) is FALSE AS STATED (two-flank counterexamples, machine-confirmed
by me); the correct statement (skip-after-bite) is what their Step-4
use needs, and that use SURVIVES. Everything else verified.

- Battery: ol2_check.py re-run by me — BYTE-IDENTICAL, invocation
  first line present (discipline fixed from round 4).
- The MOD-3 LEMMA hand-verified by me (with t 0-indexed 0..k-1:
  TopSum(t) = Sum_{s=k-t..k} 3^s has s >= 1, so 0 mod 3; BotSum
  (sigma) contains 3^0, so 1 mod 3; tables re-verified). The
  T1-trace conclusion is sound: no input b sits at a plant position
  undisplaced; the plants/gaps carry the T1-channel demand through
  the OL-1 channel INDEPENDENTLY of F-pure labels — this is a clean
  resolution of the D1'' gap in the composition, and the round-4
  corollary's withdrawal is correctly scoped (nothing else used the
  strong form).
- E1 fresh-encoded and hand-traced: pattern = input minus its last
  a, replacement = rev minus its last a — ONE splice, output
  a^9 b a^3 b a = rev(D(2;3)) ✓; exactly one F-pure run (the last
  atom, from the top run) ✓. E2 runs (9,11,9) ✓ (the glue damage).
  D1''-strong honestly OPEN (my k=4 consistency example unrealized;
  no refutation).
- THE CORRECTION (fired-set lemma (i)): "a single-b pattern fires
  at a SUFFIX" is FALSE for TWO-FLANK patterns — my machine probe
  (coord_r5_check.py): [eps/a^3 b a^9]X on D(4;3) fires at {1,3};
  [eps/a b a^3]X fires at {0,2,3}; at k=5, {1,3,4} — non-suffix,
  not even suffix-containing (the window at junction 1 consumes all
  of run 2, so junction 2 cannot fit). Their A1 battery covered
  only ONE-FLANK patterns (a^i b, b a^i, i=0..40) where the suffix
  property GENUINELY holds (my re-run: 0 non-suffix over k=2..5).
  The correct general statement — SKIP-AFTER-BITE — holds in my
  probe (0 violations, k=3..5 x i<=9 x j<=27): every skipped
  junction immediately follows a firing, and the consequence the
  composition needs (NO single-b pass deletes exactly a proper
  prefix {0..m-1}) SURVIVES (0 violations; the resumption argument:
  after a skip the next junction has a full run before it and fits).
  The lemma must be restated + the A1 battery extended; the round's
  Step-4 use is unaffected.
- The bonus construction [eps/b][aa/aaa]X = a^{3^k} hand-derived by
  me (run j>=1 -> 2*3^{j-1}, run 0 untouched, merge = 1 + 2*Sum
  3^{j-1} = 3^k) and machine-verified k=1..6 — the B=3 analog of
  E_last; ends free at depth 2; a genuine TL(iii) datapoint.
- The L_m tightness runs (1,120),(4,117),(13,108),(40,81) verified
  = the (BotSum(m), TopSum(k-m-1)) pairs.
- OL-2's five steps read and scrutinized; grades honest (analysis
  grade conditional on TL; Step-4 bookkeeping and Step-5 termination
  precisely located as the write-out pieces). The psi-descent gap
  phenomenon (no chain value an exact power) machine-checked by them
  (part C) and consistent with my round-3 record.

## Lane B round 6 verification — PO closed; TL unconditional; the recurrence battery (verified 2026-09-22)

VERDICT: ACCEPTED. PO is proved; TL is unconditional (with INV4's
bookkeeping at case-analysis altitude, honestly graded); the
recurrence battery is built, calibrated, and measured.

- Machine: po_rec.c rebuilt by me (cc -O2), both seeds BYTE-IDENTICAL
  past the invocation line (22 checks, 0 failures, 1.7 s / 2.5 s);
  invocation discipline held. The six disclosed development bugs
  (two array smashes, the silent zero-controls bug, the POL cap
  truncation, the early-exit, the replica first-check) are exactly
  the right process record.
- PO-1 (window anatomy): proof hand-scrutinized and SOUND — the
  consecutive-b-stretch argument (no T-b can lie strictly between
  the matched b's; interiors match exactly; the head bite is c_0 BY
  CONSTRUCTION) is the circularity-breaker, and the observation that
  the value induction needs only bites + span ranges + fired counts
  is correct. My fresh encoding (coord_b6_check.py): random
  multi-b windows on D(k;3) plus bitten/merged texts — consecutive
  b's, exact interiors, bites = the pattern's own boundary runs:
  0 violations (after fixing MY check's boundary bug: j <= pos for
  c_0 = 0 windows, where the window starts with the matched b).
- EPT: proof hand-scrutinized — the dominance/cancellation induction
  on the super-increasing base is the standard exponential-polynomial
  argument correctly adapted; my ord_p(3) spot checks (ord_7 = 6,
  ord_5 = 4, ord_13 = 3) confirm the period arithmetic the battery
  and the residue machinery lean on.
- Replica structure fresh-encoded: the junction runs on T =
  [X/'b']X are 2 (copy 0: r_0 + copy head) and 3^k + 3^c + 1 for
  c >= 1 (copy c-1's tail + r_c + copy c's head) — my derivation,
  machine-confirmed. ONE MINOR REPORT-TEXT SLIP: the parenthetical
  "(the run before copy c's separator 0 is 3^c + 1)" is correct only
  for c = 0; for c >= 1 it is 3^k + 3^c + 1. No tested claim is
  affected (the c_0 = 3, 4 thresholds only need copy 0's junction =
  2). Their threshold patterns fresh-encoded by me: copy 0 fails,
  k-1 fire, k=4..7 — matches their 24/24 exactly.
- The recurrence battery: the theory (per slot/cell, v(k) =
  Sum A_d 3^{dk} + (ak+b), annihilated by (x-1)^a prod (x^{L_d} -
  3^{d L_d})) is the right machine-facing corollary; the honest
  charter correction (order counts degree families — a LOWER-BOUND
  probe of M_V) is accurate; the calibration story (the mineq=1
  order-12/2-equation coincidence on the period-7 adversarial,
  hand-verified and priced in) is exemplary; the measured teeth
  (0/8 spurious at BOTH regimes; 7/7 controls with correct minimal
  polys; k^2+7 REJECTED — C1's affine-junk stratum machine-enforced;
  417 comps, 6 sig leads all hand-dispositioned) all reproduce in
  the byte-identical log.
- Grades verified as accurate: PO-1/EPT/PO-3/PO-4 full altitude;
  INV4 case-analysis altitude (the one notch — B round 7's target);
  PO-3(c) phase table by finiteness.

### Program status (updated)

TL IS UNCONDITIONAL (modulo INV4's altitude notch). The endgame
residue after this round: OL-1 (Lane C round 20, in flight), the
OL-2 write-outs (Lane D round 6, landed — being verified), and
INV4's bookkeeping (B round 7). Lane D's round-6 report (landed)
claims OL-2 at "proved conditional on TL + S4.3-general" with
S4.3-general the single remaining piece.

## Lane D round 6 verification — FSL' + the OL-2 write-outs (verified 2026-09-22)

VERDICT: ACCEPTED. All three charter tasks landed at the claimed
grades; my fresh encodings confirm every witness.

- Battery: fsl6_check.py re-run by me — BYTE-IDENTICAL, invocation
  first line. The disclosed first-run crash (index-list as array)
  and the round-5 B1 gap closure (COR-B now covers ALL single-b)
  are the right process record.
- The RECURSION THEOREM hand-verified (the scan mechanics closed
  form: fire_sigma iff c_sigma >= i and R_{sigma+1} >= j, with
  c_{sigma+1} = R_{sigma+1} - j*[fire_sigma] — the left bite stays
  in run sigma's remnant and never affects later junctions) and
  fresh-encoded: 600 random two-flank cases on D(k;3),
  suffix-merged, psi-mapped AND bitten texts — 0 mismatches vs
  direct greedy.
- COR-A's cascade proof hand-scrutinized (including the sharp
  m = k-1 inequality R_{k-1} < i+j <= R_0+R_1 < 3^k <= R_{k-1}
  and its coarsening version); COR-B/COR-B1 fresh-encodd: the
  k=2 prefix exception [eps/a.b.a^3]X = {b_0}; the k=3 resumption
  {0,2}; the size-1 interior {1} at j = 9 with the j = 7,8
  boundaries {1,2}; the COR-A/B sweeps k=3..5 x i,j<=12: zero
  clean prefixes, zero interior blocks. SKIP-AFTER-BITE +
  RESUMPTION confirmed as my round-5 probe found them.
- The CLASS-ESCAPE lemma read and hand-scrutinized: the boost pad
  a^{S+1} makes run 0 the maximum, turning the one-flank threshold
  set into the PREFIX {0} — the controlled break of the
  increasing-run class, one junction per escape, increase restored
  (Sum_[0..t] < 3^{t+1}). Sound — and the right account of why
  COR-A's exclusions live on the class.
- The BLOB LANDING hand-derived by me BEFORE reading their machine
  (S = Sum_{s>m} 3^s + Sum_{[0..m]} = 3^{m+1}*(3^{k-m}-1)/2 +
  Sum_{[0..m]}, so [eps/a^{3^{m+1}}][eps/b]X = a^{Sum_[0..m]}
  EXACTLY — the deletion map U -> U mod p lands where the psi-map
  cannot) and fresh-encoded m=0..4 at k=6. The correction of
  round-5's gap-phenomenon reading is genuine and right.
- MASS fresh-encoded (p=1..40 on D(6;3): suffix-or-empty, never
  small-dead-larger-alive — 0 violations); E2 prefix isolation
  ([eps/a^{3^{t+1}}]X = D(t;3).b^{k-t}, t=0..4) and E5 halver gap
  ((3^{m+1}+1)/2 = Sum_[0..m] + 1, m=0..4) both hand-derived and
  fresh-encoded.
- S4.1-S4.6 + R6.2 read and hand-scrutinized: the assembly is
  coherent, the regimes honestly bounded (clean vs correction), and
  the grades accurate. One cosmetic note: the recursion theorem's
  phrase "the window consumes the last c_sigma atoms" is loose
  (it consumes the last i; the remaining c_sigma - i stay as
  remnant) — the formula and all uses are correct.

### Program status (updated)

OL-2 stands at PROVED CONDITIONAL ON TL (= PO, now unconditional
modulo INV4's altitude notch) + S4.3-general — ONE named piece,
the compensation/lucky-sum channel. OL-1 (Lane C round 20) has
landed and is next to be verified. The endgame residue after this
wave: S4.3-general (Lane D round 7), OL-1's located gap (Lane C
round 21), INV4 altitude (Lane B round 7, in flight).

## Lane C round 20 (OL-1 match-exactness) — VERIFIED, ACCEPTED

Coordinator verification record, 2026-09-22. Artifacts:
`rev-try/ROUND20_REPORT.md`, `verify_r20_ol1.py`, `r20.log`
(two runs, invocation-first, the honest anomaly-then-fix record),
my `rev-try/coord_r20_check.py` + `coord_r20.log` (run 1 = my own
two check bugs, diagnosed by hand, preserved; run 2 = 0 failures).

- Reproduction: run 2 byte-identical on all verdict lines (their
  wall 2.15 s, mine 2.14 s; MAXRSS within noise). Run 1's two T3d
  anomalies ((Delta=-3,c=8) 4 hits, (Delta=-9,c=8) 3 hits) hand-
  confirmed as arithmetic ghosts (FIT at s0=0 needs 8<=0 and 8<=-6,
  both false); the fix (applying the necessary FIT filter to T3/T3d
  and adding T4iv) made the verified statements stronger, not
  weaker. The census bookkeeping is internally consistent: run 2's
  {1717,17,0,11,280} sums to 2025, and the run1->run2 delta is
  exactly 140 cross-pair two-hits + 140 one-hits -> 280 ghosts.
- LEMMA M hand-derived independently BEFORE reading their machine:
  I re-derived the plant depth via the cumulative path (depth =
  Sum_{i<=sigma} L_i + t_sigma*M_R + rho_j, using
  Sum_{i<=sigma} L_i = BotSum(sigma) - t_sigma*p1 - (t_sigma+1)p0)
  and confirmed the closed form BotSum(sigma)+t*Delta-p0+rho_j and
  the inherited form BotSum(j)+t*Delta; locality bounds check. My
  own greedy simulation (never rescans inserted text) == my formula
  construction == the evaluator on 400 RANDOM (p0,p1,M,k) cases
  including p0=0, p1=0, and empty-R deletion — far broader than
  their 20 fixed cases.
- K2's pair-equation classification re-proved by my DIGIT ARGUMENT
  (stronger than the K(d) appeal): repunit blocks sum digitwise
  with digits <=2 and no carries, so I(u2,v2)=I(u1,v1)+I(s1+1,s2)
  forces the two blocks adjacent — exactly two orders = ladder rung
  (v1=s1) or cross-pair (u1=s2+1, common top). Exhaustive sweep: 182
  solutions, no third family. The CROSS-PAIR KILL uses FIT at the
  REAL firing s1 (c <= Delta+p1 = p1 <= 3^{s1+1} < c) — so K2 for
  real channels is FULLY PROVED BY HAND, independent of the
  machine's idealization filter. Corollary core follows by hand:
  a ladder's rungs I(u,sigma) have top sigma <= k-1 < k, never a
  mirror target I(t+1,k) (top k); so each realizable channel
  serves at most one mirror target. Ladder cap and mirror floor
  (I(t+1,k) >= I(k,k) = 3^k) fresh-encoded.
- LEMMA S hand-verified: the ghost inequality (sigma <= k-2 forces
  c > 3^{s+1} via (2*3^k - 3^{k-1}+1)/2), the window identity
  3^k - c = BotSum(u-1), the u=1 (p1 in {3^k-1,3^k}) and u=k
  ((3^k+1)/2 <= p1) specializations, the exclusivity argument
  (the early u-1 hit is FIT-killed for u <= k-1 since
  2*3^k > 3^{u+1}-1), and the drift two-case split (p1 >=
  3^k - BotSum(u-1) - (t+1)Delta, deficit bounded or Payment-routed).
  All fresh-encoded, 0 violations.
- T4i/T4iii HAND-DERIVED BEFORE RUNNING: T4iii's Delta=0 exactly,
  single firing at k-1, plant depth = BotSum(k-1)-3^{k-1}+
  (5*3^{k-1}+1)/2 = 3^k = I(k,k), output = D(k-2)+b+R, both top
  runs fully consumed (TWO part-B slots), c=(3^k+1)/2 at Lemma S's
  u=k window bottom — byte-exact k=4..6. T4i: all k separators
  fire, output runs 3,9,27,81 (each copy's 'aa' tail merges with
  the next remnant: 2+(3^{s+1}-2)=3^{s+1}), plants at BS(s)-1 =
  I(1,s) — the u=1 ladder. My own 6500-pass census loop: 0
  mirror-depth plants on D(5;3), matching their T4ii.
- Mod-3 closure hand-verified (BS(j) = (3^{j+1}-1)/2 = 1 mod 3,
  I(t+1,k) = 0 mod 3, no solution) and fresh-encoded.

THREE FLAGS (report-text/precision, none a false tested claim):

1. K(a) REPORT-TEXT SLIP: the parenthetical "with a gap of exactly
   one scale between them or overlap at a single point" is WRONG as
   a description of the machine's classes (and of the truth): a gap
   leaves two blocks, an overlap leaves a digit 2 — neither is an
   interval sum. The code's merge classes (b+1==c / d+1==a /
   empty side) and my digit argument agree: CONSECUTIVE MERGES
   ONLY. Fix the wording.
2. THE s4 SOUNDNESS PARAGRAPH IS INVALID AS WRITTEN: "real-FIT
   c <= 3^{s_r+1} implies filter-FIT" — the machine's filter
   anchors at the FIRST IDEALIZED hit s0, which can precede the
   first real firing. My concrete exhibit (fresh-encoded):
   P = b.a^81, R = a^35.b.a^46 on D(7;3) realizes channel
   c=35 (Delta=0; 35 = I(2,3)-I(0,0), so it IS in their census
   class), fires at 3..6, has ZERO real hits (depths 75,156,399,
   1128 — no interval sums), but its IDEALIZED hit set {0,1} is a
   cross-pair and the filter ghosts it (35 > 3^{s0+1}=3). So the
   census EXCLUDES realizable channels; it is corroboration, not
   coverage. The THEOREM survives because the hand kill uses FIT
   at the real firing (verified independently above) — T3's
   "every REALIZABLE channel" line should be re-anchored to the
   hand proof, not the filter.
3. THE s6 INHERITED-LOOPHOLE CLOSURE IS OVERSTATED ("PROVED"):
   the mod-3 step is airtight, but the content step ("material
   before an inherited separator is a subsequence of the input's
   increasing ladder") is FALSE when firings precede j — copies
   intervene, and maximal a-runs can be mixed remnant/copy
   material. The correct closure: an inherited separator at a
   mirror depth needs >= (3^k+1)/2 of b-free insertion mass
   before it (mirror-prefix mass exceeds BotSum(j)) — i.e. exact
   deep intermediates, the trichotomy's case (b)/(c), priced by
   OL-2/Payment. Downgrade to "mod-3 case proved; drift case
   routed via (b)/(c)"; the counting corollary should list this
   as a third condition (or take the Omega(k) version: at most a
   bounded number of mirror targets can be inherited, each
   forcing deep supply). Precise write-out routed to Lane C
   round 21.

### Program status (updated)

OL-1 LANDED: Lemma M/FIT fully verified; K2 for real channels
fully hand-proved (my digit-argument version, independent of the
machine filter); Lemma S verified with the exclusivity; the
trichotomy assembles with (a) and (c) proved and (b) = OL-2.
Remaining OL-1 residue: the Delta>0 multi-hit closure (their
located gap, routed via Payment) and the inherited-loophole
precise write-out (flag 3) — both routed to Lane C round 21.
Endgame residue after this wave: S4.3-general (Lane D round 7, in
flight), Lane C round 21 (Delta-closure + loophole write-out),
Lane B round 7 (INV4 — just landed, verification next). Then
Lane A's final integration.

## Lane B round 7 (INV4 line-by-line) — VERIFIED, ACCEPTED; TL at full altitude

Coordinator verification record, 2026-09-22. Artifacts: `rev-split/
ROUND7_REPORT.md`, `gram7.c`/`gram7`/`gram7.log`/`gram7_k8.log`; my
`rev-split/coord_b7_check.py` + `coord_b7.log` (run 1: two script
bugs of MINE — S_ shadowing and a leftover [S_]; run 2: 0 failures).

- Round-6 slip fix CONFIRMED IN PLACE: po_rec.c rebuilt from the
  corrected source; BOTH round-6 seeds (271828, 314159) reproduce
  BYTE-IDENTICALLY past the invocation line — the corrected junction
  formula (3^k + 3^c + 1, c >= 1) moves no tested claim, exactly as
  their coincidence analysis said (thresholds bite only at copy 0
  where both forms give 2). The formula is now load-bearing in
  gram7's decb grammar and machine-matches.
- gram7.c rebuilt from source: BOTH logs byte-identical past the
  invocation line (17 grammars, 150 checks, 0 failures; 101 checks
  at the uniform k<=8 window). The engine is exactly the described
  formalism: directives as DATA (kind/form/index bounds/OF body),
  forms as (k, j) with ambient-index shadowing, dir_count = tree
  size (k-independent by construction), expansion compared EXACTLY
  against a built-in greedy evaluator implementing the primitive
  (insert-and-skip, never rescan).
- ALL 17 grammar forms HAND-DERIVED BY ME independently (before
  cross-reading the source's forms): decb = [X/'b']X runs [2] +
  per c in [0..k-2] ([3^1..3^{k-1}], 3^k+3^{c+1}+1) + [3^1..3^{k-1}]
  + [2*3^k], count k^2+1; thresh = [b/'aaabaaab']decb — the window
  needs [>=3 run's last 3 a's][b][EXACTLY-3 run][b], so it fires
  only at (J_{c-1}, copy c's 3^1-run), c>=1 (copy 0's head 2 < 3):
  k-1 firings, each deleting the 3^1-run, biting J_{c-1} by -3,
  merging two separators; expected [2, 3^1..3^{k-1}, 3^k+1] +
  per c in [1..k-2] ([3^2..3^{k-1}], 3^k+3^{c+1}-2) + [3^2..3^{k-1},
  2*3^k], count k^2-k+2 = 101-9 at k=10; dropab = [eps/'ab']X = ONE
  run S-k (each window eats its b too — their machine-caught error
  #1 is a real catch); dfirst's seam merge [4, 3^2..3^k] (error #2
  likewise); dlast glue 3^{k-1}+3^k; Eleak S+3^j; Eprod
  1+floor(3^j/2)*S; Elast (S+k+1)/2; Ecbox/Esmm/Eh2 chains; half/
  third/dbl/shave/dblmerge. My fresh battery (coord_b7_check.py,
  prov.py, k=3..7): 17/17 forms byte-exact, decb and thresh counts
  included. The two grammar-engine errors they disclosed are both
  in the merge algebra and both now machine-exact — the discipline
  working, and the corrections match my hand derivations.
- The formalism hand-scrutinized: the nested-directive repair of
  round 6's block-type defect (decb's X-copies have k+1 interior
  runs — no V-fixed block type; the OF device fixes it) is the
  right move and makes the Theta(k^2) reconciliation a theorem
  (grammar <= 3^d(2|u|+1) directives, expansion <= (k+2)^d). The
  type-count recursion arithmetic checked (3x split multiplicity:
  masked family + two edge-adjusted families per scrutinee family
  directive; C adds D+2 with the seam split — induction closes).
  AIS-CLOSURE's proof (arrangement regions x residues x EPT-tests,
  closed under Booleans, affine substitution with period T_V*A_V,
  bounded projection) is sound — the standard induction, stated
  once cleanly as asked. The S-rules (S-i mask + bite-adjusted
  edges via PO-1(v); S-ii OF-insertion with arity+1 and alpha-
  renaming; S-iii count) with the fired set consumed at EXACTLY
  TWO POINTS (the OF instance set and the masks/edges) — the
  circularity-breaker made precise at grammar level, and the
  combined INV1-INV5 induction now closes at line-by-line altitude.
- HONEST SOFTNESS, accepted and recorded (their own flag): the
  Merge Lemma's piece-count bound (D_V+2) is a three-line
  emission-path sketch, not a full enumeration — same depth-bounded
  stacking as the nesting bound; and the machine's direct expansion
  covers interval index sets (the periodic/EPT-masked corner is
  covered indirectly via round 6's [rec] battery: 557 slots,
  0 signature-slot leads). Parked as the natural next-round
  extension (one grammar with a genuinely periodic mask).
- The TL LaTeX statement (report section 5) read line-by-line:
  matches rounds 5-7 content (strata with anchored exponents, the
  honest 8*#S+O_V(1) ledger, first/last M<=2 boundary clause,
  k-affine + T_V-periodic junk, the profile-grammar clause with
  O_V(3^d |V|) nodes and Theta(k^d) expansion). DECISION for the
  integration: keep BOTH constants — 8*#S+O_V(1) in clause (ii)
  (run level), (d+2)*M per form in the grammar clause — no
  unification needed. One wording note for Lane A: T_V's
  definition should say the lcm is over {2} union {ord_p(3) : p a
  pattern length or tiling modulus coprime to 3} union {p : p
  such a modulus}, with 3-divisible moduli handled by EPT's
  eventual vanishing (the current "ord_p(3), |p|" shorthand is
  readable but imprecise).

### Program status (updated)

TL IS NOW AT FULL ALTITUDE AND UNCONDITIONAL: PO (round 6) +
INV1-INV5 with INV4 line-by-line (this round). The endgame residue
is TWO pieces: Lane D's S4.3-general (in flight) and Lane C's
round 21 (the Delta>0 multi-hit closure + the inherited-loophole
precise write-out — flagged in my round-20 verification). Lane B's
optional hardening round (the periodic-mask grammar) is parked.
When the two pieces land and verify, Lane A mounts the final
integration: dichotomy.tex at the hook, the two-lemma paragraph
with TL's ready LaTeX, part (ii) flipped to proved.

## Lane D round 7 (S4.3-general, the compensation channel) — VERIFIED,
## ACCEPTED at catalog altitude; G1/G2 located; one fired-set statement
## flagged

Coordinator verification record, 2026-09-22. Artifacts: `rev-wall/
s43_check.py`/`s43.log` (0 FAILS, 1.2 s), REPORT.md R7.0-R7.7; my
`rev-wall/coord_d7_check.py` + `coord_d7.log` (three runs; every
failure diagnosed as MY OWN bug by hand before re-running: a wrong E1
construction, a non-constructive sampler, and a missing fourth piece
in the n=4 probe; final: 0 failures).

- Reproduction: BYTE-IDENTICAL (all parts; 1.2 s). The refutation
  record (R7.0) is honest and the corrections are real: I independently
  confirmed the tripler refutes the round-5 "psi-maps never land"
  view BEFORE reading their machine code ([a^3/a^2] on run 3^sigma:
  floor(3^sigma/2) windows aa->aaa gives 3(3^sigma-1)/2+1 =
  (3^{sigma+1}-1)/2 = I(0,sigma) — hand-derived; k=2..5 fresh-encoded).
- Hand-verified: 7.1 (v_3(I(u,v)) = u; the unit part (3^L-1)/2 = 1
  mod 3); 7.2 INCLUDING my own proof of the integer-iff step ((3^{L'}-
  1)/(3^L-1) in Z iff L | L', by division with remainder — the
  remainder term x^r - 1 is too small to be divisible); 7.3's
  inequality (i+j <= 4*3^u < 3^{u+2}/2 <= 3^{v+1}/(v-u+1), so |R| < 0
  always); the full merge [a^3/abaa]X = a^S = a^{I(0,k)} (net 0 per
  fire, fires never stop); H2's formula Sigma I(0,sigma) =
  (3^{k+2}-2k-5)/4 (hand-derived, fresh-encoded k=2..8, never lands);
  E1's identity (the halver over the isolated prefix: sum (3^s+1)/2 =
  (I(0,t)+t+1)/2); E3's mod-3 obstruction ((3^{m+1}+1)/2 = 2 mod 3 vs
  I(a,b) in {0,1}); the F and G fixed-box windows; the pair-merge
  witness at k=5.
- My OWN constructive catalog for the obligation lemma (my ranges:
  a,b <= 8, u,v <= 7, |t| < 3^u): 2269 solutions, ZERO violations of
  the m*-1 form — independent confirmation of their 21833-solution
  catalog. THE n=4 PROBE: 210075 four-piece solutions on a smaller
  box: ZERO violations at m*-1 (and none at m*-2) — the lemma
  EXTENDS beyond n=3 as stated, which is STRONGER than their G2
  expectation (slack log_3 n): the m*-1 form may hold for all n, or
  the slack grows far slower. G2 data for their round 8.
- ONE STATEMENT FLAG (the round's only defect, in R7.3's H3b
  sentence): "the fires exactly at the junctions sigma with
  3^{sigma+1} >= j" is FALSE in general, and its own hand note in the
  same sentence blocks junction u+1. My machine-confirmed probes:
  (a) the witness (i=1, j=27) at k=7 fires {2,4,5,6} — junction 3
  blocked (remnant 0 < i), junctions 5,6 CHAIN after 4 (the k=5
  witness works only because k cuts the chain off); (b) the stated
  window's interior (i=1, j=20, u=2: 18 < 20 <= 27) fires {2,3,4}:
  runs 2..5 chain into ONE run — NO width-1 atom; (c) the CORRECT
  window for the atom I(u,u+1) is max(3^u, 3^{u+1}-i) < j <= 3^{u+1}
  (block junction u+1), confirmed u=1..3 at j = 3^{u+1} — the chain
  to the right merges the tail but the atom itself is bounded by the
  blocked junction. The fix: state the fired set with their OWN
  round-6 recursion theorem (fire_sigma iff c_sigma >= i and
  R_{sigma+1} >= j; c_{sigma+1} = R_{sigma+1} - j[fire_sigma]) —
  which is exactly its domain. The witness and the atom claim stand;
  the parameter window and the fired-set sentence need the correction.
- The assembled atom obligation law read carefully: the free
  boundaries (the full merge I(0,k); top-anchored values; J(V)), the
  stopping-flank/isolation/blob walk pricing, the composition
  collapse ([R/tripler-text] on the tripler text = R — fresh-encoded),
  the induction closing at C = 2 (1 + (m*-1)/2 >= m*/2). ACCEPTED at
  CATALOG altitude: the pieces are interval sums, machine-exhaustive
  (their catalog + mine); G1 (TL-strata pieces: Sigma q_i 3^{e_i} +
  (Ak+B) + beta) and G2 (piece count) are the precisely located
  remaining write-out to reach round-6 altitude; G3 the constant.

### Program status (updated)

OL-2 now reads: PROVED on TL (unconditional, Lane B rounds 5-7) +
S4.3-general at CATALOG altitude, with G1/G2 located (Lane D round
8, next) and the H3b fired-set correction. The endgame residue: Lane
C round 21 (Delta-closure + the inherited-loophole write-out, in
flight), Lane D round 8 (G1+G2 + the H3b fix, dispatching now), and
Lane B round 8 (landed: the periodic-mask grammar + the two-color
profile refinement + the INV3 measure form — verification next).
Lane A's integration charter is updated; final dispatch after C21
and D8.

---

## Lane B round 8 (rev-split) — VERIFIED AND ACCEPTED (2026-09-22)

### What I verified (all of it)

- **Byte-identical reproduction**: rebuilt gram8.c from source
  (`gcc -O2`), ran `gram8 gram` and `gram8 meas` fresh; both logs
  reproduce byte-identically past the invocation line. Totals as
  claimed: 478 checks (gram) + 144 (meas), 0 failures, 19 grammars.
- **Hand derivations (done BEFORE reading their machine code)**:
  - tile4 = [b/'aaaa']X: run j -> b^{floor(3^j/4)} a^{Lambda_j},
    Lambda_j = 3^j mod 4 (1 even / 3 odd — period 2); two-color
    profile [a:Lambda_j; b:1+floor(3^{j+1}/4)] — verified by direct
    text construction at k=3,4,5 by hand (k=5: [1,1,3,9,3,81,3] —
    fire at j=2 merges 2+1+6 = 9, at j=4 merges 20+1+60 = 81).
  - mod2 = [b/'bab']tile4: the fired set {even j in [2..k-1]} —
    hand-verified three ways: the match test Lambda_j = 1 (the
    interior-run exactness), the boundary exclusions (j=0 no b
    before; j=k no b after), and the greedy disjointness (the
    material between consecutive windows is floor(3^{j+1}/4) +
    Lambda_{j+1} + floor(3^{j+2}/4) >= 29 at the smallest j, so
    leftmost = increasing j). merged(j) = floor(3^{j-1}/4) + 1 +
    floor(3^j/4) = (3^{j-1}+3^j)/4 at odd j (their formula, indexed
    by the SURVIVING a-run — initially read it as indexed by the
    fired run and recomputed; theirs is right). The k=3 mod2 text
    abaaabbbbbbbbbbaaa reconstructed by hand (a-count 7, b-count 10).
  - The measure forms: mod2 odd cell v_b = 1 + 9(9^m-1)/8 (I derived
    (9^{m+1}-1)/8 independently); even cell = 1 + 9(9^{m-1}-1)/8 +
    1 + (3^k-1)/4; decb (k+1)S / k^2; thresh -6(k-1) / -(k-1);
    tile4 residue-split sums. The 199297 count at k=12:
    (797161-25)/4 + 13.
- **My fresh battery** (rev-split/coord_b8_check.py, 3 s): (0) my own
  single-pass sweep (find-based, lsubst insert-and-skip semantics)
  == the PV evaluator at k=3..9 for both compositions; (1) tile4
  profiles k=3..12 + the exponential a-run-only count (199297 at
  k=12) vs 25 two-color entries; (2) mod2 per-cell profiles k=3..12
  byte-exact vs my hand forms, fired count = floor((k-1)/2), 15
  entries at k=12; (3) all measure closed forms k=3..12 (decb/thresh
  via PV at k<=9); (4) the 17 round-7 outputs b-simple (85
  evaluations — all b-runs = 1, the precondition the a-run-only
  view needed); (5) the two-color profile <-> text bijection (300
  round-trips) and rule-Z NON-injectivity (ab/abb, aabab/aababb) —
  the necessity of the refinement, machine-witnessed. FAILS: 0.
  (One bug of mine en route: I swapped #odd/#even in my v_a formula;
  v_b survived the swap only by the mod-4 accident (true numerator
  = 0 mod 4, swapped = +2, floor unchanged) — my error, no claim of
  theirs moved.)
- **The substantive finding accepted**: round-7 INV4's a-run-only
  profile is NOT an invariant of the class — tile4's a-run-only
  view has Theta(3^k) entries (rule-Z silence about b-structure
  loses faithfulness: the profile does not determine the text). The
  two-color refinement (maximal a-runs AND b-runs, zero-structure
  absorbed into b-run values in the unchanged EPT form class,
  expansion <= 2M+1) is REQUIRED for the induction's correctness —
  not cosmetic. Lane A's mount must use the two-color wording.

### Program status (updated)

Lane B round 8 VERIFIED. Remaining: Lane C round 21 (landed,
verification next), Lane D round 8 (in flight). Lane B dispatched
one final round: fold the two-color refinement into the paper-ready
TL LaTeX (the INV4 profile clause, the Merge Lemma b-piece wording,
the S-i mask sentence with mod2 as the exhibit, T_V's domain with
ord_4(3) = 2) so Lane A mounts a final block; optional p=7
(ord_7(3) = 6) only if early.

---

## Lane C round 21 (rev-try) — VERIFIED AND ACCEPTED, one flag (2026-09-22)

### What I verified

- **Byte-identical reproduction**: rebuilt round21_delta.c; the census
  reproduces d5/d6/d8/d9.txt byte-identically (29/80/364/667 survivors;
  candidate triples 33486/166995/2062928/5761734). The battery
  (verify_r21_deltaclosure.py) re-ran: all VERIFIED. The three
  ROUND20_REPORT.md fixes confirmed in place (K(a) with the repunit
  digit proof; §4 corroboration re-labeling; §6 rerouted through INH).
- **Hand derivations (before reading their machine code)**:
  - D1's chain exactly: W = (3^{k+1}-3^u-3^{sigma+1}+1)/2, FIT gives
    c <= Delta+3^{sigma+1}, so (t+1)Delta >= W-3^{sigma+1}; for sigma
    <= k-2: 3^u <= 3^k and 3^{sigma+1} <= 3^{k-1} give W >=
    (5*3^{k-1}+1)/2, whence (t+1)Delta >= (3^k+1)/2 and Delta > 0.
  - D2's identity W = 3^k - BotSum(u-1) at sigma = k-1 and the
    deficit bound 3^k - p1 <= 2 BotSum(u-1) = 3^u - 1.
  - D3 (one plant per firing per channel; the earlier of two mirror
    services has sigma <= k-2, D1 applies). MR's per-firing Delta =
    M_R - p0 - p1 and mass conservation Sum f_i Delta_i = 0 (the
    final output mass = S). INH's bound I(t+1,k) - BotSum(j) >=
    (3^k+1)/2; the mod-3 separation correctly scoped (I(u,v) = 0 mod 3
    for u >= 1 vs BotSum = 1: the Delta=0 survivors only reach the
    b=0 ladder).
  - The tightened FIT pigeonhole: t_1 firings at distinct junctions
    in [0,sigma_1) force tau_0 <= sigma_1 - t_1.
  - E1: depths BotSum(sigma)+6sigma+2 = 3, 12, 27, 60 at k=4: hits
    I(1,1), I(1,2), I(3,3) — the 3-hit drifting channel, real. E2:
    depths [3,120,243,384,579] on D(5;3), mirror I(5,5)=243 at
    sigma=2 <= k-2, debt 342 >= 122, mass 934 = S+5*114; the family
    Delta=(3^k-15)/2. E3: [a^9/(abaaa)] on D(2;3) = a^9 b a^9
    (survivor at 9 = I(2,2), never-inserted 0, inserted 9 >= 5);
    [a^27/(abaaa)] on D(3;3) = a^27 b a^59 (survivor 27 = I(3,3),
    second copy at a-depth 35).
- **My fresh battery** (rev/coord_c21_check.py, 0.3 s, FAILS: 0):
  E1/E2/E3 via the evaluator byte-exact vs my hand forms (E1's output
  separator depths and hit classification at k=4..7; E2's depths, the
  mirror service, the mass bookkeeping, the general family; E3's
  texts and survivor depths); D1/D2/INH arithmetic sweeps at
  k=6..9 / 4..8; the pigeonhole over all subsets; T5 (my flag-2
  exhibit) with the planted depths [75,156,399,1128] = BotSum(s)+35
  (Delta=0) and zero anchored hits. Two bugs of mine en route (the
  separator-depth extraction returned b-to-b GAPS not cumulative
  depths; a wrong 81-per-fire term in my T5 formula — Delta = 0): the
  evaluator was right both times, no claim of theirs moved.
- **MY CENSUS AT k=5** (full independent re-enumeration, my own
  constraint reading, two-sided tightened window): 29 survivors,
  SET-EQUAL to their d5.txt, with E1's and E2's records present.
  All d6/d8/d9 records re-validated (collinearity, integrality,
  t-feasibility, the tightened upper window, monotonicity).

### The flag (census bookkeeping, not load-bearing)

**19 census records (d8: 3, d9: 16) violate the tightened LOWER
bound c >= -3^{sigma_1 - t_1}.** Their v1->v2 fix tightened only the
upper window. Proof of the lower bound: c = rho_j - p0 >= -p0, and at
the channel's first firing tau_0 <= sigma_1 - t_1 the leading flank
satisfies p0 <= 3^{tau_0} <= 3^{sigma_1 - t_1}. Every ghost has
-c > 3^{sigma_1-t_1} (machine-checked, e.g. (3,6,7,(4,3),(7,2),
(8,1),t1=1,D=3,c=-16): p0 >= 16 > 9 = 3^2). Corrected counts: 361
(k=8), 651 (k=9); k=5/6 unchanged. All 19 ghosts are NON-mirror
records (their last hit has a < k+1), so the mirror-branch population
claim is unaffected and the <= 4 real-hit bound only tightens.
Dispatched to Lane C as a small round-21b: two-sided window, re-run,
update section 2 + the ledger. Also noted: E3's side remark "depth
36 = I(2,3)" counts the CHARACTER position; the a-mass depth is 35
(the survivor claim at 27 = I(3,3) is the load-bearing part).

### Program status (updated)

The demand side is now COMPLETE in the form Lane A needs: Theorem D
(D1/D2/D3/MR) + Lemma INH + the disjunctive counting corollary, all
hand-proved and fresh-verified; the census is corroboration with
corrected numbers. Lane D round 8 has landed (G1 strata closure + G2
mass form + the H3b erratum) — verification next. Lane B is on the
final LaTeX fold. After D8 verifies: Lane A's integration (the last
step).

### Round 21b addendum (verified same day)

Lane C applied the two-sided window immediately. Verified: rebuilt
round21_delta.c; the v3 census reproduces byte-identically at all four
k with exactly my corrected numbers 29/80/361/651; my battery now
passes with ZERO lower-bound ghosts; the mirror-branch populations
byte-identical to v2 (their check: d8 78 debt + 74 window, d9 124 +
108 — all 19 removed ghosts were non-mirror, as I derived); the E3
side remark fixed (a-mass 35, character position 36); the report
carries the honest three-version process record (v1 81/384/721, v2
80/364/667 one-sided, v3 29/80/361/651 two-sided). One residual
one-liner flagged to them: the distinct-(Delta,c) channel counts are
23/57/218/365 (my count, matching theirs at k=6/8/9); their report's
"13" at k=5 is stale (the file has 23). Lane C's line is now CLOSED:
the demand side is complete — every path to a mirror depth is priced
(plant window / mass debt / survivor supply).

---

## Lane D round 8 (rev-wall) — VERIFIED AND ACCEPTED (2026-09-22)

### What I verified

- **Byte-identical reproduction**: g1g2.log and the post-erratum s43.log
  both reproduce byte-identically past the invocation line (0 FAILS
  each; s43's new md5 noted in their R8.7).
- **Hand derivations (before reading g1g2_check.py)**:
  - The H3b corrected window max(3^u, 3^{u+1}-i) < j <= 3^{u+1} with
    i <= 3^u: j > 3^u blocks sigma <= u-1 (the right flank does not
    fit run u); j > 3^{u+1}-i blocks u+1 (the shrunken remnant);
    j <= 3^{u+1} allows fire_u; the fires above u+1 chain
    (3^{sigma+1}-j >= 2*3^{u+1} >= i); the atom I(u,u+1) is bounded
    by the surviving b_{u-1}, b_{u+1}.
  - The gap bound arithmetic: no stratum within g scales below d*
    gives (1/D)3^{d*} <= M 3^{d*-g} + |gamma|; above the EPT
    boundary d* >= log_3(2D|gamma|) the gamma term contributes <=
    1/(2D), so 3^{g-1} <= DM. The downward induction on d*.
  - 8.4's three cases (spanning / carry chain with 3^g <= M / count
    channel via 7.2), each giving obligation >= m*-1-floor(log_3(DM)).
  - G2: the n=7 witness 7 I(0,1)+8 = 36 = I(2,3) with the double
    2-scale carry (9 at scale 0 and 9 at scale 1 -> the target
    1100_3), M = 20 = 9+9+1+1 (I recount: pieces 7+7, bite 2+2,
    target 1+1); the n <= 6 impossibility (concentration 6+2 = 8 <
    9 = 3^2); my n=4 datum explained (concentrated mass <= 6 < 9);
    the count-channel absorption (c = 3^j needs multiplicity 3^j
    <= M). The exhibits 3 I(0,1) = I(1,2) (M = 6), 9 I(1,3) =
    I(3,5) (M = 28), deficits 1/2/2 vs floor(log_3 M) = 1/2/3.
  - The INV3 coordination: G(r,T,m) = 3^{m-(r-1)T} (3^{rT}-1)/(3^T-1)
    with the coefficient landing exactly in 7.2's length-divisibility
    class (c I(u,u+T-1) = I(u,u+rT-1); Lane B's v_b family
    (9^m-1)/8 I(0,1) = I(0,2m-1)).
  - The C=2 closing arithmetic (1 + (m*-1)/2 >= m*/2 iff
    2+m*-1 >= m*).
- **My fresh battery** (rev-wall/coord_d8_check.py, 9.4 s, FAILS: 0):
  (0) my own 351-case H3b sweep -- my fired_rec (the round-6 recursion
  theorem) predicts the EVALUATOR's pair-merge output exactly at every
  (u,i,j), and window <==> (fire_u & !fire_{u-1} & !fire_{u+1})
  <==> the atom I(u,u+1) appears: EXACT (18 window hits); (1) my own
  strata catalog (F1/F2/F3, 3 pieces, |bite| <= 18, targets
  3 <= u < v <= 6): 144149 digit-assignments, the collected identity
  Sum mu_d 3^d = 0, the top-defect inequality, the gap bound
  3^g <= M_below, and the deficit bound (the mass form): 0 violations
  each; (2) my own exhaustive interval probe (a,b <= 3, u < v <= 3,
  |t| < 3^u, multiplicity <= 7): 139895 multiset solutions -- a
  SUPERSET of their 52959 (no +/- canonicalization; netting pairs
  kept) -- with the m*-1 violations EXACTLY {7: 1}: the unique
  violator is the witness 7 I(0,1)+8 = I(2,3), and the mass form 0
  violations on the whole superset (their claim confirmed on a
  strictly larger search); (3) the exhibits' arithmetic and digit
  masses, the F3 -> 7.2 coordination (including Lane B's v_b
  instance), the C=2 closing.

### The one wording flag (for the mounted statement)

R8.1's gamma formula has "+ t" while the bite's digits are ALSO in
mu_d ("the bite's raw digits at the low scales") -- double-counted
as written. The machine's convention (g1g2_check.py lines 158-162,
and what G2's M = 20 computation and 8.3's |gamma| = O(k) both
require) is: the affine+junk+bite are ALL collected as low-scale
digit material in mu (their battery's own note: "the (Ak+B) and the
junk are COLLECTED into the bite"), so M absorbs the O(log k) digit
mass and gamma is empty. Lane A's mount of the final law should use
the machine's convention, not the R8.1 sentence.

### Program status (updated)

OL-2/S4.3-general is now at FULL ALTITUDE and verified: the strata
obligation lemma (8.4), the mass form (G2) with the transition at
n = 7, the C=2 induction, and the final law depth >= (min(v,k-u) -
1 - floor(log_3 M))/2 with Omega(min(v,k-u)) surviving. With Lane
C closed (round 21b) and Lane D closed (this round), the remaining
work: Lane B round 9 verification (the final TL LaTeX with the three
C-R9 corrections -- landed), then Lane A's final integration.

---

## Lane B round 9 (rev-split) — VERIFIED AND ACCEPTED (2026-09-22)

The final TL LaTeX, the three replication corrections, and p = 7.

- **Byte-identical reproduction**: gram9.log (511 checks), gram9_meas.log
  (144), tl_witness.log (29) all reproduce byte-identically from rebuild.
  The LaTeX block compiles standalone (my extraction + pdflatex with
  amsthm theorem/remark declared: EXIT 0, zero errors, zero undefined
  references — the only fix my wrapper needed was the remark
  environment that main.tex's preamble provides).
- **Hand derivations (before reading their machine code)**:
  - C-R9-1 CONFIRMED: the replication refutation — decb = [x/b]x has
    k^2+1 a-runs; decb^2 = [decb/b]decb has k^4+1 (82 at k=3) at tree
    height 3; decb^3 has k^8+1 = 6562. The exponent is the ADDITIVE
    nesting depth (Delta(S) <= Delta(F)+Delta(R)); the a-run recursion
    A' = A + B(R_w - 2) unrolls 10 -> 82 -> 6562. Round 7's
    tree-depth bound was wrong as mounted; every rounds-5-8 battery
    expression had a 1-D fired set, which is why it held there.
  - C-R9-2 CONFIRMED: I derived the ENTIRE decb^2 k=3 value table
    independently before running anything: decb(D) = [2,3,9,31,3,9,37,
    3,9,54]; decb^2 = head 4 = 2+2; sites 3,9 x27; junctions
    31 = 27+3+1, 37 = 27+9+1 x9; seams 59 = 54+3+2, 65 = 54+9+2 x3;
    junction seams 87 = 54+31+2, 93 = 54+37+2; end 108 = 54+54 --
    82 runs, every value and multiplicity. The anchoring split (the
    seams anchor at k + the OUTER site index; the junctions at the
    INNER copy index) is real.
  - C-R9-3's closing arithmetic (|S| >= |F|+3 => |S|^2-|F|^2 >=
    6|F|+9) checks; the two-tier bound is hand-derived (their honest
    flag: not machine-pinned beyond m <= 3; the decb^2/decb^3 grammar
    pins are the disclosed successor task).
  - tile7: Lambda_j = 3^j mod 7, cycle 1,3,2,6,4,5 (ord_7(3) = 6);
    profile [a:Lambda_j; b:1+floor(3^{j+1}/7)] -- the k=13 head
    1 1 3 2 2 4 6 12 4 35 5 105 1 hand-verified digit by digit.
  - mod7: fired set {j: 6|j} cap [1..k-1] (the match test Lambda_j=1
    iff 6|j; boundary exclusions as in mod2), #fired = floor((k-1)/6),
    the surviving family = the COMPLEMENT class (the Boolean-closure
    mask -- their engine finding: round 8's single-residue masks were
    an engine artifact), merged b = floor(3^{j+1}/7)+1+floor(3^{j+2}/7)
    before the run after each fired site, the 417 = 104+1+312 at k=13.
- **My fresh battery** (rev-split/coord_b9_check.py, 0.4 s, FAILS: 0):
  the chain counts k^2+1/k^4+1/k^8+1 with the recursion identity; the
  FULL decb^2 k=3 value table vs the evaluator (my multiset
  construction, byte-exact); tile7 profiles k=3..13 + the exponential
  a-run-only count; mod7 profiles k=3..13 vs MY complement-class
  prediction with the merged-b formula and the fired-count identity;
  the C-R9-3 arithmetic.

The mounted LaTeX (ROUND9_REPORT.md section 1) is the paper-ready
block: two-color profile clause with the entry bound 2 N_V (k+2)^{Delta_V}
(N_V explicit -- their note 1: the tighter literal product is NOT
certified for deep V), Merge uniformly over both colors, S-i masks as
Boolean combinations of residue tests, T_V's domain with ord_4(3) = 2
and ord_7(3) = 6 both exhibited, per-cell selection, clause (i)'s
ambient-index anchoring (reducing verbatim to round 7's at arity one),
and the two-tier directive count.

### Program status: ALL FOUR LANES CLOSED. Final integration next.

Verified inventory for Lane A: TL (the round-9 LaTeX block), OL-1 +
Theorem D + Lemma INH + the disjunctive corollary (rounds 20-21b, the
v3 census 29/80/361/651, channels 23/57/218/365), OL-2/S4.3-general at
full altitude (the atom obligation law, the R8.1 gamma identity as
fixed), the demand-side trichotomy. Nothing else outstanding.

---

## FINAL INTEGRATION VERIFIED (Lane A's mount of the endgame) — 2026-09-22, coordinator

VERDICT: ACCEPTED. thm:dichotomy (ii) is PROVED and unconditional in
main.tex: "each E fails on the strongly super-increasing inputs D(k;3)
(any fixed base B >= 3 works; base 2 is the degenerate boundary,
Prop dich:prop:boundary) beyond separator count k > c_E #S(E) + c'_E —
linear in the pass count." The governing directive is discharged:
rev is not L-reachable, over every finite alphabet |Sigma| >= 2 at
once (coding invariance). Nothing committed (user commits externally).

My verification (all fresh, this session):
* BUILD: my own pdflatex x2 — 104 pages, 0 errors, 0 undefined refs,
  0 citations undefined, 0 overfull; only warnings = the 10
  pre-existing font-shape lines + the amsmath \vec note. Matches A's
  report exactly.
* FULL DIFF vs my pre-integration snapshot (365 added / 21 removed):
  14 status-flip wire-ins (abstract, intro x2, open-problem list,
  landscape, alphabet intro, conj:union evidence, frontier lead-in
  2421, rem:price, toll closing 2611, architecture 2613, hook ->
  integration record, conclusion 3004) + the mounted apparatus
  between the dichotomy proof and the Unary Edge. Nothing else.
  No stale "conditional on the two structure lemmas" remains for the
  dichotomy (line 2604's "Conditional on lem:structure" is the
  pre-existing, untouched toll region — a self-contained structural
  fact the dichotomy does not cite).
* STATEMENT CHECKS: the family overclaim fixed per charter item 1
  (strongly super-increasing D(k;3); base 2 recorded as the boundary
  via the mounted dich:prop:boundary with the round-19 offset-cost
  ceiling); the effective bound k > c_E #S + c'_E; the tightness
  remark kept inside the proof (engine Theta(k) depth, Theta(k^2)
  size); (i)/(iii) untouched.
* MOUNT FIDELITY, systematic: label-by-label normalized diff of the
  verified round-18 fragment (rev-try/dichotomy.tex) vs the mounted
  apparatus — 12/17 statements mounted; every difference is exactly
  the prescribed rewiring (Assumption dich:L1 -> Theorem thm:TL in
  escapeA/escapeB/PAYMENT; "conditional on the demand assumption" ->
  "with the demand side below"; lane-attribution bracket tails
  dropped; \mathcal D macro; em-dashes; the round-19 boundary update
  to dich:prop:boundary). The 5 unmounted labels are the superseded
  pieces (dich:L1, dich:L2, dich:thm:main, dich:thm:dichotomy,
  dich:rem:machine). The escape propositions keep the fragment's
  explicit "Status: analysis" markers per its stated status
  discipline; their kills now cite the PROVED TL.
* TL BLOCK: mounted thm:TL + rem:TLprof diffed against
  rev-split/ROUND9_REPORT.md sec 1 — differences are EXACTLY the four
  disclosed ones (remark's first sentence dropped — Sec 2 defines the
  pass; "(Remark~\ref{...})" -> "(the remark below)"; em-dashes; the
  T_V display split across two align lines). No content change.
* B5 (b)-(f): all present in the ledger's history paragraph (the
  halver's irreducible +k/2; the tripler's non-dyadic slopes with
  the supply/demand mismatch s nmid 3^Delta 2^d; both constants kept
  un-unified 8#S+O_V(1) / (d+2)M_V; E_prod's count-times-S class
  with the corrected run forms S(3^j-1)/2+1 and 1+floor(3^k/2)*S; the
  3^t site-term reading with E_leak (S+3^0,...,3^k)).
* DEMAND SIDE vs my verified inventory: M/FIT/K2/S/D/INH/FSL/trace/
  ATOM/counting all match; census cited as corroboration only
  (29/80/361/651 + 23/57/218/365 + <=4 hits + bottom-ladder-only);
  D1''-weak mounted (strong form explicitly not entered); the round-4
  corollary recorded WITHDRAWN inside dich:lem:trace's proof; the
  gamma convention exactly as my D8 flag fixed it. Hand re-derived
  THIS session: L2.1's interval identity I(u,v) = 3^{v-k}S -
  (3^u-3^{v-k})/2; K2's cross-pair kill (c >= (5*3^{s2}+1)/2 >
  3^{s1+1} violates the trailing-flank fit); D1's chain (W >=
  (5*3^{k-1}+1)/2 at u=k, sigma=k-2 worst case; W-3^{s+1} >=
  (3^k+1)/2); FIT's mounted weakened window (a fortiori from the
  per-firing flank bounds: -c <= p0 <= 3^{t0} <= 3^{s0}); the
  mirror-difference identity I(t+1,k)-I(t'+1,k) = (3^{t'+1}-3^{t+1})/2.
* MACHINE NUMBERS all trace to logs I reproduced byte-identically
  (r20's 113,826 kernel census; r21's T3 2,025 constant families /
  11 ladders / 0 two-hit; T6d's 29/80/361/651 and 23/57/218/365;
  T7's INH exhibits; the fired-set 3,211; the D1 replay 1,594).
* SS19 of rev/REPORT.md: complete (19.1 inventory, 19.2 the three
  honest one-liners — (beta)-interface stated-not-proved carried by
  the supply branch AND disclosed inline in the corollary itself,
  stronger than the charter required; EPT-licensed swept domains;
  -O(log k) slack and C in [2,4] refinements; 19.3 the residue map;
  19.4 artifacts).
* FRESH BATTERY (mine, the one soft spot I found): the part-(ii)
  parenthetical "any fixed base B >= 3 works" was architectural —
  all machine work was at bases 2-3. I re-derived and machine-checked
  the BASE-4 analogues (rev-try evaluator; 4 channels x k=4..6
  byte-exact for Lemma M's double-bite recursion; D1's chain with
  W >= (11*4^{k-1}+1)/3; Lemma S's window c = 4^k - BotSum(u-1);
  INH's mod-4 separation; the flank-cap power separation; the
  E1-analogue depths BotSum(s)+6s+2): FAILS: 0. The parenthetical is
  now machine-witnessed at a second base. (Two of my own bugs fixed
  en route: a pattern-parse precedence slip and a separator-
  replacement assembly error in my predictor — the evaluator was
  right both times; the discipline working as designed.)
  Battery: jobs tmp coord_b4_check.py, < 1 s.

PROGRAM STATE: all four lanes closed and verified; the endgame
integrated and integration verified. The paper (docs/proof/main.tex,
104 pp) states and proves: reversal is not computable by any
substitution expression on Sigma* — the failure effective at k >
c_E #S(E) + c'_E on D(k;3) — hence (coding invariance) rev is not
L-reachable over any finite alphabet of at least two letters. Open
remains: the once-primitive's reachability, and the union's exact
criterion r in L. Ready for the user's external commit.

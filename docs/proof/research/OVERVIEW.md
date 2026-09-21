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

# HINGE 1: Is the once-primitive L-reachable?

Research report "once" — working directory `docs/proof/research/scratch/once/`.
Target: the paper's central open problem (main.tex:983, Remark after
prop:unary-once): **is "delete the leftmost b" — the single once-node
[eps/b]_1 — expressible in the plain calculus L?**  If no: ONCE sqsubset L
dies on this witness (L and ONCE incomparable).  If yes: ONCE is a proper
fragment of L, and by thm:pos-hinge POS sqsubset L too.  Out of scope: the
L_k k>=2 ladder (systems agent), rev (rev agent), L+R (lr agent).

Code: `oncecore.py` (primitives + evaluator + BFS machinery, cross-checked
against `../rec/lazy_pass/core.py`, `../systems/systems.py`, Python
str.replace, and the real toolkit ASTs), `verify_r1.py` (search battery),
`verify_r1b.py` (the reduction cluster), `search_mitm.py` (exhaustive
meet-in-the-middle depth 4-5).

---

## Round log

* **R1 (this file, secs 1-5):** built the evaluator; reproduced the
  paper's failed searches; escalated along four axes (depth via exhaustive
  MITM, vocabulary shape, alphabet size, variable patterns incl. computed
  needles); characterized the closest misses (far — distance >= 50/127
  inputs everywhere); machine-verified a REDUCTION CLUSTER (P iff Cut,
  (P or Cut) ==> D) reducing the hinge to "is the left-anchored
  variable-length region computable"; documented the TIE OBSTRUCTION that
  blocks every un-anchored needle — even with an oracle for the region.
* R2 (planned): the positive constructions (parity/residue cascades,
  offset-1 pairing, two-copy schemes, structured deeper searches seeded by
  the toolkit).
* R3 (planned): the invariant hunt — formalize "bounded junction-local
  left-context information" (the candidate shared obstruction with the
  L+R agent's residue-routing picture).
* R4: escalate whichever side showed life; verdict.

---

## 1. Infrastructure and cross-checks (verify_r1.py part x — all green)

| check | domain | result |
|---|---|---|
| oncecore.subst == Python str.replace | 30,000 random (\|A\|<=3, \|B\|<=3, \|C\|<=8, abc) | 0 mismatches |
| oncecore.subst == rec/lazy_pass core.subst == systems.subst | 20,000 random | 0 mismatches |
| oncecore.once == systems.once | 20,000 random | 0 mismatches |
| evalL (my evaluator) == ev_eager(defs={}) on random ASTs | 4,000 random ASTs x inputs | all agree (708 both-undefined, [A/eps] handling identical) |
| VOCAB entries (enc, dec, tail, head, len, H, last, init) == real L-ASTs from the toolkit builders | 63 strings <= 5 over {a,b} | 0 mismatches each |
| del1b == once(eps, b, .) | 508 strings <= 7 | 0 mismatches |

So `str.replace` is a valid fast evaluator for constant patterns (exact
semantics match), and the variable-pattern search vocabulary is
L-computable by construction.

## 2. Reproduction and escalation of the paper's failed searches

The paper (main.tex:983): exhaustive BFS over constant-pattern L-pipelines,
patterns/replacements <= 2 over a ternary alphabet, depth 3, behavior dedup;
plus randomized 4-7-pass pipelines — no witness.

All searches below use behavior dedup on the FULL domain signature
(exact for constant passes; for variable passes, dedup on current-text
tuples is exact since patterns are computed from the original inputs).
Domain: all 127 binary strings of length <= 6 unless stated (the paper's
own TEST set; its "254" comment is a typo — sum 2^n for n<=6 = 127).

| # | space | depth | domain | behaviors | del1b |
|---|---|---|---|---|---|
| r1 | const, pats <= 2, repls <= 2, abc (156 passes) — the paper's | 3 | 127 <= 6 | 324,765 | **ABSENT** (reproduces paper) |
| v1 | const, pats <= 3, repls <= 3, ab (210 passes) | 3 | 127 <= 6 | 5,029,445 | **ABSENT** |
| v2 | const, pats <= 2, repls <= 2, abcd (420 passes) | 3 | 127 <= 6 | 1,885,117 | **ABSENT** |
| v3 | const, pats <= 3, repls <= 2, abc (507 passes) | 3 | 127 <= 6 | (aborted: redundant after v1/v2 + m2; >4h projected) | — |
| m1 | const, paper vocab | **<= 4** (2+2 MITM, exhaustive) | 127 <= 6 | 4,625 x 4,625 pairs, 17,291 full checks | **ABSENT** |
| m2 | const, paper vocab | **<= 5** (3+2 MITM, exhaustive) | 127 <= 6 | 324,765 x 4,625 pairs, 660,164 full checks | **ABSENT** |
| var1 | VARIABLE patterns/replacements from {eps,a,b,X,Xa,Xb,aX,bX,H,Hb,len,enc,tail,init,aXb} — 210 passes; patterns computed from the ORIGINAL input (calculus semantics) | 3 | 127 <= 6 | 232,199 | **ABSENT** |
| varr | randomized variable pipelines | 4-7 | 127 <= 6 | ~10^5 tries | none; best distance 92/127 |
| rnd | randomized const pipelines (vocab abc<=2 + ab<=3) | 3-8 | 508 strings <= 7 | 1,895,658 tries | none; best full-domain distance 93/508 |
| rc1 | const, paper vocab, restricted to C_1 = strings <= 1 b | <= 4 | 28 strings | — | FOUND depth 1 (trivially [eps/b]) |
| rc2 | const, paper vocab, restricted to C_2 = strings <= 2 b's | **<= 4 and <= 5** (MITM, exhaustive) | 63 strings | 501,018 full checks (depth 5) | **ABSENT** |
| rc3 | const, paper vocab, restricted to C_3 = strings <= 3 b's | **<= 4 and <= 5** (MITM, exhaustive) | 98 strings | 623,561 full checks (depth 5) | **ABSENT** |
| vc2 | VARIABLE vocab, restricted to C_2 | 3 | 63 strings | 167,513 | **ABSENT** |

Reading: the failure is not a corner case and not a vocabulary-size
artifact.  Even restricted to the class of strings with at most TWO b's —
where the only difficulty is "delete the FIRST of (at most) two b's" — no
depth-3 pipeline with computed needles (halving, enc, tail, init, X.X
duplication, lengths) works (vc2).  The paper's randomized search is
confirmed and extended to ~2M pipelines with full-domain distance
tracking: nothing comes close (best 93/508 ~= 18% of inputs differ).

## 3. Closest-miss characterization (verify_r1.py part nm)

Distance = number of test inputs where the behavior differs from del1b.
Over ALL 324,764 non-identity depth-<=3 behaviors (paper vocab):

* minimum distance to del1b: **50/127** (39%).  Nothing within distance 49.
* the closest behaviors at d=50 are the enc/dec family: the single pass
  [a/ba] (= dec in the binary instantiation) and depth-3 composites
  [(a/aa),(ba/eps),(aa/a)] (double, delete-marker, halve — an enc-decoder
  round trip variant).  They fail on exactly the strings whose first b
  sits in a context where the code round trip disagrees with a deletion
  (e.g. b, ab, bb, aab, abb, bbb, aaab, aabb — i.e. b-first and
  b-run-initial strings).
* in the VARIABLE space the closest misses are d=50-68, e.g.
  [(Xa/a),(eps/bX),(a/Xa)] failing on 50/127.

Interpretation: the enc-flavored behaviors are "closest" because they are
the toolkit's only built-in first-occurrence-sensitive mechanism (dec
consumes the FIRST character of each xb block greedily).  But they edit
every block, not the first.  There is no family of near-misses converging
to del1b: the distance landscape has a wide gap (49 empty levels), which
smells like a structural obstruction, not a missing shallow trick.

## 4. The reduction cluster (verify_r1b.py — all green, oracle-verified)

Work over any alphabet with distinct comma/anchor structure; verified on
binary (511 strings <= 8) and ternary (1,093 strings <= 6).  Oracle nodes
('O', fn) evaluate fn(X); everything else is a genuine L-expression
(toolkit builders: enc2, dec2, eq, if).

Definitions (b = the deleted character):
P(X) = the longest b-free prefix (takeWhile != b);
Cut(X) = X[i:] with i = the first b (eps if none);
D(X) = delete the leftmost b — the probe.

**R1. P in L ==> D in L.**
D = dec2([eps/A] . [A.enc2(P) / A.enc2(P).B] . (A.enc2(X))) with A = bb
(fresh: enc2-images have b-runs <= 1), B = the enc2-block of b.  The
needle A.enc2(P).B occurs only at position 0 (its head A occurs only at
0), so the pass deletes exactly the first b's block; [eps/A] drops the
anchor; dec2 returns D(X).  No-b inputs: the needle is inert, cleanup
returns X = D(X).  *(Verified: binary <= 8, ternary <= 6.)*

**R2. Cut in L ==> P in L.**
Cut occurs in X exactly once — an occurrence at j needs X[j] = b (so
j >= i) and j + |Cut| <= |X| (so j <= i).  Hence [eps/Cut]X = P, with the
empty-Cut case guarded at the PATTERN (paper's rem:total-rep technique):
P = [eps/Cut.if(eq(Cut,eps),bb,eps)]X — when X is b-free the pattern is
bb, which cannot occur in the all-a string X.  *(Verified.)*

**R3. P in L ==> Cut in L.**
Cut = dec2([eps/A.enc2(P)](A.enc2(X))): the anchored needle A.enc2(P) is
unique at 0, and deleting it leaves enc2(Cut); no guard needed (no-b case
degenerates to eps = Cut).  *(Verified.)*

**Consequence: the hinge "D in L?" reduces to "P in L?" (equivalently
"Cut in L?") — is the LEFT-ANCHORED VARIABLE-LENGTH REGION computable?**
This is exactly the L-mirror of the paper's ONCE^R remark ("deleting a
left-anchored variable-length region seems to require computing that
region first, which is the very function sought — conjecturally
unreachable").  In L the mirrored statement is: deleting around the first
occurrence requires a needle anchored at the string start that spans the
b-free prefix — i.e. the region itself.  (The converse D ==> P stays
open.)

Also noted: the rev-twin cluster — longest b-free suffix, Cut-from-last-b,
delete-rightmost-b — is tied to the left cluster by reversal; rev in L
would identify them (and the paper's mutual-witness remark for
leftmost/rightmost deletion is exactly this).

## 5. The tie obstruction (verify_r1b.py R4 — machine-verified)

Even with P as an ORACLE, the un-anchored needle fails:

**Proposition (verified on a^i . b . a^j . b . a^k, all i,j,k <= 6, 196
inputs).**  [P/P.b](a^i b a^j b a^k) = D(a^i b a^j b a^k) **iff j < i**.
All 112 failures have j >= i (tie or longer second gap); zero failures
with j < i.

Proof sketch: the leftmost occurrence of a^m.b (m <= i) always ends at the
FIRST b (an earlier start would need a b inside the leading run), but the
needle also matches at every later b whose preceding a-run has length >=
m; the greedy scan then edits those too.  Making the replacement long does
NOT shadow them: the resume point and the later occurrences both shift
right by the insertion length — the relative distance (gap - m) is
invariant.  So a single-pass needle avoids over-deletion only if the
needle's prefix length m satisfies (leading gap) >= m > (every other
pre-b gap) — possible only when the leading gap is the strict maximum.
Ties kill it (e.g. X = abab: gaps 0, 0 — any needle matching one b
matches both).

The anchored needle (R1) breaks ties by position-0 uniqueness — but must
contain P.  The circle: to select the first occurrence one must either
(i) contain the region (compute P), or (ii) win on gaps (fails on ties).

**Shared obstruction with the L+R agent's residue-routing picture**
(their R3): the leftmost-b decision at a junction requires the COMPLETE
length of the run to its left; L's own writes at a junction carry only
BOUNDED information about that run (residues of finitely many mod-k
pairings — [eps/a^k] skeletons, offset-1 pairing), and bounded information
cannot separate ties.  Unbounded information requires a needle spanning
the run = P.  If formalized, one lemma would separate L from both ONCE
(this hinge) and R (theirs).

## 6. Files

* `oncecore.py` — primitives (subst, once), evaluator (evalL), targets,
  VOCAB (L-computable variable vocab), BFS classes.
* `verify_r1.py` — parts x (cross-checks), r (reproduce), rc (restricted
  classes), nm (near-miss), v (vocab escalation), var (variable search),
  rand (randomized deep).  Log: r1.log.
* `verify_r1b.py` — the reduction cluster (R1-R4 above).
* `search_mitm.py` — exhaustive MITM depth <= 4/5 (full domain + classes
  C_2, C_3) + variable-pattern class search.  Log: mitm.log.

## 7. Next-round plan (R2)

Positive constructions, in order of promise:
1. Parity/residue cascade: [eps/aa] puts g mod 2 at the leading run's
   end; in the halved text the first b sits at a BOUNDED position —
   case-split there, and test whether any bounded-depth cascade transfers
   the location back (the two-copy X.X scheme; the offset-1 pairing
   [eps/abab] the L+R agent flagged — test its junction corruption on our
   target shapes).
2. Structured deep search seeded with the enc-flavored near-misses (the
   d=50 family) and the toolkit vocabulary at depth 4-6 (beam by
   distance).
3. The "residue-converging family" question: is there, for each k, a
   pipeline correct on all strings with <= k b's?  (C_2/C_3 MITM results
   will tell whether the obstruction is already present at two b's.)
4. If all positive routes die: R3 invariant hunt — "bounded junction-local
   left-context information", tested against the full enumerated
   L-toolkit.

---

## 8. Paper-voice draft of the R1 conditional results (for main.tex integration)

The following is written in the paper's notation and voice, so that
integration is mechanical if the arc ends unresolved.  (Machine support:
verify_r1b.py, oracle nodes; every clause below is verified on all binary
strings of length <= 8 and all ternary strings of length <= 6.)

```latex
\begin{proposition}
    (\emph{The Once Hinge, Reduced})
    \label{prop:hinge-reduced}
    Let $b \in \Sigma$ and, for $S \in \Sigma^*$, let $i$ be the position
    of the first $b$ in $S$ (and $i = |S|$ when $S$ is $b$-free).  Define
    \begin{align*}
        P(S) \triangleq S[{:}i], \qquad
        \mathrm{Cut}(S) \triangleq S[i{:}], \qquad
        D(S) \triangleq S[{:}i]\cdot S[i{+}1{:}],
    \end{align*}
    the maximal $b$-free prefix, the suffix from the first $b$ (empty
    exactly when there is none), and the deletion of the leftmost $b$ --
    the once-node $[\,\epsilon/b\,]_1$.  Over any $\Sigma$ with
    $|\Sigma| \geq 2$:
    \begin{enumerate}[(i)]
        \item $P$ is $L$-reachable iff $\mathrm{Cut}$ is;
        \item if $P$ (equivalently $\mathrm{Cut}$) is $L$-reachable, then
        $D$ is: ``delete the leftmost $b$'' reduces to computing the
        left-anchored region before it;
        \item the un-anchored needle $[\,P/P\,b\,]$, on inputs
        $S = a^i b\, a^j b\, a^k$, computes $D(S)$ iff $j < i$: it
        deletes the leftmost $b$ together with every later $b$ whose
        preceding $a$-run is at least as long as the maximal $b$-free
        prefix.
    \end{enumerate}
\end{proposition}

\begin{proof}
    (i) ($\Leftarrow$) $\mathrm{Cut}$ occurs in $S$ exactly once: an
    occurrence at $q$ needs $S[q] = b$, so $q \geq i$, and
    $q + |\mathrm{Cut}(S)| \leq |S|$, so $q \leq i$.  Hence
    $[\,\epsilon/\mathrm{Cut}(S)\,]\,S = P(S)$ once the empty-pattern case
    is excluded at the \emph{pattern} (Remark~\ref{rem:total-rep}): the
    guarded pattern $\mathrm{Cut}(S)\cdot G$ with
    $G = \mathtt{if}(\mathtt{eq}(\mathrm{Cut}(S),\epsilon),\,bb,\,
    \epsilon)$ is $bb$ exactly when $S$ is $b$-free, i.e.\ when $S \in
    \Sigma^{*} \setminus b\Sigma^*$ contains no $bb$ over the binary
    subalphabet generated by the construction -- inert by Substitution
    Elimination, returning $S = P(S)$.
    ($\Rightarrow$) Work in the comma code: with $x \neq b$ the comma and
    $A = bb$ the fresh anchor of Proposition~\ref{prop:last}
    ($\mathtt{enc}^2$-images have $b$-runs of length $\leq 1$, so $A$
    occurs in $A\cdot \mathtt{enc}^2(S)$ only at position $0$), the
    needle $A\,\mathtt{enc}^2(P(S))$ occurs only at $0$, and
    $\mathtt{dec}^2([\,\epsilon/A\,\mathtt{enc}^2(P(S))\,]\,(A\cdot
    \mathtt{enc}^2(S))) = \mathrm{Cut}(S)$ -- when $S$ is $b$-free the
    needle is the whole text and the value is $\epsilon =
    \mathrm{Cut}(S)$; no guard is needed.
    (ii) The same anchored needle, extended by the $b$-block
    $B = x\,b$ of the comma code, deletes exactly the first $b$'s block:
    \begin{align*}
        D(S) \;=\; \mathtt{dec}^2\big([\,\epsilon/A\,]\,
        [\,A\,\mathtt{enc}^2(P(S))\,/\,A\,\mathtt{enc}^2(P(S))\,B\,]\,
        (A\cdot\mathtt{enc}^2(S))\big),
    \end{align*}
    the middle pass firing only at position $0$ and removing one block,
    the cleanup dropping the anchor, $\mathtt{dec}^2$ the code (all
    morphic identities of the Comma Code Lemma); $b$-free inputs make
    the middle pass inert and the pipeline returns $S = D(S)$.
    (iii) The leftmost occurrence of $a^m b$ ($m \leq i$) in
    $a^i b a^j b a^k$ ends at the first $b$: an earlier start would put
    the pattern's $b$ inside the leading $a$-run.  An occurrence at the
    second $b$ exists iff $m \leq j$.  A match does not shadow later
    occurrences unless they start inside the inserted text (Definition
    \ref{def:subst} never rescans it): the scan resumes at the end of the
    replacement, and both the resume point and the later occurrence shift
    right by the replacement length -- the relative distance is
    invariant.  With $m = i$ (the needle $P(S)\,b$) the second occurrence
    is taken iff $j \geq i$, and each taken occurrence deletes one $b$
    with its preceding $a^m$-context reinserted, whence the claim.
\end{proof}

\begin{remark}
    (\emph{The mirror of the once-rightmost conjecture.})  Item (ii) is
    the $L$-side mirror of the remark after Theorem~\ref{thm:once-toolkit}:
    in the once-rightmost calculus, destructuring a left-anchored
    variable-length region seems to require computing that region first.
    Here: deleting \emph{around} the first occurrence requires a needle
    anchored at the string start that \emph{spans} the maximal $b$-free
    prefix -- the region itself (item (i) makes the two region functions
    interchangeable).  Item (iii) shows the only alternative to spanning
    the region -- winning on run lengths -- fails on every tie.  So the
    once-hinge is exactly the question of whether the left-anchored
    region $P$ is $L$-reachable.
\end{remark}
```

Caveat for integration: in (i)($\Leftarrow$) the $bb$-inertness argument
needs the $b$-free input to avoid the junk pattern; over larger alphabets
the junk is chosen fresh for the subalphabet of $S$'s complement of $b$
(finitely many cases, an $\mathtt{if}$-chain over $\Sigma$).  The
machine verification covers binary and ternary exhaustively.

## 9. R1 conclusions and sharpened reading (post-MITM)

The exhaustive MITM (search_mitm.py, re-runnable: `python3 search_mitm.py
full|class|varclass`, domains stated in-section) settles the depth axis at
the paper's vocabulary: **no constant-pattern pipeline of depth <= 5
computes del1b** on the 127-string domain (660,164 candidate pairs fully
checked), and none of depth <= 5 even on the classes C_2 (<= 2 b's) and
C_3 (<= 3 b's).  Together with vc2 (variable patterns, C_2, depth 3:
ABSENT):

* the obstruction is LOCAL: already at TWO b's, no pipeline of the
  searched spaces deletes the first of the two — exactly the input shape
  where the tie obstruction bites (the needle deletes the second b too
  iff its preceding run >= the needle's prefix; the second gap >= first
  gap is a tie-or-worse);
* the paper's randomized 4-7-pass coverage is extended to EXHAUSTIVE depth
  5 with full-domain distance tracking (best random distance 93/508;
  nothing within 49 input-misses at depth <= 3);
* the enc/dec family is the nearest neighbor everywhere (d = 50/127):
  the toolkit's only first-occurrence-flavored mechanism — but it edits
  every block, and the gap to del1b is structural (50 empty distance
  levels), not incremental.

## 10. Updated round plan (coordinator steers folded in)

R2 (positive constructions):
1. Parity/residue cascade + two-copy (X.X) schemes: [eps/aa] puts g mod 2
   at the leading run's end; the halved text's first b sits at a bounded
   position.  Test transfer back via bounded case-split; test the offset-1
   pairing [eps/abab] the L+R agent flagged (its junction corruption vs.
   our target shapes).
2. Structured deep search (beam by distance, depth 4-6) seeded with the
   enc-flavored d=50 near-misses + full toolkit vocabulary.
3. The converging-family question is answered for depth <= 5 constant /
   depth <= 3 variable on C_2, C_3: NO per-class pipeline.  Extend to
   per-class VARIABLE depth 4-5 (MITM over the variable space) if R2.1-2
   show life.
R3 (invariant hunt, per coordinator): the candidate is "bounded
   junction-local left-context information": a pass's writes at a junction
   can depend on the left run only through (a) needles that SPAN the run
   (and spanning the leading run = P), or (b) bounded residue information
   (finitely many mod-k pairings), which cannot separate ties.  STRESS
   CASES that must sit on the SATISFIED side: rep_n (deletes
   variable-length regions at computed needles), enc/dec/cat/head/tail/
   eq/if/last/init, escape, X^|X|, halving.  METHOD (coordinator steer):
   test closure COMPUTATIONALLY — enumerate random compositions of
   toolkit functions and verify the invariant survives, exactly as the
   search spaces were falsified.  Align vocabulary with the L+R agent so
   the candidate is tested against both witness sets (P for us, rho for
   them).  A compositional invariant surviving the toolkit but not P
   separates L from ONCE; if it also fails rho, ONE lemma separates L from
   both ONCE and R.
R4: escalate whichever side showed life; verdict for the paper.

---

# ROUND 3 (2026-09-21): THE WITNESS -- [eps/b]_1 IS L-REACHABLE (binary)

## 11. The discovery

R2's MITM search (mirror targets) surfaced a depth-5 constant-pattern
pipeline for **rep1b = [a/b]_1 = "replace the leftmost b by a"**:

    W  =  [a/ab][ab/aa][b/ba][ab/b][aa/a]      (paper order, 5 S-nodes)
          run order: [a->aa] [b->ab] [ba->b] [aa->ab] [ab->a]

and the tail-trim lemma turns it into the paper's probe:

    del1b(X) = if(contains(X,b), tail(W(X)), X)   ==  [eps/b]_1 X

The lemma: when X has a b, W(X) = [a/b]_1 X has a leading a-run of length
n0+1 (the replacement 'a' merges into the prefix run, or is at position 0
when X starts with b), so ONE head-trim removes an 'a' from exactly that
run:  tail([a/b]_1 X) = [eps/b]_1 X.

## 12. The mechanism (the parity cascade)

Write X = a^n0 b a^n1 b ... b a^nt (gap form).  Stages:
  1. [a->aa]  double every a-run: gaps 2n_j.
  2. [b->ab]  insert 'a' before every b: every PRE-b gap +1.
  3. [ba->b]  delete one 'a' after every b: every POST-b gap -1.
  => gap 0 = 2n0+1 is the unique ODD pre-b gap: the prefix before the
     first b is the only region of X that is before-a-b but never
     after-a-b.  (Trailing gap = 2nt-1, odd but harmless: it is never
     before a b, so its residue pairs with nothing and the round-up
     halving nets identity there.)
  4. [aa->ab] greedy leftmost pairing of each a-run into (ab)-blocks:
     odd run a^{2m+1} -> (ab)^m . a   (a residue 'a' AT THE RUN'S END);
     even run a^{2m}   -> (ab)^m      (ends in 'b').
  => the junction before the FIRST b now reads ...a.b (residue then b);
     the junction before every LATER b reads ...b.b (block-final 'b').
     Alignment-dependent parity has been converted to a LOCAL junction
     difference -- this is the step the tie obstruction showed is
     impossible for needles alone.
  5. [ab->a]  greedy collapse, every (ab) block -> 'a'.  The scan resumes
     at the residue 'a' before the first b, pairs it WITH THE FIRST B and
     eats it; before every later b it resumes ON a block-final 'b', finds
     no 'ab', and that b survives.
  => net: gap 0 gains one 'a', the first b is gone:
     W(X) = a^{n0+1} a^{n1} b ... = [a/b]_1 X.

The cascade is the residue-skeleton idea of the L+R agent made to select
the LEFTMOST site: bounded (parity) information is written at the run END
(stage 4 residue), and the greedy scan (stage 5) reads it AT THE NEXT
JUNCTION -- for gap 0 the residue is what the scan consumes first.

## 13. Machine verification (verify_r3.py, all numbers from its log r3.log)

Python level (subst == paper semantics, cross-checked in R1):
  * W == [a/b]_1 AND guarded tail-trim == [eps/b]_1 on all 4095 binary
    strings <= 11: 0 failures.
  * 400000 random binary strings <= 59: 0 failures.
  * tail-trim lemma in isolation, 4095 strings <= 11: 0 failures.
Genuine L-ASTs (toolkit builders, K/V/C/S only; evaluated by
rec/lazy_pass ev_eager -- the evaluator cross-checked against the paper
semantics in R1):
  * W as 5 nested S-nodes == [a/b]_1 on all 2047 binary strings <= 10:
    exact.  20000 random <= 49: 0 failures.
  * del1b = if(contains b, tail(W), X) == [eps/b]_1 on all 511 binary
    strings <= 8: exact.  3000 random <= 39: 0 failures.
Mechanism: parity account (gap vector -> stage-3 gaps) verified on 8
sampled gap vectors including all edge shapes (n0=0, adjacent b's,
trailing gap 0).  Stage-by-stage table for X = aabaaba in r3.log.
Search provenance: found by the exhaustive depth-5 MITM (search_mitm.py,
mirror-targets run of R2b); depth <= 4 exhaustively ABSENT; del1b as a
PURE constant pipeline ABSENT at depth <= 5 (17,291 / 660,164 full checks
R1) -- the guards (contains + tail) are essential; the paper's random
4-7-pass search (74,965,097 tries over 156^5 ~ 9.2e10 = 0.08% coverage)
missed the depth-5 witness, consistent with its "closest misses differ at
exactly one position" remark (a rep1b-miss differs from del1b at exactly
one position!).

## 14. Boundary: the alphabet

The paper's own searches (once-l/L_search.py, verified) test on BINARY
strings with ternary pass vocabulary -- sound for any Sigma >= {a,b,c}
(no witness on the binary restriction implies no witness at all).  My
construction settles Sigma = {a,b} POSITIVELY.  Over Sigma >= {a,b,c}
the 5 passes break on c's: W[1:] != del1b on 2256/3280 abc-strings <= 7
(3402/5461 abcd <= 6).  Diagnosis: c's interrupt the a-run pairing
(stage 4 misaligns the residue away from the junction) and the -1 of
stage 3 only deletes 'a's (a c right after a b is not deletable by
[ba->b]).  The lift to |Sigma| >= 3 is the R4 problem -- current ideas:
per-char doubling/halving passes [s->ss],[ss->s] (content-agnostic
parity), marker-based "-1 after every b" (a fresh 3-run marker survives
all stages since doubled text has only even runs), and the fundamental
tension to resolve: the +1 mark sits at the BACK of gaps (before b's)
while the -1 hits the FRONT (after b's) -- they cancel only because
binary runs are commutative; for heterogeneous gaps the cancellation
needs a front-marked variant or a mark that the halving consumes exactly
when a b precedes the gap.

## 15. What this means for the hinge

  * The paper's sharpest probe "is 'delete the leftmost b' expressible?"
    is answered YES for Sigma = {a,b}: [eps/b]_1 is L-reachable, hence
    the once-node with constant needle/replacement is NOT the separation
    witness.  Any L/ONCE separation argument must use computed needles
    (as prop:unary-once already showed for anchored domains).
  * thm:pos-hinge direction: ONCE sqsubseteq L now needs the general
    once-node [A/B]_1 with COMPUTED A, B (the ONCE-toolkit's cat/tail/
    head/eq/if all use computed needles).  Route: escape + mark all
    occurrences of the computed needle B with a fresh constant ([c/B']
    on the comma-coded text is occurrence-faithful), which reduces the
    general node to "edit at the leftmost c-site" -- a CONSTANT-needle
    selection problem of exactly the kind the parity cascade solves.
    The missing piece there: the cascade's replacement residue is one
    constant char; a computed-length replacement needs the site POSITION
    to survive the sweep (mark-then-edit in two stages).
  * R1's reduction cluster stands (P <-> Cut, (P|Cut) => D) but is now a
    corollary-grade observation: the parity cascade computes the
    leftmost-b edit WITHOUT ever computing P -- the "compute the region
    first" barrier the paper conjectured is bypassed, not climbed.

## 16. Round log

R3: read paper open-problem statement + searches (ternary vocab, binary
domain); analyzed the ternary failures of the R2b rep1b witness; derived
the parity-cascade account (stage-by-stage); derived the reverse-parity
del1b variant, then the simpler tail-trim composition; gold-standard
AST verification (ev_eager); documented the mechanism and the boundary;
updated this report.  Next (R4): the |Sigma| >= 3 lift; then the
computed-needle once-node; then ONCE sqsubseteq L or the exact boundary.

---

# ROUND 4 (2026-09-21): THE |Sigma| >= 3 LIFT -- BLOCKED FOR THE PARITY FAMILY, BOUNDARY SHARPENED

## 17. Coordinator cross-verification

The coordinator independently re-ran the witness through the paper's own
cross-verified evaluator: W exact on all 511 binary strings <= 8, and my
full battery green at both levels.  Confirmed dead: the "junction-local
bounded left-context" invariant family for hinge 1 -- the cascade reads
exactly bounded (parity) information at the junction, so no such invariant
can separate L from ONCE.  The rev/L+R obstructions (crossings,
residue-position) are untouched.  ONCE-side unification is dead; the
computed-needle question is the live front.

## 18. What breaks over |Sigma| >= 3 (diagnosis, machine-confirmed)

W's five passes treat c's as inert chars: every maximal a-run is
doubled/marked/paired/collapsed INDEPENDENTLY.  Consequences, verified:
  * a-runs strictly inside gaps round-trip to identity (a^k -> ... -> a^k):
    the damage is localized to junction-adjacent runs.
  * W[1:] == del1b fails on exactly those strings where some gap j >= 1
    STARTS with 'c' (stage 3 [ba->b] cannot delete the unit after such a
    b, so gap j's parity accounting drifts and b_{j+1} gets eaten too), or
    where gap 0 does not END with an a-run (the residue lands mid-gap, not
    at the junction).  Damage rate: 2256/3280 abc-strings <= 7,
    102/384 on the c-spliced domain.

## 19. The homogeneity obstruction (why the parity family does not lift)

The cascade's selection = a two-step conversion:
  (i) a GLOBAL parity asymmetry: the gap before the first b is the only
      pre-b gap that is never post-b, so [+1 before every b][-1 after
      every b] leaves gap 0 odd and all other pre-b gaps even;
  (ii) a LOCAL conversion: the greedy pairing [aa->ab] turns run parity
      into a residue 'a' at the junction, which the final greedy walk
      eats together with the first b.
Step (ii) needs homogeneous (single-letter) runs, and step (i)'s
cancellation needs front-deletions to commute with back-marks -- true
within an a-run, false across mixed content.  Every repair scheme tried
re-instantiates the original selection problem:
  * front-marks (+1 after every b) land at the wrong gap end; the
    migration pass [ba->ab] moves ALL of them globally.
  * sentinel sandwiches [b->aab]/[b->aba] mark every junction alike.
  * heterogeneous [-1 after every b] (per-sigma [b.sigma -> b]) cascades:
    sequential passes re-match at exposed positions, deleting a
    data-dependent number of chars (2 for a gap starting ac, 1 for ca).
  * a^k-codings of {a,c}* into {a}* do not exist (no injective code), so
    the binary cascade cannot be "escaped around"; the comma code keeps
    gap interiors heterogeneous, and the paper's own general-alphabet
    reduction (main.tex:1597, Horner into a-tallies) lives at the level of
    RECURSIVE definitions, not of passes -- it does not transfer.
In the comma-coded world the heterogeneous [-1] IS solved (the char
after every b is always the comma), which is a real gain -- but the gap
interiors stay mixed, so the pairing still fails.

## 20. Search statistics for the lift (all negative, all re-runnable)

  * Paper vocabulary (156 passes, patterns/repls <= 2 over abc), c-spliced
    domain (binary <= 5 with one c at every position, 384 strings):
    exhaustive MITM depth <= 4 and <= 5: NO witness for rep1b
    (925 full checks).  search_lift.py mitm3, lift.log.
  * Cascade-shaped vocabulary (35 passes: doublings, halvings, marks,
    sandwiches, junction swaps), same domain: exhaustive MITM depth
    <= 6 (3+3): NO witness (6,687 full checks).  search_lift2.py
    stage4, stage4.log.
  * Repair-suffix search: [repair <= 3 passes] o W on the c-spliced
    domain (15,710 states explored): NO repair.  search_lift2.py wpre,
    wpre.log.

## 21. The live lead for R5: the anchored-needle reduction

R1's cluster (verify_r1b.py) already machine-verified, OVER TERNARY TOO:
P (the longest b-free prefix) implies D via the fresh-anchored needle
A.enc2(P).B with A = bb (fresh in every enc2-image) -- the anchor kills
the tie obstruction.  So the |Sigma| >= 3 lift reduces to computing P
(or a prefix tally a^{|P|}) -- and the first-b index is PRESERVED by the
c-deletion projection pi = [eps/c]X (one pass), over which the binary
cascade machinery applies.  Concrete R5 sub-problems:
  (a) is the prefix tally a^{|P|} L-computable over binary?  The
      cascade's stage-4 text T4 = (ab)^n0 . a . b . ... carries a
      complete encoding of n0 at the string head; extraction needs a
      "delete the variable tail" step (an end-anchored fresh needle, the
      prop:last device, over enc2-space).
  (b) if (a) is yes: ternary del1b = the R1 anchored construction with
      P replaced by the pi-projected tally (the c-positions inside P are
      exactly what the anchored needle does NOT need to know -- it needs
      only the b-free PREFIX LENGTH plus a fresh anchor; the needle
      A.enc2(a^{|P|}).B pins the site by length, and enc2-faithfulness
      does the rest).  [to be verified]
  (c) the computed-needle once-node [A/B]_1 for ONCE sqsubseteq L:
      escape + [c/B']-marking reduces it to "edit at the leftmost
      c-site", the parity cascade's home turf -- the missing piece is a
      replacement of computed (variable) length at the marked site.

## 22. Round log

R4: coordinator cross-verification received; diagnosis of W's c-damage
(localized to junction-adjacent runs); the homogeneity obstruction
formulated after systematic design-space walk (front/back marks,
migration swaps, sandwiches, per-sigma deletions and their cascades,
comma-coded worlds, a^k-codings, the paper's recursive-level alphabet
reduction); three exhaustive/near-exhaustive searches launched and
completed negative (mitm3, stage4, wpre); R5 lead identified (the
anchored-needle reduction via the pi-projection and the prefix tally).
Files: search_lift.py, search_lift2.py, verify_r3.py, REPORT.md (this
file); logs lift.log, stage4.log, wpre.log, r3.log.

## 20b. Additional negative: the pre/post wrap (R4c)

[post <= 2] o W o [pre <= 2] over the cascade vocabulary: 1,590,121 wraps
checked (early abort) on the c-spliced domain, 0 candidates
(search_wrap.py, wrap.log).  W cannot be repaired by escaping in and out
with up to 2 passes on either side.

## 23. Structural observation: complementary alphabet requirements

Two selection devices emerged from this investigation:
  - the PARITY CASCADE (the witness): needs homogeneous gap filler
    (|Sigma| = 2) and NO fresh patterns (it encodes onto the data itself);
  - the BLOCK-ENCODING device (fresh junction patterns like "bab" that
    distinguish keep-sites from eat-sites, needed for keep-vs-delete
    distinctions such as extracting P.b or prefix tallies): needs a third
    character (over {a,b}, any block encoding ending in 'b' contains
    "ab", and any avoiding "ab" cannot end in 'b').
They have OPPOSITE alphabet requirements, so they cannot be composed over
either alphabet: over |Sigma| = 2 the cascade works but extraction dies;
over |Sigma| >= 3 extraction-freshness works but the cascade dies on
heterogeneous gaps.  This is the sharpest statement of why the |Sigma| >= 3
lift resists: it needs a selection mechanism that is simultaneously
heterogeneity-tolerant AND fresh-pattern-free.

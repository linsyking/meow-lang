# ROUND 8 REPORT — HARDENING: periodic index masks, two-color profiles, the measure form

Lane B (rev-split). Charter: the coordinator's round-8 message (candidate (a):
one grammar whose index-set mask is GENUINELY PERIODIC, closing the disclosed
machine-coverage gap in INV4's S-i rule; candidate (b) if early: the measure
form INV3 on the same executable footing, FORM coordinated with Lane D's
round-7 OL-2 needs). Family D(k;3). Theory first; machine confirms.

Artifacts: `gram8.c`, `gram8` (binary), `gram8.log` (`./gram8 gram`), 
`gram8_meas.log` (`./gram8 meas`). Nothing else touched; gram7.c and all
earlier artifacts frozen (round-7 logs remain byte-verified).

**Verdict: (a) DELIVERED and machine-exact. (b) DELIVERED as form (the
charter's stated scope) — four measure closed forms, per cell, three-way
checked. The round also surfaced a REQUIRED REFINEMENT of INV4's profile
clause (two-color profiles), with measured evidence — this is the substantive
finding and is in §2.**

---

## §0 What landed

1. **The genuinely periodic mask** (`mod2`): an expression whose fired set is
   the residue class {even j ∈ [2..k−1]} — periodic in the site index with
   period 2, NOT an interval, NOT a threshold, NOT a periodic *coefficient*
   riding an interval family. The grammar pins the surviving family as the
   ODD residue class mod 2 via a masked OF. Directive count k-independent
   (6/8 per cell). Machine-exact at k=3..12, both parity cells.
2. **The two-color profile refinement**: outputs with consecutive b's have
   exponentially many zero a-runs in the round-7 a-run-only view (measured:
   25 two-color entries vs 199,297 a-run entries at k=12) — the a-run-only
   profile would break INV4's polynomial-expansion clause. The two-color
   profile (a-runs AND b-runs, maximal b-runs) absorbs the zero-structure
   into b-run VALUES (anchored exponentials + periodic corrections — the
   unchanged form class) and keeps the expansion polynomial. Round 7's 17
   grammars are b-simple (all b-runs = 1 — now machine-SELF-CHECKED, not
   assumed), which is exactly why the a-run-only view sufficed there.
3. **The measure form (INV3) on the same footing**: hand EPT closed forms of
   the a-count and b-count for tile4, mod2 (both cells), decb, thresh —
   residue-class geometric sums — checked three ways (closed form vs text
   counts vs grammar-expansion sums), k=3..12 per cell. 144 checks, 0
   failures. This is the channel Lane D's OL-2 wants (§3).

Totals: `./gram8 gram` = 478 checks, 0 failures (19 grammars × k-ranges);
`./gram8 meas` = 144 checks, 0 failures. Both 0.5s / 0.1s. Rebuild from
source reproduces both logs byte-identically.

---

## §1 The construction (theory first)

### 1.1 The periodic family: tile4 = [b/'aaaa']X

Pattern 'aaaa' is b-free with p = 4; the pass scans run j = a^{3^j}: windows
tile from offset 0 (a window cannot cross a b, and the greedy leftmost
scan restarts at each run's first char), so run j's output is
'b'^{⌊3^j/4⌋} · a^{Λ_j} with the remnant

  Λ_j = 3^j mod 4 = 1 (j even), 3 (j odd)  — **periodic in j with period 2**.

(For j ≤ 1, ⌊3^j/4⌋ = 0 and the "remnant" is the whole run: Λ_0 = 1,
Λ_1 = 3 — the same formula.) Two-color profile (maximal b-runs):

  [a:Λ_0, b:1+⌊3^1/4⌋, a:Λ_1, b:1+⌊3^2/4⌋, …, a:Λ_{k−1}, b:1+⌊3^k/4⌋, a:Λ_k],

i.e. OF j=0..k−1: [T(a=Λ_j); T(b=1+(3^{j+1}−Λ_{j+1})/4)]; T(a=Λ_k).
4 directives (OF + 2 body + final T), 2k+1 entries. Hand-checked at k=3 (profile
[1,1,3,3,1,7,3]) and k=4 ([1,1,3,3,1,7,3,21,1]) by direct text
construction before coding; machine-exact at k=3..12.

### 1.2 The genuinely periodic fired set: mod2 = [b/'bab']tile4

P = 'bab' is multi-b, m = 1: by the round-6 PO-1 anatomy a window is a
stretch of two consecutive scrutinee b's β₀, β₁ with the interior run
matching c₁ = 1 EXACTLY and zero boundary runs (c₀ = c₂ = 0 — always
satisfiable). In tile4's text, the a-runs with a b on both sides are
exactly the remnants Λ_j, j ∈ [1..k−1] (Λ_0 has no b before it; Λ_k none
after; b-pairs inside a b-run have interior 0 ≠ 1). So the match test is

  Λ_j = 1  ⟺  3^j ≡ 1 (mod 4)  ⟺  **j EVEN**,

and the fired set is **{even j ∈ [2..k−1]}** — the residue class mod 2 with
the V-fixed pre-period {j ≥ 2} (j = 0 excluded by the text boundary, j = 1
by Λ_1 = 3). This is an EPT-refined Ind predicate of exactly the form
AIS-CLOSURE states (interval × residue), and it is NOT expressible as a
finite union of intervals: the gap the charter targets. Greedy leftmost =
the sites in increasing j (no match can start before the first site);
the material separating the windows at even j and even j+2 is exactly
⌊3^{j+1}/4⌋ + Λ_{j+1} + ⌊3^{j+2}/4⌋ ≥ 6 + 3 + 20 = 29 characters (the
remaining b's of b-run(j→j+1), the odd remnant Λ_{j+1} = 3, the b's of
b-run(j+1→j+2) before β₀), so the windows are disjoint and greedy
leftmost fires exactly the residue class.

Effect of a firing at even j (PO-1: interior cut freedom zero — the
interior run is consumed whole; bites are the pattern's own boundary runs,
here 0):

  window = [last b of b-run(j−1→j)] + a^{Λ_j} + [first b of b-run(j→j+1)] → 'b',

so a-run j is deleted and the surrounding b-material merges into ONE b-run

  b-merged(j) = ⌊3^{j−1}/4⌋ + 1 + ⌊3^j/4⌋   (two bite-adjusted b-runs + insert)

— a merge of 3 b-pieces per firing, inside the Merge Lemma's (D_V+2)
budget. The surviving a-runs: j = 0 and the ODD residue class. The
**per-cell** structure (the formalism's cells, parameter k mod 2):

  k odd:  [a=1; b=1; a=3; OF j odd in [3..k]: [b=merged(j); a=3]]
  k even: [a=1; b=1; a=3; OF j odd in [3..k−1]: [b=merged(j); a=3];
          b=1+⌊3^k/4⌋ (untouched — no window at even j=k exists, as β₁
          would need a b after the final a-run); a=Λ_k=1]

The **OF's index set carries the periodic mask** (mod 2, residue 1): the
masked family is still ONE directive; grammar size stays k-independent
(6 directives odd cell, 8 even cell). Hand-derived at k=3 (odd cell,
profile [1,1,3,9,3] — verified by direct text construction:
`[b/'bab']([b/'aaaa']X) at k=3 = abaaabbbbbbbbbbaaa`) and k=4 (even cell,
[1,1,3,9,3,21,1], likewise by direct construction) before coding; the
machine confirms at k=3..12. The k=12 profile head:
[1, 1, 3, 9, 3, 81, 3, 729, 3, 6561, 3, 59049, 3, …] — the masked family
and the merged b-runs (3^{j−1}+3^j)/4 = 9, 81, 729, … visible directly.

Machine cross-check on the fired set: surviving a-runs = (entries+1)/2,
so #fired = (k+1) − (entries+1)/2; checked equal to ⌊(k−1)/2⌋ = |{even j ∈
[2..k−1]}| at every k (the residue-class count).

### 1.3 Why this closes the S-i gap

Round 7's engine implemented interval index sets only; the S-i rule's
span/mask consumption point had only the [rec] battery's 557 slots as
indirect confirmation. Round 8: (i) the engine's F and OF directives take
a mask (j in set iff j ≡ mres mod mmod) — the Ind residue predicate made
executable; (ii) mod2's grammar USES it as the load-bearing structure
(mutation test: disabling masks fails mod2 at every k, §4); (iii) the
fired set enters the grammar exactly as AIS-CLOSURE says — the complement
of the mask times the interval, bite-adjusted at the edges (here bites are
0, the general case is round 7's thresh) — and the R-insertion merges are
within the Merge budget (3 b-pieces here). The two PO-3 consumption
points are unchanged; nothing new is consumed.

---

## §2 The two-color profile refinement (the formalism finding)

**The defect in the round-7 statement.** Round 7's INV4 pinned the "run
sequence" (a-lengths, b's implicit). That is only complete for outputs
without consecutive b's: tile4's output has ⌊3^j/4⌋−1 zero a-runs between
window-b's, and the a-run-only profile of tile4 has

  #a-run entries = #b's + 1 = Σ_{j=0..k} ⌊3^j/4⌋ + k + 1 = Θ(3^k)

entries — at k=12: **199,297** (machine-measured; formula: (S − ΣΛ_j)/4 +
k + 1 = (797161 − 25)/4 + 13). A V-fixed grammar cannot pin a
Θ(3^k)-length sequence (INV4's clause: expansion ≤ (k+2)^{D_V}·M_V,
polynomial). The a-run-only profile is therefore not an invariant of the
class; it worked in rounds 5–7 only because every battery output was
b-simple.

**The refinement.** The profile is the TWO-COLOR run sequence: the
alternation of maximal a-runs and maximal b-runs
[a_0, b_0, a_1, b_1, …, a_m] with every b_i ≥ 1, interior a_i ≥ 1, and
a_0, a_m ≥ 0. Consecutive b's form ONE b-run — the zero-structure is
absorbed into b-run VALUES, which are anchored exponentials plus periodic
corrections (tile4: 1 + (3^{j+1} − Λ_{j+1})/4) — the unchanged EPT form
class, so AIS-CLOSURE needs no new closure properties. The expansion is
polynomial: #b-runs ≤ #a-runs + 1, total entries ≤ 2M+1 where M is the
old a-run bound; the constants absorb this at run level. The Z-rule
restates as: zero a-runs are not entries (they are b-run merges).

**What changes in INV4 (wording for Lane A).**
- Profile clause: "the grammar emits the two-color run sequence (a-runs
  and b-runs, maximal b-runs)" — expansion ≤ 2·(k+2)^{d}·(D_V+2)·M_V
  entries; clause (ii)'s 8·#S+O_V(1) run-level count is unchanged if runs
  are counted per color, or with the factor 2 absorbed into O_V(1).
- Merge Lemma: b-runs enter as mergeable pieces with the same per-window
  budget — an emitted b-run merges ≤ D_V+2 pieces (mod2 demonstrates 3).
- S-rules: unchanged in structure; the S-i span/mask predicate applies to
  both colors' index sets; S-ii's insertions can create b-material (here
  the inserted 'b' participates in a 3-piece merge).
- Per-cell grammars: unchanged mechanism; mod2's cells are selected by
  k mod 2 (a T_V-type periodic parameter, T = 2) — now executable.

**Backward compatibility, machine-verified.** All 17 round-7 grammars run
in BOTH modes: the round-7 a-run mode (regression, exact — same
comparisons as round 7) and the two-color mode, where the engine weaves
b=1 entries and SELF-CHECKS that every b-run of the text is exactly 1
(the b-simple property is now a checked precondition of the weave, not
an assumption). 17/17 in both modes.

**The T_V note (standing, per the coordinator's decision):** unchanged —
T_V's lcm domain spelled out as {2} ∪ {ord_p(3) : p a pattern/tiling
modulus coprime to 3} ∪ {p : p such a modulus}; both constants kept
(8·#S+O_V(1) run level; (d+2)·M grammar level). Note this round's mask
uses p = 4 (not coprime to... 4 is coprime to 3; ord_4(3) = 2): consistent
with the domain statement — the mask's period 2 IS ord_4(3).

---

## §3 The measure form (INV3) on the same footing — the Lane D channel

Charter scope for (b): the FORM, not the proofs. The engine gained a
`[meas]` mode: for each of decb, thresh, tile4, mod2 the HAND closed forms
of the a-count and b-count are checked three ways at k=3..kmax per cell —
closed form vs text counts, grammar-expansion sums vs text counts:

- decb: v_a = (k+1)·S, v_b = k².
- thresh: v_a = (k+1)·S − 6(k−1), v_b = k² − (k−1)  (k−1 firings).
- tile4: v_a = #(even j ∈ [0..k]) + 3·#(odd j ∈ [1..k]);
  v_b = k + ((3^{k+1} − 3)/2 − (3o+e))/4, o = #odd[1..k], e = #even[1..k].
- mod2, k = 2m+1: v_a = 1 + 3(m+1); v_b = 1 + 9(9^m − 1)/8.
- mod2, k = 2m: v_a = 2 + 3m; v_b = 1 + 9(9^{m−1} − 1)/8 + 1 + (3^k − 1)/4.

All 144 checks pass. The FORM, for Lane D's OL-2/S4.3-general channel:
**measures of two-color profiles are anchored exponentials + affine +
residue-class-periodic terms; a periodic fired set enters the measure as
a parity split of the geometric sums** — the odd/even residue sums
collapse to geometric series in 9 = 3² (e.g. mod2's v_b = 1 + 9(9^m−1)/8:
the merged-b family (3^{j−1}+3^j)/4 summed over odd j). The window cost
is linear in #fired with #fired = the residue-class count. This is the
EPT phenomenon at measure level and is exactly the shape their OL-2
consumes; no proofs were touched.

---

## §4 Machine record

- `gram8.c` (new file; gram7.c frozen): engine extensions —
  (1) Drec gained `mmod, mres` (periodic mask on F and OF index sets;
  the 17 round-7 grammar literals are UNCHANGED — the new fields default
  to 0 = no mask, C semantics); (2) per-cell grammars (cellk: d/nd for
  k odd, d2/nd2 for k even); (3) `profile2` two-color extraction;
  (4) `weave1` + the sep1 self-check (all b-runs = 1) for the round-7
  grammars; (5) `[meas]` mode. Battery + evaluator identical to round 7
  except two new entries (CONSTS gained "aaaa" at index 13).
- `gram8.log` = `./gram8 gram`: 19 grammars — 17 round-7 regression
  (both modes) + tile4 + mod2 (two cells): **478 checks, 0 failures**,
  0.5s. mod2 expansion 15 entries at k=12; tile4 25 entries at k=12.
- `gram8_meas.log` = `./gram8 meas`: **144 checks, 0 failures**, 0.1s.
- **Mutation tests** (scratch copies in /tmp, not artifacts): masks
  disabled → mod2 fails at every k (length + fired-count checks);
  profile2's b-walk corrupted → 126 FAILs; f_b4nxt off-by-one → 10 FAILs.
  The new checks have teeth.
- **Determinism**: rebuilt from source; both logs reproduce
  byte-identically.
- **No machine-caught hand errors this round** (round 7 had two). Honest
  reading: the construction rides on round-5/7-verified arithmetic (Λ =
  3^j mod 4; the merged-b derivation), and both cells were hand-derived
  and text-verified at k=3/k=4 BEFORE coding; the machine's role was
  confirmation at 10 ks per cell, per the discipline. The mutation tests
  are what establish that a wrong derivation WOULD have been caught.
- **Scope still not directly machine-verified** (disclosed): (i) masks
  with modulus > 2 (engine supports arbitrary mmod; only mod 2
  exercised — the natural next case is p = 7, ord₇(3) = 6); (ii) masked F
  (kind 1) — implemented, unexercised; (iii) masks at OF depth ≥ 2
  (composition untested); (iv) the Merge Lemma's b-piece budget beyond the
  demonstrated 3; (v) the INV3 proofs themselves (form only, per charter).

---

## §5 Next-round candidates

1. **Modulus > 2**: a fired set periodic with period ord_p(3) > 2 (p = 7
   gives period 6; p = 13 gives 3) — exercises arbitrary mmod and a
   pre-period structure richer than an interval cut. Closes the remaining
   disclosed scope item (i).
2. **INV3 proofs** (beyond form) — only if Lane D's OL-2 lands and wants
   the channel deepened; otherwise the form delivered here suffices.
3. Standing: T_V wording to Lane A (§2); both-constants decision recorded.

*— Lane B, rev-split, 2026-09-22. Machine checks confirm hand
derivations; they do not replace them.*

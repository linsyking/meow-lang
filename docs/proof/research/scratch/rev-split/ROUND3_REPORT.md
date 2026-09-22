# ROUND 3 REPORT — rev-split lane: the Telescope at varying k (Lane B)

[Transcribed by the coordinator from the lane's final message,
2026-09-22. Machine artifacts on disk: varying_k.c / varying_k /
varying_k.log (rebuilt and re-run by the coordinator; OPS/CEN/FP
exact, SD/SB seed-dependent counts with 0 failures at every probe —
the log's invocation was unrecorded, the lane's bookkeeping slip #3).
Coordinator's OVERVIEW entry is the verification record.]

Everything green — full battery 1,755,621 checks, 0 failures, 0.8 s;
the round-2 drift check surfaced one number (schema_p.log run 1 reads
765 exprs / 293,507 cells; the OVERVIEW entry had 293,307 — the
coordinator's transcription slip, since corrected in place).

## 1. Task 1 — THE MULTIVARIATE TELESCOPE (Theorem MT)

*Survives, k-free (part a):* the per-pass accounting `N_out = N_F +
c_w(N_R−N_P)`, `M_out = M_F + c_w(M_R−M_P)` (exact, any k), and all
three count mechanisms — tiling `c_w = (T_c − Λ)/p` with Λ now a sum
over **k+1** runs; computed moduli via slabs; anchored/adjacent via
site conditions. For each **fixed** k the same ordered refinement
(slabs → residue classes of the run-vector → pinned-polynomial
coincidence cuts) is locally finite in the (k+1)-dimensional
run-vector space: counts and totals are functions of (S_a, k) on
cells.

*The "cannot" (part b — the charter's guess is false as stated):*
**totals are NOT functions of (S_a, k).** Witness: the
ceiling-halver [a/aa]X has `N = Σ⌈r_t/2⌉ = (S_a + ν)/2` with ν =
#odd runs; at fixed (S_a, k), ν takes every value of the right
parity in [0, k+1], so N takes **⌈(k+1)/2⌉ distinct values — Θ(k)
spread** (machine-verified exactly, k = 1..7, every composition).
Site-local data is not uniform because each site contributes an
independent residue: any statistic determining Λ = Σ(r_t mod p) must
read Θ(k) bits. The correct surviving pinning is the
**residue-vector**: finite per k with #cells = M^{k+1}·(slabs)·
(coincidences) — **no k-uniformly-bounded finite partition exists**,
and no quasi-polynomial-in-(r_0..r_k, k) family at the (S_a,k)
granularity. This is exactly the degeneration of the fixed-k
"S-function per cell".

[Coordinator's bridge note for Lane C's lemma 1: the halver
degeneration does NOT kill the pinned-schema on the super-increasing
family w^(k), where the family itself pins the residues (one odd
run, distinct powers); the lemma must exploit the family's residue
structure rather than assert a general (S_a,k)-granularity.]

## 2. Task 2 — centerpiece: the uniform-interleave calculus, three
firing constraints, and the Separation Budget

**FU calculus.** Every S-node value is `q_0 R q_1 R … R q_t`, same R
at every firing, remnants in input order; positions flow by: X ↦
identity, K ↦ ∅, C ↦ concatenation, S ↦ block-deletion ∪
replication-interleave of Σ(R) at window positions.

**Lemma SD (site distinctness).** If a scrutinee's positive runs are
pairwise distinct and the pattern has ≥ 2 b's with at least one
positive interior run, the pass fires **at most once**. Proof: two
windows would put equal interior run-sequences at two distinct
skeleton positions; positive-run distinctness forces the same
position, contradicting disjointness. Exception class: b^q-type
patterns (all interiors zero) — the T5 tilers. Sharp both ways
machine-verified: 2007 qualifying cases, 0 multi-firings; 1036/1993
controls (q ≤ 1 or 'bb'-type) fired multiply.

**Theorem FP (final-pass constraint).** If E(w) = rev(w) with w's
runs positive and pairwise distinct, and the top S-node fires t ≥ 2
times, then R(w) has **at most one b**. Proof: the t disjoint copies
of R(w) sit verbatim in rev(w); each copy's consecutive b's are
consecutive skeleton b's of rev(w), so each copy's interior run
profile equals rev's local profile; two copies with ≥ 2 b's and a
positive interior force the same skeleton interval (distinctness),
contradicting disjointness; the all-zero-interior case contains
'bb', excluded by positive runs. Machine: 4000 forced multi-b
multi-fire cases — every output ≠ rev with the repeated profile;
Lane C's E_rev: 343/343 correct reversals with top pass exactly
t = 1 (consistent: its top R = 'b'). [Converges with Lane C's
hand-proved Final-Pass Lemma, round 16 §2.]

**Theorem SB (Separation Budget — the no-progress lemma, merge-free
regime).** Label each a-character by its input run. Call a derivation
**merge-free** if every maximal a-run of every value carries material
from ≤ 1 input run. Let Φ'(V) = # of distinct input-adjacent pairs
(t, t+1) appearing as a *reversed separation* in V(w) (a b with run
t+1's material immediately left, run t's immediately right). Then
(i) Φ'(rev(w)) = k for every w ∈ W_k — no genericity needed; (ii)
merge-free derivations satisfy Φ'(S(R,P,F)) ≤ Φ'(F) + Φ'(R) + 4 and
Φ'(C(A,B)) ≤ Φ'(A) + Φ'(B) + 2 — the multi-firing junction pairs
collapse because each new pair is **pinned by one of R's four
boundary-adjacent run labels**, so t firings contribute ≤ 4
*distinct* pairs regardless of t; hence **Φ'(E) ≤ 4·#S(E) + 2·#C(E),
a fixed budget**. (iii) **No merge-free E computes rev on W_k for k
beyond its size — in particular no merge-free unifier exists, and
any unifier must merge input-run material into common a-runs on
every input with k > 4#S + 2#C.** Machine: 2112/2112 random
merge-free derivations respect even the tighter 2#S + 2#C (the
tight constant is open; the hand proof gives 4/2).

**Pollution witness (merge-freeness is load-bearing).** E_poll =
[(merge·b)/'aa']merge: one pass whose every junction separation sits
between merged runs carrying **all** labels — Φ' = k with budget 8
(verified at k = 9, 10). So merging is the unbounded flip-creating
resource; flip-counting alone can never prove the no-go.

**Lemma DECOMP.** C-nodes split the problem: if E(w) = A(w)·B(w) =
rev(w) then A(w) = rev(suffix), B(w) = rev(prefix), and inductively
the fixed C-tree's leaves reverse a partition of w into consecutive
intervals in reverse order; by pigeonhole some leaf's subtree
reverses an interval with unboundedly many separators, and its top
must be an S-node (X only reverses separator-free intervals, where
rev = identity). This reduces the unification question to S-topped
trees reversing unbounded-separator intervals — exactly where SD,
FP, and SB apply.

**Open core (precise).** Can merging + q ≤ 1 patterns (the
k-adaptive class: SD and FP push all bulk work there) reverse
unbounded k at fixed size/depth? The budget theorem shows any
impossibility proof must fire in the mergey regime; E_poll shows
order-inversion alone is cheap there — the obstruction, if it
exists, must live in run-length exactness (final singleton runs with
the exact reversed lengths). For Lane D: any invariant candidate
that holds merge-free is already budgeted and cannot obstruct; it
must be merge-sensitive. For Lane C: every multi-firing final
replacement is confined to ≤ 1 b, and multi-b positive-interior
patterns are single-firing on distinct-run texts — the constructive
channel is narrow and precisely mapped.

## 3. Task 3 — toll at varying k: the exclusions STRENGTHEN, nothing
becomes vacuous

At each fixed k the same machinery runs in the (k+1)-dimensional
vector space; the level-pigeonhole needs S_a beyond N(k) = #cells
meeting the slice (finite per k, growing with k: M^{k+1}·poly).
Since an E computing a b-free split on the union U_kW_k would compute
it on each W_k, the per-k exclusion (S_a > N(k)) kills the union
statement outright — the k-dependence enters only through the
per-k threshold, never the conclusion. Caveat at round-2 honesty bar:
conditional on the general-k profile write-out (Schema P was proved
at k = 2; the mechanisms are k-free per Theorem MT(a), so the
skeleton carries over — same status as round 2's Lemma S: closed at
skeleton level). No new obstructions appear at varying k, and none
are needed. (D_last's a-total is S_a — Lemma S concerns totals and
counts, not run lengths; its run profile (r_0, r_{k−1}+r_k) is
pinned-polynomial, as Schema P claims.)

## 4. Task 4 — Lane C's k-adaptive mechanisms classify correctly; no
new profile entry needed

D_last = [ε/(b·mrg·a)](X·mrg·a) and D_first are q = 1, zero-interior
patterns whose S-domination flank (S_a+1) pins a single firing at
the last/first separator **whatever k is** — verified in closed form
on all 349,524 run-vectors for k = 1..8 including zero runs, along
with the skeleton-preserving shave [b/ab], the merge-shave [ε/ab]
(fires at junctions with r_t ≥ 1, b's survive exactly at zero-run
junctions), and the halver. Concatenated scrutinees are covered by
P0 (concatenation = junction merge of profiles); the counts of
multi-site k-adaptive ops are census statistics — (S_a, k,
residue-vector)-functional per MT, exactly as Lemma S requires at
fixed k. The only write-up action: make explicit that F may be a
concatenation node and that profile operations apply verbatim.

## Machine record (all in rev-split/, all ≤ 1 s)

`varying_k.c` / `varying_k` / `varying_k.log` — five modes: SD (2007 +
controls), OPS (1,747,600 checks over k = 1..8), CEN (all
compositions, k ≤ 7, exact parity-census law), FP (4000 + Lane C
engine 343), SB (2112 merge-free + witness). **Total 1,755,621
checks, 0 failures.**

[Coordinator's reproduction note: OPS/CEN/FP exact at the default
and probed seeds; SD/SB case counts seed-dependent (default tr=400:
203/197/400/214); 5 fresh seeds at tr=4000 all give the exact total
1,755,621 / 0 failures; the lane's seed was unrecorded — told to log
the full invocation (mode, seed, trials) in the log header from now
on.]

## Status and next-round candidates

The unification question is now precisely located: bounded-depth
reversal must be mergey, k-adaptive (q ≤ 1 bulk), and length-exact;
the flip budget is closed. Next round candidates: (a) a
merge-sensitive budget (charge pollution to the merging passes and
bound total creation-then-deletion under length exactness); (b) the
tight SB constant; (c) the general-k profile write-out to make the
toll lift unconditional.

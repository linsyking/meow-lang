# CHARTER (round 4 for this lane): MAJOR INTEGRATION — 15C + B-2 + THE FRONTIER REWRITE

Coordinator, 2026-09-22. Everything below is verified by me
(machine: fresh encodings, byte-identical reproductions, hand-traced
witnesses) and recorded in research/OVERVIEW.md — the "Lane C round
15C + Lane B round 2 verification" section and the "Correction +
exact engine sizes" section directly below it. RULE: every claim you
integrate must trace to those entries or to the artifacts listed;
where the record says "skeleton-level" or "refuted as stated", the
paper must say exactly that. No new math.

## Part 1 — the record (research/scratch/rev/REPORT.md; your writes there work)

1. ROUND 15C (Lane C's report is verbatim at
   /home/cc/.claude/jobs/54aca51d/tmp/laneC_report.md — 8 KB; the
   round-15 and 15B context is already in rev-try/REPORT.md):
   - E_rev = [b/(a.mrg.b)](Cc.a.Bb) computes rev on W2 =
     {a^i b a^j b a^k} — MERGE-CATALYZED SELECTIVE DELETION. mrg =
     [e/b]X = a^S; P1 = [e/(b.mrg.a)](X.mrg.a) = a^i b a^{j+k}
     (fires only at b#2: following run k+S+1 >= S+1 vs b#1's j <= S);
     P2 = [e/(a.mrg.b)](a.mrg.X) = a^{i+j} b a^k (only at b#1);
     Cc = [b/P2](mrg.b.mrg) = a^k b a^{i+j}; Bb = [b/P1](mrg.b.mrg)
     = a^{j+k} b a^i; T2 = Cc.a.Bb; final pattern a^{S+1}.b fires
     only at T2's second b, shaving exactly S+1, leaving j. The
     K('a') pad and the +1 are PAIRED EDGE-GUARDS (no middle-run
     isolation — 13.7's wall is bypassed, not broken).
   - V_h-equivalence survives with witness h=0: V_0 IS E_rev's
     value. PREFIX-DOMINANCE (Lane D's round-1 invariant) is REFUTED
     as a universal invariant: V_0 = a^k b a^j b a^i has lead run
     k-typed (0,0,1); also V_1 = a^k b a^{j+1} b a^{i+1} =
     [b.a/b]E_rev. Escape mechanisms (for the record): (a)
     merge-padded CONCATENATED scrutinees (X.mrg.a, a.mrg.X) —
     enabling windows at the first/last separator; (b) complement
     boxes [s/L_m](mrg.s.mrg) with S-typed leads.
   - THE GENERAL ENGINE (any separator word s_1..s_k, letters
     distinct from filler 'a', REPEATS ALLOWED):
     del_last(E,s) = [e/(s.mrg.a)](E.mrg.a); del_first(E,s) =
     [e/(a.mrg.s)](a.mrg.E); L_m = del_first^(m-1) del_last^(k-m) X
     = a^{r_0+..+r_{m-1}} s_m a^{r_m+..+r_k}; D_m =
     [s_m/L_m](mrg.s_m.mrg); T' = D_k.a.D_{k-1}...a.D_1; one
     per-letter pass [s/(s.mrg.a)] fires at every separator except
     the last, shaving S+1 leaving r_{m-1}; output = rev.
     SIZES (my machine counts — USE THESE, see the correction
     below): same-letter words DAG nodes 9k^2+2k+4, S-nodes
     k^2+k+1, S-DEPTH 2k+1 (mixed words within O(k): cbb 97/14/8,
     cbccb 245/32/12, cbccbcc 465/58/16). E_rev itself is the
     hand-optimized k=2 case: tree 75 nodes / 14 S-nodes / S-depth 4;
     DAG 41 / 6. ONE SIZE CONVENTION in the paper: syntactic size =
     TREE; give DAG counts parenthetically where relevant.
     IMPORTANT: depth is Theta(k), NOT constant — do not write
     "S-depth 4 for all k" anywhere. This engine SUPERSEDES round
     15B's distinct-separator bounds (4k^2-1 S-nodes, S-depth 2k):
     repeats included, strictly smaller; reconcile Patch 2's counts
     accordingly (15B's theorem becomes a corollary of the general
     engine).
   - Artifacts: rev-try/verify_t5_rev.py + t5_rev.log,
     verify_t6_general.py + t6_general.log; MY battery
     rev/verify_round17.py + round17_verify.log (ALL VERIFIED, 33 s:
     fresh encoding 12^3 grid + 500 random + 300 adversarial;
     intermediates; prov never DB + injective; laundered
     L_a.L_b.E_rev = rev with prov = (); V_0/V_1; the engine on 11
     separator words incl. k=5 'cbccb'; CH2 closed form; sizes);
     Lane B's independent rebuild rev-split/verify_lc_rev.py.
2. LANE B ROUND 2 as a round (no report file exists — reconstruct
   from my OVERVIEW.md entry + rev-split/ artifacts schema_p.c,
   schema_p, schema_p.log, verify_lc_rev.py):
   - TELESCOPE LEMMA (closes the residual table at PROOF-SKELETON
     level): every window count is an S-function on cells of a
     finitely parameterized arrangement; multiplicities enter only
     through template-group sums (P1) and per-run counts telescope
     to letter totals, prior window counts, or pinned constants.
     Entries closed: (iii) T5 explosive tilings/nestings (CH3:
     T5^3 = a^{S+2S^3} exact); (i) computed replacements at
     anchored sites; (ii) nested computed patterns on periodic
     regions; b-free-length closure via totals-IH at smaller depth.
   - P4 REFUTED AS STATED by CH2 = [merge/'bb'].[bb/aa]X: on the
     all-odd cell the output contains the singular run
     a^{S(i+j-2)/2+1} — k-slope -S/2 on a fixed-S plane, unbounded,
     hence not A(i,j,k)+P(S). Root cause: merged singular runs
     absorb PARTIAL template-group sums. REPAIR (P4'): run lengths
     live in the closure of {affine junction parts; S-function
     template lengths} under sums, products (S-function)x(pinned
     polynomial), and exact division; affine x affine never arises;
     finiteness via exact polynomial division + provenance recursion.
     THREE WRITEUP SITES conflated the template-length and
     multiplicity directions — fix all three: P4's parenthetical,
     profile (B), T5's parenthetical. Replace P4's PROOF, keep its
     CONCLUSION.
   - Battery reproduction: mode t5 byte-identical (4,192 checks, 0
     failures); cells run 1 = default invocation (777111/1000)
     byte-identical (765 exprs, 293,307 cells, unexplained 0);
     runs 2-3 seeds unrecorded (bookkeeping slip) but 20+ fresh
     seeds all "unexplained 0".
3. LANE D addendum to your §16: prefix-dominance refuted as a
   universal invariant (V_0/V_1 constructible; escapes (a)/(b)
   above; the invariant survives only on the non-merge-padded,
   constant-pattern stratum). A status block, like lem:structure's.

## Part 2 — the paper (docs/proof/main.tex)

a. ssec:frontier REWRITE (the big one): the current central claim —
   that a fixed-alphabet obstruction, if one exists, can only live
   at the colliding-separator (same-letter two-b) family — is now
   REFUTED by E_rev. New presentation: THE POSITIVE THEOREM — for
   every finite alphabet and every fixed separator structure
   (letters distinct from the filler, repeats allowed), rev is
   computable in L (statement + proof sketch: E_rev's mechanism,
   edge-guards, and the general engine's L_m/D_m/T'-fold/shaves;
   sizes as above; artifacts cited). Then the precise new frontier:
   VARYING SEPARATOR COUNT — one expression computing rev on ALL of
   Sigma* (U_k W_k). State it as the open problem that remains.
b. lem:structure (Lemma S): P4 refuted as stated; P4' repair
   replaces the proof, conclusion kept; the Telescope Lemma closes
   the residual table at SKELETON level — mark that status
   explicitly (the write-out is the remaining task, currently
   unowned). Keep the finiteness-is-load-bearing note (my
   level-pigeonhole spec was circular as stated; P4'/degree-
   separation is what delivers finiteness).
c. prop:toll: reposition — it excluded the b-free splits (a^j,
   a^{i+j}, ...), which the final construction NEVER needs. It is
   now a self-contained structural theorem OFF the main line; the
   endgame chain's V_h-necessity arrow is DEAD (V_0 constructible).
   Re-route the chain accordingly; record prefix-dominance's
   refutation where §16 uses it.
d. Lane E consistency: Gamma(E_rev) = {a,b} = Sigma — Corollary 4
   tightness; the current dichotomy: fixed structure = always
   computable (verified), unbounded alphabet = never (Lane E),
   uniform/varying k = OPEN.
e. Wire-ins (intro, alphabet section, conclusion) updated to that
   story.
f. Build must stay clean: 0 errors, 0 undefined refs, 0 overfull;
   report page count. Nothing committed to git (user commits).

## Context you may need

- rev/REPORT.md is the arc record (rounds 1-16 through your §14-§16
  integration; 15C and B-2 are the missing rounds — this charter
  supplies their content).
- The general engine's per-letter pass [s/(s.mrg.a)] fires at every
  separator except the LAST (following run r_0 <= S): that is the
  k-adaptivity fact Lane C's next round builds on.
- Parallel lanes now running (do not wait on them; integrate what
  exists): Lane C — the unification construction; Lane D — varying-k
  obstruction hunt; Lane B — Telescope at varying k. Any NEW results
  from them will arrive as later rounds; this charter covers the
  VERIFIED record only.

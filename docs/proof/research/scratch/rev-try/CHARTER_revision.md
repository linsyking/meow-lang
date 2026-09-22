# CHARTER (round 18 for this lane): THE FRAGMENT REVISION — B >= 3, L1'', L2's status

Coordinator, 2026-09-22. Your round 17 is verified (battery reproduces;
FP(ii) strengthening hand-scrutinized and sound; part B's two-deep-sizes
result is a genuine strengthening). But TWO things landed mid-round that
the fragment must absorb — both verified by me, both in
research/OVERVIEW.md (the "Lane B round 4, Lane C round 17, Lane D
round 3 verification" entry):

## 1. dich:L1 is the REFUTED form (Lane B round 4)

L1-as-stated (tweak-or-finite-affine) is FALSE: E_leak =
[(mrg.b)/'b']X has runs exactly (S+2^0, ..., S+2^{k-1}, 2^k) and
E_prod = [mrg/'aa']X has runs exactly (1, S, 2S, ..., S*2^{k-1}) —
neither tweak nor affine (tweak-distance 2^j-1 grows; alpha=1 forces
beta=2^j). I verified both with fresh encodings on B=2 (k=1..10) AND
B=3 (E_leak k=1..8; E_prod's B=3 form is S*(3^j-1)/2+1, my derived
closed form, verified k=1..7 — odd runs tile as (aa)^{(3^j-1)/2}a).
REPLACE dich:L1 with the closure form L1'': every a-run is in the
closure of {site terms, S, constants} under +, -, x by pinned counts
(concretely Q(S) + Sum_{i<=m} kappa_i P_i(2^{t_i}) Q_i(S)) with the
TERM LEDGER M_V <= #S(E)+O(1) — status: machine-supported (exact
9-expression battery + 40,896/40,896 random compositions), the
write-out is Lane B's round in flight. Cite E_leak/E_prod as the
refutation witnesses of the narrow form (honest history).

## 2. The staging family must migrate to B >= 3 (Lane D round 3)

w^(k) (base 2) is the BOUNDARY of super-increase (2^j =
Sum_{i<j}2^i + 1) and TELESCOPES: E_last = [eps/b][a/aa]X = a^{2^k}
— the LAST RUN, b-free, S-depth 2. Also E_smm = a^{2^k-1} (b-free
sum-minus-max), E_h2 = a^{2^{k-1}}, all machine-verified (65 checks +
my fresh encodings k=0..11). So on B=2: V1/V2-type extraction-
impossibility is DEAD, and your descent must not lean on it. On
B >= 3 the gap separation HOLDS (I verified k=5..14, past the
documented small-k coincidences). D's recommendation, ADOPTED:
migrate the staging family to D(k;3) = a^{3^0} b a^{3^1} ... b
a^{3^k}. NOTHING IS LOST — it is still a subfamily of {a,b}*.
The B=2 degeneracy becomes a PROPOSITION in the fragment (the
boundary telescopes; extraction is free there; uniform rev on the
B=2 family itself remains open — 4 structured attempts fail at
k=2,3,4).

## 3. L2's status UPGRADES (Lane D round 3)

D PROVED the supply side: L2.1 SLOPE-PINNING (exact re-separations
need interval sums Sum_[u..v] B^i = alpha*S + err, alpha = B^{v-k},
|err| <= (B^u-1)/(B-1); exact cuts at top-offset d require dyadic
slope B^{-d}; the tweak channel covers only O(1) offsets from an
end; pairwise distinct, power-separated on B >= 3) and L2.2 PER-NODE
SUPPLY <= 4, UNCONDITIONAL (each firing cuts only at its window's
two ends with the same amounts; interior pattern runs are DEMANDS by
Match Anchoring). Your part-B result (fully-consumed values subset
of {p0,p1,p0+p1} — at most 2 deep sizes per flank pattern on the
powers) is the per-pattern core that complements them. So dich:L2
should be RESTRUCTURED: the proved parts (L2.1, L2.2, your part B)
stated as lemmas; the remaining assumption is only the DEMAND side
(reversal at unbounded k requires cuts at Omega(k) distinct offsets)
— which is D's round in flight, and which your descent assembly
consumes.

## The revision tasks

1. Migrate the family: D(k;3) throughout (statement of dich:thm:main,
   the descent, the assumptions); keep a short remark recording WHY
   (the B=2 degeneracy proposition).
2. dich:L1 -> the closure form L1'' + term ledger, with the
   refutation witnesses cited and B's attribution.
3. dich:L2 -> restructured: proved supply lemmas (L2.1/L2.2/part B)
   + the demand assumption (attributed to D, in flight).
4. Re-derive the escape-B kill and dich:thm:main's proof sketch
   WITHOUT extraction-impossibility support: the route is FP -> SD
   -> SB -> B's PAYMENT theorem (mergey flips must be stripped by
   downstream exact deep cuts) -> slope-pinned supply (<= 4 per
   node, <= 2 deep sizes per flank pattern) -> demand (D's lemma,
   in flight). The chain-sum channel still routes to the demand
   side. The effective bound stays linear in #S.
5. B's E_leak/E_prod also mean: pinned SLOPES are not just
   {alpha S + beta} — the closure includes S x pinned products
   (degree >= 2 terms are Omega(S), hence top sizes; the deep
   reachable values are the linear-in-S terms with bounded site
   references — the term ledger). Make sure the descent's use of
   "pinned multiples sit at top sizes" is re-derived in this form.
6. Keep every Status line accurate after the changes; the fragment
   must remain integration-ready (Lane A waits at the hook).

## Rules (user directives, hard)

- No new unverified claims; machine runs <= 1 minute; log full
  invocations; scripts + logs in rev-try/; report back to me.
- If you want a side quest AFTER the revision: the B=2 uniform-rev
  question (D's 4 failed attempts are the starting map; the
  telescoping extractions are now free tools — E_last/E_smm/E_h2).
  Only after tasks 1-6 are solid.

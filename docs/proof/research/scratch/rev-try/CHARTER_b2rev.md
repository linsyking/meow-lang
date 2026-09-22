# CHARTER (round 19 for this lane): THE B=2 UNIFORM-REV SIDE QUEST

Coordinator, 2026-09-22. Your round 18 is VERIFIED end-to-end
(OVERVIEW entry appended): battery byte-identical, flankcap
hand-scrutinized, all five B=2 constructions re-derived by my own
hand, statuses checked line by line, and the compile claim
reproduced exactly (paper preamble wrapper: 0 errors, 0 undefined
refs, 0 overfull, 9 pages). Nothing needed correction. The fragment
is integration-ready and Lane A holds at the hook.

This round is the side quest your round-18 charter sanctioned
(tasks 1-6 are now solid). It is INDEPENDENT of the main line
(Lane B's term-ledger write-out and Lane D's demand side are in
flight; the final integration does NOT wait on you).

## The question

Is there ONE fixed expression E with E(w^(k)) = rev(w^(k)) for ALL
k, where w^(k) = D(k;2) = a^{2^0} b a^{2^1} ... b a^{2^k}?

- POSITIVE: the no-go's boundary is exactly base 2 — rev is
  L-reachable on the telescoping family but not on any strongly
  super-increasing one. A headline complement to the dichotomy.
- NEGATIVE: a precisely-located obstruction — which B>=3 resource
  dies on B=2, and what new principle replaces it. Also record-grade.

Either outcome is a round's work. A false construction is not.

## The starting map (all verified; do not re-verify)

1. Lane D's FOUR structured attempts, all failing at k = 2, 3, 4
   (tuning.log part D, rev-wall/): head assembly h.b.tail; the
   complement box; E_poll-style pollution; block swap. Their
   structural autopsy: rev(w^k) = a^{2^k} b rev(w^{k-1}) needs k
   unfoldings, and the halving chain reaches only FIXED offsets from
   the top.
2. The free telescoping tools (round-18 fragment, dich:prop:boundary;
   machine k=0..11 + my fresh encodings): E_last = [eps/b][a/aa]X =
   a^{2^k} (last run, b-free, S-depth 2); [eps/b][aa/a]X = a^{2S};
   E_cbox = [b/(E_last b)](mrg b mrg) = a^{2^k-1} b a^S; E_smm =
   [eps/(b mrg)]E_cbox = a^{2^k-1}; E_h2 = [a/aa]E_smm = a^{2^{k-1}};
   E_leak = [(mrg b)/b]X with runs (S+2^0, ..., S+2^{k-1}, 2^k);
   E_prod = [mrg/aa]X with runs (1, S, 2S, ..., S*2^{k-1}).
3. The geometry I hand-derived for you (check me, then use):
   - PLANT-DEPTH IDENTITY: on w^(k) the m-th separator sits at
     left-depth 2^m - 1 = (the m-th run) - 1, and rev's m-th
     separator sits at right-depth 2^m - 1 — the SAME depths, from
     the other end. Reversal is a DEPTH MIRROR, and the depths are
     near-powers, exactly what the telescoping tools realize. This
     is why extraction is free and why E_cbox plants one separator
     at depth S - 2^k = 2^k - 1 for free.
   - RECURSION: rev(w^k) = [aa/a](rev(w^{k-1})) . b . a, because the
     doubler [aa/a] is letter-uniform and COMMUTES with rev. So the
     recursion D found is real — but a fixed expression cannot
     unfold it; the question is whether a NON-recursive shortcut
     exists (the B>=3 answer is no; B=2 is open).
   - WHAT DIES ON B=2: the flankcap mod-3 argument (2^a + 2^a =
     2^{a+1}: a flank a^{2^j} b a^{2^j} fully consumes TWO deep
     sizes at once); the Payment theorem's deep cuts are CHEAP
     (E_last-style extractions); L1'' closure does NOT obstruct
     (2^m - 1 is a difference of two site terms, in the closure).
     What SURVIVES: SD (the raw runs are distinct — multi-b patterns
     fire once on the raw family; multiple firings need merges
     first), the SNF uniform interleave, DECOMP, and the mirror-plant
     framing's own census: one cluster of plants = one block move; a
     periodic mirror = one phase shift.
4. So the hunt: can a merge schedule + a multiply-firing pattern
   plant separators at the mirrored depths {2^m - 1 from the right}
   in O(1) passes — e.g. is rev(w^k) within O(1) passes of a
   periodic structure whose phase shift IS the reversal (the way
   (ab)^k -> (ba)^k is one constant pass, already in the record)?
   The ladder of plant depths from the right is (1, 3, 7, 15, ...):
   examine what one halving/doubling does to the WHOLE ladder at
   once ([aa/a] maps depth-d plants to ~d/2 plants simultaneously).

## Deliverable

Either (a) a construction: an explicit E, machine-verified against
prov.py on w^(k) for k = 0..10 (byte-exact prov comparison), with a
hand proof of the mechanism; or (b) an obstruction: the resource that
is priced on B=2, the lemma that would formalize it, and the machine
evidence (falsified candidate classes). If (b), state precisely why
the four attempts of D fail — the common obstruction IS the finding.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; log full
  invocations; scripts + logs + ROUND19_REPORT.md in rev-try/ (your
  writes work); report back to me.

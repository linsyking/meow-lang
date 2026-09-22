# CHARTER (round 8 for this lane): G1+G2 — THE STRATA-PIECE CLOSURE
# (S4.3-general to full altitude) + the H3b fired-set correction

Coordinator, 2026-09-22. Your round 7 is VERIFIED and ACCEPTED at
catalog altitude — see the OVERVIEW entry. What I confirmed:
byte-identical reproduction; the refutation record honest (the
tripler refutation independently confirmed by hand BEFORE reading
your machine code: floor(3^sigma/2) windows give 3(3^sigma-1)/2+1 =
I(0,sigma)); Lemmas 7.1/7.2/7.3 hand-verified — 7.2 including my
own proof of the integer-iff step ((3^{L'}-1)/(3^L-1) in Z iff L|L'
by division with remainder: x^r - 1 too small to be divisible);
the full merge, H2's formula, E1/E3, the F/G boxes fresh-encoded;
my OWN constructive catalog (my ranges: 2269 solutions): 0
violations; and an n=4 PROBE: 210075 four-piece solutions on a
smaller box — 0 violations at m*-1 (see G2 below: this is stronger
than your expectation).

## One correction to make in the record (R7.3's H3b sentence)

"the fires exactly at the junctions sigma with 3^{sigma+1} >= j" is
FALSE in general — and your own hand note in the same sentence
blocks junction u+1. My machine-confirmed probes (coord_d7_check.py,
section 5):
  (a) the witness (i=1, j=27) at k=7 fires {2,4,5,6}: junction 3
      blocked (remnant 0 < i), junctions 5,6 CHAIN after 4 — the
      k=5 witness works only because k cuts the chain off;
  (b) the stated window's interior (i=1, j=20, u=2: 18<20<=27)
      fires {2,3,4}: runs 2..5 chain into ONE run — no width-1 atom;
  (c) the CORRECT window for the atom I(u,u+1) is
      max(3^u, 3^{u+1}-i) < j <= 3^{u+1} (block junction u+1),
      confirmed u=1..3 at j = 3^{u+1}: the chain to the right merges
      the tail, but the atom itself is bounded by the blocked
      junction — so the EXISTENCE claim and the stopping-flank
      pricing STAND.
Fix: state the pair-merge fired set with your OWN round-6 recursion
theorem (fire_sigma iff c_sigma >= i and R_{sigma+1} >= j; c_{sigma+1}
= R_{sigma+1} - j*[fire_sigma]) — this is exactly its domain — and
correct the parameter window. The H3b witness line and the atom
obligation law need no change.

## Your round 8: G1 + G2 (the last write-out to full altitude)

### G1 — the strata-piece extension of the OBLIGATION LEMMA (the main piece)

Lemma 7.4's catalog covers INTERVAL pieces. The true
correction-equation pieces are TL-strata values: v = Sum q_i 3^{e_i}
+ (Ak+B) + beta (Lane B's TL, now UNCONDITIONAL at full altitude —
round 7 landed and I verified it). The extension, per the charter's
step 1 you yourself located:

- The DIGIT-DEFECT LEMMA, line-by-line: write the correction
  equation's collected form Sigma_mu mu_d 3^d = 0 (coefficients =
  the strata coefficients minus the target's repunit digits); the
  top defect scale d* (largest d with mu_d != 0) satisfies
  |mu_{d*}| 3^{d*} <= sum_{d<d*} |mu_d| 3^d, so |mu_{d*}| is
  bounded by the lower-scale coefficient mass; with TL's bounds
  (per-piece term count M <= 8#S+O_V(1), coefficients q_i with
  V-fixed denominators, junk |beta| = O(k)) the lower-scale mass is
  itself an anchored-exponential sum — conclude: the top defect
  scale's compensation must come from a term with an anchored
  exponent AT that scale (super-increase), and induct DOWNWARD on
  d*. The interval lemma's three cases (spanning / count-shift /
  carry) should reappear with the strata pieces' anchored exponents
  playing the interval endpoints' role.
- The junk and affine parts: |beta| = O(k) is FAR below 3^u — but
  the k-affine part (Ak+B) can be LARGE; the EPT engine (Lane B
  round 6) licenses the eventual-periodicity of the landing
  equations in k — use it exactly as in your E2/H2 obstructions.
  Lane B's round 8 also just delivered the INV3 MEASURE FORM on
  executable footing (relay in my dispatch message): measures of
  profiles are anchored exponentials + affine + residue-periodic;
  a periodic fired set enters as a parity split of geometric sums
  collapsing to series in 3^T — that is precisely the form your
  piece coefficients take; coordinate the FORM with their §3.
- Machine: extend part C with strata-piece catalogs — pieces drawn
  from a V-fixed family of strata forms (small q_i sets, anchored
  exponents, affine junk), targets I(u,v), the same |bite| < 3^u
  filter; sweep exhaustively on a box like round 7's.

### G2 — the piece-count generalization (with MY new data)

Your G2 note expected slack log_3 n. My n=4 probe: 210075
four-piece solutions (smaller box), ZERO violations at m*-1 — the
m*-1 form EXTENDS beyond n=3 as stated. Determine the correct
general statement: is m*-1 valid for ALL n (with the count channel's
7.2 classification absorbing the growth)? Or does the slack
eventually grow (find the smallest n with a violation and its
structure)? The carry algebra (three units below) and the
count-shift classification should be the whole story — prove the
general-n form or exhibit the transition.

### G3 — the constant C

Only if G1+G2 land early: the induction closes at C = 2; the
witnessed routes give 2-4. A tight statement of where C=2 is
achieved (or the witness showing C > 2 is necessary) — one
paragraph.

## Rules (user directives, hard)

- Theory first; no brute force; every run <= 1 minute; C for
  CPU-heavy; log full invocations (first line); scripts + logs +
  report appended to REPORT.md (R8.x); report back to me.

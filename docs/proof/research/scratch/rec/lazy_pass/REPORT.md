# The Lazy-Pass Calculus: Recursive Definitions over raw L

**Research report "rec-lazy-pass"** — working directory
`docs/proof/research/scratch/rec/lazy_pass/`.  Target paper:
`docs/proof/main.tex` ("A Theory of String Substitution over Finite
Alphabets").  Notation and theorem numbers below refer to that paper
(`def:subst` = Definition 1, `def:exp`/`def:den` = the expression grammar and
eager denotation of Section 3, `def:deg`/`lem:length`/`thm:fp` = Section 4,
`cor:towers` = the Markov-amplifier tower of Section 5.6).  All machine work
is in `core.py` / `toolkit.py`; verification scripts `verify_round*.py`;
every claim tagged **[VERIFIED]** below was executed and is reported with its
domain.

Alphabet throughout: `Sigma = {a, b}` (the paper's constructions need
`|Sigma| >= 2`; we work at the weakest alphabet).  Encoding characters
`b_ = a`, `x_ = b` (the paper's sigma_1, sigma_2); booleans `TOP = b`,
`BOT = a` (the paper's `|Sigma| = 2` choice of Prop. prop:instances).  All
of the paper's Section-2 toolkit is therefore available as **call-free
expressions** (raw L): `enc, dec, benc, bdec, cat, head, tail, eq, if,
enc^2, dec^2, contains`.

---

## 0. What this report delivers

| # | Statement | Status |
|---|-----------|--------|
| T1 | The lazy-pass machine is a **conservative extension** of L: on call-free programs it agrees with def:den wherever the eager denotation is defined. | PROVED (Sec. 2) + VERIFIED |
| T2 | **Guarded recursion is expressible**: the two-way pattern gate `sel` forces exactly one branch; the structural-recursion scheme over it computes every string-primitive-recursive function. | PROVED (Sec. 3) |
| T3 | **Reversal is computable** — the Sec. 5.6 hinge dissolves under recursion. | PROVED (Sec. 3.3) + VERIFIED (all strings <= 6) |
| T4 | **Universality**: the calculus computes exactly the partial computable functions over `Sigma*`.  Self-recursion suffices; mutual recursion is definable. | PROVED (Sec. 4) |
| T5 | `X |-> X^{2^{|X|}}` (unreachable in L, Section 4) is computable. | PROVED (Sec. 5.1) + VERIFIED (|X| <= 4) |
| T6 | A mu-search (string square root) and a two-counter machine run on small inputs. | VERIFIED (Sec. 5.2) |
| T7 | Programs that diverge under the eager semantics terminate under lazy-pass (re-gating). | PROVED + VERIFIED (Sec. 5.3) |
| T8 | Totality of a definition is undecidable. | SKETCH (Sec. 6) |
| T9 | A **total** definition with tower-of-exponentials output growth — the Section-4 polynomial bound dies for total recursive programs too. | PROVED (Sec. 5.4) + VERIFIED (lengths 4, 6, 14, 254) |

---

## 1. The lazy-pass calculus

### 1.1 Syntax

**Definition (recursive programs).**  A *program* is a finite list of named
definitions

    f_i(X_1, ..., X_{m_i}) = E_i        (i = 1..k)

where each `E_i` is an *extended expression* over the parameters of `f_i`:

    E  ::=  X_j                      parameter
         |  w                         constant string (w in Sigma*)
         |  E_1 E_2                   concatenation
         |  [ R / P ] E               substitution node (P pattern, R
                                     replacement, E scrutinee) — the paper's
                                     node, extended
         |  f_j(E_1, ..., E_{m_j})    call (arity must match)

`L` is exactly the call-free fragment.  A program is *closed* if every call
targets a defined name (checked by `core.check_program`).  As in the paper,
`E_1 E_2` is eliminable sugar (thm:core); we keep it for readability.  The
macro architecture is unchanged from the paper's remark after thm:core: a
body is an expression, and substitution `E[F/X]` (now allowed to substitute
call nodes) is macro expansion.

### 1.2 The small-step machine (official semantics)

**Definition (machine).**  A configuration is `(c, K, H)`:

* **heap** `H`: a finite map from *locations* to cells `val(w)`,
  `thunk(e, rho)`, or BLACKHOLE;
* **environment** `rho`: a tuple of locations (one per parameter);
* **control** `c`: `ev(e, rho)` (evaluate extended expression `e` under
  `rho`) or `val(w)`;
* **stack** `K` of frames `catL(e2, rho)` | `catR(w)` | `subE(R, P, rho)` |
  `subP(T, R, rho)` | `subR(T, B)` | `upd(loc)`.

The **transition relation** is the following deterministic system
(`H[l|->v]` is heap update; `K o< f` pushes `f`):

    (1)  ev(w, rho)              ->  val(w)
    (2)  ev(X_i, rho)            ->  val(w)                    if H(rho(i)) = val(w)
    (3)  ev(X_i, rho)            ->  ev(e, rho'), K o< upd(l), H' = H[l|->BLACKHOLE]
                                                               if H(rho(i)) = thunk(e,rho'), l = rho(i)
    (4)  ev(X_i, rho)            ->  ERR_bh                     if H(rho(i)) = BLACKHOLE
    (5)  ev(E1E2, rho)          ->  ev(E1, rho), K o< catL(E2, rho)
    (6)  ev([R/P]E, rho)         ->  ev(E, rho),  K o< subE(R, P, rho)
    (7)  ev(f_j(e_1..e_m), rho) ->  ev(E_j, rho')  where rho' = (l_1..l_m) fresh,
                                  H' = H[l_t |-> thunk(e_t, rho)]   (call-by-need: no
                                  argument evaluated yet)
    (8)  val(w),  K = catL(e2,rho).K'  ->  ev(e2, rho), K = catR(w).K'
    (9)  val(w),  K = catR(v).K'       ->  val(vw)
    (10) val(T),  K = subE(R,P,rho).K' ->  ev(P, rho), K = subP(T,R,rho).K'
    (11) val(B),  K = subP(T,R,rho).K' ->
              ERR_eps                               if B = eps
              val(T)                                if B != eps and B not-substring-of T
                                                    (R never forced)
              ev(R, rho), K = subR(T,B).K'          if B != eps and B substring-of T
    (12) val(A),  K = subR(T,B).K'     ->  val([A/B]T)   (greedy pass, def:subst)
    (13) val(w),  K = upd(l).K'        ->  val(w), H' = H[l|->val(w)]
    (14) val(w),  K = []               ->  HALT(w)

**Initial configuration.**  `run(f_i, S_1..S_{m_i})` starts with
`H_0 = {l_t |-> val(S_t)}`, `c = ev(E_i, (l_1..l_{m_i}))`, `K = []`.

**Semantics of a program.**  `f_i(S_1..S_m) = w` iff the machine halts in
`HALT(w)`.  Halting in `ERR_eps` means *undefined* (the `[A/eps]`
discipline); `ERR_bh` and nontermination are the two forms of *divergence*.
This is the single official semantics; everything else in the report is
derived from it.

Rule (11) is the whole design: **the replacement is demanded only if the
pattern occurs in the scrutinee's value.**  Everything else is strict:
scrutinee and pattern are always forced (rules 6, 10, 11), arguments of
calls are shared thunks (rule 7), a forced thunk is memoized (rule 13).

### 1.3 Basic properties

**Proposition 0 (determinism).**  For every configuration at most one rule
applies, so each initial configuration has exactly one run.
*Proof.*  By inspection: the control and the top-of-stack determine the rule
uniquely; rules (2)-(4) are disjoint on the cell's tag; rule (11)'s three
cases are disjoint. []

**Proposition 1 (call-free termination).**  If the control expression
contains no f-node (and the environment's cells hold values, not thunks),
the run halts with `HALT(w)` or `ERR_eps`.
*Proof.*  The machine evaluates a finite evaluation tree: each node is
entered once per occurrence in a demand, and each pass (rule 12) does finite
work on finite strings.  Formally, structural induction on `e` via the
big-step rules of Sec. 1.4, equivalent by Theorem A. []

**Proposition 2 (forcing coincidence).**  With shared thunks, forcing the
replacement once-if-any-match and once-per-match compute the same value:
the greedy pass of def:subst inserts the same string `A = <<R>>` at every
match, so `[A/B]T` is independent of when (or how often) `A` was computed.
With call-by-name (no sharing) the value is the same and only the work
differs; with call-by-need each argument/replacement is evaluated at most
once per activation.
*Proof.*  The value of a pass is a function of the three values alone
(def:subst is a function `Sigma* x (Sigma* \ {eps}) x Sigma* -> Sigma*`);
evaluation order and duplication cannot change it because the machine is
pure (no rule observes the heap except through the thunk memoization, which
is value-preserving). []

**Proposition 3 (blackhole = divergence).**  If a run halts in `ERR_bh`, no
value is definable for that initial configuration.
*Proof.*  The big-step semantics of Sec. 1.4 has no rule for reading
BLACKHOLE, so no derivation exists; if the machine could also halt with `w`,
Theorem A(i) would give a big-step derivation of `w` for the same initial
configuration — contradicting determinism (Prop. 0). []

### 1.4 The big-step demand semantics (equivalent, for proofs)

**Definition.**  The judgment `<e, rho, H> << w, H'>` is inductively defined
by the rules:

    (K)       <w, rho, H> << <w, H>
    (V-val)   <X_i, rho, H> << <w, H>                  if H(rho(i)) = val(w)
    (V-thunk) <X_i, rho, H> << <w, H''>                 if H(rho(i)) = thunk(e,rho'),
              <e, rho', H[l|->BLACKHOLE]> << <w,H'>, H'' = H'[l|->val(w)],  l = rho(i)
    (C)       <E1E2, rho, H> << <w1w2, H2>        if <E1,rho,H><<<w1,H1> and <E2,rho,H1><<<w2,H2>
    (S-inert) <[R/P]E, rho, H> << <T, H2>         if <E,rho,H><<<T,H1>, <P,rho,H1><<<B,H2>,
                                                  B != eps, B not-sub-of T   (R never entered)
    (S-fire)  <[R/P]E, rho, H> << <[A/B]T, H3>    if <E,rho,H><<<T,H1>, <P,rho,H1><<<B,H2>,
                                                  B != eps, B sub-of T, <R,rho,H2><<<A,H3>
    (F)       <f_j(e_), rho, H> << <w, H''>       if H' = H[l_t |-> thunk(e_t,rho)] (fresh l_t),
                                                  <E_j, (l_1..l_m), H'> << <w, H''>

There is **no rule** for `B = eps` (stuck: `[A/eps]`), none for reading
BLACKHOLE, and no other stuck configurations.  Implemented in
`core.ev_bigstep`.

**Theorem A (small-step = big-step).**  Fix a closed program.
(i) If `<e, rho, H> << <w, H'>` then the machine from `ev(e, rho)` with heap
`H` and empty stack halts in `HALT(w)`.
(ii) If the machine from `ev(e, rho)`, `H`, empty stack halts in `HALT(w)`
(resp. `ERR_eps`), then `<e, rho, H> << <w, H'>` for some `H'` (resp. no
derivation exists; the stuck point is an empty pattern).
*Proof sketch (routine inductions).*  (i) Induction on the derivation,
strengthened to nonempty stacks: for each frame constructor there is one
"progress rule" (e.g. from `<E,rho,H> << <T,H1>` and the frame
`subE(R,P,rho).K'` conclude from a derivation of `<P,rho,H1> << <B,H2>` etc.),
and the six progress rules mirror rules (8)-(13).  (ii) Induction on run
length: the run decomposes into the sub-runs demanded by the big-step rules;
each frame pushed is matched by exactly one pop; heap cells created in a
sub-run are fresh (the freshness invariant: an activation's cells are
disjoint from every other activation's cells, so the caller's state is
untouched except through the argument thunks).  `ERR_bh` is handled through
Prop. 3's argument. []  **[VERIFIED]** — `verify_round2.py` runs both
evaluators side by side on random recursive programs (including divergent
ones) and checks agreement on every halting and stuck outcome.

**Lemma (Call Lemma / sub-run decomposition).**  For any call `f_j(e_1..e_m)`
under environment `rho`: the machine's behavior on the call is (the sub-runs
evaluating each demanded `e_t` under `rho`, memoized in the argument cells)
composed with the machine's run of `E_j` on the resulting values; in
particular the value of the call depends only on the argument values.
*Proof.*  From rule (7) and Theorem A: the cells `l_t` are fresh, `E_j`'s
evaluation reads them only by rules (2)-(4), each read either returns the
memoized value or triggers the unique evaluation of `e_t` under `rho` in a
state disjoint from the caller's. []

### 1.5 Design justification

**(a) Why the replacement slot, and only that slot.**  Two facts of the
paper itself force the reading.

* *Substitution Elimination* (`[A/B]S = S` when B not-sub-of S): the
  operator **discards** the replacement's value entirely when the pattern
  is absent.  The eager denotation (def:den) computes that value and then
  throws it away; the lazy-pass machine simply refuses to compute it.  On
  call-free total sub-expressions the two are indistinguishable (T1 below),
  so the lazy reading is the *demand-side refinement* of the same operator —
  not a new operator.
* The paper's own Remark rem:total-rep shows the eager discipline hurting:
  the naive guard `if(eq(X_i,eps), identity, round_i)` fails *because eager
  evaluation forces the branch*; the paper must contort the guard into the
  pattern position.  Under lazy-pass a replacement-position guard is sound
  natively (the branch is a thunk), which is exactly what recursive calls
  need.  The pattern position must stay strict in any case: the gate test
  `B in T` needs `B`, and `B = eps` must remain undefined — the machine
  keeps `[A/eps]` undefined by rule (11), first case.

**(b) Why call-by-need for arguments.**  A recursive call that must be gated
has to reach its gate unevaluated.  With call-by-value arguments, any call
used as a delayed branch is forced at the call site, and gating is lost (the
Omega-example of Sec. 5.3 makes this concrete: the same program text
diverges eagerly and terminates lazily).  Call-by-name would also work but
re-evaluates; call-by-need evaluates each argument at most once per
activation (Prop. 2), which keeps the complexity claims of Sec. 5 honest.
A minimality fact proved in Sec. 4.3: *argument* laziness alone would not
suffice either — the operator-level laziness of rule (11) is the
load-bearing one (with pure inlining and a single self-recursive function
one gets universality without any helper calls at all).

**(c) Forcing once-if-any vs once-per-match.**  The pass inserts the same
value at every greedy match; with sharing there is exactly one evaluation
and its value is replicated by the pass (Prop. 2).  This is why the design
needs no per-match forcing discipline and why `[R/P]E` still denotes a
function of the three values.

**(d) Relation to the eager denotation.**  T1 in Sec. 2: agreement wherever
the eager denotation is defined; the lazy semantics can be strictly more
defined, and only in one way — a replacement sub-expression whose value is
discarded because the pattern does not occur.  Every other undefinedness
(empty pattern, undefined scrutinee) is shared.

### 1.6 Denotational remark (least fixpoint)

For a program P define, for tuples of partial functions
`F_ = (F_1..F_k)` with `F_i : (Sigma*)^{m_i} -> Sigma*` (flat domain, BOT =
undefined, order pointwise), the functional Phi by

    Phi(F_)_i(S_) = D<<E_i>>_{F_}(S_)

where `D<< >>_{F_}` is the compositional reading of Sec. 1.4's rules with
calls interpreted as lookups in `F_` (the S-inert rule *not* consulting
`D<<R>>`).  Monotonicity: induction on expressions — each clause is monotone
in its strict arguments and the test `B not-sub-of T` is stable under `T`
(flat order).  Continuity: each value depends on `F_` at finitely many
argument points (a body has finitely many call nodes), so
`Phi(sup F_n) = sup Phi(F_n)`.  Hence Phi has a least fixpoint
`F* = sup_n Phi^n(BOT_)`, and `f_i(S_) = w` iff `F*_i(S_) = w`.  We take
the operational machine as the official semantics and use this remark as a
certificate; Sections 3-5 never need the denotational form (each
construction's termination is proved by an explicit measure).

---

## 2. Conservative extension of L

**Definition (lazy denotation of call-free expressions).**  For call-free E
define `<<E>>^L : (Sigma*)^n -> Sigma*` by the clauses of def:den *except*
that the substitution case reads

    <<[R/P]E>>^L(S_) = <<E>>^L(S_)      if <<P>>^L(S_) != eps, <<E>>^L(S_) defined,
                                              and <<P>>^L(S_) not-sub-of <<E>>^L(S_)
    <<[R/P]E>>^L(S_) = [<<R>>^L(S_) / <<P>>^L(S_)] <<E>>^L(S_)
                                          if <<P>>^L(S_) != eps, it occurs in <<E>>^L(S_),
                                             and all three are defined
    <<[R/P]E>>^L(S_) = BOT              if <<P>>^L = eps or <<E>>^L = BOT or
                                          (the pattern occurs and <<R>>^L = BOT)

**Lemma 2.1.**  For call-free E and a heap of values, the machine computes
`<<E>>^L`: it halts with `w` iff `<<E>>^L(S_) = w`; it halts in `ERR_eps`
iff `<<E>>^L(S_) = BOT` because of an empty pattern; and it never diverges.
*Proof.*  By Theorem A it suffices to read the big-step rules: they are
literally the clauses above, with no rule for the empty pattern, and Prop. 1
rules out divergence. []

**Theorem T1 (conservative extension).**  Let E be call-free.
(i) If the eager denotation `<<E>>` (def:den) is defined on `S_` with value
`w`, then the lazy-pass machine on `(E, S_)` halts with value `w`.
(ii) If the machine halts in `ERR_eps`, then `<<E>>` is undefined on `S_`.
(iii) Consequently the lazy-pass calculus is a conservative extension of L:
on the common domain of the eager denotation the two semantics coincide, and
f-free programs never diverge.
*Proof.*  (i) Induction on E.  Constants, parameters, concatenation: the
machine's rules (1),(2),(5),(8),(9) compute exactly the same values; the
eager clauses are strict and defined, and by the induction hypothesis each
sub-run returns the eager value.  For the substitution node `[R/P]E0`
suppose `<<E>>(S_) = [A/B]T` with `A = <<R>>(S_)`, `B = <<P>>(S_) != eps`,
`T = <<E0>>(S_)` — all defined.  The machine evaluates the scrutinee (IH:
value T), then the pattern (IH: value B != eps, so rule 11 does not take the
ERR_eps branch).  If `B not-sub-of T`, rule 11 returns `val(T)`, and
`[A/B]T = T` by **Substitution Elimination**: the machine's answer equals
the eager value.  If `B sub-of T`, the machine evaluates R (IH: value A) and
returns `val([A/B]T)` by rule 12 — the eager value; by Prop. 2 the pass's
value is a function of the three values, so the reordering of R's
evaluation is immaterial.  (ii) The machine reaches `ERR_eps` only through
rule 11 with an empty pattern value, i.e. `<<P>>(S_) = eps` for some
sub-expression P that the machine forced; the eager denotation forces at
least those sub-expressions (it forces every sub-expression), so it is
undefined too.  (iii) Immediate from (i), (ii) and Prop. 1. []

**Remark (the extension is strict, in exactly one way).**  The lazy
semantics is more defined than the eager one only through discarded
replacements.  Witness: `E = [[X/eps]Y / b]X` (a replacement whose own
pattern is empty): on `X = a` (which contains no b) the eager denotation is
undefined while the machine returns `a`.  This is precisely the phenomenon
the paper wrestles with in Remark rem:total-rep, relocated to the
replacement slot where it is harmless.  **[VERIFIED]**: verify_round1.py (c).

**Remark (what stays strict).**  The pattern and the scrutinee are forced
always; `[A/eps]` stays undefined; and the paper's `if` still forces both
branches — its construction embeds both branch expressions inside `enc(.)`
*scrutinees* (`if(C,X,Y) = dec([enc(Y)/bb][enc(X)/TOP][bb/BOT]C)`), so
call-by-need thunks passed as X and Y are forced unconditionally.  **All
guarding must go through pattern gates** — the subject of Sec. 3.

**Verification (round 1).  [VERIFIED]**  `verify_round1.py`: (a) all eight
toolkit families (`enc/dec`, `cat`, `head/tail`, `eq`, `if`, `enc^2/dec^2`,
`benc`, `contains`) agree with Python truth on 400 random string pairs each
(lengths <= 8, Sigma = {a,b}); (b) conservativity: 9000 random call-free
expressions (<= 2 variables, depth <= 3, patterns biased to include
empties) — on all **5475** where the eager denotation is defined, the
machine returned the same value; of the 3525 eager-undefined cases the
machine erred (ERR_eps) on 3200 and returned a value on 325 (strict
extension, always of the discarded-replacement form); zero timeouts, zero
disagreements.  (c) the strict-extension witness above.

---

---

## 3. Pattern gates and guarded recursion


### 3.0 Guarding: what does and does not guard, and a finding

**Under the EAGER denotation nothing guards.**  `def:den` evaluates all
three sub-expressions of every node, so a recursive call in any position of
a branch of the paper's `if` — or of any other expression — is forced
unconditionally; this is exactly the paper's pain in Remark `rem:total-rep`
("an if(eq(X_i,eps), identity, round_i) still *evaluates* round_i").  The
only conditional in the calculus must therefore come from the runtime.

**Finding (the paper's `if` is already a pattern gate under lazy-pass).**
Look at the Selection construction under rule (11):

    if(C,X,Y) = dec( [enc(Y)/bb] ( [enc(X)/TOP] [bb/BOT] C ) )

For C = TOP: the pass [bb/BOT] is inert (BOT not in TOP), the pass
[enc(X)/TOP] fires (Direct Substitution on the one-character scrutinee) and
forces X — and the final pass [enc(Y)/bb] sees the enc-image of X, which
contains no bb (Theorem `thm:enc`(ii)), so it is INERT and Y is never
forced.  For C = BOT symmetrically: [bb/BOT]BOT = bb, [enc(X)/TOP] is inert
(X never forced), [enc(Y)/bb]bb = enc(Y) forces Y.  So under the lazy-pass
machine:

* the condition is forced;
* exactly the taken branch is forced (once);
* the taken branch's value is returned verbatim (dec o enc = id).

**[VERIFIED]** (`verify_round4.py` D1, D1b, D1c): probes in the two branch
slots of `if(C, probeT(u), probeE(v))` — only the taken branch's probe
activates, for C in {TOP, BOT}; `if(TOP, X, Omega) = if(BOT, Omega, X) = X`
with Omega never forced, while the SAME program text diverges under the
eager semantics; and an entire structural-recursion scheme runs through
`if` with no gate machinery at all — `revif(X) = if(isne X,
cat(revif(tail X), head X), eps)` reverses all 127 strings of length <= 6
exactly.

Two consequences.  First, the lazy-pass discipline is the *minimal* repair
of the eager calculus's one visible defect: the guarded `rep` of Remark
`rem:total-rep` can be written naively — put the round in the branch of an
`if` on `eq(X_i, eps)`; the round's renaming pattern `enc^2(X_i)` is only
evaluated when the branch is taken, i.e. when it is nonempty.  Second, all
guarding still *goes through pattern gates* — `if` gates through the
[enc(X)/TOP] pass, whose pattern occurs in the intermediate value exactly
when C = TOP.  The explicit gate below (`sel`) makes the gate VALUE a
constant (P or Q) and is used for the schemes; `if` itself is a verified
alternative (D1c).

**Why the naive one-way gate is unsound.**  The scheme
`F(X) = [B(X, F(tail X))/P] if(isne X, P, H(X))` — a recursive call in the
replacement of a pass whose gate value is P exactly when X != eps — looks
like the natural guarded recursion, but the *closed*-gate value H(eps) may
itself contain P, in which case the pass fires inside the base value.
Witness (verified in `verify_round4.py` D2):
`F(X) = [Omega(X)/a] if(isne X, a, a)` diverges on X = eps although the
intended base case is the constant a.  The two-way gate avoids this: the
gate values are the constants P and Q, and branch values travel through
`enc^2` — they never meet the patterns.

### 3.1 The two-way gate

**Definition (sel).**  Fix the encoding characters b != x (of enc^2) and set

    P = b b x,      Q = x b b

(three-character markers; both contain bb; P not-sub-of Q; Q not-sub-of P).
Define the 3-ary function sel by

    sel(C, u, v) = dec^2_x( [enc^2_x(X3)/Q] [enc^2_x(X2)/P] if(X1, P, Q) )

— the definition `sel(X1,X2,X3)` with the displayed body, where `if` is the
paper's Selection and enc^2/dec^2 the Comma Code.  (For Sigma = {a,b},
b = a, x = b: P = "aab", Q = "baa".)

**Theorem 3.1 (two-way gate).**  For C in {TOP, BOT} and any values u, v:
(i) sel(TOP, u, v) = u and sel(BOT, u, v) = v;
(ii) the machine on (TOP, u, v) forces X1 and X2 (each exactly once) and
never X3; on (BOT, u, v) it forces X1 and X3 and never X2.
*Proof.*  (i) By the Selection theorem if(TOP,P,Q) = P.  The inner pass
`[enc^2(X2)/P]` has pattern P != eps and P occurs in the gate value (it
*is* the gate value), so rule (11) evaluates the replacement enc^2(X2) —
whose innermost pass has X2 as scrutinee, forcing it — and by **Direct
Substitution** `[enc^2(X2)/P]P = enc^2(X2)`.  The outer pass
`[enc^2(X3)/Q]`: its pattern Q = xbb contains bb, and enc^2-images have
b-runs of length <= 1 (Comma Code Lemma (ii)), so Q does not occur in
enc^2(X2); the pass is inert.  Finally dec^2(enc^2(u)) = u (Comma Code
Lemma (i)).  The case C = BOT is symmetric: P = bbx does not occur in
Q = xbb (compare character-wise at positions 0 and 2), so the P-pass is
inert; `[enc^2(X3)/Q]Q = enc^2(X3)` by Direct Substitution; dec^2 returns
v.  (ii) X1 is the scrutinee of the if-construction's innermost pass
`[bb/BOT]X1` — forced unconditionally.  X2 occurs in the body exactly once,
inside enc^2(X2) in the *replacement* slot of the P-pass: a replacement is
evaluated only when its pattern occurs (rule 11), which is exactly when
C = TOP; X3 symmetrically for Q and C = BOT.  "Exactly once" is
call-by-need memoization (Prop. 2). []

**Corollary 3.2 (verbatim return).**  sel returns the taken branch's value
unchanged (dec^2 o enc^2 = id).  This is what makes sel usable as a
*definition scheme*: no wrapping discipline is imposed on branch values.

**Remark (the naive one-way gate is unsound).**  The scheme
`F(X) = [B(X, F(tail X))/P] if(isne X, P, H(X))` — a recursive call in the
replacement of a pass whose gate value is P exactly when X != eps — looks
like the natural guarded recursion, but the *closed*-gate value H(eps) may
itself contain P, in which case the pass fires inside the base value.
Toy witness (verified in `verify_round4.py` (D)):
`F(X) = [Omega(X)/a] if(isne X, a, a)` diverges on X = eps although the
intended base case is the constant a.  The two-way gate avoids this
entirely: the closed-gate value is the constant Q, the open-gate value the
constant P, and the branch values travel through enc^2 — they never
interact with the patterns.  All guarding below goes through sel.

### 3.2 The expansion (macro) lemma

**Lemma 3.3 (heap extension).**  If <e, rho, H> << <w, H1> then for every
heap H' extending H by fresh cells, <e, rho, H'> << <w, H1'> where H1'
extends H1 by fresh cells.  The derivation reads only cells reachable from
rho and allocates only fresh cells.
*Proof.*  Induction on the derivation: each rule's premises read the
environment's cells or cells allocated by the sub-derivations; by the
freshness invariant (Sec. 1.4, Call Lemma) these are disjoint from the
extension. []

**Lemma 3.4 (expansion / beta for extended expressions).**  Let E be an
extended expression with distinguished variable Z, and G an extended
expression (calls allowed).  Then the machine value of `E[G/Z]` under rho
agrees with the machine value of E under rho with Z bound to a cell holding
`thunk(G, rho)`: same value, same stuckness, same divergence.
*Proof.*  Structural induction on E, via Theorem A (big-step).  At a
Z-site, `E[G/Z]` carries a syntactic copy of G; each *forced* copy
evaluates under rho in a heap state that differs only by fresh cells
(Lemma 3.3), so by determinism all forced copies yield the same value v,
and the shared cell of the right-hand side yields the same v.  For the
substitution node the case analysis of rule (11) depends only on the
pattern and scrutinee values, which agree by the induction hypothesis;
when the pass is inert the replacement copy (resp. the thunk) is never
entered.  Termination agreement follows: a forced copy terminates iff the
thunk does (identical evaluations, Lemma 3.3). []

This is the extended-calculus analogue of the paper's Lemma lem:beta;
it licenses inlining an arbitrary (call-containing) expression into a
call-free scheme body, which is how the schemes below are written.

### 3.3 The guarded structural-recursion scheme

**Definition (scheme S1).**  Given call-free total expressions
B(X, Y_, Z) (the step; Z the recursion variable) and H(X, Y_) (the base),
define

    F(X, Y_) = sel( isne(X),
                    B(X, Y_)[ F(tail X, Y_) / Z ],
                    H(X, Y_) )

— the definition F whose body is the sel-call shown, with the recursive
call inlined at Z's occurrences in B.  (isne(X) = if(eq(X,eps),BOT,TOP),
call-free and total.)

**Theorem 3.5 (guarded structural recursion).**  Under the lazy-pass
machine the definition of scheme S1 is total on (Sigma*)^{1+k} and
satisfies

    F(eps, Y_)     = H(eps, Y_)
    F(aT, Y_)      = B(aT, Y_, F(T, Y_))        for every a in Sigma, T in Sigma*.

*Proof.*  Termination and the equations together, by strong induction on
|X|.  If X = eps: isne(eps) = BOT, so by Theorem 3.1(ii) the machine forces
X3 = H(eps, Y_) — call-free and total, hence terminating (Prop. 1) with
the value of its eager denotation (T1) — and never X2; sel returns that
value: F(eps, Y_) = H(eps, Y_).  If X = aT: isne(aT) = TOP; the machine
forces X2 = B(aT, Y_)[F(T, Y_)/Z].  By Lemma 3.4 this evaluates as B with
Z's value = the value of the call F(T, Y_).  Each forced Z-site activates
that call, whose arguments have |T| < |X|; by the induction hypothesis and
the Call Lemma it terminates with a value w_T independent of the
activation.  B is call-free total, so its evaluation terminates on any
inputs; if Z is never forced its value is irrelevant, otherwise it is w_T.
Hence X2 terminates with B(aT, Y_, w_T), and sel returns it:
F(aT, Y_) = B(aT, Y_, F(T, Y_)). []

### 3.4 Reversal

**Theorem 3.6 (reversal is computable).**  The definition

    rev(X) = sel( isne(X), cat( rev(tail X), head X ), eps )

i.e. B(X, Z) = cat(Z, head X), H(X) = eps, is total and computes
S |-> reverse(S).  The Sec. 5.6 hinge ("is reversal L-reachable?") therefore
dissolves once recursion is admitted: reversal is lazy-pass computable.
*Proof.*  B and H are call-free and total (cat, head, tail are raw-L, Thm
thm:headtail / thm:cat).  Theorem 3.5 gives totality and
rev(eps) = eps, rev(aT) = cat(rev(T), a) = rev(T)·a; induction on |S| gives
rev(S) = reverse(S). []

**Verification (round 2).  [VERIFIED]**  `verify_round2.py`:
(A) small-step = big-step: 400 random 3-definition recursive programs
(extended grammar, arities 1-2, depth <= 3, including pattern-empty and
blackhole cases): 400/400 agreements — 119 with equal values, 51 both-stuck,
230 both-no-value-within-cap; 0 disagreements.
(B) sel: B1 — 200 random triples (branches of length <= 8): values exact.
B2 — 100 runs with identity probes as branches: taken branch's probe
activated exactly once, untaken branch's probe never activated, in all 100.
B3 — sel(TOP, X, Omega(X)) with Omega(X) = cat(Omega(X), X): lazy machine
returns X (Omega never forced); the *same program text* diverges under the
eager semantics.
(C) scheme: C1 — rev on ALL 127 strings of length <= 6 over {a,b}: exact
(max 1701 machine steps), plus 20 random strings of length <= 10: exact.
C2 — len (S |-> a^|S|) on all 127 strings of length <= 6: exact.
C3 — par (step function built from if/eq, not cat) on all 255 strings of
length <= 7 plus 60 random of length <= 12: exact.

---

## 4. Universality

### 4.0 The general scheme

The scheme of Sec. 3.3 generalizes: the recursion argument need not be
`tail X`.

**Scheme S.**  Given call-free total expressions C (a {TOP,BOT}-valued
*gate*), t (the *descent*), B (the *step*), H (the *base*), define

    F(X, Y_) = sel( C(X,Y_),  B(X,Y_)[ F(t(X,Y_), Y_) / Z ],  H(X,Y_) )

with |t(X,Y_)| < |X| whenever C(X,Y_) = TOP.  (S1 is C = isne, t = tail.)

**Theorem 4.0.**  Scheme S is total and satisfies
F = (C ? B(-, F(t(-))) : H(-)) pointwise.
*Proof.*  As Theorem 3.5, with the measure |X| and the descent |t| < |X|
when the gate is open.  Note the base case fires exactly when C = BOT, and
the taken branch is returned verbatim (Cor. 3.2). []

**Theorem 4.1 (primitive-recursive closure).**  Every function obtained
from the raw-L toolkit (constants, projections, cat, head, tail, eq, if,
and with it every call-free total expression) by composition and structural
recursion on a string argument with parameters — i.e. every
*string-primitive-recursive* function — is definable in the lazy-pass
calculus.
*Proof.*  Composition: a definition may call any earlier definition (the
program is a list; the construction is stratified), and inlining a
call-containing expression into a call-free body is sound by Lemma 3.4.
Structural recursion on the first argument with parameters is Scheme S
with C = isne, t = tail.  The equations hold by Theorem 4.0. []
**[VERIFIED]** instances: rev, len, par (Sec. 3), ADD, MULT, the parsers
PCNT / DROPB / TAKEA / SKIPAB, V, ODD, DIGITS (Sec. 4.4 and
`verify_round3.py`).

### 4.1 Pattern-gated minimization

**Theorem 4.2 (the mu-scheme).**  Let P : Sigma* -> {TOP,BOT} and next :
Sigma* -> Sigma* be total definable.  Define

    W(X_, Y) = sel( P(X_,Y),  Y,  W(X_, next(Y)) )
    F(X_)    = W(X_, eps)

Then F(X_) = the shortlex-least Y with P(X_,Y) = TOP, and F(X_) diverges if
there is none.  (Shortlex = the order whose successor is next.)
*Proof.*  The recursive call sits in the ELSE branch of the gate, so it is
forced exactly when P = BOT (Theorem 3.1).  If the trajectory
Y_0 = eps, Y_{k+1} = next(Y_k) first satisfies P at step n, then by
induction on n the machine returns Y_n: each unfolding computes P (total),
takes the THEN branch exactly at depth n.  If no Y_k satisfies P: by
induction on k, after k unfoldings the machine is in the same
configuration shape with Y = Y_k and P(X_,Y_k) = BOT, so the gate never
closes; no rule errors (all sub-expressions total); the run is infinite
(the call rule (7) is a tail transfer, so the stack stays bounded — this is
divergence by unrolling, not by regress). []

The needed `next` is itself definable:

    incr(X)  = sel( isne X, sel( eq(head X, b),  a . incr(tail X),
                                   succch(head X) . tail X ),  a )
    next(S)  = rev( incr( rev(S) ) )

— little-endian increment (Scheme S) conjugated by reversal (Thm 3.6).
**[VERIFIED]**: the orbit of next from eps lists all 127 strings of length
<= 6 over {a,b} in exactly the shortlex order.

**Corollary 4.3 (a mu-search, executed).**  SQRT(X) = mu Y. cat(Y,Y) = X
(the string square root): W as above with P = eq(cat(Y,Y), X).
**[VERIFIED]**: exact on all 15 squares X = w.w with |w| <= 3; on six
non-squares no value is produced within the step cap (divergent, as the
mu-scheme predicts).

### 4.2 Two-counter machines, compiled

**Definition (2CM configurations).**  A configuration of a two-counter
machine with instructions 1..s (pc 0 = halt) is coded by the string

    b^i . a^{x+1} . b . a^{y+1} . b        (i = pc, x = counter 1, y = counter 2).

**The compiler** (`verify_round3.py, cm2_defs`) maps an instruction list
over {halt; inc(r,j); decjz(r,jz,jnz)} to definitions:
parsers PCNT (leading b-run = the pc, as a b-tally), DROPB, TAKEA, SKIPAB
(four Scheme-S definitions, machine-independent); projections
Xc = tail(TAKEA(DROPB c)), Yc = tail(TAKEA(SKIPAB(DROPB c))); the
constructor MK(i,x,y) = b^i a a^x b a a^y b (raw-L cat); the step function
as a sel-tree over eq(PCNT(c), b^i) with one raw-L case per instruction
(inc: append a tally a; decjz: eq(Xc,eps) selects the jump); and the driver

    RUN(c) = sel( eq(PCNT(c), eps), out(c), RUN(step(c)) )

— the pattern-gated while loop: the recursive call is forced exactly while
the machine has not halted.  **[VERIFIED]**: a doubling machine
(c2 := 2 c1) — MAIN(a^n) = a^{2n} for n = 0..5; an adder —
RUN on 20 initial configurations (n,m), c2 = n + m exactly.

### 4.3 The universality theorem

**Theorem T4 (universality).**  For |Sigma| >= 2 the lazy-pass calculus
computes exactly the partial computable functions (Sigma*)^n -> Sigma*.
*Proof.*  (a) Every partial computable f is definable.  The coding
V : Sigma* -> a-tallies (Horner with a sentinel bit, Scheme S:
V(eps) = a, V(cT) = 2 V(T) + idx(c)) is injective, and its inverse DIGITS
(Scheme S over the raw-L floor-halving pipeline [a/b][eps/a][b/aa] — the
mirror of the paper's Section 5.6 halving pipeline) is definable;
**[VERIFIED]**: DIGITS(V(X)) = X on all 63 strings of length <= 5.
By Minsky's theorem the partial function n |-> m with n = V(X),
m = V(f(X)) is computed by some two-counter machine M_f; Section 4.2's
compiler turns M_f into definitions, and f = DIGITS(RUN_M(INIT(V(X))))
composes them.  (b) Every definable function is partial computable: the
machine of Sec. 1 is effective (each rule is primitive recursive in its
data; the accompanying interpreter is a witness), so by Church's thesis —
or a direct coding of configurations — its partial functions are partial
computable. []

**Proposition 4.4 (self-recursion suffices; mutual recursion is
definable).**
(i) Every construction in Sections 3-4 is *stratified*: a definition calls
only itself and definitions introduced before it.  The dependency graph of
the universality construction is a DAG plus self-loops.  Hence NO MUTUAL
RECURSION IS NEEDED.
(ii) Mutual recursion is nonetheless available: given mutually recursive
f, g, define one self-recursive F on tagged pairs.  Verified instance
(even/odd on tallies): tags b / bb on a-tallies; the dispatch is the
raw-L occurrence test contains(P, bb); the tag is stripped by the deletion
pipeline [eps/b][eps/bb] (inert on the other tag since tallies contain no
b); the flip is cat(newtag, T).  In general the two components are
protected by enc (marker-immune images) and the tags chosen among the
markers bbx, xbb of Sec. 3.1, with the projections definable by Scheme-S
marker scans.  So mutual recursion adds no expressive power.
**[VERIFIED]**: direct mutual (even, odd) and the single-F tagged version
agree with parity on tallies 0..8 (18 pairs, exact). []

**Remark (alphabet).**  Everything in this report — the gate, the schemes,
the mu-loop, the 2CM compiler — ran over Sigma = {a,b}, the weakest
alphabet of the paper's hypothesis.

---

## 5. Consequences

### 5.1  The Section-4-unreachable function X |-> X^{2^{|X|}}  (T5)

**Definition** (`verify_round4.py`, test_T5):

    A(S, W)   =  sel( isne(S),  A(tail S, cat(W, W)),  W )
    EXP(X)    =  A(X, X)

**Theorem 5.1.**  EXP is total and EXP(X) = X^{2^{|X|}}.
*Proof.*  This is Scheme S (Thm 4.0) on S, so total; the value is by
induction on |S|: A(eps, W) = W = W^{2^0}, and
A(aT, W) = A(T, W^2) = (W^2)^{2^{|T|}} = W^{2^{|T|+1}} = W^{2^{|aT|}};
EXP(X) = A(X, X) = X^{2^{|X|}}. []

The function is unreachable in L: the paper's Section 4 shows any L-value
of X has length <= C(1+|X|)^d (Lemma lem:length), and |X|.2^{|X|} exceeds
every such bound.  What breaks is informative: a recursive definition
unrolls |X| times, so the *degree of an expression* no longer bounds the
growth of its value — the length/degree machinery of Section 4 is a
statement about pipelines (Prop. prop:pipeline), and recursion is not a
pipeline.
**[VERIFIED]**: EXP exact on ALL 31 strings of length <= 4 (|X| = 4 gives
output length 64).

### 5.2  The executed mu-search and two-counter machines  (T6)

The mu-search SQRT (Sec. 4.1) and the 2CM compiler (Sec. 4.2) were executed
on the machine: SQRT on the 15 squares |w| <= 3 (exact) and 5 non-squares
(no value within cap, as intended); the doubling 2CM on n = 0..5 and the
adder 2CM on 20 configurations (exact).  Together with Thm 4.3 these are
the task's "mu-search or counter-machine example actually run".

### 5.3  Re-gating: eager-divergent programs that terminate lazily  (T7)

Three witnesses, all run under BOTH semantics on the SAME text
(`verify_round4.py` D/E; D2's counterpart in round 2 B3):

* **E1 (discarded replacement).**  `[Omega(X)/b]X` on X = a: the pattern b
  does not occur in a, so the machine returns a and never forces Omega;
  the eager denotation evaluates the replacement slot and diverges.
* **E2 / D1b (gated branch).**  `sel(TOP, X, Omega(X))` and
  `if(TOP, X, Omega(X))`: the untaken branch is a thunk that is never
  forced; call-by-value forces it and diverges.
* **D3 (no gate at all).**  Ungated `F(X) = cat(F(tail X), head X)`
  diverges under BOTH semantics — a structural recursion needs the gate;
  with it (D1c, round 2 C1) the very same body is `rev`.

Moral: the eager calculus's only obstruction to recursion is that every
position is strict; the lazy-pass machine removes precisely the two
strictnesses that matter (the replacement slot, and the argument slots of
calls), and this suffices for universality (Sec. 4) while changing nothing
on the eager-defined domain (T1).

### 5.4  Tower growth from a TOTAL definition  (T9)

**Definitions** (`verify_round4.py`, tower_defs) — the paper's once-primitive
REPL rebuilt by structural recursion, then the two restarts of Sec. 5.6 as
gated while loops:

    PRE(B,S)    =  S starts with B                       (Scheme S on B)
    LEN(S)      =  a^{|S|}                               (Scheme S on S)
    DROP(S,k)   =  S minus |k| characters                (Scheme S on k)
    REPL(A,B,S) =  replace the LEFTMOST occurrence of B in S by A
                   (Scheme S on S; the once-primitive of Sec. 5.1)
    AMP1(S)     =  sel( contains(S,ab),  AMP1(REPL(baa,ab,S)),  S )
    AMP2(S)     =  sel( contains(S,aa),  AMP2(REPL(ab,aa,S)),  S )
    BLOCK(S)    =  AMP1(AMP2(S))
    TWR(S)      =  sel( isne(S),  [eps/b](BLOCK(TWR(tail S))),  aaaa )

AMP1 and AMP2 are exactly the paper's restart nodes `[baa/ab]^m` and
`[ab/aa]^m` (Def. def:markov) — the mu-scheme of Thm 4.2 with the
recursive call forced precisely while the pattern still occurs.  Both
terminate (below), so these particular while loops cannot diverge; BLOCK
composes them in the order of Corollary cor:towers ([ab/aa]-restart
first, then the amplifier), and TWR iterates BLOCK down |S|.

**Theorem 5.4 (tower growth from a total definition).**  TWR is total,
and TWR(S) = a^{K_{|S|}} for every S, where K_0 = 4 and
K_{n+1} = 2^{K_n/2 + 1} - 2.  Hence |TWR(S)| >= 2^{K_{|S|-1}/2}: each
additional input character adds one exponentiation level — the output
length is a tower of exponentials of height |S| in the input length.
Consequently the polynomial length bound (Lemma lem:length) and the
polynomial-time soundness (Thm thm:fp) fail for TOTAL recursive programs,
not merely for divergent ones.
*Proof.*  Totality: PRE, LEN, DROP, REPL are Scheme-S instances (Thm 4.0);
AMP2 is the restart of a length-preserving rule with A != B, total by the
paper's Thm thm:termination(ii); AMP1 is the restart of the amplifier,
total by Thm thm:amplifier (exactly v(S) - #a(S) steps); BLOCK and TWR
are Scheme-S compositions of total definitions.  Growth: by the amplifier
formula (Cor. cor:towers), BLOCK(b^m a^K) = b^{m+j} a^{2^{j+1}-2+(K mod 2)}
with j = floor(K/2).  Induction on |S|, all K_n even (K_0 = 4 and
2^{t+1}-2 is even): TWR(tail S) = a^{K_n} with n = |S|-1, so
BLOCK(a^{K_n}) = b^{K_n/2} a^{2^{K_n/2+1}-2}, and the [eps/b] pass strips
the b-prefix, giving K_{n+1} = 2^{K_n/2+1} - 2 >= 2^{K_n/2}. []
**[VERIFIED]**: REPL vs Python single-leftmost on 240 cases — exact;
AMP1 and AMP2 vs the paper's `restart()` primitive (imported from
paper_variants/verify_variants.py) on 80 random strings len <= 7 — exact
agreement; BLOCK vs the amplifier formula on 24 inputs (m <= 2, K <= 8) —
exact; TWR on ALL 15 strings of length <= 3: TWR(S) = a^K with
K = 4, 6, 14, 254 by |S| — exact.  (K_4 = 2^128 - 2 is forced by the
verified formula but lies beyond any feasible run.)

### 5.5  What this means for the paper's landscape

* The Sec. 5.6 hinge "is reversal L-reachable?" **dissolves one level
  up**: reversal is lazy-pass-computable (Thm 3.6, and through the paper's
  own `if`, Sec. 3.0/D1c).  The question for call-free L is untouched —
  every construction here uses recursion, so we contribute no evidence
  either way about raw L.
* The complexity row gains a clean entry: bounded pipelines = polynomial
  (thm:fp); recursive definitions = all partial computable functions,
  with totality undecidable (Sec. 6) and tower growth already inside TOTAL
  programs (Thm 5.4).  The paper's Markov row (cor:towers) exhibits the
  same growth, but there via the variant primitive; here it sits inside a
  conservative extension of the baseline calculus.
* The Remark rem:total-rep repair: under lazy-pass the naive guard
  `if(eq(X_i,eps), identity, round_i)` is sound — the round's renaming
  pattern enc^2(X_i) is evaluated only when its branch is taken, i.e. only
  when X_i is nonempty (the if-gate finding, Sec. 3.0).  The paper's
  pattern-position guard remains the right construction for the EAGER
  calculus.

---

## 6.  Totality of a definition is undecidable  (T8)  [SKETCH]

**Proposition 6.**  There is no algorithm deciding, given a definition F
of the lazy-pass calculus, whether F is total (i.e. F(w) is defined for
every w in Sigma*).
*Sketch (reduction from the 2CM halting problem; routine given the
compiler of Sec. 4.2).*  Given a 2CM M and input w, the compiler produces
definitions RUN_M and INIT_M; add

    H_{M,w}(X)  =  out( RUN_M( INIT_M(w) ) )

whose body does not mention X.  By the driver analysis of Thm 4.2,
H_{M,w} is total iff M halts on w, and diverges on every input otherwise.
A totality decider would decide 2CM halting, which is undecidable
(Minsky).  Replacing `out` by any non-constant decidable post-processing
gives the Rice-style extension to every nontrivial extensional property
of the computed partial function.  The same reduction shows: whether a
given F converges on a GIVEN input is undecidable. []

---

## 7.  Verification summary

Interpreter: `core.py` (small-step machine of Sec. 1, big-step demand
semantics, eager reference for def:den) + `toolkit.py` (raw-L builders
transcribed from the paper's Section 2, incl. the pass-order convention
"rightmost listed pass runs first").  All runs over Sigma = {a,b} with
b_ = a, x_ = b, TOP = b, BOT = a.  Logs: round1..4.log.

| round | test | domain | result |
|---|---|---|---|
| 1 (a) | toolkit builders vs Python truth | 400 random pairs per family, 8 families | 8/8 OK |
| 1 (b) | conservativity (T1) | 9000 random call-free exprs | 5475/5475 agree where eager defined; 3525 eager-undefined of which 3200 Err + 325 strictly-more-defined; 0 mismatches |
| 1 (c) | strict-extension witness | 1 | OK |
| 2 (A) | small-step = big-step | 400 random recursive programs, caps 150k steps / 4000 depth | 400/400 agree (119 value, 51 stuck, 230 no-value both) |
| 2 (B) | sel values / forcing / divergent 3rd arg | 200 triples / 100 runs / 1 | all OK |
| 2 (C) | rev / len / par schemes | all 127 strings <= 6 + 20 random <= 10 / 127 / 315 <= 7 + 60 random <= 12 | all exact |
| 3 (A) | next = rev.incr.rev vs shortlex | orbit of 127 strings from eps | exact |
| 3 (B) | mu-search SQRT | 15 squares + 5 non-squares | exact / no value (as intended) |
| 3 (C) | ADD, MULT on tallies | 36 pairs, 72 evals | exact |
| 3 (D) | HALF, ODD, V, DIGITS | 40 tallies; 63 strings roundtrip (126 evals) | exact |
| 3 (E) | mutual vs single-F even/odd | tallies 0..8, 18 pairs | exact |
| 3 (F) | 2CM compiler | doubling n=0..5; adder 20 configs | exact |
| 4 (D) | if-gate finding, naive-gate witness, ungated recursion | probes (2), divergent branches (2), rev through if (127), witnesses (3) | all OK |
| 4 (E) | eager-vs-lazy, same text | 2 witnesses | OK |
| 4 (T5) | EXP = X^{2^{|X|}} | all 31 strings \|X\| <= 4 | exact |
| 4 (T9) | REPL / AMP1 / AMP2 / BLOCK / TWR | 240 / 80 / 24 / 15 | all exact |

No FAIL line in any log; all four `verify_roundN.py` exit 0.

---

## 8.  PROVED / VERIFIED / CONJECTURAL

**PROVED** (full proof in this report):
P0 determinism of the machine; P1 call-free termination (machine = paper's
denotation, no infinite runs); P2 forcing coincidence (once-if-any =
once-per-match; the value does not depend on when R is forced, only on
whether); P3 blackhole detection = divergence; Theorem 3.1 (the two-way
gate sel); the Sec. 3.0 finding that the paper's `if` IS a pattern gate
under lazy-pass (both directions, with the thm:enc(ii) non-occurrence
argument) and that the NAIVE one-way gate is unsound (witness D2);
Theorem 3.5 / 4.0 (Scheme S, guarded structural recursion); Theorem 3.6
(reversal); Sec. 4.1 (PR closure); Theorem 4.2 (the mu-scheme);
Theorem 4.3 (universality — the definability half is constructive from
the 2CM compiler, the other half is the interpreter); Proposition 4.4
(self-recursion suffices; mutual definable from self); Theorem 5.1
(X^{2^{|X|}}); Theorem 5.4 (tower growth from a total definition).

**PROVED at routine-induction level** (proof given as a sketch with the
full induction spine; cross-checked by machine):
Theorem A (small-step = big-step, 400/400); Lemmas 3.3/3.4 (heap
extension, expansion); the LFP remark of Sec. 1.6 (monotone, continuous,
Kleene chain = big-step semantics).

**SKETCH** (labeled as such): Proposition 6 (totality undecidable);
the coding details of the 2CM compiler's non-termination half of Thm 4.3
(configuration bookkeeping is routine and machine-checked, not written out
to the last clause); Sec. 1.6's claim that the lazy denotation is the
least fixed point.

**VERIFIED**: the table of Sec. 7 — in particular everything the task
demanded: reversal on all strings <= 6 (127 strings, and again through the
paper's own if); X^{2^{|X|}} for |X| <= 4; the mu-search and a 2CM
executed; eager-divergent programs terminating once re-gated; tower growth
4, 6, 14, 254 on all 15 strings of length <= 3; conservativity on 9000
expressions; machine consistency on 400 recursive programs.

**CONJECTURAL / OPEN** (new questions this work raises):
1. **The eager recursive calculus is probably NOT universal.**  Under the
   eager semantics every position is strict, so every call node in a body
   is evaluated at every activation; a terminating eager definition needs
   every forced-call chain well-founded.  Ackermann is eager-computable
   (both nested calls decrease a lexicographic measure), but an
   unbounded mu search seems to have no strict-position encoding —
   the guard itself is what is missing.  We did not attempt the precise
   characterization.  Confidence in non-universality: medium-high.
2. **Which single non-strictness suffices?**  Universality here used the
   replacement slot's non-strictness (via if/sel); call-by-need argument
   slots alone (strict replacement) were not investigated.  Sec. 4.3's
   inlining observation suggests replacement-laziness ALONE suffices
   (macro-expand arguments); whether argument-laziness alone suffices is
   open.  Confidence that replacement-laziness suffices: high.
3. **Nothing here bears on the paper's open hinges for call-free L**
   (once in L? reversal in L? right-to-left behavior).  All constructions
   use recursion; no evidence either way about raw L is contributed.

### Confidence in the headline results

| result | status | confidence |
|---|---|---|
| T1 conservative extension | PROVED + 9000-case sweep | very high |
| if is a pattern gate (lazy) | PROVED (mechanism) + probes + 127-string scheme | very high |
| T2/T3 guarded recursion + reversal | PROVED + exhaustive <= 6 | very high |
| T4 universality, self-recursion suffices | construction PROVED, converse witnessed | high |
| T5 X^{2^{\|X\|}} | PROVED + exhaustive <= 4 | very high |
| T7 re-gating dissolves eager divergence | PROVED + witnesses | very high |
| T8 totality undecidable | SKETCH (routine reduction) | high |
| T9 tower from a total definition | PROVED + formula-verified + 15 inputs | very high |
| small = big step | PROVED (sketch) + 400 programs | high |

*End of report.*

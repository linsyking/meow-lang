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

## 3. Pattern gates and guarded recursion — planned (round 2)

## 4. Universality — planned (round 3)

## 5. Consequences — planned (round 4)

## 6. Undecidability of totality — planned (round 4)

## 7. Verification summary — planned

## 8. PROVED / VERIFIED / CONJECTURAL — planned

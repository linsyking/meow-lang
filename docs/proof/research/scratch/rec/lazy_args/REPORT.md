# Recursive Definitions over L: the Lazy-Arguments (Call-by-Need) Semantics

Research agent `rec-lazy-args` for *"A Theory of String Substitution over Finite
Alphabets"* (`docs/proof/main.tex`).  Working directory:
`docs/proof/research/scratch/rec/lazy_args/`.  Companion scripts: `lrec.py`
(core), `checks.py` (verification suite), `search.py` (exhaustive separation
search).  Notation and numbering of the paper are used throughout: `def:subst`
(the primitive `[A/B]S`), `def:exp`/`def:den` (expressions and their strict
denotation), `Lemma beta`/`cor:closure` (Section 3), `def:reachable`.

---

## 0. Answer in one paragraph

Fix the paper's calculus `L` (`def:exp`/`def:den`) and extend it with finitely
many named first-order recursive definitions (`L_rec`), the only new node being
the call `f(E_1,...,E_m)`.  Give it the **lazy-arguments** runtime semantics:
call-by-need -- arguments become thunks -- while **every constructor stays
exactly as strict as in `def:den`** (a pass `[R/P]E` evaluates all three of
`R`, `P`, `E`; concatenation evaluates both concatenands).  Then:

* **Forcing is purely syntactic.**  A thunk for argument `i` of a call to `f`
  is forced **iff the parameter is live in `f`**, where liveness is the *least
  fixpoint* `S* = mu F` of the occurrence/position operator `F` defined in
  Section 3 -- and this is decidable in polynomial time (Theorems 1, 2).
* **Termination is input-independent.**  The live call tree is a syntactic
  object; a lazy-args program halts on *all* inputs or on *none*
  (Theorem 3).  Halting is decidable in polynomial time: it is exactly
  acyclicity of the *live dependency graph* (Section 4).
* **Recursion is inert.**  A halting program denotes `[[E']]` for the plain-`L`
  expression `E'` obtained by pruning dead call subtrees and expanding
  (Theorem 4; the expansion is an iterated `Lemma beta` step); a non-halting
  program denotes bottom everywhere (Theorem 5).  Hence **the lazy-args
  calculus denotes exactly `L`'s partial functions** (Theorem 6), and
  everything it computes is polynomial-time with the exponent bounded by `E'`.
* **Operational separation despite denotational equality.**  Minimal programs
  where lazy halts (with a value) and eager diverges exist already at total
  size 6 (size 4 if 0-ary calls are allowed); eager can also *err* where lazy
  yields a value (dead argument with an eps-pattern), at total size 9.  No
  1-function program separates (Lemma 8.1, proved).  All of this is
  machine-verified (Section 9).

Sections 1-2 fix the semantics, Sections 3-4 the two syntactic analyses,
Sections 5-7 the theorems, Section 8 the separation examples, Section 8.5 the
hand-off note for the *lazy passes* variant, Section 9 the verification
results, Section 10 the status ledger.  Status labels: **PROVED**
(pen-and-paper proof in this report), **VERIFIED** (machine-checked on the
stated domains), both or neither.

---

## 1. Setting: `L_rec`

Fix a finite alphabet Sigma with |Sigma| >= 2.  Recall the paper's primitive
(`def:subst`): `[A/B]C` scans `C` once left-to-right, replaces every
occurrence of `B` by `A` taking the leftmost match first, never rescanning
inserted text; `[A/eps]` is **undefined**.

**Definition 1.1 (expressions, bodies, programs).**  An `L_rec` *program* is a
finite family `D = (f_1, ..., f_k)` of pairwise distinct function symbols, each
with an *arity* `m_j in N`, together with a *body* `B_j` for each and a *main*
expression `M`, over the grammar

```
E ::= x_i  (i-th parameter of the enclosing body)      variable
    | W    (W in Sigma*)                                constant
    | [R/P]E                                           pass
    | E1 E2                                            concatenation
    | f_l(E_1, ..., E_{m_l})                           call  (l <= k)
```

`M` uses the input variables `X_1, ..., X_n` in place of parameters.  No other
constructors, no higher order, no built-ins beyond the primitive; the Section-2
toolkit (`enc`, `dec`, `cat`, `head`, `tail`, `eq`, `if`, `rep_n`) is *not*
primitive here -- it is reachable in `L` and therefore usable as an
abbreviation (a macro) inside bodies, with every macro argument a live
position.  We write `size(E)` for the node count (`1` for leaves, `1 + sum of
children` otherwise) and `size(D, M) = sum_j size(B_j) + size(M)`.

**Remark (the crucial strictness stipulation).**  Under `def:den` the
denotation of `[R/P]E` is `[[R]/[[P]][[E]]`, *undefined when `[[P]] = eps`*,
with undefinedness propagating from all three children.  The lazy-args
semantics keeps this exactly: **inside a body, every occurrence of every
constructor child is evaluated** -- the replacement slot (its value is needed
at composition time), the pattern slot (its value is needed, at minimum, to
check `!= eps`; even a pass over scrutinee `eps` evaluates `R` and `P`), the
scrutinee, and both concatenands.  The **only** non-strict position in the
whole calculus is a call argument.  Consequently, in raw `L` there are *no*
parameters that occur yet never force: every occurrence of a parameter at an
evaluated position forces its full string value.  (Positions that never force
exist only under operator-level non-strictness -- the "lazy passes" variant of
the other agent; see the hand-off note, Section 8.5.)

---

## 2. Operational semantics: explicit thunks, complete strictness

**Definition 2.1 (thunk machine).**  A *heap* `H` is a finite partial map from
thunk identifiers to cells in one of the states
`susp(E, rho)` (unevaluated closure), `val(w)` (memoized value), `err`
(memoized eps-pattern outcome).  An *environment* `rho` maps parameter indices
of the body being evaluated to thunk identifiers; the input variables `X_i`
are bound directly to the input strings `S_i`.  The big-step evaluation
relation

```
(E, rho, H) |~ (o, H')      o in { val w | err }
```

is given by:

* **(const)** `(W, rho, H) |~ (val W, H)`.
* **(var)**  `(x_i, rho, H) |~ (val S_i, H)` for input variables; for a
  parameter, *force* the thunk `H(rho(x_i))`:
  `val(w) |-> (val w, H)`; `err |-> (err, H)`; `susp(E', rho')` |-> evaluate
  `(E', rho', H) |~ (o, H'')`, **update the cell** to the outcome
  (memoization), and return `(o, H'')`.
* **(cat)**  evaluate **both** children (in either fixed order):
  `(E_1, rho, H) |~ (o_1, H_1)`, `(E_2, rho, H_1) |~ (o_2, H_2)`; outcome
  `val(w_1 w_2)` if both are values, else `err`.
* **(pass)**  evaluate **all three** of `R`, `P`, `E`; if any outcome is
  `err`, or the pattern value is `eps`, the outcome is `err`; otherwise
  `val([r/p]e)` by `def:subst`.
* **(call)**  for `f(E_1,...,E_m)`: create *fresh* thunks `t_i =
  susp(E_i, rho)` (arguments are **not** evaluated), let `rho' = {x_i |-> t_i}`
  and return the outcome of `(B_f, rho', H')`.

A configuration **diverges** if no derivation exists for it; the *run* of
program `(D, M)` on input `S` is the evaluation of `M` with the input
environment.  Outcomes: *value* (halts), *err* (halts, undefined), *diverge*.

**Definition 2.2 (denotation).**  `[[M]]^LA_D(S) := w` if the run on `S` yields
`val w`; **undefined** if it yields `err` or diverges.  (The two undefined
causes are identified, as in the partial-function reading of `def:den`.)

**Remarks.**

1. *Order independence.*  The set of inputs on which the machine yields a
   value, and the values themselves, do not depend on the order in which
   constructor children are evaluated: a value outcome requires all children
   to have been evaluated to values, and the combination is a function of the
   child values.  What *can* depend on a sequential (early-exit) order is only
   the labeling of an undefined outcome as `err` vs. `diverge`.  The
   *completely strict* presentation above (errors do not cut siblings off;
   only divergence dominates) makes even that labeling order-independent, and
   it is the presentation used in all theorems below; Section 8.5 notes where
   an early-exit order would trade a divergence for an `err`.
2. *No black holes.*  Thunk environments only reference thunks created
   strictly earlier (the environment at a call site predates the call's
   thunks), so a thunk can never be forced while already being forced: there
   are no cycles in the forcing chain.  This uses first-orderness -- there is
   no self-application.  Memoization then guarantees each thunk is evaluated
   at most once per run.
3. *Sharing.*  The semantics is call-by-need (memoized); call-by-name would
   evaluate an argument once per occurrence instead of once per call.  All
   results below (termination, values, denotations) hold for call-by-name as
   well -- only the work bound changes -- because values are pure.  The
   interpreter implements call-by-need as instructed.

---

## 3. Liveness: the least fixpoint

Fix a program `(D, M)`.  Write `Param_f = {x_1, ..., x_{m_f}}` for `f`'s
parameters.

**Definition 3.1 (S-evaluated positions).**  Let `S` be any set of pairs
`(f, i)` ("parameter `i` of `f` is assumed live").  The set `Eval_S(B_f)` of
*S-evaluated positions* of `f`'s body is defined by structural recursion from
the root: the root is evaluated; every constructor child (the three children
`R, P, E` of a pass, the two children of a concatenation) of an evaluated
position is evaluated; and argument `i` of a call `g(...)` at an evaluated
position is evaluated **iff** `(g, i) in S`.  Positions not reached by this
recursion are *dead*.  (Note that `Eval_S` does not depend on any input
value: it is a property of the body and of `S` alone.)

**Definition 3.2 (the liveness operator and `S*`).**
For a set `S` of pairs define

```
F(S) := { (f, i) :  x_i occurs at some position of Eval_S(B_f) } .
```

`F` is monotone in `S` (more assumed-live arguments expose more occurrences)
on the finite lattice `2^{sum_f m_f}`, so it has a least fixpoint

```
S* := mu F  =  F^k(empty)  for  k >= sum_f m_f ,
```

reached by Kleene iteration from `empty` in at most `sum_f m_f` steps (each
iteration adds at least one pair or stops; computable in polynomial time, in
fact in `O(|D|^3)` by the standard worklist method).  A pair `(f, i) in S*`
is **live**; `(f, i) not in S*` is **dead**.

**Why the *least* fixpoint.**  Liveness is a "is ever forced" property, and
forcing propagates outward from actual occurrences, not inward from
assumptions: a parameter passed into an argument slot that is itself never
evaluated must be dead, even if the callee's body mentions its parameter.
Concretely, for `f(x) = g(x)`, `g(y) = f(y)` we get `F(empty) = empty`, so
`S* = empty`: no run ever forces anything (each body is a single call whose
argument is a variable thunk never forced), which is exactly right
operationally.  The *greatest* fixpoint here is `{(f,1), (g,1)}` -- wrong.
(Any *pre*-fixpoint `S` with `F(S) <= S` also satisfies the Confinement
Theorem 1 below; `S*` is the most precise one.)

**Liveness is transitive through call chains** -- the point of the fixpoint:
whether an occurrence of `x_i` counts is decided by descending `Eval_S`
through *live argument slots only*, so a parameter that reaches a forcing
position only through a dead slot of an inner call is dead, iteratively to
any depth.  Two canonical shapes, both machine-verified (Section 9, checks
(d)):

* *Deadness propagated through two definitions:*
  `K(C) = c` (`C` unused), `M(B) = K(B)`, `P(A) = Q(M(A))`, `Q(U) = U`.
  `(K,1)` dead (no occurrence) `=>` `(M,1)` dead (its only occurrence is in
  `K`'s dead argument) `=>` `(P,1)` dead (its only occurrence is in `M`'s dead
  argument).  Kleene: `empty -> {(Q,1)} -> stable`.
* *A call dead through two call levels:*
  `F(X) = G(X, H(F(tail X), X))`, `G(A,B) = A`, `H(U,V) = U`.
  Here `(H,1)` and `(H,2)` are live *in H*, but the only call to `H` sits in
  `G`'s dead argument 2, so nothing of `H`'s arguments is ever forced, and
  with it the recursive call `F(tail X)` is dead through two call levels.

**The eager semantics as a degenerate case.**  Call-by-value is the same
theory with `S = S_all :=` all pairs: every argument of every call is
evaluated, `Eval_S_all(B)` = all positions, and the "liveness" question
disappears.  All theorems below transfer verbatim with `S_all` in place of
`S*` (Theorem 7).

**Proposition 3.3 (dead parameters vanish from live positions).**
For every `f`: if `(f, i) not in S*` then `x_i` has *no* occurrence at any
`S*`-evaluated position of `B_f`; equivalently all its occurrences (if any)
lie under dead argument slots of inner calls.  This is exactly the fixpoint
equation `F(S*) = S*` read as a statement about occurrences.  Consequently,
in every run, an argument expression passed to a dead parameter is *never
started at all* -- not merely never finished.

---

## 4. The live unfolding and the live dependency graph

**Definition 4.1 (live unfolding).**  Define the map `U` from (expression,
environment of already-unfolded argument trees) to trees over the plain-`L`
grammar of `def:exp` plus input-variable leaves:

```
U(x_i, rho)   = rho(x_i)
U(W, rho)     = W
U([R/P]E,rho) = [U(R,rho)/U(P,rho)] U(E,rho)
U(E1 E2,rho)  = U(E1,rho) U(E2,rho)
U(g(D_1..D_m),rho) = U(B_g, rho')   where  rho'(y_i) = U(D_i, rho)  if (g,i) in S*
```

(dead arguments are not unfolded and not substituted: by Proposition 3.3 the
substitution `rho'` is only ever queried on live parameters).  `U(M)` denotes
`U(M, {X_i |-> X_i})`: the *live unfolding* of the program, a possibly
infinite but finitely branching tree **containing no call nodes and no
placeholders** -- every leaf is a constant or an input variable.  (The
interpreter asserts at every variable lookup that the parameter is live; no
assertion ever fired.)  For machine purposes one uses the *shared* unfolding
(DAG): a live argument is unfolded once and its tree is shared among all
occurrences of the parameter; the DAG and the tree have the same denotation
because `def:den` is compositional.

`U(M)` is the promised `E'`: it is obtained (i) by *pruning dead call
subtrees* -- deleting every argument expression passed to a dead parameter --
and (ii) by *expanding calls into bodies with live arguments substituted*,
i.e. by iterated application of the substitution mechanism that `Lemma beta`
proves semantics-preserving (`[[E[F_i/X_i]]] = [[E]] o ([[F_1]], ..., [[F_n]])`),
and whose closure under composition is `cor:closure`.  See Theorem 6.

**Definition 4.2 (live dependency graph).**  Nodes: pairs `(o, pi)` with `o`
a function name (or `main`) and `pi` an `S*`-evaluated *call position* in
`o`'s body.  Edges from a call node `c = (o, pi)` calling `g`:

* *(callee edge)* `c -> (g, pi')` for every `S*`-evaluated call position
  `pi'` of `B_g`;
* *(argument edge)* `c -> (o, pi i pi'')` for every `S*`-evaluated call
  position below `pi i ...`, where `i` ranges over *live* argument indices
  of `c`.

Roots: the `S*`-evaluated call positions of `M`.  This is a finite graph
(at most one node per syntactic call site per owner).

**Proposition 4.3 (finiteness = acyclicity).**  `U(M)` is finite iff no cycle
of the live dependency graph is reachable from the roots.  Moreover this is
decidable in polynomial time (it is an SCC computation on a graph of size
`O(|D|)`).

*Proof.*  The unfolding below an instance of call node `c` consists of (the
body of its callee, and its live argument subtrees) -- exactly the material
reachable through the two edge kinds -- and every call instance inside it is
an instance of a graph-successor of `c`.  So unfolding nodes project onto
walks in the graph; an infinite branch (Koenig: finitely branching) visits
infinitely many call instances, hence some syntactic call node twice, and the
segment between the two visits closes a walk in the graph, whose nodes are
all `S*`-evaluated because the unfolding only walks evaluated positions.
Conversely a reachable cycle can be pumped: following it from a root gives an
infinite branch.  Finally, if the reachable graph is acyclic, the unfolding's
call instances have bounded depth (longest path in the graph) and finitely
branching trees of bounded call-depth are finite.  QED

**Proposition 4.4 (eager counterpart).**  With `S_all` in place of `S*`,
Definitions 4.1-4.2 give the *full* unfolding and the *full* dependency graph
of the eager machine; Proposition 4.3 holds verbatim: the eager machine halts
on all inputs iff no cycle is reachable in the full graph.  Since `Eval_{S*}
subset Eval_{S_all}` position-wise, the live unfolding is a position-collapse
of the full one; in particular *eager-halting implies lazy-halting*, and the
separation programs of Section 8 are exactly the programs in between.

---

## 5. The three core theorems

**Theorem 1 (Confinement: dead means never forced).**
For every input, every run (halting or divergent), and every event of the
run: if a parameter thunk is forced, its pair is in `S*`; and if the
evaluation of a position of some body is started, that position is
`S*`-evaluated.  In particular an argument expression passed to a dead
parameter is never started, on any input, in any run.

*Proof.*  Order the events of the run temporally (event = "start evaluating
position `pi`", which for a variable leaf *is* "force the thunk of the
corresponding parameter"; the two clauses are proved simultaneously).  By
induction on the event order, no event violates either clause.  A started
position is either the root of a body (evaluated by definition), or a
constructor child of an already-started position (evaluated whenever its
parent is, by complete strictness), or the root of argument `i` of an
already-started call to some `g`.  In the last case the argument's
evaluation begins exactly when its thunk is forced, i.e. at the moment an
occurrence of `g`'s parameter `x_i` at some position `q` of `B_g` is
started; that start is a causally earlier event, so by induction `q` is
`S*`-evaluated, whence `(g, i) in F(S*) = S*`, and the argument position --
argument `i` of an `S*`-evaluated call to `g` with `(g, i) in S*` -- is
`S*`-evaluated.  A
forced thunk is forced at a variable leaf of the callee's body whose position
was started, hence by induction `S*`-evaluated; but by the fixpoint equation
`F(S*) = S*` (Proposition 3.3) no dead parameter occurs at any `S*`-evaluated
position.  QED

**Theorem 2 (Full Visitation: live means forced, in halting runs).**
If the run halts (with a value or with `err`), then for every started call to
`f`, every position of `Eval_{S*}(B_f)` was started, and every live parameter
of `f` was forced.

*Proof.*  Induction on the completed evaluation derivation.  A completed
pass node has all three children completed; a completed concatenation both
children (complete strictness -- an early-exit order would break here, see
Section 8.5); a completed call has the callee body completed.  So by
structural induction every `S*`-evaluated position of the body is started.
A live parameter `(f, i)` has, by the fixpoint equation, an occurrence at an
`S*`-evaluated position; that position is started, i.e. the thunk is forced.
QED

**Theorem 3 (Termination dichotomy; input-independence).**
For every input `S`: the lazy machine halts on `S` **iff** `U(M)` is finite.
Consequently a lazy-args program halts on all inputs or on none, and halting
is decidable in polynomial time (Proposition 4.3); which of the two happens
is a property of the program text alone.

*Proof.*  (`<=`)  Suppose `U(M)` finite.  Run the machine on any input.  Each
evaluation instance of the run corresponds injectively to a node of the
*shared* unfolding (the DAG of Definition 4.1): body positions of a call
instance correspond one-to-one to the unfolding nodes below it, and each
thunk's single evaluation corresponds to the argument subtree it carries.
Each unfolding node is evaluated at most once (memoization; no black holes,
Remark 2.2), and each single evaluation terminates: constants, variables and
concatenations trivially, and a pass is one application of `def:subst`,
which is a total terminating scan on any strings with nonempty pattern --
the empty pattern yields the halting outcome `err`.  So the run performs
finitely many finite steps and halts.

(`=>`)  Suppose the run on some input halts.  By Theorem 2 every
`S*`-evaluated position of every started call is started; by induction along
the dependency graph, *every* node of the live dependency graph reachable
from the roots is started (the roots are started when `M` is evaluated; each
edge target is started once its source's instance is).  Now each dependency
edge forces a strict *temporal* ordering: if `c -> c'` is an edge, the call
instance `c'` is started strictly after the call instance `c` -- for a callee
edge because `c'` is inside the body evaluation belonging to `c`; for an
argument edge because the argument thunk of `c` is forced only during the
callee's body evaluation, which begins after `c` is started.  A reachable
cycle would therefore give `start(c) < start(c)`, contradicting the
irreflexivity of the (well-founded, finite) event order.  So the reachable
graph is acyclic, and `U(M)` is finite by Proposition 4.3.  QED

**Corollary 3.1 (what "termination" can depend on).**  If `U(M)` is finite,
the machine halts on every input; the *outcome* (value vs. `err`) may vary
with the input exactly as the plain-`L` expression `U(M)`'s definedness does
(an eps-pattern at a live position is data-dependent -- this is `def:den`'s
own undefinedness, nothing new).  If `U(M)` is infinite, no input yields a
value at all: under the completely-strict presentation the machine diverges
on every input.

---

## 6. What the semantics denotes

**Theorem 4 (Adequacy: well-founded programs are plain L).**
If `U(M)` is finite then for every input `S`:

```
[[M]]^LA_D(S)  =  [[U(M)]](S)          (denotation of def:den),
```

as partial functions -- the machine yields `val w` iff the plain denotation of
`U(M)` on `S` is `w`, and it yields `err` iff that denotation is undefined
(eps-pattern at a live position, or undefined child).

*Proof.*  By Theorem 3 the machine halts on every input, so Theorem 2 applies
to every run.  Induct on the structure of the shared unfolding DAG.  For a
node holding constant `W` the machine returns `W`.  For an input variable
leaf the machine reads the input.  For a pass node `[R/P]E`: the three
children are evaluated (complete strictness) and by induction their values
are the plain denotations of the corresponding subtrees; the machine errs iff
some child errs or the pattern value is `eps`, exactly the undefinedness
condition of `def:den`, and otherwise returns `[r/p]e` by `def:subst`.  The
concatenation case is the same.  For a *call* node `g(D_1..D_m)` with live
arguments `D_i`: the machine creates thunks and evaluates `B_g` in their
environment; the unfolding places `U(D_i)` at each occurrence of `x_i`, and
its plain denotation equals the value the thunk computes (by induction on the
argument DAG), once; memoized re-forcings return the same value, matching
the repeated occurrences of the same subtree in the unshared tree.  Dead
arguments contribute nothing on either side (Theorem 1 and Proposition 3.3).
At the root this gives the claim.  QED

**Theorem 5 (Collapse: ill-founded programs are bottom everywhere).**
If `U(M)` is infinite, then `[[M]]^LA_D` is the everywhere-undefined partial
function; under the completely-strict presentation the machine diverges on
every input.

*Proof.*  A big-step derivation is a finite tree.  A value derivation of the
root must, by the induction of Theorem 2 (which needs only value outcomes:
every constructor child of a node producing a *value* was evaluated to a
*value*), visit every node of `U(M)` -- a value-producing pass node evaluated
all three children to values, a value-producing call evaluated the callee
body to a value, and live parameters occur at visited positions.  An infinite
tree cannot be visited by a finite derivation.  So no input yields a value.
Under complete strictness, an `err` derivation likewise requires all
constructor children evaluated, so no `err` derivation exists either: the
machine diverges.  (An early-exit order could still return `err` -- undefined
either way; see Section 8.5.)  QED

**Theorem 6 (Class equality: recursion is inert under lazy arguments).**
The partial functions denoted by lazy-args `L_rec` programs are exactly the
`L`-reachable partial functions (`def:reachable`):

```
{ [[M]]^LA_D : programs (D, M) }   =   { partial f : f reachable in L } .
```

Moreover each is computable in polynomial time, with degree bounded by a
function of the program (indeed of `U(M)`), so no lazy-args program computes,
e.g., `X |-> X^{2^{|X|}}`.

*Proof.*  (`<=`)  If `U(M)` is finite, `[[M]]^LA = [[U(M)]]` by Theorem 4,
and `U(M)` is a plain expression of `def:exp`, so the function is reachable;
if `U(M)` is infinite, the function is empty-domain, which is the restriction
of any `[[E]]` to the empty subdomain.  (`>`)  A call-free program is an
`L` program.  For the complexity clause: `U(M)` is a fixed finite expression,
so the paper's `Lemma length` and `Theorem thm:fp` apply to it verbatim; and
the machine's work is (number of DAG nodes) times (polynomial string work per
node) -- call-by-need evaluates each DAG node once, on strings bounded by
`Lemma length` applied to `U(M)`.  (The unfolding itself may be exponentially
larger than the program -- duplication of arguments -- but it is a *fixed*
finite object per program, as in the paper's per-expression statements.)
QED

**The connection to `Lemma beta` / `cor:closure`.**  `U(M)` is built by
iterated call expansion; a single expansion step replaces a call
`g(E_1, ..., E_m)` (dead arguments pruned) by `B_g[E_i/x_i]`, and `Lemma
beta` is precisely the statement that expression substitution commutes with
`[[.]]`.  When the live dependency graph is acyclic one can order the
expansions topologically, and each step turns the function into a composition
of the reachable functions `[[B_g]]` with the argument functions --
`cor:closure`'s closure shape.  Theorem 4 is the semantic content; the
fixpoint (Section 3) is what makes the pruning step sound.

---

## 7. Comparison with the eager (call-by-value) semantics

**Definition 7.1.**  The eager machine is Definition 2.1 with the (call) rule
replaced by: evaluate **all** argument expressions to values first (all of
them, always), then evaluate the callee body with parameters bound to the
values.

**Theorem 7 (eager = the `S_all` case).**  Theorems 1-6 hold verbatim for the
eager machine with `S*` replaced by `S_all` and `U(M)` by the full unfolding
of Definition 4.1/4.4.  In particular:

1. eager termination is input-independent and polynomial-time decidable;
2. the eager class is also exactly `L`'s partial functions -- *denotational
   equality of the two calculi*;
3. eager-halting implies lazy-halting (position-collapse, Proposition 4.4);
4. **Dead Irrelevance:** if both machines halt on an input, and the eager one
   yields a value, both yield the *same* value.  (If the eager machine yields
   a value, all positions of the full unfolding were evaluated to values, in
   particular the live ones, so the lazy machine halts and computes the same
   plain denotation `[[U(M)]]` of the live unfolding; dead positions cannot
   influence values, only definedness.)

The two machines differ operationally in exactly two ways, both exhibited in
Section 8:

* **strong separation:** eager diverges where lazy yields a value (the dead
  argument contains an infinite live-free regress);
* **weak separation:** eager errs where lazy yields a value (the dead
  argument has an eps-pattern; both machines halt).

---

## 8. Separations: smallest examples

Size = total node count (`Section 1`).  Search space for the exhaustive claims
(`search.py`, log `search_run.log`): Sigma = {a,b}; constants as atoms from
{'', 'a'} (any constant is one node; termination, liveness and acyclicity
depend only on structure, and the eps/non-eps distinction is the only
constant distinction that matters for value-vs-err); 1 or 2 functions with
arities in {0,1,2} (arity >= 3 cannot beat the minima below by node counting: a strong
separation needs, in `F`'s body, a call to `G` with at least one dead
argument carrying a call to `F` -- at least `1 + 1 + 1 = 3` nodes -- plus a
`G` body and a main; with all functions 0-ary that is the size-4 minimum, and
every arity >= 1 anywhere in a live slot adds at least the nodes of the
variables involved, giving >= 6 (constant denotation) resp. >= 7
(input-dependent), all exceeded by any arity-3 carrier: e.g. 0-ary `F` with
3-ary `G` needs `F() = G(c,c,F())` = 5 body nodes alone);
bodies arbitrary; main any expression containing >= 1 call node; programs
whose bodies contain no call at all are skipped when hunting divergence-based
separations (a reachable cycle needs a call in some body and a call in main).
A program **strongly separates** if the lazy machine yields a value on some
input and the eager machine yields a value on *no* input; **weakly** if both
halt and eager errs on some input where lazy yields a value.

**Lemma 8.1 (no 1-function strong separation).  [PROVED]**
If `D` has a single function `F`, then whenever the lazy machine halts, the
eager machine halts.  Hence no 1-function program strongly separates.

*Proof.*  First note the *minimal-depth* trick, used twice: in a one-function
program, a call to `F` of minimal depth in an expression is not inside any
call's argument (its enclosing call would be a call to `F` of smaller
depth), so it is reached from the expression's root through constructor
children only, and is therefore `S`-evaluated **for every** `S` -- in
particular for `S*`.

Case 1: `B_F` contains a call to `F` and `M` contains a call to `F`.
Let `c` be a minimal-depth call to `F` in `B_F`; by the trick it is an
`S*`-evaluated call position of `B_F`, hence a node of the live dependency
graph with a self-loop (callee edge to itself).  Let `c_0` be a
minimal-depth call to `F` in `M`; by the trick it is a root of the graph,
and its callee edge reaches `c`.  So a cycle is reachable: `U(M)` is
infinite and *the lazy machine diverges on every input* (Theorem 3).  So
"lazy halts" is false in this case.

Case 2: `B_F` contains a call to `F` but `M` does not.  Then no call is ever
started by either machine (`M` is the only entry, and with one function a
call-free `M` contains no calls at all): both machines just evaluate `M`.

Case 3: `B_F` contains no call to `F`.  Then the full unfolding is the
one-step expansion of `M` (main's calls to `F` expand once, and nothing
recurses), which is finite -- so the *eager* machine halts too (its own
Theorem 3), and a fortiori the lazy one; by Dead Irrelevance both yield the
same value, unless the eager one errs on a dead argument of a main call --
which is exactly the weak-separation escape hatch, not a strong one.

In every case where the lazy machine halts, the eager machine halts as
well.  QED

(Machine confirmation: 622 one-function programs of size <= 6 with calls in
body and main scanned -- 0 strong separations.)

**Theorem 8 (minimal separations).  [PROVED + VERIFIED]**

| class | smallest | program (size) | lazy | eager |
|---|---|---|---|---|
| strong, 0-ary allowed | 4 | `F() = G(F())`, `G(A) = 'a'`, main `F()` | `'a'` everywhere | diverges everywhere |
| strong, arity >= 1 | 6 | `F(X) = G(F(X))`, `G(A) = 'a'`, main `F(X)` | `'a'` everywhere | diverges everywhere |
| strong, input-dependent denotation | 7 | `G(A,B) = A`, `F(A) = F(A)`, main `G(X, F(X))` | identity | diverges everywhere |
| weak (no recursion needed) | 6 | `F(A) = 'a'`, main `F(['a'/'']'a')` | `'a'` everywhere | `err` everywhere |
| weak, data-dependent | 6 | `F(A) = 'a'`, main `F(['a'/X]'a')` | `'a'` everywhere | value iff `X != eps` |

All five were run on all inputs of length <= 4 (Section 9).  The conjecture's
own example `F(X) = G(X, F(tail X))`, `G(A,B) = A` (size 24 with `tail`
expanded) is the same shape as row 3 with `tail X` for `X` inside the dead
argument -- verified as well: lazy = identity, eager diverges.

*Exhaustive-search evidence for minimality* (2-function programs, arities in
{0,1,2}, constants {'', a}):

| total size | programs scanned | strong separations | weak separations |
|---|---|---|---|
| <= 3 | 31 | 0 | 0 |
| 4 | 55 | **4** | 0 |
| 5 | 1346 | 34 | 0 |
| 6 | 6533 | 144 | 0 |
| 7 | 60136 | 2441 | 64 |

Refinements (machine-checked): all 72 strong separations of size 6 with
`arity(F) >= 1` have *constant* denotation (a non-constant one needs the
input in a live slot of `F`'s body besides the dead recursive argument: at
least 7 nodes); of size 7, 84 of 1224 are input-dependent.  The weak class
does not need recursion at all, which is why its true minimum (6) sits below
the 2-function-with-body-call enumeration (7); the size-6 weak programs use
the *main* call as the dead-slot carrier, e.g. rows 4-5 of the table.

**Operational reading.**  Under lazy arguments, dead slots are free: the
programmer may write `G(X, F(tail X))` -- a guarded recursion shape -- but
the recursion is only ever *evaluated* if `G` uses its second argument;
otherwise the whole regress is skipped.  Under eager evaluation the same
program loops forever.  Denotationally both are `L`-reachable (Theorems 6
and 7.2): eager's function is empty-domain, lazy's is the identity.

---

## 8.5  Hand-off note: where operator-level non-strictness ("lazy passes")
## would break this argument

This report's semantics keeps `def:den` exactly: the pass `[R/P]E` evaluates
*all three* of `R`, `P`, `E`, even when `P` does not occur in the value of
`E` (and even when the scrutinee is `eps`).  The variant handled by the
`lazy_pass` agent instead makes the *operator* non-strict -- `[A/B]S = S`
when `B not subset S`, without evaluating `A` (the "for free" clause of
`def:subst`).  That is a different semantics, and every load-bearing step of
the present development is affected at an identifiable place:

1. **Forcing stops being syntactic (kills Conjecture 1).**  A replacement
   slot is a forcing position only *conditionally* -- the value of `R` is
   needed exactly when the pattern value occurs in the scrutinee value.  So
   the analogue of `Eval_S` (Definition 3.1) must make replacement positions
   data-dependent; there is no set of evaluated positions depending on `S`
   alone, hence no syntactic fixpoint `mu F`.  A sound *over*-approximation
   exists (declare all replacement slots evaluated): Theorem 1's
   confinement half survives in weakened form (never forced => not in the
   approximation), but Theorem 2 (Full Visitation) fails outright: in a
   halting run, a live parameter occurring only in replacement slots may
   never be forced.

2. **The live call tree becomes input-dependent (kills Conjecture 2).**
   Whether a call inside a replacement slot is ever started depends on
   whether the surrounding pattern occurs in the surrounding scrutinee -- a
   property of the data.  Concretely, over Sigma = {a,b}:
   `F(X) = [F(X)/b]X` terminates with value `X` exactly on the `b`-free
   inputs and diverges on every input containing `b`: termination is no
   longer all-or-nothing, and no analogue of the live dependency graph
   (Definition 4.2) can exist as a finite syntactic object.

3. **No single `E'` (kills Conjecture 3's proof, and possibly its
   statement).**  The unfolding of Definition 4.1 substitutes argument
   *expressions* into a fixed body; under lazy passes the body that is
   effectively evaluated depends on the data (which passes fire), so the
   program does not denote one plain expression.  Whether the resulting
   *class* still coincides with `L`'s partial functions is exactly the open
   question handed to the `lazy_pass` agent; the two candidate breakage
   points to attack are (i) a recursion that terminates on a data-dependent
   domain while computing something on it, and (ii) the interaction of the
   `eps`-pattern undefinedness with skipped replacements.  (For what it is
   worth: the example above still denotes an `L`-reachable partial function
   -- identity restricted to `b`-free strings -- so it does not separate.)

4. **Err-vs-divergence labeling.**  Under lazy passes the natural
   sequentialization *is* early-exiting at the replacement slot, so the
   "completely strict constructors" convention of Definition 2.1 loses its
   point; the all-or-nothing divergence dichotomy of Theorem 5 has no
   analogue.

5. **What is orthogonal.**  The two non-strictness axes are independent:
   lazy *arguments* (this report) makes call slots non-strict; lazy *passes*
   makes the replacement slot non-strict.  All results here are compatible
   with any evaluation order of the three pass children (Section 2, Remark 1)
   precisely because the pass itself stays strict.

---

## 9.  Verification (methodology of the paper: everything finite is checked)

Implementation: `lrec.py` (core: `sub` copied from
`research/scratch/paper_variants/verify_variants.py`, i.e. `def:subst`;
AST; liveness fixpoint by Kleene iteration; live/full dependency graphs with
reachability + cycle detection; live unfolding with runtime assertion of
Proposition 3.3; lazy machine with explicit `Thunk` objects, states
`susp/busy/val/err`, memoization and step budgets; eager machine; plain-`L`
evaluator on `sub`; the Section-2 toolkit `enc/dec/tail/head/eq/if` built as
expression trees over Sigma = {a,b} with `b = sigma_1 = 'a'`,
`x = sigma_2 = 'b'`).  Reproduce with `python3 checks.py` and
`python3 search.py 7 6`.

**(0) Toolkit sanity (the plain-`L` evaluator agrees with native string
operations).**  `enc/dec` round trip: all 255 strings of length <= 7.
`tail`, `head`: all 63 strings of length <= 5.  `eq`: 961 pairs of length
<= 4; `if` on both branches of each.  All pass.

**(a) Dead-argument examples (Section 8 table).**  For each of the seven
flagship programs (the conjecture's `F(X) = G(X, F(tail X))` example, its
`tail`-free version, the constant, zero-ary, mirror, mutual-recursion and
eager-error variants): `S*` computed, live unfolding `E'` built, and on all
31 inputs of length <= 4: lazy machine outcome == plain-`L` denotation of
`E'` (values *and* eps-undefinedness), eager machine diverges (or errs
everywhere, for the error class).  All pass; the dead-parameter assertion in
the unfolding never fired.

**(b) Input-independence of termination.**  Corpus: 12 curated programs
(recursive and non-recursive, live and dead divergences, eps-pattern cases)
plus 241 distinct random programs (1-3 functions, arities 0-2, bodies of
1-3 constructor depth, random constants).  For each program the syntactic
prediction (acyclic live dependency graph) was compared with the machine on
every input: arity 1 -> all 31 strings of length <= 4; arity 2 -> all 225
pairs of length <= 3.  Result: 253 programs, 13141 halting runs, **zero
mismatches**: every predicted-halting program halted on every input (the
largest step count of any of the 13141 halting runs was 60, against a
300,000-step budget), and every predicted-diverging program (82 of them,
8822 divergent runs in total) ran to its 4,000-step divergence budget on
every input.  Statistics: 171 lazy-halting (169 of them also eager-halting, 2
lazy-only), 82 lazy-diverging; 16 input-instances of the eager-err/lazy-value
weak separation.

**(c) Well-founded programs agree with the pruned plain-`L` expression.**
For every predicted-halting program of the corpus (171), the live unfolding
`E'` was built (no cap hits) and its `sub`-based plain-`L` denotation was
compared with the lazy machine on every input: **zero mismatches**, in both
directions (values equal; eps-undefinedness sets equal).

**(d) Liveness through chains.**  The two examples of Section 3 verified:
`S*` of the fixpoint-chain program is exactly `{(Q,1)}` (deadness of `(P,1)`
and `(M,1)` established only through the chain), and the dead-through-two-
call-levels program unfolds to `X` and terminates under lazy on all inputs
while eager diverges.  In addition, the machines were instrumented to record
every forced pair and every started call, on *every* run of the corpus
(halting and budget-stopped): **confinement held in all runs** (forced set
subseteq `S*`, including all 82 divergent runs) and **full visitation held
in all 13141 halting runs** (every live parameter of every started call was
forced).  No black hole state was ever reached.

**(e) Minimality of the separations.**  The exhaustive enumeration of
Section 8 (68,101 two-function programs of size <= 7 and 622 one-function
programs of size <= 6 scanned; log `search_run.log`): counts as in the table;
smallest strong separation total size 4 (4 programs), all winners re-verified
operationally (lazy value on sampled inputs, eager divergence, `E'` and
`S*` printed); smallest weak separation inside that space size 7, and the
true weak minimum (one function, dead slot in main, no recursion) size 6,
verified directly.

**(f) Eager/lazy agreement.**  On every input of every corpus program where
both machines halt: whenever eager yields a value, lazy yields the same
value (Dead Irrelevance confirmed); no input had lazy err while eager yields
a value.  The only disagreements are the 16 weak-separation input-instances
(eager err, lazy value), all caused by eps-patterns in dead arguments.

---

## 10.  Status ledger

**PROVED (full proofs above):**

1. Forcing is syntactic: liveness `S* = mu F` (Definitions 3.1-3.2,
   Proposition 3.3); a thunk is forced iff its parameter is live, *per
   started call, in halting runs* (Theorems 1-2); liveness is transitive
   through call chains by construction; decidable in polynomial time.
   Confidence: high.  [Conjecture 1 of the task: confirmed, with the
   refinement that in *divergent* runs only the "dead => never forced"
   direction holds, and that live pairs of calls never started are vacuous.]
2. Termination is input-independent and decidable: halts on all inputs iff
   the live unfolding is finite iff the reachable live dependency graph is
   acyclic (Theorem 3, Propositions 4.3-4.4).  Confidence: high.
   [Conjecture 2: confirmed.]
3. Well-founded programs denote `[[E']]` with `E'` the pruned-and-expanded
   plain-`L` expression (Theorem 4; the expansion is an iterated `Lemma
   beta` step, matching `cor:closure`); ill-founded programs denote bottom
   everywhere (Theorem 5); hence the lazy-args calculus denotes exactly
   `L`'s partial functions, all polynomial-time computable with
   expression-bounded degree (Theorem 6) -- recursion is inert.
   Confidence: high.  [Conjecture 3: confirmed.]
4. The eager semantics is the `S_all` case of the same theory: same class,
   eager-halting => lazy-halting, value agreement (Theorem 7).  Confidence:
   high.
5. No one-function program strongly separates (Lemma 8.1); the minimal
   separations are as in Theorem 8's table.  Confidence: high for the
   lemma; high for the minima within the stated search space (constants as
   atoms from {'', a}, arities <= 2; arities >= 3 and longer constants are
   argued away by node counting, not enumerated).
6. Call-by-need and call-by-name agree on termination and values (Section 2,
   Remark 3: both compute the same unfolding; by-name re-evaluates argument
   copies but a finite tree has finitely many occurrences).  Confidence:
   high; proof is a sketch but routine.

**VERIFIED (machine, domains stated in Section 9):** items 1-5 above on the
stated domains, in particular confinement and full visitation instrumented
on all 13141 halting runs and all divergent runs of the corpus; denotation
agreement with `E'` on all halting programs; input-independence on all
short inputs; the separation table operationally; the Section-2 toolkit
reimplemented from the paper against native string operations.

**CONJECTURAL / open (not needed for the conclusions, recorded for
completeness):**

* Exact complexity of the liveness fixpoint + acyclicity decision (here:
  naive Kleene `O(|D|^2)`-ish and DFS; a linear-time combined analysis may
  exist).  Low importance.
* Whether the minimal separating programs of Theorem 8 remain minimal under
  richer constants (argued yes by node counting: any constant is one node
  and no constant value can create or destroy a call cycle) -- an argument,
  not an enumeration.  Medium confidence.
* Handed off: the entire "lazy passes" axis (Section 8.5) -- data-dependent
  forcing, no syntactic liveness, no input-independent termination; whether
  that calculus still denotes exactly `L`'s partial functions is open and
  is the `lazy_pass` agent's problem.

**Bottom line.**  Under call-by-need with `def:den`-strict constructors,
first-order recursion over raw `L` is *inert*: every program is either
denotationally a plain pipeline (`E'`, computable by pruning dead call
subtrees -- the least-liveness fixpoint -- and expanding), or it diverges
everywhere; which case holds is decidable in polynomial time from the
program text; and the calculus reaches exactly `L`'s partial functions --
while still separating operationally from eager evaluation on programs as
small as four nodes.

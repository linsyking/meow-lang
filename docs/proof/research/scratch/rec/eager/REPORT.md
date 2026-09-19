# The Eager Recursive Calculus L_rec: Recursion Is Inert

Research report for "A Theory of String Substitution over Finite Alphabets"
(main.tex, Sections 2-4). Stage: first-order recursive definitions under EAGER
(call-by-value, all-strict) semantics. Files: `eager.py` (machinery),
`verify_eager.py` (verification suite; 31,995 checks, 0 failures).

**Verdict on the conjecture.**

* **(1) TRUE, with two refinements.** Every definition that lies on a
  call-graph cycle is undefined (bottom) on every input -- and so is every
  definition that *can reach* a cycle (a strictly larger class in general).
  But "diverges on every input" must be read as "never returns on every
  input": the failure is *error or divergence*, and which one occurs is
  evaluation-order-dependent (program P8 below is cyclic and always
  *errors*, never diverging). The proof is a two-line Kleene induction;
  Konig's lemma is not needed and, as sketched, has a gap (Section 4.3).
* **(2) FALSE as stated; true after a one-node patch.** Plain
  substitution-inlining via Lemma beta is *call-by-name-flavored*: when a
  callee ignores an argument, the substituted expression drops it, but the
  eager call node is strict in *all* its arguments. A concrete acyclic
  counterexample where naive inlining differs from the eager semantics is
  verified below (P10). The fix is a strict-sequence combinator built from
  one substitution node, `seq(F,G) := [F*sigma*/F*sigma*]G` (Section 3.3,
  Lemma 3) -- valid over every finite alphabet. With the patch, acyclic
  programs inline exactly.
* **(3) TRUE -- the knockout holds.** The eager recursive calculus denotes
  *exactly* the same partial functions as L (Theorem G). Recursion adds
  nothing under eager semantics.

Throughout: Sigma is a finite nonempty alphabet (the paper's standing
assumption for Sections 2-4 is |Sigma| >= 2; every construction below works
for |Sigma| >= 1, verified also over Sigma = {a}); [A/B] is Definition
def:subst ([A/eps] undefined); [[E]] is Definition def:den; Lemma beta is
the paper's Composition/beta lemma. I write bottom for "undefined" and, for
a partial function g, "g = bottom" for "g is the everywhere-undefined
(empty) function".

---

## 1. The calculus L_rec

**Syntax.** A *program* is a finite list of definitions
P = (f_1, ..., f_k), where f_j has arity m_j >= 0 and a *body*
B_j in ExpRec_{m_j}. ExpRec_m is the grammar of Definition def:exp
(variables X_1..X_m, constants W in Sigma*, the node [R/P]E, concatenation
E1E2) closed under one new construction:

    f_l(E_1, ..., E_q)      (q = m_l, arity-checked; no higher-order).

k = 0 is permitted (then ExpRec = Exp). The base primitive is raw L: no new
built-ins; Section 2 constructions appear only as inlined bodies.

**Undefinedness.** As in Section 3: [[R/P]E] is undefined when [[P]] = eps;
every constructor of Exp (and the call node, see 2.1) is *strict* in *all*
its sub-expressions.

**Call graph.** Edge j -> l iff B_j contains a call node f_l(.) (at any
syntactic depth). A *cycle* is a nonempty path j -> ... -> j. Define

    C := { j : some cycle is reachable from j }

(i.e. j lies on a cycle, or B_j contains a call to some l with l in C --
equivalently, C is the smallest set containing all cycle members and closed
under "calls a member"). For j not in C, D(j) := the length of the longest
call-edge path starting at j (D(j) = 0 if no callees); the region reachable
from j is a finite DAG (if a cycle were reachable, j would be in C), so
D(j) <= k-1. Both C and D are computable in linear time in the program size.

## 2. The denotational semantics: least fixed point

### 2.1 Interpretations and the rho-relative denotation

An *interpretation* is a tuple rho = (g_1,...,g_k) of partial functions
g_j : (Sigma*)^{m_j} -> Sigma* (partial). For E in ExpRec_m define
[[E]]_rho : (Sigma*)^m -> Sigma* by the clauses of Definition def:den plus
the call clause:

    [[f_l(E_1,...,E_q)]]_rho(S) = g_l([[E_1]]_rho(S), ..., [[E_q]]_rho(S))

-- *undefined if any [[E_i]]_rho(S) is undefined* (call-by-value: all
arguments are evaluated, used or not) or if g_l is undefined at the argument
tuple. All other clauses are as in def:den and strict: [[R/P]E]_rho is
undefined if any of [[R]]_rho, [[P]]_rho, [[E]]_rho is undefined or
[[P]]_rho = eps.

**The semantic functional.** Let D_j be the partial functions
(Sigma*)^{m_j} -> Sigma* ordered by graph inclusion (g ⊑ h iff dom g is a
subset of dom h and g = h on dom g); D := D_1 x ... x D_k. This is a cpo:
directed suprema are pointwise unions; bottom = (bottom,...,bottom). Define

    Phi : D -> D,   Phi(rho)_j := [[B_j]]_rho .

**Definition (denotation).** The denotation of program P is the *least fixed
point* of Phi. It exists because Phi is monotone (Lemma 1) and, being
continuous (Corollary 2), satisfies Kleene's theorem: lfp Phi is the supremum
of the chain phi^n where

    phi^0 := bottom,   phi^{n+1} := Phi(phi^n)   (i.e.
    phi^{n+1}_j(S) = [[B_j]]_{phi^n}(S)).

We write [[f_j]] := lfp_j and call phi^n_j the *n-th Kleene approximant*.

### 2.2 Monotonicity

**Lemma 1 (monotone agreement).** If rho ⊑ rho' then for every E in ExpRec
and S: [[E]]_rho(S) ⊑ [[E]]_{rho'}(S) (i.e. if the left side is defined,
both equal).

*Proof.* Induction on E. Variables and constants are interpretation-free.
For [R/P]E' and E1E2: if the rho-value is defined then the rho-values of all
immediate sub-expressions are defined, hence (IH, flatness) equal to the
rho'-values, so the same pass / concatenation applies. For a call node
f_l(E_1,...,E_q): if the rho-value is defined, all [[E_i]]_rho(S) are defined
and (IH) equal the rho'-values; and g_l(T) = v for the common tuple T, so
g'_l(T) = v by rho ⊑ rho' (agreement on dom g_l). □

### 2.3 Continuity

**Lemma 2 (finite queries).** If [[E]]_rho(S) = v then there is a finite set
Q of pairs (l, T) such that every rho' that agrees with rho on Q (same
value, including definedness, at each (l,T) in Q) satisfies
[[E]]_{rho'}(S) = v.

*Proof.* Induction on E. Variables/constants: Q is empty. For [R/P]E' and
E1E2: the union of the sub-expression query sets (each sub-value is
reproduced by rho' by IH, so the same pass/concatenation yields v). For a
call node: the argument query sets from the IHs force each
[[E_i]]_{rho'}(S) = [[E_i]]_rho(S) = u_i; add the single pair
(l, (u_1,...,u_q)) to force g'_l(u) = g_l(u) = v. □

**Corollary 2 (continuity).** Phi is continuous: for every directed set A
contained in D, Phi(sup A) = sup_{rho in A} Phi(rho).

*Proof.* The >= direction: Lemma 1, extended to directed sups. The <=
direction: if Phi(sup A)_j(S) = [[B_j]]_{sup A}(S) = v, Lemma 2 gives a
finite Q; each (l,T) in Q is answered by the union sup A at some
rho_{l,T} in A, and directedness gives rho_N above all of them; rho_N agrees
with sup A on Q, so Phi(rho_N)_j(S) = v. □

So Kleene's theorem applies and the denotation is *exactly* the union of the
graphs of the approximants: [[f_j]](S) = v iff phi^n_j(S) = v for some n.

**Remark (why the least fixpoint is load-bearing).** Fixpoints are far from
unique: for f(X) = f(X) the functional is the identity on the
f-component -- *every* interpretation is a fixpoint, including "identity".
The least one is bottom, and that is the one matching the operational
reading (Section 3) and the one intended by "eager". A greatest-fixpoint
semantics would behave completely differently.

## 3. The operational semantics and the seq combinator

### 3.1 Fuel-indexed eager evaluation

Fix a deterministic left-to-right order (the order affects only the
error/divergence split, never values or definedness -- Lemma 6). Define
O_n(E, T) in {Val(v), Err, Cut} for n >= 0 ("fuel" n) by structural
recursion:

* O_n(X_i, T) = Val(T_i); O_n(W, T) = Val(W).
* O_n([R/P]E, T): evaluate R, then P, then E, each by O_n(.,T); the first
  Cut stops everything with Cut, the first Err with Err; if all are
  Val(r), Val(p), Val(e) and p = eps the outcome is Err, else Val([r/p]e).
* O_n(E1E2, T): evaluate E1 then E2 as above; Val of the concatenation.
* O_n(f_l(E_1,...,E_q), T): evaluate the arguments in order; if all are
  Val(v_1),...,Val(v_q): if n = 0 the outcome is Cut, else O_{n-1}(B_l, v).
  (Entering a callee's body costs one fuel unit; arguments are evaluated at
  the current fuel.)

Run O_n(B_j, S) for n = 0,1,2,...

**Lemma 5 (stability).** If O_n(E,T) = Val(v) then O_{n+1}(E,T) =
Val(v); if O_n(E,T) = Err then O_{n+1}(E,T) = Err.

*Proof (routine, included).* Induction on n with an inner structural
induction. Val: all sub-evaluations that produced Vals produce the same
Vals at fuel n+1 (inner IH), and the eps-check is unchanged. Err: the
*first* anomaly in the fixed left-to-right order is reached again at fuel
n+1 (all earlier sub-evaluations were Vals at fuel n, hence Vals at n+1 by
IH) and is Err again by IH. Cut: no claim. □

So every (E, T) has a well-defined *limit outcome*: Val(v) ("Halt with
v"), Err, or Cut for all n ("Div"). Trichotomy holds by construction.

**Lemma 6 (order irrelevance for values).** For any two evaluation orders,
the set of inputs on which some O_n yields Val(v), and the value v, are the
same. Only the Err/Cut boundary can move.

*Proof (routine).* The value-producing recursive computations differ only
in sequencing; the conjunction "all sub-values defined" is
order-independent, and the composed value is the same associatively. □

### 3.2 Agreement of the two semantics

**Theorem A (denotational = operational).** For every j and S:
the limit outcome of (B_j, S) is Val(v) **iff** [[f_j]](S) = v; and the
limit outcome is Err or Div **iff** [[f_j]](S) = bottom. (The Err/Div split
is the order-dependent refinement of bottom.)

*Proof.* First the correspondence at finite fuel, by induction on n with an
inner structural induction on E:

    O_n(E, T) = Val(v)  iff  [[E]]_{phi^n}(T) = v,      and
    O_n(E, T) in {Err, Cut}  implies  [[E]]_{phi^n}(T) = bottom.

Variables/constants: both sides immediate. The pass and concatenation
clauses mirror the clauses of [[.]]_{phi^n} (the eps-check is the Err
condition; strictness is the first-anomaly rule; both sides undefined
together). The call clause: the arguments correspond by inner IH; if all
are defined with values v then O_n continues to O_{n-1}(B_l, v) when n >= 1,
which by the outer IH (on n-1) is Val(w) iff [[B_l]]_{phi^{n-1}}(v) = w --
i.e. iff phi^n_l(v) = w, which is exactly [[f_l(E)]]_{phi^n}(T); when n = 0
the outcome is Cut and phi^0_l = bottom. If some argument is Err/Cut then
[[E_i]]_{phi^n}(T) = bottom by inner IH and the call is bottom by
strictness. (The converse direction of the second line, and with it the
"only if" of the first, follows by contraposition: if [[E]]_{phi^n}(T) = v
then the argument evaluations must define all arguments and the recursion
shows Val(v).)

Now: if some O_n(B_j,S) = Val(v) then phi^n_j(S) = v, so [[f_j]](S) = v
(lfp is above phi^n, Lemma 1 applied to the chain). Conversely if
[[f_j]](S) = v then phi^n_j(S) = v for some n (Kleene: the lfp is the union
of the approximants' graphs), so O_n(B_j,S) = Val(v) and the limit is Val(v)
by Lemma 5. The bottom cases are the contrapositives. □

### 3.3 The strict-sequence combinator (the one new tool)

**Lemma 3 (seq).** Fix sigma in Sigma. For F, G in Exp_m define

    seq(F, G) := [F*sigma* / F*sigma*] G     (F*sigma* is the expression
                                              F followed by the character
                                              sigma).

Then for all S: [[seq(F,G)]](S) = [[G]](S) if [[F]](S) is defined, and
bottom otherwise. (One node; no alphabet restriction; works for
|Sigma| = 1.)

*Proof.* The node [R/P]E with R = P = F*sigma* evaluates R, P, E strictly.
If [[F]](S) = bottom then [[R]](S) = bottom (concatenation is strict in its
first argument), so the node is bottom. If [[F]](S) = u then the pattern
value is u*sigma*, which is nonempty (it ends with the character sigma); by
the paper's Identity Substitution theorem ([A/A]S = S for A != eps) the
pass is the identity, and strictness in E gives the value [[G]](S) (bottom
if G is bottom). □

So "evaluate F, discard, then G" is L-expressible by a single substitution
node. (I first used the heavier if(eq(F,F),G,w) -- requiring |Sigma| >= 2 --
before noticing that [F*sigma*/F*sigma*] does the job over any alphabet.)

**Lemma 4 (force).** Let U in Exp_q be call-free and let F_1,...,F_q be in
Exp_m. Let Used(U) be the set of indices of variables occurring in U and
define

    force(U, F) := seq-wrapping of U[F_1/X_1,...,F_q/X_q], one wrap
    seq(F_i, .) for each i not in Used(U)   (in any order).

Then [[force(U,F)]](S) = [[U]]([[F_1]](S),...,[[F_q]](S)) in the strict
sense: defined with value [[U]](u) iff every [[F_i]](S) is defined (u the
tuple of values), and bottom otherwise -- *independently of whether U uses
its arguments*.

*Proof.* If every [[F_i]](S) = u_i: each wrap is the identity by Lemma 3
(its F is defined), so the value is [[U[F/X]]](S); by Lemma beta' below this
is [[U]](u). If some [[F_i]](S) = bottom: if i not in Used(U), the outer
wrap seq(F_i, .) is bottom by Lemma 3; if i in Used(U), then U[F/X] is
bottom because the sub-expression F_i occurs (Lemma beta'), and any
remaining wraps either propagate bottom (Lemma 3) or pass it through
(strictness). □

**Lemma beta' (occurrence-sensitive substitution).** Let E in Exp_q and
F_1,...,F_q in Exp_m. Extend [[E]] to bottom-arguments by reading variables
through the flat order (a variable leaf reading bottom makes the whole
bottom; constants are total). Then for all S in (Sigma*)^m:

    [[E[F_1/X_1,...,F_q/X_q]]](S) = [[E]]([[F_1]](S),...,[[F_q]](S)),

both sides being undefined together. In particular the substituted
expression is bottom at S iff some [[F_i]](S) = bottom *with X_i occurring
in E*, or the ordinary evaluation of E at the defined completion is
undefined.

*Proof.* Induction on E, sharpening the paper's proof of Lemma beta by
making its undefinedness clause explicit. Variable: X_i[F/X] = F_i, and
[[X_i]](bottom at i) = bottom. Constant: both sides W. Concatenation and
the pass: strictness on both sides composes with the IH; the eps-check
[[P[F]]](S) = eps corresponds to [[P]](u) = eps (bottom is not eps). □

**Remark -- the paper's Lemma beta is call-by-name-flavored.** Lemma beta'
makes precise that *expression substitution evaluates an argument only
where it occurs*. This is exactly where the user's conjecture (2) has a
gap, and it is a genuinely eager-vs-lazy distinction:

* The paper's **cor:closure** survives, because Definition def:reachable
  declares a *partial* function reachable when it is a *restriction* of
  some [[E]]: the strict composite of reachable g, h_i equals the
  denotation of E_g[E_{h_i}/X] restricted to {S : all h_i(S) defined} -- a
  subdomain. So the corollary is true as stated, with this reading.
* But the **exact** (unrestricted) strict composite needs Lemma 4: the
  witness is force(E_g, [E_h]), not E_g[E_h/X]. If the paper ever wants
  cor:closure without the restriction clause (moot for total functions,
  but not for partial ones), this is the one-line fix. Counterexample to
  the naive version (verified, P10): g(Y) = 'q' (constant body),
  h(X) = [b/X]X (bottom exactly at X = eps); the strict composite is bottom
  at eps, while the substituted expression is defined at eps.

## 4. Core theorems

### 4.1 Unfolding: every approximant is L-reachable

Define Omega_m := [a/eps]w in Exp_m for any fixed a in Sigma and w in Sigma*
(for m = 0 take w = 'c'): [[Omega_m]] = bottom, the empty partial
function. Define syntactic unfolding by induction on n:

* unfold_0(f_j) := Omega_{m_j};
* Unfold_{n+1} recurses structurally through variables, constants, [R/P]E
  (all three positions) and E1E2, and replaces each call node
  f_l(E_1,...,E_q) by **force**(unfold_n(f_l), Unfold_{n+1}(E_1), ...,
  Unfold_{n+1}(E_q));
* unfold_{n+1}(f_j) := Unfold_{n+1}(B_j).

Every unfold_n(f_j) is a call-free expression of Exp_{m_j} -- a plain L
expression.

**Theorem B (unfolding).** For all n, j, S:
phi^n_j(S) = [[unfold_n(f_j)]](S), both sides undefined together. In
particular every Kleene approximant is L-reachable.

*Proof.* Induction on n with an inner structural induction on E in
ExpRec_m proving [[Unfold_{n+1}(E)]](S) = [[E]]_{phi^n}(S). All cases but
the call are immediate from the inner IH. The call node
f_l(E_1,...,E_q): by the outer IH [[unfold_n(f_l)]] = phi^n_l as partial
functions; by the inner IH [[Unfold_{n+1}(E_i)]](S) = [[E_i]]_{phi^n}(S) =
u_i; by Lemma 4
[[force(unfold_n(f_l), Unfold_{n+1}(E))]](S) equals phi^n_l(u) when all u_i
are defined and bottom otherwise -- which is exactly the rho-relative
semantics [[f_l(E)]]_{phi^n}(S). □

(Note that without the force-wraps this theorem is *false* -- that is
exactly the P10 counterexample class; the suite cross-checks phi^n against
[[unfold_n]] for every n, and this is how the gap was found.)

### 4.2 Vacuity

**Theorem C (vacuity).** If j is in C (i.e. j lies on a cycle, or calls --
directly or transitively -- a definition that does), then [[f_j]] = bottom:
undefined on *every* input. In fact phi^n_j = bottom for every n >= 0.

*Proof.* First the auxiliary claim: j in C implies B_j contains a call node
to some l in C. If j lies on a cycle, the next node l of that cycle is a
callee and is itself in C. Otherwise j reaches a cycle by a path of length
>= 1 whose first edge j -> l is realized by a call node of B_j, and l still
reaches the cycle, so l is in C.

Now induction on n. phi^0 = bottom everywhere. Assume phi^n_j = bottom for
all j in C, and let j be in C, S arbitrary. Choose a call node
c = f_l(E_1,...,E_q) in B_j with l in C. Its value under phi^n is
phi^n_l([[E]]_{phi^n}(S)) = bottom -- regardless of whether the arguments
are defined, because phi^n_l is *everywhere* undefined. Since every
constructor of ExpRec is strict in every sub-expression, bottom at c
propagates: [[B_j]]_{phi^n}(S) = bottom. Hence phi^{n+1}_j = bottom.
Taking the union, [[f_j]] = bottom. □

**Corollary C.1 (never returns).** By Theorem A, for j in C the limit
outcome of every input is Err or Div -- the program never halts on any
input. Both modes occur: f(X) = f(X) always Divs; P8 below always Errs.

**Corollary C.2 (dead arguments confirm).** Eager evaluation evaluates
*all* arguments of every call node, used or not (the call clause of 2.1): a
cycle reachable only through an argument the callee ignores still kills the
caller (P3: F(X) = cat(G(H(X)), 'c') with G(Y) = 'q' and H(X) = H(X) gives
[[F]] = bottom although G ignores its argument). This is the exact dual of
the Lemma-beta gap of 3.3: strictness is what makes vacuity airtight, and it
is also what makes naive inlining insufficient.

### 4.3 The Konig's-lemma discussion (the proof sketch, repaired)

The conjecture's sketch was: the call tree is syntax-determined; a cycle
makes it infinite; Konig gives an infinite path; strictness propagates
bottom to the root. Two steps need repair, neither fatal:

1. **"Syntax-determined" is false as stated.** A child of a node exists
   only if the call node's *arguments evaluate to defined values* -- a
   data-dependent condition whose truth is part of what the argument
   establishes; and under a fixed evaluation order an *error in a sibling
   sub-expression preempts the exploration*, so the tree of *performed*
   entries can be finite even on a cycle (P8: f(X) = cat([a/eps]X, f(X))
   always errs before ever touching f). The corrected object is the
   *entry tree*: nodes are the body instances (f_l, T) entered during the
   fuel-n evaluations, ordered by the fuel-n traces; its limit is a
   well-defined finitely-branching tree.
2. **Konig is not needed for vacuity** -- the induction of Theorem C is
   strictly simpler and immune to both issues, because it never has to
   construct the tree. Where Konig (or rather pigeonhole on the *finite*
   call graph) genuinely lives is the *converse* direction:

**Theorem D (divergence locus).** (i) If j is not in C then no input Divs:
the limit outcome is always Val or Err. Indeed O_n(B_j, S) is never Cut for
n >= D(j). (ii) Conversely, Div on any input implies j is in C.

*Proof.* (i) Say an expression E has call-depth d(E) := 0 if it contains no
call node, else max over call nodes f_l(.) in E of 1 + d(B_l) (where
d(B_l) = D(l): paths from l). Claim: for all E, T, n with d(E) <= n,
O_n(E,T) is never Cut. Induction on n with structural inner induction. A
call node f_l(E) with d = 1 + d(B_l) <= n: its arguments satisfy d(E_i) <=
d <= n (their call nodes are among E's), so by inner IH none of the
argument evaluations Cuts; then the body is evaluated at fuel n-1 and
d(B_l) = d - 1 <= n - 1, so by outer IH (on n-1) it does not Cut. Since
j not in C makes the region below j a DAG, d(B_j) = D(j), so fuel n = D(j)
never Cuts -- and a never-Cut limit is Val or Err. (ii) Suppose the limit
is Div. Let Entry_n be the set of body instances entered by the fuel-n
evaluation. Stability (Lemma 5) makes the traces monotone: Entry_n is
contained in Entry_{n+1}. If Entry_inf := the union of the Entry_n were
finite, the evaluation structure would be a finite tree in which each body
instance fires each of its finitely many call nodes at most once (the
evaluator is structural and evaluate-once), so for n larger than the
maximal entry depth nothing is ever Cut and the outcome is Val or Err --
contradiction. So Entry_inf is an infinite, finitely-branching tree, and by
Konig's lemma it has an infinite branch j -> l_1 -> l_2 -> ... of entered
definitions -- an infinite walk in the finite call graph, which by
pigeonhole revisits some node: a cycle is reachable from j, i.e. j is in
C. □

So the true picture is a perfect dual pair: **C = exactly the definitions
that can never return; non-C = exactly those that can never diverge.** An
infinite call tree can never return a value (Theorems A + C): strictness
forbids it, and the fixpoint and operational readings agree.

### 4.4 Inlining: acyclic programs are plain L

Define the complete inlining for j not in C by well-founded recursion on
the DAG (topological order; callees first): Inline recurses structurally
through B_j and replaces each call node f_l(E_1,...,E_q) by
**force**(E^inf_l, Inline(E_1), ..., Inline(E_q)). Set

    E^inf_j := Inline(B_j)   for j not in C,   E^inf_j := Omega_{m_j}
    for j in C,

and rho^inf := ([[E^inf_j]])_j.

**Theorem E (inlining).** rho^inf is *the* least fixed point:
Phi(rho^inf) = rho^inf and lfp = rho^inf. Hence for j not in C:
[[f_j]] = [[E^inf_j]] exactly (a plain L expression), and for j in C:
[[f_j]] = [[Omega]] = bottom (re-proving Theorem C denotationally).

*Proof.* **rho^inf is a fixpoint.** Let j be in C. By the auxiliary claim of
Theorem C, B_j contains a call node to some l in C, whose value under
rho^inf is rho^inf_l(.) = bottom; strictness gives [[B_j]]_{rho^inf} =
bottom = rho^inf_j. Let j not be in C: every call node in B_j targets a
definition l not in C (else j would be in C), so with U := E^inf_l and
F_i := Inline(E_i), structural induction on B_j (using Lemma 4 for the call
case and Lemma beta' for the others, exactly as in Theorem B's proof but
with rho^inf in place of phi^n) gives [[Inline(B_j)]](S) =
[[B_j]]_{rho^inf}(S). So Phi(rho^inf)_j = rho^inf_j.

**lfp is below rho^inf.** phi^0 = bottom ⊑ rho^inf, and
phi^{n+1} = Phi(phi^n) ⊑ Phi(rho^inf) = rho^inf by Lemma 1; hence the
supremum of the phi^n is below rho^inf.

**rho^inf is below lfp.** For j in C there is nothing to prove (rho^inf_j =
bottom). For j not in C, let psi^n := the interpretation that agrees with
rho^inf on {l not in C : D(l) < n} and is bottom elsewhere. Claim: psi^n ⊑
lfp for all n. psi^0 = bottom. For the step it suffices to show psi^{n+1} ⊑
Phi(psi^n), since then psi^{n+1} ⊑ Phi(psi^n) ⊑ Phi(lfp) = lfp by Lemma 1
(and lfp is a fixpoint by continuity: Phi(sup phi^n) = sup Phi(phi^n) =
sup_{n>=1} phi^n = lfp). If D(j) >= n or j is in C then psi^{n+1}_j =
bottom. If j not in C and D(j) <= n: every callee l of j has
D(l) <= D(j)-1 <= n-1 < n, so psi^n and rho^inf agree on every definition
queried while evaluating B_j (only callees are queried); hence
[[B_j]]_{psi^n} = [[B_j]]_{rho^inf} = [[E^inf_j]] = psi^{n+1}_j. Finally
take n = D(j)+1: psi^n_j = [[E^inf_j]] ⊑ lfp_j. □

**Theorem F (quantitative stabilization).** The Kleene chain stabilizes at

    K := max(1, max_{j not in C} (D(j)+1))   (<= k),

i.e. phi^n = lfp for all n >= K; on C, phi^n = bottom for all n >= 0
already.

*Proof.* On C this is Theorem C. For j not in C, strengthen Theorem B's
statement to sub-expressions: for E in ExpRec whose call nodes all target
definitions outside C, put d(E) := 0 if E has no call node, else
1 + max D(l) over the targets l. Claim: for all n >= d(E),
[[Unfold_n(E)]] = [[E]]_{rho^inf}. Induction on d(E) with structural inner
induction. The call node case: Unfold_n(f_l(E)) =
force(unfold_{n-1}(f_l), Unfold_n(E)); here d(E) >= 1 + D(l) so
n - 1 >= D(l) = d(B_l), and the outer IH on the callee (whose d(B_l) =
D(l) < d(E)) gives [[unfold_{n-1}(f_l)]] = rho^inf_l; the inner IH
(d(E_i) <= d(E) <= n) gives the arguments; Lemma 4 and Lemma beta'
assemble [[E]]_{rho^inf}. Since d(B_j) = D(j), taking n >= D(j)+1 gives
phi^n_j = [[unfold_n(f_j)]] = [[B_j]]_{rho^inf} = [[E^inf_j]] = lfp_j. □

### 4.5 The main theorem

**Theorem G (recursion is inert under eager semantics).** Over any finite
nonempty alphabet Sigma: for every program P and every definition f_j,

    [[f_j]] = [[E^inf_j]]    with E^inf_j in Exp_{m_j} a plain L expression
                             (E^inf_j = Omega = [a/eps]w if j is in C; the
                             inlining otherwise).

Consequently the eager recursive calculus L_rec denotes *exactly* the
partial functions denoted by L itself: **L_rec = L**. The
everywhere-undefined function was already L-definable ([[a/eps]X_1]);
every other L_rec denotation is an inlining of acyclic calls.

*Proof.* Immediate from Theorems C and E: the two cases cover every j, and
both right-hand sides are L expressions of the right arity. Conversely
L is contained in L_rec: given E in Exp_n, the one-definition program with
body E satisfies Phi(rho)_1 = [[E]] for every rho (no call nodes), so
lfp_1 = [[E]]. □

**Remarks.**

* **What survives of Section 3 verbatim.** Since every L_rec denotation is
  an L denotation, the entire theory of Sections 3-4 applies unchanged:
  Safe implies total, pipeline normal form, the polynomial-time bound
  (Theorem thm:fp), the growth hierarchy. One can even read a *safety*
  condition off the program: j not in C and the inlining (or the bodies)
  safe implies [[f_j]] total.
* **Cost.** The inlining can blow up exponentially in the call-depth (each
  call edge duplicates the callee's body; force adds a factor per unused
  argument; seq duplicates F once). This is irrelevant for expressiveness
  but means the *naive eager interpreter* can be exponentially slower than
  the polynomial-time bound of the function it computes; memoization (as
  in the Kleene evaluator of `eager.py`) removes the recomputation. Note
  that for j in C the interpreter never halts, matching bottom.
* **Decidability.** "Does f_j fail on *all* inputs" is decidable (j in C, a
  linear-time graph property -- Theorems C/D give both inclusions, so the
  notions coincide). Whether a *given* input halts is decidable by
  evaluating the finite inlining. Totality of [[f_j]] (j not in C) reduces
  to totality of the inlined L expression -- the paper's Safe analysis
  applies; the general question inherits the open status of the
  L-equivalence questions.
* **What would break inertness.** Exactly the two escape hatches not
  available here: (i) *non-strict* positions -- lazy arguments (a call node
  that skips evaluating an unused argument would already let
  f(X) = if(eq(X,eps), a, f(tail X)) terminate on every input, by Lemma
  beta'!), or lazy passes ([R/P]E not evaluating E when P does not occur in
  E); (ii) a coinductive / greatest-fixpoint reading (streams). These are
  the sibling research threads (lazy_args, lazy_pass, streams); the eager
  case is the baseline they must beat, and the bar is: *any* departure from
  bottom-on-C or from L-equality is a genuine semantic change.
* **Edge cases, explicitly.** (a) *Partial bodies* (data-dependent bottom
  via empty patterns): carried throughout by the "undefined together"
  clauses of Lemmas beta'/4; tested by P4, P7, P10 and the random
  batteries. (b) *n = 0*: zero-arity definitions are uniform in the theory
  (Omega_0 = [a/eps]'c'; the single 0-tuple input) -- tested by P5, P5b;
  empty programs (k = 0) make L_rec = L by definition. (c) *f(X) = f(X)*:
  Theorem C with a length-1 cycle; note every interpretation is a fixpoint
  here, so the *least*-fixpoint stipulation is load-bearing (the remark in
  2.2). (d) *Mutual cycles f -> g -> f*: Theorem C (any cycle length) --
  tested by P4. (e) *Dead arguments*: confirmed strict -- Corollary C.2,
  tested by P3 (cyclic) and P10 (acyclic, where it is the only difference
  between eager and naive inlining). (f) *Infinite call tree returning a
  value*: impossible -- Theorems A + C/D; the fixpoint and operational
  readings agree on everything, with only the Err/Div split
  order-dependent.

## 5. The interpreter and its results

`eager.py` implements three *independent* computations of the semantics,
which the theorems prove must agree:

1. **Kleene approximants** phi^n_j (memoized, denotational, order-free);
2. **Unbounded eager operational runs** (left-to-right, fuel-capped):
   outcomes Halt(v) / Err (empty pattern) / Cut (fuel exhausted, presumed
   Div);
3. **Syntactic unfolding/inlining to plain L** (call-free), evaluated by a
   pure-L evaluator.

The pass [A/B] is `subst(A,B,C)` imported from
`research/scratch/paper_variants/verify_variants.py` (the brief's `sub`).
The Section-2 toolkit (cat, tail, head, eq, if) is inlined as raw
expression trees exactly per the paper's formulas (Theorems thm:cat,
thm:headtail, Equality, Selection), so test bodies use no built-ins.
Section A of the suite first re-verifies those builders against Python
reference semantics (846 checks).

**Suite** (`verify_eager.py`, 31,995 checks, 0 failures, about 2 s):

* **A.** Toolkit builders: cat/tail/head on all strings over {a,b} of
  length <= 4; eq/if on all pairs/triples of length <= 2 with both selector
  values. 846 checks.
* **B/C. Hand-written programs** (each run through the full battery below):

  | program | C | kleene bound K | stab | run outcomes (all inputs) |
  |---|---|---|---|---|
  | P1 F(X)=cat(F(tail X),X) | {F} | 1 | 0 | cut on all 7 (diverges) |
  | P2 G(X)=cat(X,tail X); H(X)=G(cat(X,b)) | none | 2 | 2 | halt on all 14 |
  | P3 G(Y)='q'; H(X)=H(X); F(X)=cat(G(H(X)),'c') | {H,F} | 1 | 1 | G halts; H,F cut (dead argument) |
  | P4 f(X)=cat(g(X),X); g(X)=[X/X]f(X) | {f,g} | 1 | 0 | cut on all 14 (mutual partial cycle) |
  | P5 g()='b'; f()=cat(g(),'a') | none | 2 | 2 | halt; f() = 'ba' |
  | P5b z()=z() | {z} | 1 | 0 | cut (zero-ary cycle) |
  | P6 G(X)=if(eq(X,eps),'a',G(tail X)) | {G} | 1 | 0 | cut on all 7 |
  | P7 F(X)=[b/X]X; G(X)=cat(F(X),tail X) | none | 2 | 2 | halt 12, err 2 (exactly X=eps) |
  | P8 f(X)=cat([a/eps]X,f(X)) | {f} | 1 | 0 | err on all 7 (error preemption) |
  | P10 d0(X)=[b/d1(d2(X))]X; d1(Y)='q'; d2(X)=[b/X]X | none | 2 | 2 | halt 19, err 2 |

  P10's two errors are d0(eps) and d2(eps) -- the eager dead-argument
  undefinedness -- while the *naive* Lemma-beta inlining of d0 is defined at
  eps (the gap, verified explicitly); the seq-patched inlining is undefined
  at eps and agrees with the eager semantics everywhere.

* **The battery** (run for every program, every definition, every input):
  (i) Theorem B: phi^n_j = [[unfold_n(f_j)]] for n = 0..3; (ii)
  stabilization index <= K (observed: stab = 0 for all-C programs -- the
  chain is bottom from n = 0 -- and stab = D(j)+1 for the acyclic ones,
  exactly the bound); (iii) j in C: phi^n = bottom at *every* n, inlined
  (Omega) undefined, runs never halt; (iv) j not in C: inlined denotation
  = phi^K, runs never Cut at fuel D(j)+2, halt value = phi value, err iff
  phi = bottom; (v) fuel-irrelevance of outcomes; (vi) Cut observed only
  for j in C.
* **D. Randomized programs** (300 over Sigma = {a,b}, mixed DAG/cyclic call
  graphs, arities 0-2, bodies of depth <= 3 with constant and variable
  patterns, including always-bottom and data-dependent-bottom patterns;
  inputs: all strings of length <= 1 per argument): 71/300 have nonempty C;
  69 exhibit Cut; 304 (j, input) Cut events -- all inside C. All battery
  checks pass.
* **E. Randomized unary programs** (150 over Sigma = {a}): all battery
  checks pass (43/150 with nonempty C) -- confirming that Omega,
  seq = [F*sigma*/F*sigma*]G, and the inlining need no second character.
* **P11.** The seq combinator itself: [[seq(X_1,X_2)]](f,g) = g for all 27
  pairs; [[seq(Omega, G)]] = bottom.

**Methodological note.** The suite is what found the two real subtleties:
the phi-level bug (an off-by-one that made the "Kleene" chain cut cycles by
memoization instead of by depth -- caught by the unfold cross-check) and,
after that fix, the dead-argument gap (unfold/inline vs phi disagreement on
random programs -- the mathematical content of 3.3). Cross-checking
independent implementations of the same theorem remains the paper's best
friend.

## 6. Status

**PROVED** (full proofs above, pen-and-paper; the constructions were
verified on finite domains):

* Theorem A -- denotational lfp = operational eager evaluation (values,
  definedness, trichotomy; Err/Div split order-dependent).
* Theorem B -- unfolding: every Kleene approximant is L-reachable (with the
  force patch).
* Theorem C -- vacuity: j in C implies [[f_j]] = bottom everywhere; a
  fortiori every cycle member. Includes the refinement (C strictly
  contains the cycle members in general) and the never-returns
  (Err-or-Div) operational reading.
* Theorem D -- divergence locus: Div implies j in C; j not in C implies
  never Div (fuel bound D(j)). [Part (ii) uses Konig's lemma on the entry
  tree plus pigeonhole on the finite call graph -- both elementary; the
  proof is complete but phrased at the level of an operational trace
  rather than a formal abstract machine, since Lemma 5/6's routine
  inductions are included but compact.]
* Theorem E -- inlining: acyclic programs denote exactly their
  (seq-patched) L inlining.
* Theorem F -- quantitative stabilization by K <= k.
* Theorem G -- **L_rec = L exactly, over every finite alphabet**;
  recursion is inert under eager semantics.
* Lemmas 1-6 (monotone agreement, finite queries/continuity, seq, force,
  beta', stability/order-irrelevance).

**VERIFIED COMPUTATIONALLY** (31,995 checks, 0 failures): agreement of the
three semantics on all hand-written programs and 450 random programs
(binary + unary) over all test inputs; vacuity (bottom at every
approximant, never halts) exactly on C and only there; no divergence
outside C; stabilization by the predicted bound; the acyclic-inlining
equality; the naive-inlining counterexample P10; the seq combinator; the
Section-2 toolkit builders used to write the test bodies.

**CONJECTURAL**: nothing needed for the main theorem. Two side
observations flagged for the paper, both minor: (1) the
cor:closure/def:reachable reading of 3.3 (the restriction clause is what
absorbs the strict-vs-naive composition difference -- worth a remark in the
paper if partial functions are ever composed); (2) the naive reading of the
user's conjecture (2) ("use Lemma beta") is false as stated -- the
corrected statement needs force/seq -- which should be folded into any
write-up of this stage.

**Confidence: high.** The proofs are short and each step is elementary; the
two places where the conjecture needed repair were found and closed, and
the interpreter agrees with the repaired theory on every test. The single
step I would still call "routine but not fully formalized" is the
trace-level phrasing of Theorem D(ii); everything else is proved in full.

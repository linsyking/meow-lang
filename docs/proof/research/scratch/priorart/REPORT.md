# Prior-art / novelty check — meow §6 "Recursive Definitions"

Paper: /home/cc/projects/meow-lang/docs/proof/main.tex
Date started: 2026-09-21. Rounds logged at bottom.

## Claims whose novelty is being checked

Primitive: single pass [A/B]S — one left-to-right sweep over S, replace every
occurrence of fixed string B by A, leftmost first, no overlaps, never rescan
inserted text; [A/eps] undefined. Patterns/replacements may come from variables
(computed from input), but each pass is a single sweep over plain strings.

- C1 Universality (Thm 6.4 / thm:universal): + named recursive definitions
  + call nodes under "lazy passes" (call-by-need args AND replacement of
  [R/P]E forced only when P occurs in value of E) = exactly the partial
  computable functions (Sigma*)^n -> Sigma*, any |Sigma| >= 2. Self-recursion
  suffices. Proof via Minsky 2-counter machines, "pattern-gated while loop"
  RUN(c) = sel(eq(PC(c),eps), out(c), RUN(step(c))).
- C2 Inertness (Thms 6.1/6.2 = thm:eager, thm:lazyargs): SAME recursion
  under eager (CBV) or lazy-arguments-only (CBNeed args, strict constructors)
  adds NOTHING: every recursive def either inlines to recursion-free
  expression or never returns; those runtimes denote exactly L (the
  call-free class).
- C3 Conservativity (prop:lpcons) + two-way gate (def:gate, thm:gate) +
  boundary = replacement slot's non-strictness (operator equation
  [A/B]S = S when B not in S regardless of A, as the recursion guard).

## Key structural facts for comparison

- The calculus WITHOUT recursion (L) computes only poly-time functions
  (bounded pipelines). Recursion + lazy passes jumps to partial computable.
  The interest: ONE non-strictness rule in the pass operator is the exact
  pivot between "nothing new" and "everything".
- Inertness = first-order string language whose only constructor (the pass)
  is strict in pattern+scrutinee, non-strict in replacement.
- Related Work cites ONLY: semi-Thue + one-rule termination, post47, markov54,
  minsky67, transductions, codes, pattern matching, combinatorics on words.
  NOTHING about macro processors, esolangs, lazy-evaluation literature,
  streaming transducers.

## Checklist (verify online; every entry needs a fetched URL)

### A. C preprocessor
- [ ] cpp computational power: demonstrations (BF interpreters, primes)
- [ ] Boost.Preprocessor recursion, "blue paint" trick
- [ ] Any PROOF of cpp's power vs demonstrations
- [ ] cpp semantics vs our lazy-pass rule (token-level, fixed token seqs,
      call-by-name-ish, no self-reference, expansion depth limit)

### B. Other macro/replacement systems
- [ ] m4 (proof or demo)
- [ ] TeX/LaTeX macro expansion
- [ ] Rust macro_rules!
- [ ] C++ templates (Veldhuizen 1995 + successors)
- [ ] Nix, Template Haskell

### C. String-rewriting esolangs / systems
- [ ] esolang /// (slashes): only op is string substitution; TC proof?
      under what evaluation?
- [ ] Thue
- [ ] Retina
- [ ] sed TC (best ref/demonstration)
- [ ] awk/perl folklore

### D. Classical theory near exact statement
- [ ] Markov normal algorithms (markov54 cited; verify fairness)
- [ ] Post canonical/tag systems (2-tag universality)
- [ ] semi-Thue sim of TMs
- [ ] Term rewriting lazy/needed strategies (Huet-Levy, call-by-need)
- [ ] "substitution-only"/"single-pass" models
- [ ] streaming string transducers + recursion = partial computable?

### E. Exact-match hunting
- [ ] "search and replace Turing complete" / "find and replace computability"
- [ ] "string substitution recursion Turing complete"
- [ ] "macro expansion lazy evaluation completeness"
- [ ] "single pass string rewriting power" / "single-pass substitution"
- [ ] "greedy leftmost replacement computability"
- [ ] "call by need string rewriting"
- [ ] "substitution calculus universality"
- [ ] "meow language string substitution" (collision check)
- [ ] "computational power of macro processors"
- [ ] "macro languages Turing complete"
- [ ] "text substitution programming language completeness"

## Verification log

(empty — filling per round)

## Round 1 (2026-09-21)
- Read §6 (1393–1596), Related Work (71–79), def:subst (110–121),
  def:exp/def:den (659–683), references.bib. Understood all four runtimes.
- Next: first broad sweep of searches (A/B/C/D/E).

---

## Round 1 findings (2026-09-21) — broad sweep

Verified entries (URL fetched or to-fetch marked):

1. **C preprocessor** — "Is the C Preprocessor Turing Complete?" (theorangeduck,
   blog). URL: https://theorangeduck.com/page/c-preprocessor-turing-complete
   FETCHED. Demonstration ONLY: a Brainfuck interpreter implemented in cpp
   (CPP_COMPLETE on GitHub). Author: "The short answer - I don't know."
   Objection quoted: "the C preprocessor cannot express unbounded recursion,
   making it incompatible with the definition of requiring an infinite tape".
   No formal proof; no discussion of substitution semantics. Type: working
   demonstration + discussion.
2. **Blue paint (cpp self-reference prohibition)** — Tony Finch, "Blue paint
   in the C preprocessor" (2024-05-21). URL:
   https://dotat.at/@/2024-05-21-blue-paint.html (TO FETCH in R2). Related:
   PVS-Studio "Cursed fire" https://pvs-studio.com/en/blog/posts/1143 and
   Stanford (Don Mitchell?) "Recursive macros with C++20 __VA_OPT__"
   https://www.scs.stanford.edu/~dm/blog/va-opt.html (Paul Fultz trick —
   recursion achievable despite blue paint) (TO FETCH).
3. **Rust macro_rules!** — "Turing Completeness", The Little Book of Rust
   Macros (TLBORM). URL:
   https://lukaswirth.dev/tlborm/decl-macros/minutiae/turing-completeness.html
   FETCHED. Proof-by-construction: tag-system (m>1) simulation; "Our macro's
   expansion will halt if and only if T halts"; "macro_rules! expansion is
   Turing-Complete". Recursion: macro may call itself; recursion_limit is an
   implementation cap ("same as noting that a computer's RAM is finite").
   Patterns = token trees; expansion is nested recursive. Type: book
   (community), rigorous construction, not peer-reviewed.
4. **/// (slashes) esolang** — wiki page FETCHED. Created by Sophie Swett
   (Ihope127) 2006. Single op: repeated string substitution /pattern/repl/.
   "it was proved Turing-complete by Ørjan Johansen in 2009, who created an
   interpreter for the Turing-complete language Bitwise Cyclic Tag" — TC even
   restricted to 2 chars. Evaluation: UNBOUNDED SUBSTITUTION LOOP (repeatedly
   replacing first occurrence until no match) = iterate-to-normal-form, like
   a Markov algorithm. NOT single-sweep; no separate recursion construct.
   URL: https://esolangs.org/wiki////
5. **Thue** — wiki page FETCHED. John Colagioia 2000. Semantics: rule list +
   initial string, NONDETERMINISTIC semi-Thue rewriting to normal form.
   TC "By showing that there is a reduction to Thue from Type-0 languages in
   the Chomsky hierarchy (unrestricted grammars)". Iterate-to-normal-form.
   URL: https://esolangs.org/wiki/Thue
6. **Retina** — wiki page FETCHED (stub). Martin Ender 2015. Regex-based
   substitution (.NET regex), category "Turing complete" but no proof on the
   page. URL: https://esolangs.org/wiki/Retina. Related: Lysxia blog
   "Programming Turing machines with regexes" (2024-06-18)
   https://blog.poisson.chat/posts/2024-06-18-turing-regex.html (TO FETCH).
7. **sed** — Blaess turing.sed via catonmat.net/proof-that-sed-is-turing-complete
   (TO FETCH in R2). HN thread id=19153713. Type: demonstration (TM written
   as sed script). Also ed(1) via Rule 110: nixwindows.wordpress.com (TO
   FETCH).
8. **C++ templates** — Veldhuizen. Two items: (a) "Using C++ Template
   Metaprograms", C++ Report 7(4):36-43, May 1995; (b) manuscript "C++
   Templates are Turing Complete" https://rtraba.com/wp-content/uploads/2015/05/cppturing.pdf (TO FETCH —
   need to check its status: unpublished manuscript?). Wiki:
   https://en.wikipedia.org/wiki/Template_metaprogramming
9. **m4** — Wikipedia-based tutorial PDF says "Turing-complete... usable as a
   practical programming language" (m4 has conditionals, arithmetic,
   recursion). GNU m4 page: http://www.gnu.org/software/m4. NEEDS a better
   primary verification in R2 (docs or a demo). Kernighan & Ritchie 1977
   original: https://wolfram.schneider.org/bsd/7thEdManVol2/m4/m4.html
10. **TeX** — Eric Zheng "The Turing-Completeness of TeX"
    https://www.ericzheng.org/thoughts/tex-turing-complete.html (TO FETCH);
    Wikipedia Turing-completeness article lists TeX, m4 as TC macro
    processors. TeX TC folklore is old; any proof?
11. **Streaming string transducers** — Alur & Černý, "Expressiveness of
    streaming string transducers", FSTTCS 2010. URL:
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2010.1
    (+ PDF https://cernyp.github.io/publications/fsttcs10/fsttcs10.pdf).
    SSTs = two-way transducers = regular string functions. NOT TC; the model
    has no general recursion. No theorem found equating "SST + recursion"
    with partial computable — but that combination is our Thm 6.4's closest
    "formal-languages" framing (constant patterns only in SST case).

### Emerging picture (R1)

- All substitution-based TC systems found so far (///, Thue, Retina, sed,
  TeX, cpp demos, Rust macros, C++ templates, m4) are EITHER iterate-to-
  normal-form rewriting OR token/AST-level macro systems with built-in
  unbounded recursion + rescanning of substituted text.
- NOBODY found so far studies: (a) single-sweep never-rescan fixed-string
  pass as the sole data operation + explicit recursion; (b) the "replacement
  forced iff pattern occurs" laziness discipline; (c) an inertness theorem
  for strict evaluation of such a calculus; (d) exact characterization as
  partial computable (rather than "can simulate a TM/TC language").

### R2 plan (next round)
- Fetch: Tony Finch blue paint; Stanford __VA_OPT__; catonmat sed;
  Veldhuizen PDF; Eric Zheng TeX; GNU m4 docs; Lysxia regex TMs.
- Search: Boost.Preprocessor recursion limits, ORDER/CHAOS libraries
  (Paul Mensonides), cpp "computational completeness" academic paper,
  "Order-pp", prime computation in cpp, expansion depth.
- Search: Nix, Template Haskell TC.

---

## Round 2 findings (2026-09-21) — C preprocessor + macro systems deep dive

12. **Stanford blog (David Mazieres), "Recursive macros with C++20 __VA_OPT__"**
    URL: https://www.scs.stanford.edu/~dm/blog/va-opt.html FETCHED.
    Blue paint = "replacing" bit on macro + "unavailable" bit on tokens (set
    never cleared). Fultz trick: "The trick ... is to avoid setting the
    unavailable bit on the macro that you want to expand recursively by
    hiding the token until another macro's rescan phase." __VA_OPT__ gives
    base case. On power: "the real limit is how much time and memory we have
    for cpp, not the fact that cpp isn't turing complete." cpp "was designed
    to guarantee termination." EXPAND chains: 5 lines = 342 rescans; torture
    program "over 100 years and many exabytes". Known spec ambiguity (CWG
    268) on when replacing bit cleared. Type: expert blog, no formal proof.
13. **Wikipedia, C preprocessor**. URL:
    https://en.wikipedia.org/wiki/C_preprocessor FETCHED. "The C
    preprocessor is not [Turing-complete], but comes close." Recursive
    computations possible "but with a fixed upper bound on the amount of
    recursion performed". Token-level substitution, staged expansion
    (rescan). Type: encyclopedia.
14. **Wikipedia, Turing completeness**. URL:
    https://en.wikipedia.org/wiki/Turing_completeness FETCHED. Lists as TC:
    "TeX, a typesetting system"; "General-purpose macro processor such as
    m4"; C++ templates under "Unintentional Turing completeness" (citing
    Meyers, Effective C++ 2005). sed and cpp NOT listed as TC. Also: XSLT,
    SQL, printf format strings(!), TypeScript types, MOV-only x86,
    TrueType, Unicode transliteration rules.
15. **PVS-Studio (D. Sokolov), "Cursed fire, or magic of C preprocessor"**.
    URL: https://pvs-studio.com/en/blog/posts/1143 FETCHED. "it paints it
    blue (the compiler jargon) and leaves it as it is" — blue paint
    prevents self-reference; deferred expansion escapes it. Type: vendor
    blog with concrete traces.
16. **Tony Finch, "Blue paint in the C preprocessor"** (2024-05-21). URL:
    https://dotat.at/@/2024-05-21-blue-paint.html — FETCH FAILED (direct x2
    and archive.org blocked). UNVERIFIED; do not cite without verification.
    (Stanford + PVS-Studio cover the same mechanism, verified.)
17. **Veldhuizen, "C++ Templates are Turing Complete"** (unpublished ms.,
    Indiana University CS). PDF FETCHED (local text extract):
    https://rtraba.com/wp-content/uploads/2015/05/cppturing.pdf Abstract:
    "We sketch a proof of a well-known folk theorem that C++ templates are
    Turing complete. The absence of a formal semantics for C++ template
    instantiation makes a rigorous proof unlikely." "The proof is
    straightforward: we show how any Turing machine may be embedded in the
    C++ template instantiation mechanism." Antecedent: Erwin Unruh's
    compile-time prime program. Related: "Using C++ Template Metaprograms",
    C++ Report 7(4):36-43, May 1995. Type: unpublished proof sketch of folk
    theorem.
18. **sed** — catonmat (Peteris Krumins) "A Proof That Sed Is Turing
    Complete": https://catonmat.net/proof-that-sed-is-turing-complete
    FETCHED. Christophe Blaess's turing.sed: "His proof is by construction -
    he wrote a Turing machine in sed"; "As any programming language that can
    implement a Turing machine is Turing complete..."; relies on comparison,
    branching (labels/goto), hold space. Type: demonstration. (HN
    discussion: https://news.ycombinator.com/item?id=19153713.)
19. **TeX** — Eric Zheng, "The Turing-Completeness of TeX" (2020). URL:
    https://www.ericzheng.org/thoughts/tex-turing-complete.html FETCHED.
    SKI combinator macros (K, S) + infinite loop \loop{\loop}; "assuming the
    implementation is correct" — author "90% sure there's a bug". Type:
    informal demonstration (TeX TC itself is old folklore; Wikipedia lists
    TeX as TC).
20. **m4** — GNU m4 manual: http://gnu.ist.utl.pt/software/m4/manual/m4.html
    (search-verified): -L/--nesting-limit (default 1024) exists to stop
    runaway recursive expansion; M. Breen "Notes on the M4 Macro Language"
    https://mbreen.com/m4.html shows recursive sigma(n) with accumulator to
    dodge nesting. Wikipedia TC page: "General-purpose macro processor such
    as m4" listed as TC. Original: Kernighan & Ritchie 1977,
    https://wolfram.schneider.org/bsd/7thEdManVol2/m4/m4.html. Type: TC
    folklore + demos; no proof paper found.
21. **Chaos-pp / Order** — Paul Mensonides 2003-2005, GitHub (ldionne mirror):
    https://github.com/ldionne/chaos-pp/blob/master/built-docs/introduction.html
    FETCHED. "a generative metaprogramming framework for C and C++";
    sister library Order (by Karvonen per Boost list). Intro page makes no
    explicit unbounded-recursion claim (docs incomplete). Type: practical
    libraries.
22. **Nix** — pure, lazy, TC (Dolstra; Krebbers et al. "Verified Interpreters
    for Dynamic Languages" calls Nix "Turing-complete, untyped functional
    language"; Dolstra talk "The Future of Nix" asks whether TC is harmful).
    URLs: https://robbertkrebbers.nl/research/articles/nix.pdf,
    https://edolstra.github.io/talks/guix-feb-2018.pdf. Full FP language —
    not near our primitive.
23. **Template Haskell** — Sheard & Peyton Jones, "Template Meta-programming
    for Haskell" (PLDI 2002), https://www.cs.tufts.edu/comp/150PLD/Papers/TemplateHaskell.pdf
    (search-verified abstract). Full Haskell at compile time — TC trivially.

### R2 conclusions
- cpp: NO proof of TC anywhere; consensus (Wikipedia) is "not TC, but
  close"; demos (BF interpreter, EXPAND torture) + recursion achievable via
  Fultz deferred-expansion trick; standard designed to guarantee
  termination; implementation limits (depth ~ bounded). Open debated
  question.
- Every macro system with proven/demonstrated TC has UNBOUNDED ITERATION OR
  RECURSION + RESCANNING of substituted text (m4 rescans, TeX rescans, Rust
  macros nested-expand, C++ templates instantiate recursively).
- No macro-system source studies a "replacement forced iff pattern occurs"
  laziness discipline. The cpp analog of our non-strictness is the deferred
  expansion trick (practical, unformalized).

### R3 plan
- Classical: Wikipedia Markov algorithm + tag system (verify markov54,
  post47, minsky67 usage fairness); Huet-Levy call-by-need/neededness;
  macro grammars (Fischer 1968) relevance check.
- Esolang remainder: Lysxia regex TMs; ed(1) Rule 110; search for other
  substitution-only esolangs.
- Exact-match hunting (section E list) + "meow language" collision check.

---

## Round 3 findings (2026-09-21) — classical theory, esolangs, exact-match

24. **Markov normal algorithms** — Wikipedia FETCHED:
    https://en.wikipedia.org/wiki/Markov_algorithm "Markov algorithms have
    been shown to be Turing-complete"; "Any normal algorithm is equivalent
    to some Turing machine, and vice versa". Evaluation: ordered rules,
    first applicable rule replaces LEFTMOST occurrence, "after each rule
    application the search starts over from the first rule" — i.e.
    iterate-to-normal-form. Our markov54 citation is used fairly.
25. **Tag systems** — Wikipedia FETCHED:
    https://en.wikipedia.org/wiki/Tag_system 2-tag universality: "a 2-tag
    system can be constructed to emulate a Universal Turing machine, as was
    done by Wang (1963) and by Cocke & Minsky (1964)"; "For each m > 1, the
    set of m-tag systems is Turing-complete"; Cook 2004 cyclic tag systems
    (Rule 110). Paper's minsky67 usage fair.
26. **Huet & Lévy, neededness/call-by-need** — search-verified (multiple
    citing papers): INRIA Rapport Laboria 359, Aug 1979, "Call by need
    computations in non-ambiguous linear term rewriting systems" (HAL:
    https://inria.hal.science/hal-04716618); journal version "Computations
    in Orthogonal Rewriting Systems" in Computational Logic: Essays in
    Honour of Alan Robinson, MIT Press 1991 (Lévy's copy:
    http://pauillac.inria.fr/~levy/pubs/81robinson1.pdf). Introduced
    NEEDED REDEXES (must be contracted in any reduction to normal form);
    basis of call-by-need. NOT applied to string-substitution calculi with
    recursion anywhere found.
27. **Wehar, "A connection between self-reference and Turing-completeness"**
    — VERIFIED via curl (WebFetch blocked by bad cert), full text read:
    http://michaelwehar.com/quines/completeness.html Informal research note
    (part of a quines tutorial). Sub(u,v,x) "replaces each occurrence of u
    with v in x". Informal theorem: "If a programming language can (1)
    perform variable assignment, (2) compute Sub, and (3) has a universal
    program, then it is Turing-complete." Control flow via SELF-REFERENCE +
    eval (Kleene recursion theorem route). KEY GATE QUOTE: "it's not
    possible for both substitutions to do something as long as the strings
    *0* and *1* don't occur in block1 and block2" — the occurrence-inertness
    equation used as an if-selector (our gate, informally). Type: informal
    online note; one direction only; assumes eval+assignment; no laziness,
    no inertness, no exact characterization.
28. **ed(1) TC via Rule 110** — VERIFIED:
    https://nixwindows.wordpress.com/2018/03/13/ed1-is-turing-complete
    (tPenguinLTG, 2018): script acts on own source, recursion via shell
    escape `!exec ed '%' < '%'`: "if you could call ed recursively, you'd be
    able to implement Rule 110"; `g` command as conditional; "The script
    does not terminate by itself." Demonstration.
29. **arXiv:2608.19397** string-rewriting survey FETCHED — classical
    content only: "They can simulate the operation of a Turing machine by
    encoding configurations as words"; NOTHING on single-pass, lazy
    strategies, or substitution-as-programming-primitive. Confirms our
    Related Work's framing is accurate.
30. **Replace esolang** — VERIFIED: https://esolangs.org/wiki/Replace (Max
    Black). Commands `find/replace` (regex), input is the program's own
    source, each command evaluated ONCE in order — a single pass, no loop,
    no recursion. NO computational class claim on the page. Closest esolang
    in spirit to the single-sweep pass; but regex-based, self-modifying,
    no recursion, no TC result.
31. **Meow collision check** — VERIFIED: esolangs.org/wiki/Meow is a
    disambiguation page (Martsadas = joke 2-register machine with labels;
    None1; tommyaweosme; Meowlang = chicken-style stack VM, TC, by Wixette;
    135yshr). None is a string-substitution language. Name-only overlap; no
    technical collision with our meow.
32. **Fischer, macro grammars** — search-verified (scispace + ADS): M. J.
    Fischer, "Grammars with macro-like productions", SWAT/FOCS 1968. Macro
    expansion with recursion + parameters generates the INDEXED languages
    (= Aho's indexed grammars, nested stack automata; per Wikipedia
    Indexed_grammar). Language-generation view; no pattern search, no
    occurrence gating; different class entirely.
33. **Streams productivity (for §6.3)** — VERIFIED from PDF (VU Amsterdam
    copy): Endrullis, Grabmayer, Hendriks, Isihara, Klop, "Productivity of
    Stream Definitions" (TCS 2010): "We give an algorithm for deciding
    productivity of a large and natural class of recursive stream
    definitions... Whereas productivity is undecidable for stream
    definitions in general, we show that it can be decided for 'pure'
    stream definitions." Related: Sijtsma 1989 (productivity notion),
    Coquand 1994 (guardedness) — secondary-verified only (via citing
    papers), see caveats below.
34. **Alur & Černý, SSTs** — VERIFIED (Dagstuhl): "Expressiveness of
    streaming string transducers", FSTTCS 2010, LIPIcs 8, pp. 1-12, DOI
    10.4230/LIPIcs.FSTTCS.2010.1. Single pass, string-valued variables,
    each at most once per RHS: power = exactly regular transductions
    (= two-way deterministic finite-state transducers = MSO transductions).
    NO recursion; NOT TC. The constant-pattern single-pass world.
35. **Garrido, Meseguer, Johnson** — "Algebraic Semantics of the C
    Preprocessor and Correctness of its Refactorings" (search-verified via
    Semantic Scholar + Meseguer's "rewriting logic semantics project" TCS
    paper crediting it as first formal semantics of cpp). Formalizes
    expansion for REFACTORING CORRECTNESS; no computational-power theorem.
    Full bibliographic data partially unverified (RG 403).
36. **Negative results (searched, nothing found)**: no theorem anywhere on
    (a) "replacement forced iff pattern occurs" as an evaluation rule;
    (b) strict/eager recursion over a substitution calculus being inert;
    (c) single-sweep substitution + recursion = partial computable;
    (d) sed's s-command-only fragment power; (e) macro-processor
    computational power as a subject of peer-reviewed study.
37. **Lysxia, "Programming Turing machines with regexes"** (2024) —
    VERIFIED: https://blog.poisson.chat/posts/2024-06-18-turing-regex.html
    NOT substitution: regexes as programs over TM tape operations
    ("Then the regular expression might as well be the program"). Adjacent
    curiosity; no overlap with our claims.
38. **Unverifiable items**: Tony Finch "Blue paint in the C preprocessor"
    (dotat.at, 2024-05-21) — fetch failed (bad cert via both http/https;
    archive.org blocked by tool). Found via search; NOT verified; do not
    cite. Retina's TC: only the category tag on a stub wiki page; no proof
    fetched. Sijtsma 1989 / Coquand 1994: only secondary citations seen.

---

## Round 4 (2026-09-21): CLOSNESS TABLE, VERDICT, PROPOSED CITATIONS

### Closeness table

Axes: (i) single-sweep pass vs iterate-to-normal-form/unbounded iteration;
(ii) fixed-string patterns vs regex/tokens/AST; (iii) recursion vs built-in
loops/labels; (iv) the laziness rule "replacement forced iff pattern
occurs"; (v) exact characterization (partial computable) vs "can simulate a
TM"; (vi) inertness / no-strict-gain results.

| # | System / source | (i) sweep | (ii) pattern | (iii) control | (iv) lazy rule | (v) exact | (vi) inert |
|---|---|---|---|---|---|---|---|
| 1 | Markov normal algorithms (1954; cited markov54) | iterate to NF | fixed strings, many rules | loop built-in | no | YES (= partial computable) | no |
| 2 | Post/tag systems (post47; Wang'63, Cocke-Minsky'64, Cook'04) | iterate | fixed productions | loop built-in | no | universal (2-tag) | no |
| 3 | semi-Thue systems (thue14, book93) | iterate to NF | fixed strings | loop built-in | no | undecidability results | no |
| 4 | /// esolang (Swett'06; Johansen'09 BCT proof) | iterate (first-occurrence loop) | fixed strings | loop built-in | no | proof-by-construction | no |
| 5 | Thue esolang (Colagioia'00) | iterate, nondeterministic | fixed strings | loop built-in | no | reduction from Type-0 grammars | no |
| 6 | Retina (Ender'15) | iterate (+ loops) | REGEX | loop built-in | no | wiki category only | no |
| 7 | sed (Blaess turing.sed) | s is one pass, but control = labels/branches + hold space | REGEX | explicit goto | no | demonstration (TM in sed) | no |
| 8 | ed(1) (tPenguinLTG'18) | substitutions + g-conditionals, recursion via !shell escape | REGEX | recursion (process spawn) | no | demonstration (Rule 110) | no |
| 9 | C preprocessor (demos; Fultz trick; Mazières'21; Garrido-M-J'06) | token subst + RESCAN of replacement | fixed token sequences | recursion banned (blue paint), deferred tricks | deferred expansion = informal analog; never formalized | NO — "not TC, but close" (Wikipedia); open debate | no (blue paint = termination device, not expressiveness thm) |
| 10 | m4 (K&R'77; GNU nesting limit) | rescan | fixed token strings | recursion + builtins | no | folklore/demos (Wikipedia lists TC) | no |
| 11 | TeX (Zheng'20 sketch; folklore) | macro expansion + rescan | token patterns | recursion | no | sketch (SKI in TeX) | no |
| 12 | Rust macro_rules! (TLBORM) | nested recursive expansion (rescan) | token TREES | self-recursion allowed (recursion_limit impl detail) | no | proof-by-construction (tag system; halts iff T halts); no class characterization | no |
| 13 | C++ templates (Unruh; Veldhuizen ms.) | template instantiation, unbounded | type/AST matching | recursion via instantiation | no | proof sketch of folk theorem | no |
| 14 | Wehar online note (quines/completeness) | Sub = replace-all (single sweep) as DATA op | fixed strings | self-reference + EVAL + assignment | no (uses occurrence-inertness as if-selector — the gate, informally) | informal one-direction sketch | no |
| 15 | Fischer macro grammars ('68) | derivation with recursion + params | nonterminal positions (NO search) | recursion | no | exact, but of INDEXED languages | no |
| 16 | Huet-Lévy neededness ('79/'91) | term rewriting strategies | terms | — | THE classical call-by-need/neededness theory; never applied to substitution+recursion over strings | — | no |
| 17 | SSTs (Alur-Černý'10) | single pass (streaming) | constant strings | NO recursion | no | exact = regular transductions | no |
| 18 | Replace esolang (Black) | single pass over command list | REGEX | NO loop, NO recursion | no | no claim | no |
| 19 | OUR Thm 6.4 | SINGLE SWEEP, never rescan | fixed strings (variable via subexprs) | recursion only | THE rule, formalized | exact: partial computable | YES (Thms 6.1-6.2) |

### Verdict

1. **Theorem 6.4 as stated is not in the literature.** The exact combination
   — single left-to-right never-rescanning sweep over plain strings as the
   ONLY data operation, recursion as the only added construct, universality
   gated by the operator's own non-strictness (replacement forced iff the
   pattern occurs), yielding EXACTLY the partial computable functions —
   appears nowhere. Closest four, with deltas:
   - Markov normal algorithms (cited): exact characterization of the same
     class, but through unbounded iteration of ordered rewriting to normal
     form; the paper's restart-variant discussion already positions this.
   - TLBORM's Rust macro proof: a real proof-by-construction (tag system,
     halts-iff-T-halts) but over token trees with recursive nested
     expansion+rescanning; no laziness rule, no class equality beyond TC,
     no inertness.
   - Wehar's note: the only source found that (a) uses the same
     replace-all-once Sub as the data operation and (b) uses the
     occurrence-inertness equation as a conditional (the gate!). But it
     assumes variable assignment and a universal program (eval), is
     informal, one-direction, and has no evaluation-order story.
   - /// (Johansen): substitution-only language, TC proven, but the
     unbounded first-occurrence substitution LOOP is built in; no single
     sweep, no recursion discipline, no characterization.
2. **The inertness contrast (Thms 6.1-6.2) is new.** No source proves —
   or even discusses — that strict or lazy-argument evaluation of recursive
   substitution programs collapses to inlining-or-divergence. The practical
   analogs (cpp blue paint blocking direct self-recursion; Boost needing
   deferred expansion to recurse at all) are termination/convenience
   devices, never expressiveness theorems.
3. **The laziness clause itself is unstudied.** "Replacement forced iff
   pattern occurs" appears NOWHERE as a formal evaluation rule. cpp's
   deferred-expansion trick is its unformalized practical cousin; Huet-Lévy
   neededness is its theoretical frame (the replacement is 'needed' iff
   the pattern occurs) but was never instantiated to string substitution.
4. The conservativity proposition and the two-way gate construction are
   new; the gate's INGREDIENT (Sub inert when pattern absent, used to
   select) appears informally in Wehar's note (and implicitly in sed's
   g-conditional folklore), which the paper should cite as the folk
   antecedent.
5. §6.3 (streams) DOES have close prior art the paper does not cite:
   productivity/guardedness of recursive stream definitions (Sijtsma 1989,
   Coquand 1994, Endrullis et al. TCS 2010 — decidability of productivity
   for 'pure' definitions, guardedness as semantic). Different setting
   (typed functional streams, no string substitution), but the questions
   (when is a recursive stream definition productive; syntactic guardedness
   too restrictive; semantic criteria) are the same shape as Thm
   thm:guardedness and should be cited.

### Proposed bib entries (verified unless flagged)

@misc{veldhuizen95tc,   %% year commonly given as 1995; undated PDF — coordinator confirm
  author = {Veldhuizen, Todd L.},
  title = {{C++} Templates are {T}uring Complete},
  howpublished = {Unpublished manuscript, Indiana University},
  note = {\url{https://rtraba.com/wp-content/uploads/2015/05/cppturing.pdf}}
}
@misc{tlborm,
  author = {Keep, Daniel and Wirth, Lukas},
  title = {The Little Book of Rust Macros: Turing Completeness},
  howpublished = {\url{https://lukaswirth.dev/tlborm/decl-macros/minutiae/turing-completeness.html}},
  note = {Tag-system simulation of macro\_rules! expansion}
}
@misc{mazieres21,
  author = {Mazi{\`e}res, David},
  title = {Recursive macros with {C++20} \texttt{\_\_VA\_OPT\_\_}},
  howpublished = {\url{https://www.scs.stanford.edu/~dm/blog/va-opt.html}},
  year = {2021}
}
@misc{wehar,
  author = {Wehar, Michael},
  title = {A connection between self-reference and {T}uring-completeness},
  howpublished = {\url{http://michaelwehar.com/quines/completeness.html}},
  note = {Informal note}
}
@misc{krumins-sed,
  author = {Krumins, Peteris},
  title = {A Proof That Unix Utility Sed Is Turing Complete},
  howpublished = {\url{https://catonmat.net/proof-that-sed-is-turing-complete}},
  note = {Describes C. Blaess's \texttt{turing.sed}}
}
@misc{slashes,
  author = {Swett, Sophie},
  title = {/// (slashes)},
  howpublished = {Esolang wiki, \url{https://esolangs.org/wiki////}},
  note = {Turing-completeness via {\O}rjan Johansen's Bitwise Cyclic Tag interpreter (2009)}
}
@misc{thue-esolang,
  author = {Colagioia, John},
  title = {Thue},
  howpublished = {Esolang wiki, \url{https://esolangs.org/wiki/Thue}}
}
@techreport{kernighan77m4,
  author = {Kernighan, Brian W. and Ritchie, Dennis M.},
  title = {The {M4} Macro Processor},
  institution = {Bell Laboratories},
  year = {1977},
  note = {Unix 7th Edition Manual, Vol.~2; \url{https://wolfram.schneider.org/bsd/7thEdManVol2/m4/m4.html}}
}
@techreport{huetlevy79,
  author = {Huet, G{\'e}rard and L{\'e}vy, Jean-Jacques},
  title = {Call by need computations in non-ambiguous linear term rewriting systems},
  institution = {INRIA},
  number = {359},
  year = {1979}
}
@inproceedings{fischer68,
  author = {Fischer, Michael J.},
  title = {Grammars with macro-like productions},
  booktitle = {Proc.\ 9th Annual Symposium on Switching and Automata Theory},
  year = {1968}
}
@inproceedings{alur10,
  author = {Alur, Rajeev and {\v C}ern{\'y}, Pavol},
  title = {Expressiveness of streaming string transducers},
  booktitle = {FSTTCS 2010},
  series = {LIPIcs},
  volume = {8},
  pages = {1--12},
  publisher = {Schloss Dagstuhl},
  year = {2010}
}
@article{endrullis10,
  author = {Endrullis, J{\"o}rg and Grabmayer, Clemens and Hendriks, Dimitri and Isihara, Ariya and Klop, Jan Willem},
  title = {Productivity of stream definitions},
  journal = {Theoretical Computer Science},
  volume = {411},
  year = {2010}
}
FLAGGED (not fully verified): garrido06 (venue/vol/pages), sijtsma89, coquand94,
Tony Finch blue-paint post (unfetchable), Retina TC proof (no page found).

### Proposed Related Work wording (for coordinator; LaTeX-ready sketch)

New paragraph, to follow the current "What is not covered" paragraph:

\paragraph{Substitution-based programming.} A folk practice programs by
substitution alone, and its universality stories all buy the loop
somewhere else. Macro processors reach Turing completeness with unbounded
recursion and rescanning of expanded text: \texttt{m4} and \TeX{} are the
standard examples \cite{kernighan77m4}, the C++ template mechanism was
sketched Turing complete by Veldhuizen (after Unruh's compile-time primes)
\cite{veldhuizen95tc}, and Rust's \texttt{macro\_rules!} expansion
simulates tag systems \cite{tlborm}. The C preprocessor, the closest
practical relative of our primitive, sits on the fence: the standard
\emph{paints a macro name blue} while it is being expanded, blocking
direct self-reference, and the consensus is that it is ``not
Turing-complete, but close''; recursion is recovered in practice only by
deferred-expansion tricks that hide the recursive call from the rescan
\cite{mazieres21} -- an unformalized cousin of the laziness clause of
Section~\ref{sec:recursion}, which no one has stated as an evaluation rule.
Esolangs isolate the idea from the other side: ///'s single operation is
repeated string substitution and its Turing completeness rests on an
embedded Bitwise Cyclic Tag interpreter \cite{slashes}; Thue is
nondeterministic semi-Thue rewriting \cite{thue-esolang}; sed is Turing
complete through labels and branches rather than through \texttt{s} alone
\cite{krumins-sed}. The nearest formal statement we know is an informal
note of Wehar \cite{wehar}: a language with assignment, global replace, and
a universal program is Turing complete -- a construction that already uses
the operator equation $[A/B]S = S$ ($B$ absent) as its \emph{if}. None of
these systems isolates the single never-rescanning sweep as the data
operation, none states the evaluation rule under which recursion buys
universality, and none separates it from the strict runtimes; that border
is what Section~\ref{sec:recursion} draws. The lazy-pass rule itself is a
neededness criterion in the sense of Huet and L\'evy \cite{huetlevy79} --
the replacement of $[\,R/P\,]E$ is needed exactly when $P$ occurs --
inherited from term-rewriting strategy theory, which has not previously
been instantiated for string substitution.

Optional sentence for the streams subsection (§6.3 / related work):

The productivity questions of Section~\ref{sec:rec-streams} are the
string analogue of the productivity of recursive stream definitions
\cite{endrullis10}, where guardedness is likewise semantic rather than
syntactic and decidability holds only for restricted classes.

Optional clause for the transductions paragraph:

The constant-pattern, call-free fragment also coincides in spirit with
the streaming string transducers of Alur and {\v C}ern\'y \cite{alur10},
single-pass machines whose exact class (the regular transductions) is what
recursion under lazy passes is here shown to escape.


"""ROUND 1 verification battery for the L+R study (see REPORT.md).

Problem of the round: set up the mixed L+R evaluator, re-verify the seed
facts, and find the smallest [A/B]^R != [A/B] witness.

Checks (all machine-verified on the stated finite domains):

  C1  rev-duality as an implementation cross-check: the ITERATIVE substR of
      lrcore vs  rev(subst(revA,revB,revC))  -- two independent derivations.
  C2  r2l-agree (prop:r2l-agree): unbordered B => [A/B]^R = [A/B]; and on
      the same domain, every disagreement has B bordered.
  C3  every bordered B in the domain admits SOME (A,C) disagreement.
  C4  the smallest disagreement triples (A,B,C) -- the "smallest witness".
  C5  thm:r2l-toolkit with THIS evaluator: enc, dec, cat, tail, head, eq, if
      built by the rec/lazy_pass toolkit, evaluated as L and as all-R
      expressions, agree on all stated inputs (value + definedness).
  C6  thm:conjugation, extended to MIXED expressions: for random mixed E,
      ev(conj(E))(rev args) == rev(ev(E)(args)), undefinedness matching;
      plus conj(conj(E)) == E.
  C7  prop:last re-verification: last / init / rotate-right over all strings
      of length <= 9 on {a,b}, with THIS evaluator.
  C8  length bound for the R-pass: |[A/B]^R C| <= |C| * (1+|A|).
"""

import itertools
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrcore import (subst, substR, rev, K, V, C, S, SR, ev, run, allR, conj,
                    size, iter_strings, borders, unbordered, fun_table, Tally)
import toolkit as tk

sg = tk.Sig(['a', 'b'], 'a', 'b', 'b', 'a')   # paper b='a', x='b', top='b', bot='a'
AB = ['a', 'b']
ABC = ['a', 'b', 'c']


# ---------------------------------------------------------------- C1

def c1_rev_duality():
    t = Tally('C1 rev-duality (iterative substR vs rev-conjugate of subst)')
    for A in iter_strings(AB, 3):
        for B in iter_strings(AB, 3, 1):
            for Cc in iter_strings(AB, 6):
                t.check(substR(A, B, Cc) == rev(subst(rev(A), rev(B), rev(Cc))),
                        (A, B, Cc))
    return t


# ---------------------------------------------------------------- C2

def c2_agree():
    t = Tally('C2 r2l-agree: unbordered B => equal')
    for B in iter_strings(AB, 4, 1):
        if unbordered(B):
            for A in iter_strings(AB, 3):
                for Cc in iter_strings(AB, 6):
                    t.check(subst(A, B, Cc) == substR(A, B, Cc), (A, B, Cc))
    return t


def c2b_differ_implies_bordered():
    t = Tally('C2b disagreement => B bordered (same domain)')
    for B in iter_strings(AB, 4, 1):
        for A in iter_strings(AB, 3):
            for Cc in iter_strings(AB, 6):
                if subst(A, B, Cc) != substR(A, B, Cc):
                    t.check(bordered := bool(borders(B)), (A, B, Cc))
    return t


# ---------------------------------------------------------------- C3

def c3_bordered_admits_witness():
    """|C| <= 7 suffices for |B| <= 4: the overlap word of a period-p pattern
    has length |B| + p <= 2|B| - 1 <= 7."""
    t = Tally('C3 every bordered B (<=4) admits some (A,C) disagreement')
    nwit = {}
    for B in iter_strings(AB, 4, 1):
        if not borders(B):
            continue
        found = None
        for A in iter_strings(AB, 2):
            for Cc in iter_strings(AB, 7):
                if subst(A, B, Cc) != substR(A, B, Cc):
                    found = (A, Cc)
                    break
            if found:
                break
        t.check(found is not None, B)
        if found:
            nwit[B] = found
    print(f'    [C3] bordered patterns with witnesses: {len(nwit)} '
          f'(e.g. B="aa" -> A,C={nwit.get("aa")}; B="abab" -> {nwit.get("abab")})')
    return t


# ---------------------------------------------------------------- C4

def c4_smallest_witness():
    """Collect ALL disagreements with |A|<=2, |B|<=3, |C|<=5 over {a,b};
    also over {a,b,c} for the 3-letter claim.  Report the minimal ones."""
    results = {}
    for name, sigma in (('binary', AB), ('ternary', ABC)):
        diffs = []
        for A in iter_strings(sigma, 2):
            for B in iter_strings(sigma, 3, 1):
                for Cc in iter_strings(sigma, 5):
                    if subst(A, B, Cc) != substR(A, B, Cc):
                        diffs.append((A, B, Cc))
        results[name] = diffs
        # minimal by (|B|, |C|, |A|):
        key = lambda t_: (len(t_[1]), len(t_[2]), len(t_[0]))
        mins = [d for d in diffs if key(d) == min(key(x) for x in diffs)]
        print(f'    [C4/{name}] {len(diffs)} disagreements total; '
              f'minimal (|B|,|C|,|A|)={key(mins[0]) if mins else None}: {mins}')
        # no disagreement with |B|=1 or |C|<=2:
        t = Tally(f'C4/{name} no disagreement with |B|<=1 or |C|<=2')
        for (A, B, Cc) in diffs:
            t.check(len(B) >= 2 and len(Cc) >= 3, (A, B, Cc))
        t.report()
    # the canonical minimal witness up to renaming, and its shape:
    (A, B, Cc) = ('b', 'aa', 'aaa')
    print(f'    [C4] canonical: [b/aa]"aaa" = "{subst(A, B, Cc)}"  vs  '
          f'[b/aa]^R"aaa" = "{substR(A, B, Cc)}"')
    # C4b: for the minimal shape (B,C) = (cc, ccc), the two values are
    # A.c and c.A (p=1), so they disagree iff A is not a power of c.
    t = Tally('C4b (B,C)=(cc,ccc): disagree iff A not a power of c')
    for c in AB:
        for A in iter_strings(AB, 3):
            dis = subst(A, c + c, c + c + c) != substR(A, c + c, c + c + c)
            t.check(dis == bool(set(A) - {c}), (A, c))
    t.report()
    return results


# ---------------------------------------------------------------- C5

def c5_toolkit():
    ok = True
    # unary constructions: all inputs of length <= 5 over {a,b}
    dom1 = [(s,) for s in iter_strings(AB, 5)]
    # cat: pairs of length <= 4
    dom2 = [(x, y) for x in iter_strings(AB, 4) for y in iter_strings(AB, 4)]
    # eq/if scrutinees length <= 3
    dom3 = [(x, y) for x in iter_strings(AB, 3) for y in iter_strings(AB, 3)]
    domif = [(c, x, y) for c in (sg.top, sg.bot)
             for x in iter_strings(AB, 3) for y in iter_strings(AB, 3)]

    cases = [
        ('enc', tk.enc(sg, V(0)), dom1),
        ('dec', tk.dec(sg, V(0)), dom1),
        ('tail', tk.tail(sg, V(0)), dom1),
        ('head', tk.head(sg, V(0)), dom1),
        ('cat', tk.cat(sg, V(0), V(1)), dom2),
        ('eq', tk.eq(sg, V(0), V(1)), dom3),
        ('if', tk.if_(sg, V(0), V(1), V(2)), domif),
    ]
    for name, e, dom in cases:
        t = Tally(f'C5 thm:r2l-toolkit {name} (L vs all-R)')
        eR = allR(e)
        for args in dom:
            a = run(e, args)
            b = run(eR, args)
            t.check(a == b, (name, args, a, b))
        ok &= t.report()
    return ok


# ---------------------------------------------------------------- C6

def rand_expr(rng, nvars, maxsize, sigma='ab', maxconst=3):
    def go(budget):
        if budget <= 1 or rng.random() < 0.25:
            if rng.random() < 0.5:
                k = rng.randint(0, maxconst)
                return K(''.join(rng.choice(sigma) for _ in range(k)))
            return V(rng.randrange(nvars))
        r = rng.random()
        if r < 0.2:
            return C(go(budget // 2), go(budget // 2))
        node = S if rng.random() < 0.6 else SR     # MIXED expressions
        return node(go(max(1, budget // 3)), go(max(1, budget // 3)),
                    go(max(1, budget // 3)))
    return go(maxsize)


def c6_conjugation(n_expr=400, n_inp=6, seed=1):
    rng = random.Random(seed)
    t = Tally('C6 conjugation on MIXED expressions')
    ti = Tally('C6 conj is an involution')
    for _ in range(n_expr):
        e = rand_expr(rng, 2, 12)
        ti.check(conj(conj(e)) == e)
        for _ in range(n_inp):
            args = tuple(''.join(rng.choice(AB) for _ in range(rng.randint(0, 6)))
                         for _ in range(2))
            a = run(e, args)
            b = run(conj(e), tuple(rev(s) for s in args))
            if a is None or b is None:
                t.check(a is None and b is None, (e, args, a, b))
            else:
                t.check(b == rev(a), (e, args, a, b))
    ti.report()
    return t


# ---------------------------------------------------------------- C7

def c7_last():
    """prop:last re-verification: last / init / rotate-right, this evaluator,
    all strings of length <= 9 over {a,b}."""
    A = sg.b + sg.b                              # 'aa' -- fresh anchor
    T = lambda: C(tk.enc2(sg, V(0)), K(A))       # enc^2(X) . aa
    PA = sg.x + 'a' + A                          # 'baaa'
    PB = sg.x + 'b' + A                          # 'bbaa'

    last_e = tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                    tk.if_(sg, tk.contains(sg, T(), PA), K('a'), K('b')))
    init_e = tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                    tk.if_(sg, tk.contains(sg, T(), PA),
                           tk.dec2(sg, tk.comp([('', PA)], T())),
                           tk.dec2(sg, tk.comp([('', PB)], T()))))
    rot_e = tk.cat(sg, last_e, init_e)

    t = Tally('C7 prop:last (last/init/rotate-right, |X| <= 9)')
    n = 0
    for L in range(10):
        for tup in itertools.product(AB, repeat=L):
            X = ''.join(tup)
            n += 1
            want = X[-1] if X else ''
            t.check(run(last_e, (X,)) == want, ('last', X))
            want = X[:-1]
            t.check(run(init_e, (X,)) == want, ('init', X))
            want = (X[-1] + X[:-1]) if X else ''
            t.check(run(rot_e, (X,)) == want, ('rot', X))
    print(f'    [C7] {n} strings, {3*n} evaluations')
    return t


# ---------------------------------------------------------------- C8

def c8_length():
    t = Tally('C8 |[A/B]^R C| <= |C|(1+|A|)')
    for A in iter_strings(AB, 3):
        for B in iter_strings(AB, 3, 1):
            for Cc in iter_strings(AB, 6):
                t.check(len(substR(A, B, Cc)) <= len(Cc) * (1 + len(A)),
                        (A, B, Cc))
    return t


# ---------------------------------------------------------------- C9

def c9_bordered_construction():
    """GENERAL witness construction sharpening prop:r2l-agree into a
    BICONDITIONAL:

        [A/B]^R = [A/B] for all A, C   <=>   B unbordered   (B != eps).

    (<=) is the paper's prop:r2l-agree.  (=> contrapositive) B bordered,
    p = smallest period of B (= |B| - longest border), C = B . B[|B|-p:]:
    occurrences of B in C are exactly at 0 and p (a q with 0<q<p would be a
    smaller period; q>p does not fit), they overlap, so the L-scan takes 0
    and the R-scan takes p:

        [a/B]  C = a . B[|B|-p:]        [a/B]^R C = B[:p] . a

    for ANY single character a (the two differ exactly when a != B[0]).
    Verified: all bordered B with |B| <= 6 over {a,b} (and, for the value
    equations, every single-char a; for the disagreement, every a != B[0])."""
    def smallest_period(B):
        lb = max((len(w) for w in borders(B)), default=0)   # longest border
        return len(B) - lb
    t = Tally('C9 bordered-witness construction a.B[-p:] / B[:p].a')
    td = Tally('C9 disagreement for every a != B[0]')
    nb = 0
    for B in iter_strings(AB, 6, 1):
        if not borders(B):
            continue
        nb += 1
        p = smallest_period(B)
        Cc = B + B[len(B) - p:]
        for a in AB:
            t.check(subst(a, B, Cc) == a + B[len(B) - p:], (B, a))
            t.check(substR(a, B, Cc) == B[:p] + a, (B, a))
            if a != B[0]:
                td.check(subst(a, B, Cc) != substR(a, B, Cc), (B, a))
    print(f'    [C9] bordered patterns |B|<=6 over {{a,b}}: {nb}, '
          f'both choices of a each')
    t.report()
    return td


# ---------------------------------------------------------------- main

if __name__ == '__main__':
    print('=== L+R ROUND 1 verification battery ===')
    ok = True
    ok &= c1_rev_duality().report()
    ok &= c2_agree().report()
    ok &= c2b_differ_implies_bordered().report()
    ok &= c3_bordered_admits_witness().report()
    c4_smallest_witness()
    ok &= c5_toolkit()
    c6_conjugation().report()
    ok &= c7_last().report()
    ok &= c8_length().report()
    ok &= c9_bordered_construction().report()
    print('ALL OK' if ok else 'FAILURES PRESENT')
    sys.exit(0 if ok else 1)

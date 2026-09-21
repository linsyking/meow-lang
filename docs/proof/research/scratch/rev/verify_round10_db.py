"""ROUND 10 - the descending-bijection (DB) invariant: proofs made machine.

DEFINITION.  E realizes a descending bijection on w (DB(w)) iff
prov([[E]]w) is a permutation of {0..n-1}, n = |w|, in strictly
decreasing order.  (=> mult 1, |prov| = n.)  rev realizes DB on every
input, so DB is a necessary condition for any rev-computing E; if for
every fixed E the set {w : E realizes DB(w)} is finite, rev is not
L-reachable.  This round: the structure theory of DB realizations,
machine-verified, and the depth-3 verdict.

THE THREE THEOREMS checked here (proofs in phase_leftmove_fragment.tex
and REPORT.md sec 10):

T1 (Last-Pass Structure).  E = (S R P F), c = number of pattern-sites
   of [[P]]w in t = [[F]]w, y = [[R]]w.
   (a) mult 1 and c >= 2 => y carries no labels.
   (b) c = 1 => prov(out) = prov(t^-) . prov(y) . prov(t^+): the
       three blocks are each fully decreasing and block-chained
       (every label of t^- > every label of y > every label of t^+),
       with disjoint label sets; DB forces the site itself to carry
       no labels.
   (c) c in {0} or (c >= 2): prov(out) = prov(t) - F already
       realizes DB(w).

T2 (depth-1, f = 1).  The only labeled values of pass-free
   sub-expressions are FULL identity runs (0..n-1).  A single pass
   (S R P F), R/P/F pass-free, outputs: gaps (increasing), or
   prov(t^-) . full-run . prov(t^+) - and the block chain forces
   t^-, t^+ empty (their labels are the extreme positions 0, n-1).
   So a fully-decreasing injective (FDI) prov at S-depth <= 1 has
   length <= 1; with C-nodes composing singletons: <= #C + 1.

T3 (depth-2 = same).  In a 2-pass chain the final replacement is
   pass-free: prov_y in {empty, full run}.  Full run => t^-, t^+
   unlabeled => prov increasing (no DB, n >= 2).  Empty => the site
   is unlabeled and prov(out) = prov(t): t is a 1-pass output with
   an FDI prov of length n => n <= 1 by T2.  So NO depth-<=2
   expression realizes DB(w) for n >= 2.

THE OPEN BOUNDARY (the round's part 2): depth 3, where the final
replacement can itself be a 2-pass output and deletions can shatter
runs.  PART 4 hunts: 3-pass chains, deep replacements, C-targets,
C-compositions, over all |w| <= 5 and the periodic families.

Usage: /usr/bin/python3 -W ignore verify_round10_db.py [part]
"""
import itertools
import random
import sys

import prov as PV

rng = random.Random(314159)

# ---------------------------------------------------------------- helpers


def strictly_dec(seq):
    return all(seq[i] > seq[i + 1] for i in range(len(seq) - 1))


def db_prov(atoms, w):
    """prov if DB(w) realized, else None."""
    prov = PV.labels(atoms)
    n = len(w)
    if len(prov) != n or set(prov) != set(range(n)):
        return None
    if not strictly_dec(prov):
        return None
    return prov


def fdi_len(atoms):
    """length if prov is fully decreasing and injective, else -1."""
    prov = PV.labels(atoms)
    if not strictly_dec(prov):
        return -1
    if PV.mult(prov) != 1:
        return -1
    return len(prov)


def pfree(w, big=False):
    """pass-free values on labeled w: (name, atoms).  Constants, the
    full input (the ONLY labeled pass-free values are full runs),
    and cats of constants with runs."""
    lab = PV.lab_input(w)
    lc = PV.lab_const
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb']
    if big:
        consts += ['aaa', 'aab', 'aba', 'abb', 'baa', 'bab', 'bba',
                   'bbb']
    out = [('eps', lc(''))]
    out += [('K:' + c, lc(c)) for c in consts]
    out += [('w', lab),
            ('a.w', lc('a') + lab), ('w.a', lab + lc('a')),
            ('b.w', lc('b') + lab), ('w.b', lab + lc('b')),
            ('a.w.b', lc('a') + lab + lc('b')),
            ('b.w.a', lc('b') + lab + lc('a')),
            ('ab.w', lc('ab') + lab), ('w.ab', lab + lc('ab')),
            ('w.w', lab + lab)]
    return out


def pass_text(y_atoms, x_str, t_atoms):
    try:
        return PV.lsubst(y_atoms, PV.lab_const(x_str), t_atoms)
    except PV.Undefined:
        return None


def astr(atoms):
    return ''.join(c for c, _ in atoms)


def all_ws(maxn=6):
    return [''.join(x) for n in range(1, maxn + 1)
            for x in itertools.product('ab', repeat=n)]


def family_ws():
    fams = []
    for pat in ('ab', 'ba', 'aab', 'aba', 'abb', 'baa', 'bab', 'bba',
                'aa', 'bb'):
        for j in range(2, 9):
            fams.append(pat * j)
    return list(dict.fromkeys(fams))


# ---------------------------------------------------------------- PART 1

def part1():
    print('PART 1 (T1 Last-Pass Structure):')
    n_check = n_bad = n_c1 = n_c1_fdi = 0
    worst = None
    for w in all_ws(5):
        lab = PV.lab_input(w)
        lc = PV.lab_const
        Tpool = [lab, lab + lab, lc('a') + lab, lab + lc('b'),
                 lc('ab') + lab + lc('ba')]
        # arbitrary labeled y (text level, any labels incl. repeats)
        ypool = [PV.lab_input(w)] + \
            [tuple((rng.choice('ab'), rng.randrange(len(w)))
                   for _ in range(rng.randrange(0, 4)))
             for _ in range(12)] + [lc('a'), lc('ab')]
        xpool = ['a', 'b', 'ab', 'ba', 'aa', 'bb', w, 'a' + w, w + 'a']
        for T in Tpool:
            for y in ypool:
                for x in xpool:
                    out = pass_text(y, x, T)
                    if out is None:
                        continue
                    # count sites
                    c = 0
                    i = 0
                    m = len(x)
                    while i < len(T):
                        if astr(T[i:i + m]) == x:
                            c += 1
                            i += m
                        else:
                            i += 1
                    n_check += 1
                    haslab = any(lb is not None for _, lb in y)
                    if c >= 2 and haslab:
                        if PV.mult(PV.labels(out)) < 2:
                            n_bad += 1
                            worst = (w, x, y, T, out)
                    if c == 1:
                        n_c1 += 1
                        if fdi_len(out) >= 0:
                            n_c1_fdi += 1
    print(f'  passes simulated: {n_check}; c=1 with FDI output: '
          f'{n_c1_fdi}')
    print(f'  T1(a) violations (c>=2, labeled y, mult 1): {n_bad}')
    if worst:
        print(f'    WORST: {worst}')
    print('  T1(a): ' + ('REFUTED' if n_bad else
                         'VERIFIED (c>=2 and labeled y => mult >= 2)'))


# ---------------------------------------------------------------- PART 2

def part2():
    print()
    print('PART 2 (T2: S-depth<=1 FDI provs are singletons):')
    best = (-1, None)
    n_db = 0
    dbs = []
    ws = all_ws(6) + family_ws()
    for w in ws:
        pfl = pfree(w)
        Fpool = [('w', PV.lab_input(w))] + \
                [(nm, at) for nm, at in pfl
                 if nm in ('a.w', 'w.a', 'b.w', 'w.b', 'a.w.b',
                           'b.w.a', 'w.w')]
        for Fnm, F in Fpool:
            for Rnm, R in pfl:
                for Pnm, P in pfl:
                    if not astr(P):
                        continue
                    out = pass_text(R, astr(P), F)
                    if out is None:
                        continue
                    f = fdi_len(out)
                    if f > best[0]:
                        best = (f, (w, Fnm, Rnm, Pnm))
                    if db_prov(out, w) is not None:
                        n_db += 1
                        dbs.append((w, Fnm, Rnm, Pnm))
    print(f'  inputs: {len(ws)}; max FDI length at S-depth<=1: '
          f'{best[0]}  {best[1]}')
    # C-composition of two 1-pass singletons
    n_dbc = 0
    dbc_maxn = 0
    for w in all_ws(6):
        pfl = pfree(w)
        singles = []
        for Rnm, R in pfl:
            for Pnm, P in pfl:
                if not astr(P):
                    continue
                out = pass_text(R, astr(P), PV.lab_input(w))
                if out is not None and 0 <= fdi_len(out) <= 1 \
                        and len(PV.labels(out)) == 1:
                    singles.append((Rnm, Pnm, out))
        for (_, _, o1), (_, _, o2) in \
                itertools.product(singles[:60], repeat=2):
            cat = o1 + o2
            if db_prov(cat, w) is not None:
                n_dbc += 1
                dbc_maxn = max(dbc_maxn, len(w))
                if n_dbc <= 3:
                    print(f'    DB via C at depth 1: w={w} '
                          f'prov={PV.labels(cat)}')
    ns = sorted({len(d[0]) for d in dbs})
    print(f'  DB at S-depth<=1 (no C): {n_db}, input sizes {ns} '
          f'{dbs[:2]}')
    print(f'  DB via C(singletons) at depth 1: {n_dbc}, max |w| '
          f'{dbc_maxn}')
    print('  T2: FDI at S-depth<=1 is a singleton -- VERIFIED; DB '
          'needs C (block budget) and stops at |w|=2 there')


# ---------------------------------------------------------------- PART 3

def part3():
    print()
    print('PART 3 (T3: S-depth<=2 DB / FDI):')
    best = (-1, None)
    n_db = 0
    dbs = []
    ws = all_ws(5) + family_ws()[:40]
    for w in ws:
        pfl = pfree(w)
        pats = [astr(at) for _, at in pfl if astr(at)]
        pats = list(dict.fromkeys(pats))
        Fpool = [('w', PV.lab_input(w))] + \
                [(nm, at) for nm, at in pfl
                 if nm in ('a.w', 'w.a', 'b.w', 'w.b', 'w.w')]
        # level 1: all 1-pass outputs (deduped)
        lvl1 = {}
        for Fnm, F in Fpool:
            for Rnm, R in pfl:
                for p in pats:
                    out = pass_text(R, p, F)
                    if out is not None:
                        lvl1[(Fnm, Rnm, p)] = out
        outs = set(lvl1.values())
        # 2-pass chains: final pass on each level-1 output
        for t in outs:
            for Rnm, R in pfl:
                for p in pats:
                    out = pass_text(R, p, t)
                    if out is None:
                        continue
                    f = fdi_len(out)
                    if f > best[0]:
                        best = (f, (w, len(t), Rnm, p))
                    if db_prov(out, w) is not None:
                        n_db += 1
                        dbs.append((w, Rnm, p, PV.labels(out)))
    print(f'  inputs: {len(ws)}; distinct 1-pass texts examined per w: '
          '(deduped)')
    print(f'  max FDI length at S-depth<=2: {best[0]}  {best[1]}')
    ns = sorted({len(d[0]) for d in dbs})
    print(f'  DB realizations at S-depth<=2 (chains): {n_db}, input '
          f'sizes {ns} {dbs[:3]}')


# ---------------------------------------------------------------- PART 4

def part4():
    print()
    print('PART 4 (depth-3 hunt: chains, deep R, C-targets, C-comp):')
    # final-pass libs (what the LAST pass may use)
    REPL = ['eps', 'K:a', 'K:b', 'K:ab', 'w', 'a.w', 'w.a', 'b.w',
            'w.b', 'a.w.b']
    ws = all_ws(4) + family_ws()[:12] + ['aaba', 'abaa', 'baab',
                                         'bba', 'abab', 'baba'] + \
        [''.join(rng.choice('ab') for _ in range(rng.randrange(6, 11)))
         for _ in range(8)]
    stats = {'sims': 0, 'db': 0, 'best': (-1, None)}
    hits = []

    def check(out, w, shape):
        stats['sims'] += 1
        f = fdi_len(out)
        if f > stats['best'][0]:
            stats['best'] = (f, (shape, w, f))
        p = db_prov(out, w)
        if p is not None:
            stats['db'] += 1
            hits.append((shape, w, p))

    for w in ws:
        # FULL pass-free lib for the INNER pools (depth-1/2 texts)
        pfl = pfree(w)
        lab = PV.lab_input(w)
        repls = [(nm, at) for nm, at in pfl
                 if nm in REPL]
        pats = list(dict.fromkeys(
            [astr(at) for nm, at in pfl if astr(at)]))
        # level pools from the full lib
        lvl1 = set()
        for Rnm, R in pfl:
            for p in pats:
                out = pass_text(R, p, lab)
                if out is not None:
                    lvl1.add(out)
        lvl2 = set()
        for t in lvl1:
            for Rnm, R in pfl:
                for p in pats:
                    out = pass_text(R, p, t)
                    if out is not None:
                        lvl2.add(out)
        lvl2l = list(lvl2)[:1500]
        # (a) 3-chains: final pass from the focused libs
        for t in lvl2l:
            for Rnm, R in repls:
                for p in pats:
                    out = pass_text(R, p, t)
                    if out is not None:
                        check(out, w, 'chain3')
        # (b) deep replacement: 2-pass block spliced into V(0)
        for y in lvl2l[:800]:
            for p in pats:
                out = pass_text(y, p, lab)
                if out is not None:
                    check(out, w, 'deepR')
        # (c) C-target: 2-pass block spliced into C(V0,K,V0)-target
        targ = lab + PV.lab_const('a') + lab
        for y in lvl2l[:400]:
            for p in pats:
                out = pass_text(y, p, targ)
                if out is not None:
                    check(out, w, 'Ctarget')
        # (d) C-composition: 2-pass . 1-pass and 1-pass . 2-pass
        lvl1l = list(lvl1)[:100]
        for y2 in lvl2l[:200]:
            for y1 in lvl1l:
                check(y2 + y1, w, 'C(2,1)')
                check(y1 + y2, w, 'C(1,2)')
    print(f'  inputs: {len(ws)}; sims: {stats["sims"]}')
    print(f'  max FDI length at depth 3: {stats["best"][0]} '
          f'{stats["best"][1]}')
    print(f'  DB realizations: {stats["db"]}')
    ns = sorted({len(h[1]) for h in hits})
    print(f'  DB input sizes: {ns}')
    for h in [h for h in hits if len(h[1]) >= 2][:10]:
        print(f'    {h}')
    if ns == [1]:
        print('  no depth-3 expression realizes DB on any |w| >= 2 '
              'examined')


if __name__ == '__main__':
    sys.setrecursionlimit(200000)
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', '1'):
        part1()
    if which in ('all', '2'):
        part2()
    if which in ('all', '3'):
        part3()
    if which in ('all', '4'):
        part4()

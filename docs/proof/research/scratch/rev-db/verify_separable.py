"""SEPARABLE-REGIME VERIFICATION BATTERY (round DB, part 1: Python).

THEOREM UNDER TEST (Separable Rigidity, hand proof in REPORT.md sec 2):
  For every expression E (ANY S-depth) and every input w whose characters
  are pairwise distinct and disjoint from Gamma(E), |w| = n:
    (a) content [[E]]w = v0 w v1 w ... w vM   (v_j in Gamma(E)*, full
        FORWARD copies of w only -- never a piece, never a reversed copy);
    (b) prov(E,w) = (0,1,...,n-1)^M  (M = surviving copy count);
    (c) for n >= 2: prov is never DB (never even FDI) and E(w) != rev(w).

The proof's ENGINE is the copy-alignment invariant: every pass's match
windows cover whole instances (never cut one).  Part C instruments exactly
that, atom by atom, and cross-checks against prov.py's independent lden.

Parts:
  A  random expressions (S-depth <= 4, all shapes incl. deep R/P) x
     random separable inputs -> (a),(b),(c).
  B  targeted adversarial expressions (piece-makers, glued-copy patterns,
     deep patterns/replacements, chains to depth 6, the round-10/11/13
     witness shapes, two-level scaffolds) x separable inputs n=2..6.
  C  instrumented evaluator with instance ids: every match window covers
     whole instances; every instance always spells w with labels 0..n-1;
     final content+prov cross-checked against lden on EVERY case.
  D  is folded into B (route-b falsification: DB/rev hit counters).

Run:  /usr/bin/python3 -W ignore verify_separable.py   (from this dir)
"""
import random
import re
import sys

from prov import lden, labels, content, lab_input, Undefined
from lcore import K, V, C, S

X = V(0)


def c3(a, b, c):
    return C(C(a, b), c)


def c4(a, b, c, d):
    return C(C(C(a, b), c), d)


def c5(a, b, c, d, e):
    return C(C(C(C(a, b), c), d), e)


def chain(passes, F):
    """passes in PAPER order (leftmost applies LAST): builds
    [R1/P1][R2/P2]...[Rk/Pk]F  with Pk applied first."""
    acc = F
    for (R, P) in reversed(passes):
        acc = S(R, P, acc)
    return acc


# --------------------------------------------------------------------------
# checks of (a),(b),(c)

def block_form_ok(prov, n):
    """prov == (0..n-1)^M ?"""
    if n == 0:
        return len(prov) == 0
    if len(prov) % n:
        return False
    R = tuple(range(n))
    return tuple(prov) == R * (len(prov) // n)


def const_letters(e):
    t = e[0]
    if t == 'K':
        return e[1]
    if t == 'V':
        return ''
    if t == 'C':
        return const_letters(e[1]) + const_letters(e[2])
    if t == 'S':
        return (const_letters(e[1]) + const_letters(e[2]) +
                const_letters(e[3]))
    raise ValueError(t)


def gamma_regex(e, w):
    letters = sorted(set(const_letters(e)))
    if not letters:
        letters = ['a']          # no constants: any gamma is fine
    g = ''.join(letters)
    return re.compile('[%s]*(?:%s[%s]*)*' % (g, re.escape(w), g))


# --------------------------------------------------------------------------
# Part A: random expressions

def rand_expr(depth, rng, size_cap, gamma='ab'):
    """random AST with S-depth <= depth; returns (expr, nodes_used)."""
    r = rng.random()
    if size_cap[0] <= 0 or depth < 0 or (depth == 0 and r < 0.55):
        if rng.random() < 0.45:
            s = ''.join(rng.choice(gamma) for _ in range(rng.randint(0, 3)))
            return K(s), 1
        return X, 1
    size_cap[0] -= 1
    if depth == 0 or r < 0.25:
        k = rng.randint(2, 3)
        parts = []
        tot = 0
        for _ in range(k):
            e, u = rand_expr(0, rng, size_cap, gamma)
            parts.append(e)
            tot += u
        acc = parts[0]
        for p in parts[1:]:
            acc = C(acc, p)
        return acc, tot
    t = rng.random()
    if t < 0.5:
        e1, u1 = rand_expr(depth, rng, size_cap, gamma)
        e2, u2 = rand_expr(depth, rng, size_cap, gamma)
        return C(e1, e2), 1 + u1 + u2
    R, u1 = rand_expr(depth - 1, rng, size_cap, gamma)
    P, u2 = rand_expr(depth - 1, rng, size_cap, gamma)
    F, u3 = rand_expr(depth - 1, rng, size_cap, gamma)
    return S(R, P, F), 1 + u1 + u2 + u3


def rand_separable(rng, nmax=7):
    pool = 'cdefghijkl'
    n = rng.randint(2, nmax)
    return ''.join(rng.sample(pool, n))


def check_case(e, w, tag, stats, echo=True):
    """None if undefined, else True/False (False = violation)."""
    try:
        val = lden(e, (lab_input(w),))
    except Undefined:
        stats['undef'] += 1
        return None
    stats['defined'] += 1
    n = len(w)
    prov = tuple(labels(val))
    cont = content(val)
    okB = block_form_ok(prov, n)
    okF = gamma_regex(e, w).fullmatch(cont) is not None
    isdb = n >= 2 and prov == tuple(range(n - 1, -1, -1))
    isrev = cont == w[::-1]
    isfdi = (len(prov) >= 2 and all(prov[i] > prov[i + 1]
                                    for i in range(len(prov) - 1)))
    stats['fdi_len2plus'] += (1 if isfdi else 0)
    if not okB:
        stats['bad_prov'] += 1
        if echo:
            print(f'  VIOLATION prov-block {tag} n={n} w={w} prov={prov}')
    if not okF:
        stats['bad_form'] += 1
        if echo:
            print(f'  VIOLATION content-form {tag} n={n} w={w} '
                  f'cont={cont[:60]}')
    if isdb:
        stats['db_hits'] += 1
        if echo:
            print(f'  VIOLATION DB {tag} n={n} w={w} prov={prov}')
    if isrev:
        stats['rev_hits'] += 1
        if echo:
            print(f'  VIOLATION rev {tag} n={n} w={w} cont={cont[:60]}')
    return okB and okF and not isdb and not isrev


# --------------------------------------------------------------------------
# Part C: instrumented evaluator with instance tracking

class Iatom:
    __slots__ = ('c', 'lab', 'iid')

    def __init__(self, c, lab, iid):
        self.c = c
        self.lab = lab
        self.iid = iid


def check_instances(val, win, stats):
    """every iid != -1: atoms contiguous, spell w, labels 0..n-1 in order;
    constants unlabeled."""
    n = len(win)
    first, last, cnt = {}, {}, {}
    for idx, a in enumerate(val):
        if a.iid == -1:
            if a.lab is not None:
                stats['bad_const_label'] += 1
            continue
        if a.iid not in first:
            first[a.iid] = idx
            cnt[a.iid] = 0
        last[a.iid] = idx
        cnt[a.iid] += 1
    for iid, f in first.items():
        if last[iid] - f != cnt[iid] - 1:
            stats['split_instances'] += 1
        seg = val[f:f + cnt[iid]]
        if ([a.c for a in seg] != [b.c for b in win] or
                [a.lab for a in seg] != list(range(n))):
            stats['bad_instances'] += 1


def ldenI(e, win, fresh, stats):
    """instrumented denotation; win = Iatoms of the input (one instance).
    Checks match windows for whole-instance coverage at every pass."""
    t = e[0]
    if t == 'K':
        return [Iatom(c, None, -1) for c in e[1]]
    if t == 'V':
        fresh[0] += 1
        return [Iatom(a.c, a.lab, fresh[0]) for a in win]
    if t == 'C':
        return (ldenI(e[1], win, fresh, stats) +
                ldenI(e[2], win, fresh, stats))
    if t == 'S':
        R, P, F = e[1], e[2], e[3]
        Tv = ldenI(F, win, fresh, stats)
        Pv = ldenI(P, win, fresh, stats)
        if not Pv:
            raise Undefined()
        Rv = ldenI(R, win, fresh, stats)
        check_instances(Tv, win, stats)
        pn = len(Pv)
        out = []
        i, tn = 0, len(Tv)
        while i < tn:
            ok = (i + pn <= tn and
                  all(Tv[i + k].c == Pv[k].c for k in range(pn)))
            if ok:
                # COPY-ALIGNMENT: window [i, i+pn) must not cut an INSTANCE
                # (iid >= 0).  Constant runs (iid = -1) are freely cuttable.
                if i > 0 and Tv[i].iid >= 0 and Tv[i - 1].iid == Tv[i].iid:
                    stats['cut_windows'] += 1
                if (i + pn < tn and Tv[i + pn - 1].iid >= 0 and
                        Tv[i + pn].iid == Tv[i + pn - 1].iid):
                    stats['cut_windows'] += 1
                stats['windows'] += 1
                remap = {}
                for a in Rv:
                    if a.iid == -1:
                        out.append(Iatom(a.c, None, -1))
                    else:
                        if a.iid not in remap:
                            fresh[0] += 1
                            remap[a.iid] = fresh[0]
                        out.append(Iatom(a.c, a.lab, remap[a.iid]))
                i += pn
            else:
                out.append(Tv[i])
                i += 1
        check_instances(out, win, stats)
        return out
    raise ValueError(t)


def run_part_C(rng, trials, stats):
    for _ in range(trials):
        e, _ = rand_expr(rng.randint(0, 4), rng, [12])
        w = rand_separable(rng, 6)
        win = lab_input(w)
        try:
            valI = ldenI(e, [Iatom(c, i, 0) for c, i in win], [0], stats)
        except Undefined:
            stats['undefI'] += 1
            continue
        gotI = ''.join(a.c for a in valI)
        provI = tuple(a.lab for a in valI if a.lab is not None)
        try:
            val = lden(e, (win,))
        except Undefined:
            stats['cross_mismatch_undef'] += 1
            continue
        got = content(val)
        prov = tuple(labels(val))
        if got != gotI or prov != provI:
            stats['cross_mismatch'] += 1
            print(f'  CROSS-MISMATCH n={len(w)} w={w}: '
                  f'{gotI[:40]!r} vs {got[:40]!r}')
        if not block_form_ok(provI, len(w)):
            stats['bad_prov'] += 1
            print(f'  VIOLATION prov-block (C) n={len(w)} w={w} '
                  f'prov={provI}')


# --------------------------------------------------------------------------
# Part B/D: targeted adversarial expressions

def adversarial():
    """(tag, expr) -- all run on separable inputs n = 2..6."""
    A, B, E = K('a'), K('b'), K('')
    WAW = c3(X, A, X)
    WAWAW = c5(X, A, X, A, X)
    return [
        # piece-makers: patterns that would cut an instance if the
        # invariant failed
        ('glue-then-cut', S(E, A, WAW)),                    # [eps/a](waw)
        ('cut-with-ww', S(C(X, X), C(X, X), S(E, A, WAW))),
        ('cut-with-wa', S(C(X, A), C(X, A), S(E, A, WAW))),
        ('cut-with-aw', S(C(A, X), C(A, X), S(E, A, WAW))),
        ('cut-with-awa', S(c3(A, X, A), c3(A, X, A), S(E, A, WAW))),
        ('deep-piece-pat', S(S(E, A, WAW), C(X, A), WAWAW)),
        # round-10 chain3 witness shapes (REPORT 10.7)
        ('r10-chain3-shape', chain([(E, K('aba')), (E, K('abbab')),
                                    (X, B)],
                                   c3(K('a'), X, K('b')))),
        ('r10-chain3-shape2', chain([(E, K('bbb')), (E, K('bab')),
                                     (C(X, K('ab')), K('a'))],
                                    C(X, K('ab')))),
        # round-11 n=2 witness shape (REPORT 11.5):
        #   [eps/(w.b.w)].[(ab.w.ba)/b](b.w.a.w.b)
        ('r11-witness-shape', chain([(E, c3(X, B, X)),
                                     (c3(K('ab'), X, K('ba')), B)],
                                    c5(B, X, K('a'), X, B))),
        # round-13 E_swap
        ('r13-E_swap', S(B, X, c3(S(E, B, X), B, S(E, B, X)))),
        # deep replacement bearing copies, many sites
        ('deepR-many-sites', S(S(X, A, WAW), A, WAWAW)),
        # deep pattern: pattern value = depth-1 value (copies, const deleted)
        ('deepP-copyval', S(WAW, S(E, A, WAW), WAWAW)),
        # two-level scaffold attempts (route b): outer pass whose pattern
        # and replacement are depth-1 values over a depth-1 scrutinee
        ('scaffold', S(S(E, A, WAW), C(X, X), S(X, A, WAWAW))),
        ('scaffold2', S(S(X, A, WAW), C(X, X), S(E, A, WAWAW))),
        ('scaffold3', S(S(E, A, WAW), S(E, A, C(X, X)), S(X, A, WAW))),
        # long chains, depth 6
        ('chain6', chain([(X, A)] * 6, WAW)),
        ('chain6-del', chain([(E, A)] + [(X, A)] * 5, WAW)),
        # C-compositions mixing branch depths
        ('Cmix', C(S(X, A, WAW), S(S(E, A, C(X, X)), C(X, X), C(X, X)))),
        # constant-pattern chains editing only the glue
        ('const-edit', chain([(K('ab'), K('a')), (E, B)],
                             c5(X, K('bb'), X, B, X))),
        # replacement = input; pattern = full input (single site)
        ('selfreplace', S(X, X, WAW)),
        # duplicating deep chains
        ('dup', S(S(X, X, C(X, X)), X, C(C(X, X), C(X, X)))),
    ]


# --------------------------------------------------------------------------

def main():
    rng = random.Random(20260922)
    stats = {k: 0 for k in
             ('defined', 'undef', 'bad_prov', 'bad_form', 'db_hits',
              'rev_hits', 'fdi_len2plus', 'cut_windows', 'windows',
              'split_instances', 'bad_instances', 'bad_const_label',
              'undefI', 'cross_mismatch', 'cross_mismatch_undef')}

    NA = 4000
    for t in range(NA):
        e, _ = rand_expr(rng.randint(0, 4), rng, [11])
        w = rand_separable(rng, 7)
        check_case(e, w, f'A#{t}', stats)
    print(f'[A] random (depth 0-4): {NA} trials, defined {stats["defined"]}, '
          f'undef {stats["undef"]}, bad_prov {stats["bad_prov"]}, '
          f'bad_form {stats["bad_form"]}, DB {stats["db_hits"]}, '
          f'rev {stats["rev_hits"]}, FDI(len>=2) {stats["fdi_len2plus"]}')

    # Part A2: deep random expressions, S-depth 5-8 (the theorem is
    # all-depths; size caps keep values bounded)
    pre = dict(stats)
    NA2 = 1500
    for t in range(NA2):
        e, _ = rand_expr(rng.randint(5, 8), rng, [13])
        w = rand_separable(rng, 5)
        check_case(e, w, f'A2#{t}', stats)
    print(f'[A2] random (depth 5-8): {NA2} trials, defined '
          f'{stats["defined"] - pre["defined"]}, undef '
          f'{stats["undef"] - pre["undef"]}, bad_prov {stats["bad_prov"]}, '
          f'bad_form {stats["bad_form"]}, DB {stats["db_hits"]}, '
          f'rev {stats["rev_hits"]}')

    # Part A3: bigger constant alphabet Gamma = {a,b,z} -- the theorem
    # treats Gamma uniformly; this exercises it.  Inputs avoid {a,b,z}.
    pre = dict(stats)
    NA3 = 1200
    pool2 = 'efghijkl'
    for t in range(NA3):
        e, _ = rand_expr(rng.randint(0, 6), rng, [12], gamma='abz')
        n_ = rng.randint(2, 6)
        w = ''.join(rng.sample(pool2, n_))
        check_case(e, w, f'A3#{t}', stats)
    print(f'[A3] random (Gamma={{a,b,z}}, depth 0-6): {NA3} trials, '
          f'defined {stats["defined"] - pre["defined"]}, undef '
          f'{stats["undef"] - pre["undef"]}, bad_prov {stats["bad_prov"]}, '
          f'bad_form {stats["bad_form"]}, DB {stats["db_hits"]}, '
          f'rev {stats["rev_hits"]}')

    ex = adversarial()
    nb = 0
    for tag, e in ex:
        for n in range(2, 7):
            w = 'cdefgh'[:n]
            r = check_case(e, w, f'B:{tag}', stats)
            nb += 1
            if r is False:
                print(f'    (adversarial case failed: {tag} n={n})')
    print(f'[B] adversarial: {len(ex)} expressions x 5 lengths = {nb} '
          f'trials; cumulative bad_prov {stats["bad_prov"]}, bad_form '
          f'{stats["bad_form"]}, DB {stats["db_hits"]}, '
          f'rev {stats["rev_hits"]}')

    run_part_C(rng, 2500, stats)
    print(f'[C] instrumented: 2500 trials, {stats["windows"]} match '
          f'windows fired, cut_instances {stats["cut_windows"]}, '
          f'split_instances {stats["split_instances"]}, bad_instances '
          f'{stats["bad_instances"]}, bad_const_label '
          f'{stats["bad_const_label"]}, cross_mismatch '
          f'{stats["cross_mismatch"]} (+{stats["cross_mismatch_undef"]} '
          f'undef-mismatches)')

    tot = (stats['bad_prov'] + stats['bad_form'] + stats['db_hits'] +
           stats['rev_hits'] + stats['cut_windows'] +
           stats['split_instances'] + stats['bad_instances'] +
           stats['bad_const_label'] + stats['cross_mismatch'] +
           stats['cross_mismatch_undef'])
    print()
    print(f'TOTAL VIOLATIONS: {tot}')
    print('VERDICT:', 'ALL CLEAN -- theorem (a),(b),(c) and the '
          'copy-alignment engine hold on this domain'
          if tot == 0 else 'VIOLATIONS FOUND')
    return 0 if tot == 0 else 1


if __name__ == '__main__':
    sys.exit(main())

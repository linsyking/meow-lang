"""ROUND 11 spot-checks: the lemmas of REPORT.md sec 11 / the fragment.

Part 1 -- Replacement elimination (the nu = 0 lemma).  In the chain2 shape
    [yf/xf].[Y/xp].F with yf LABELED (a pass-free value with nu = #V >= 1),
    an FDI output with exactly c = 1 site forces prov(yf) = R^nu to be an
    FDI block, impossible for n >= 2.  Checked: FDI outputs with c = 1 and
    yf labeled must not exist (n >= 2).  Cross-checks: T1(a) -- FDI with
    c >= 2 and yf labeled must not exist either; DB hits anywhere: none.
    (v3, round-12 repair 3: the old "label-free c = 1" count was DEAD CODE
    -- yf was drawn only from the labeled sub-library, so the count was
    structurally 0 and the c = 1 check was not demonstrated live.  Part 1
    is now two modes: '1' = elimination (unchanged sweep, yf labeled);
    '1c' = the LIVE CONTROL -- yf drawn from the FULL pass-free library
    (25 forms vs 10 labeled), which must yield MANY FDI outputs with
    c = 1 and a label-free final replacement and still ZERO with c = 1
    and a labeled one.  Control domain reduced to all |w| <= 3 plus
    abab/abba so the widened 2.5x library still fits in 60 s.)

Part 2 -- Frame (alpha)/(beta).  For every FDI output of the chain
    [eps/xf].[Y/xp].F with beta = |xf| >= n, every surviving labeled atom
    in a w-run of an INSERTED COPY at interior offset o (1 <= o <= n-2)
    satisfies
        (alpha)  xf[-o:]  == w[:o]        (the left match ends at the pick)
        (beta)   xf[:n-1-o] == w[o+1:]    (the right match starts at q+1)
    and any two interior copy-picks at offsets o, o+1 force w to be
    constant on [0,o] and on [o+1,n-1] (the break lemma).  NOTE: on the
    domain no output happens to carry two interior copy-picks at adjacent
    offsets, so the break COMPOSITION is not directly exercised; each of
    its two factors (alpha/beta at a single offset) is.  (v2 fix: the
    BREAK-R comparison was length-mismatched and could never fire; it
    now checks constancy on [o+1, n-1] directly.)

Part 3 -- B-rigidity.  For uniform w = a^k, FDI output, beta >= n, xf
    having >= 2 maximal a-runs and starting and ending with an a-run
    (e_0 = e_last = empty): every interior copy-pick at t-position q sits
    in a maximal a-run of t equal to exactly [q - lam_last, q + lam_1 + 1).

Part 4 -- the step-(2) kills of Theorem 3, on uniform w = a^k: every FDI
    output with beta >= n that HAS an interior copy-pick must have a
    final pattern starting AND ending with 'a' and containing a non-'a'
    char (contrapositive of: X[0] != a and X[-1] != a contradict the
    frames; X = a^beta makes the greedy check at the pick's own position
    succeed and delete it).

Each part runs in well under 60 s; run them separately if preferred.
Usage:
    /usr/bin/python3 -W ignore verify_round11.py [1|1c|2|3|4|all]
    (1c is the round-12 live control for part 1; 'all' skips it so that
    no single invocation exceeds 60 s.)
"""
import itertools
import sys

import prov as PV


def pfree(w):
    lab = PV.lab_input(w)
    lc = PV.lab_const
    consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'aba',
              'abb', 'baa', 'bab', 'bba', 'bbb']
    out = [('eps', lc(''))] + [('K:' + c, lc(c)) for c in consts]
    out += [('w', lab), ('a.w', lc('a') + lab), ('w.a', lab + lc('a')),
            ('b.w', lc('b') + lab), ('w.b', lab + lc('b')),
            ('a.w.b', lc('a') + lab + lc('b')),
            ('b.w.a', lc('b') + lab + lc('a')),
            ('ab.w', lc('ab') + lab), ('w.ab', lab + lc('ab')),
            ('w.w', lab + lab)]
    return out


def tagged_f(w, r):
    return [(c, i, r) for i, c in enumerate(w)]


def copy_atoms(Y, ctr):
    out = []
    prev = None
    j = -1
    for (c, l) in Y:
        if l is None:
            out.append(((c, None), ('copy', ctr, None)))
            prev = None
            continue
        if prev is None or l <= prev:
            j += 1
        out.append(((c, l), ('copy', ctr, j)))
        prev = l
    return out


def inner_pass(F, xp, Y):
    m = len(xp)
    t = []
    i, n = 0, len(F)
    ctr = 0
    last_run, slice_id = None, {}
    while i < n:
        if ''.join(a[0] for a in F[i:i + m]) == xp:
            ctr += 1
            t.extend(copy_atoms(Y, ctr))
            last_run = None
            i += m
        else:
            c, l, r = F[i]
            if r != last_run:
                slice_id[r] = slice_id.get(r, 0) + 1
                last_run = r
            t.append(((c, l), ('slice', r, slice_id[r])))
            i += 1
    return t


def final_pass(pat, t, repl):
    """greedy [repl/pat] on t, tracking t-indices; repl = atom list or
    None for deletion.  Returns (out, tidx, nmatch)."""
    m = len(pat)
    out, tidx = [], []
    i, n = 0, len(t)
    nm = 0
    while i < n:
        if ''.join(a[0][0] for a in t[i:i + m]) == pat:
            nm += 1
            if repl is not None:
                out.extend(repl)
            i += m
        else:
            out.append(t[i])
            tidx.append(i)
            i += 1
    return out, tidx, nm


def is_fdi(out):
    prov = [a[0][1] for a in out if a[0][1] is not None]
    if not prov or len(set(prov)) != len(prov):
        return None
    if not all(prov[i] > prov[i + 1] for i in range(len(prov) - 1)):
        return None
    return prov


def is_db(prov, n):
    return prov == list(range(n - 1, -1, -1))


def sigma_runs(x, s):
    """maximal s-runs of string x: list of (start, length)."""
    out, i, L = [], 0, len(x)
    while i < L:
        if x[i] == s:
            j = i
            while j < L and x[j] == s:
                j += 1
            out.append((i, j - i))
            i = j
        else:
            i += 1
    return out


def rich_free(w):
    """pass-free forms with two-sided constants (the B-rigidity firings
    need b's on both sides of the runs).  Returns [(name, atoms)]."""
    lab = tuple((c, i) for i, c in enumerate(w))
    lc = PV.lab_const
    return [
        ('w', lab), ('w.w', lab + lab),
        ('b.w', lc('b') + lab), ('w.b', lab + lc('b')),
        ('a.w.b.w.a', lc('a') + lab + lc('b') + lab + lc('a')),
        ('b.w.a.w.b', lc('b') + lab + lc('a') + lab + lc('b')),
        ('w.b.w', lab + lc('b') + lab),
        ('ab.w.ba', lc('ab') + lab + lc('ba')),
        ('ba.w.ab', lc('ba') + lab + lc('ab')),
        ('w.abbaw', lab + lc('abbaw')),
    ]


def rich_tagged(name, atoms):
    """tag a rich pass-free value's atoms with original-run ids."""
    F, ri, prev = [], -1, None
    for (c, l) in atoms:
        if l is not None and prev is None:
            ri += 1
        F.append((c, l, ri if l is not None else -1))
        prev = l
    return F


def part1(mode='elim'):
    ws = [''.join(x) for n in range(2, 5)
          for x in itertools.product('ab', repeat=n)]
    ws += ['ab' * j for j in range(3, 6)] + ['aab' * j for j in range(2, 4)]
    ws = list(dict.fromkeys(ws))
    if mode == 'control':
        # Round-12 repair 3: the LIVE CONTROL.  yf is drawn from the FULL
        # pass-free library (labeled + label-free), so the "c = 1 and
        # label-free" bucket can actually fire; the elimination bucket
        # (c = 1, labeled) must stay 0 on the widened draw as well.
        # Reduced input domain (|w| <= 3 plus abab/abba): the full library
        # is 2.5x the labeled one and the full 33-input sweep would exceed
        # the 60 s budget.
        ws = [w for w in ws if len(w) <= 3] + ['abab', 'abba']
    n_fdi_c1_lab = n_fdi_c1_free = n_fdi_c2_lab = n_db = n_sims = 0
    bad = []
    for w in ws:
        n = len(w)
        pfl = pfree(w)
        pats = [p for p in dict.fromkeys(''.join(c for c, _ in at)
                                         for _, at in pfl) if p]
        Fs = [('w', tagged_f(w, 0)),
              ('a.w', [('a', None, -1)] + tagged_f(w, 0)),
              ('w.a', tagged_f(w, 0) + [('a', None, -1)]),
              ('w.w', tagged_f(w, 0) + tagged_f(w, 1))]
        if mode == 'elim':
            Ys = [(nm, at) for nm, at in pfl
                  if any(l is not None for _, l in at)]
        else:
            Ys = list(pfl)       # the FULL library (25 forms)
        for Fnm, F in Fs:
            for Ynm, Y in Ys:
                for xp in pats:
                    t = inner_pass(F, xp, Y)
                    for xf in pats:
                        for ynm, yf in Ys:
                            repl = [((c, l), ('ins', 0, None))
                                    for (c, l) in yf]
                            out, tidx, c = final_pass(xf, t, repl)
                            n_sims += 1
                            prov = is_fdi(out)
                            if prov is None:
                                continue
                            lab = any(l is not None for _, l in yf)
                            if c == 1 and lab and n >= 2:
                                n_fdi_c1_lab += 1
                                bad.append(('ELIM', w, Fnm, Ynm, xp,
                                            xf, ynm))
                            if c == 1 and not lab:
                                n_fdi_c1_free += 1
                            if c >= 2 and lab:
                                n_fdi_c2_lab += 1   # T1(a) cross-check
                            if is_db(prov, n) and n >= 2:
                                n_db += 1
                                bad.append(('DB', w, Fnm, Ynm, xp, xf,
                                            ynm))
    if mode == 'elim':
        print('PART 1 (replacement elimination, labeled library): '
              '%d sims over %d inputs' % (n_sims, len(ws)))
        print('  FDI outputs with c=1 and labeled final replacement: %d'
              % n_fdi_c1_lab)
        print('  [cross-checks] FDI with c>=2, labeled: %d (T1(a));'
              ' DB hits: %d' % (n_fdi_c2_lab, n_db))
        print('  (the c=1 check is shown LIVE by mode 1c: the same sweep'
              ' with the final replacement drawn from the FULL pass-free'
              ' library yields many c=1 label-free FDI outputs and still'
              ' 0 labeled ones)')
    else:
        print('PART 1c (live control, FULL library incl. label-free): '
              '%d sims over %d inputs' % (n_sims, len(ws)))
        print('  FDI outputs with c=1 and LABELED final replacement: %d'
              % n_fdi_c1_lab)
        print('  FDI outputs with c=1 and LABEL-FREE final replacement:'
              ' %d  <- the c=1 channel is live' % n_fdi_c1_free)
        print('  [cross-checks] FDI with c>=2, labeled: %d (T1(a));'
              ' DB hits: %d' % (n_fdi_c2_lab, n_db))
        live = n_fdi_c1_free > 0
        print('  verdict:', 'VERIFIED' if (not bad and live)
              else 'REFUTED' if bad else 'DEAD CONTROL (no label-free'
              ' c=1 FDI arose -- check the domain)')
        return not bad and live
    for b in bad[:10]:
        print('   ', b)
    print('  verdict:', 'VERIFIED' if not bad else 'REFUTED')
    return not bad


def part2():
    ws = [''.join(x) for n in range(2, 6)
          for x in itertools.product('ab', repeat=n)]
    fams = ['ab' * j for j in range(2, 8)] + ['aab' * j for j in range(2, 5)] + ['bba' * j for j in range(2, 4)]
    ws = list(dict.fromkeys(ws + fams))
    n_fd = n_fire = n_pair = 0
    bad = []
    for w in ws:
        n = len(w)
        rf = rich_free(w)
        pats = [p for p in dict.fromkeys(''.join(c for c, _ in at)
                                         for _, at in rf) if p]
        Fs = [(nm, rich_tagged(nm, at)) for nm, at in rf]
        Ys = [(nm, at) for nm, at in rf
              if any(l is not None for _, l in at)]
        for Fnm, F in Fs:
            for Ynm, Y in Ys:
                for xp in pats:
                    t = inner_pass(F, xp, Y)
                    if not any(tg is not None and tg[0] == 'copy'
                               for _, tg in t):
                        continue
                    for xf in pats:
                        if len(xf) < n:
                            continue     # Frame needs beta >= n
                        out, tidx, c = final_pass(xf, t, None)
                        prov = is_fdi(out)
                        if prov is None:
                            continue
                        n_fd += 1
                        # interior copy-picks: (offset, t-position)
                        ip = []
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None or tg is None \
                                    or tg[0] != 'copy':
                                continue
                            o = at[1]
                            if 1 <= o <= n - 2:
                                ip.append((o, tidx[s]))
                        for o, q in ip:
                            n_fire += 1
                            if xf[-o:] != w[:o]:
                                bad.append(('ALPHA', w, Fnm, Ynm, xp,
                                            xf, o, xf[-o:]))
                            if xf[:n - 1 - o] != w[o + 1:]:
                                bad.append(('BETA', w, Fnm, Ynm, xp,
                                            xf, o, xf[:n - 1 - o]))
                        # break lemma: picks at adjacent offsets
                        offs = sorted(o for o, _ in ip)
                        for i in range(len(offs) - 1):
                            if offs[i + 1] == offs[i] + 1:
                                o = offs[i]
                                n_pair += 1
                                if w[:o + 1] != w[0] * (o + 1):
                                    bad.append(('BREAK-L', w, Fnm, Ynm,
                                                xp, xf, o))
                                if w[o + 1:] != w[o + 1] * (n - 1 - o):
                                    bad.append(('BREAK-R', w, Fnm, Ynm,
                                                xp, xf, o))
    print('PART 2 (frame alpha/beta): FDI outputs with beta>=n: %d'
          % n_fd)
    print('  interior copy-picks checked: %d; adjacent-offset pairs: %d'
          % (n_fire, n_pair))
    for b in bad[:10]:
        print('   ', b)
    print('  violations: %d -- %s' % (len(bad),
                                      'VERIFIED' if not bad else 'REFUTED'))
    return not bad


def part3():
    ws = ['a' * k for k in range(2, 11)]
    n_fd = n_fire = 0
    bad = []
    for w in ws:
        n = len(w)
        rf = rich_free(w)
        consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'aba',
                  'abb', 'baa', 'bab', 'bba', 'bbb', 'aabaa', 'abaa',
                  'aabaabaa', 'abaabaa', 'aabaabaabaa']
        consts += ['ab' * k + 'a' for k in range(1, 7)]
        pats = [p for p in dict.fromkeys([''.join(c for c, _ in at)
                                          for _, at in rf] + consts) if p]
        Fs = [(nm, rich_tagged(nm, at)) for nm, at in rf]
        Ys = [(nm, at) for nm, at in rf
              if any(l is not None for _, l in at)]
        # eligible final patterns: beta >= n, >= 2 maximal a-runs,
        # starting and ending with an a-run (e_0 = e_last = empty)
        elig = []
        for xf in pats:
            if len(xf) < n:
                continue
            runs = sigma_runs(xf, 'a')
            if len(runs) < 2:
                continue
            if runs[0][0] != 0 or runs[-1][0] + runs[-1][1] != len(xf):
                continue
            elig.append((xf, runs[0][1], runs[-1][1]))
        for Fnm, F in Fs:
            for Ynm, Y in Ys:
                for xp in pats:
                    t = inner_pass(F, xp, Y)
                    if not any(tg is not None and tg[0] == 'copy'
                               for _, tg in t):
                        continue
                    txt = ''.join(a[0][0] for a in t)
                    truns = sigma_runs(txt, 'a')
                    runof = {}
                    for st, ln in truns:
                        for p in range(st, st + ln):
                            runof[p] = (st, st + ln)
                    for xf, lam1, lamL in elig:
                        out, tidx, c = final_pass(xf, t, None)
                        prov = is_fdi(out)
                        if prov is None:
                            continue
                        n_fd += 1
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None or tg is None \
                                    or tg[0] != 'copy':
                                continue
                            o = at[1]
                            if not (1 <= o <= n - 2):
                                continue
                            q = tidx[s]
                            if q not in runof:
                                bad.append(('BRIG-nowun', w, Fnm, Ynm,
                                            xp, xf, q, o))
                                continue
                            n_fire += 1
                            st, en = runof[q]
                            if st != q - lamL or en != q + lam1 + 1:
                                bad.append(('BRIG', w, Fnm, Ynm, xp,
                                             xf, q, o, st, en))
    print('PART 3 (B-rigidity, uniform w): eligible FDI outputs: %d'
          % n_fd)
    print('  interior copy-picks checked: %d' % n_fire)
    for b in bad[:10]:
        print('   ', b)
    print('  violations: %d -- %s' % (len(bad),
                                      'VERIFIED' if not bad else 'REFUTED'))
    return not bad


def part4():
    """Step-D kills of Theorem 3, on uniform w = a^k: for every FDI
    chain2 output with beta = |xf| >= n that has an interior copy-pick
    (offset 1 <= o <= n-2), the final pattern must start AND end with
    'a' and contain a non-'a' char.  (Contrapositive of the three kills:
    X[0] != a contradicts frame beta; X[-1] != a contradicts frame
    alpha; X = a^beta makes the greedy check at the pick's own position
    succeed, deleting it.)"""
    ws = ['a' * k for k in range(3, 11)]
    n_fd = n_fire = 0
    bad = []
    for w in ws:
        n = len(w)
        rf = rich_free(w)
        consts = ['a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'aba',
                  'abb', 'baa', 'bab', 'bba', 'bbb', 'aabaa', 'abaa',
                  'aabaabaa', 'abaabaa', 'aabaabaabaa']
        consts += ['ab' * k + 'a' for k in range(1, 7)]
        pats = [p for p in dict.fromkeys([''.join(c for c, _ in at)
                                          for _, at in rf] + consts) if p]
        Fs = [(nm, rich_tagged(nm, at)) for nm, at in rf]
        Ys = [(nm, at) for nm, at in rf
              if any(l is not None for _, l in at)]
        for Fnm, F in Fs:
            for Ynm, Y in Ys:
                for xp in pats:
                    t = inner_pass(F, xp, Y)
                    if not any(tg is not None and tg[0] == 'copy'
                               for _, tg in t):
                        continue
                    for xf in pats:
                        if len(xf) < n:
                            continue      # frames need beta >= n
                        out, tidx, c = final_pass(xf, t, None)
                        prov = is_fdi(out)
                        if prov is None:
                            continue
                        n_fd += 1
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None or tg is None \
                                    or tg[0] != 'copy':
                                continue
                            o = at[1]
                            if not (1 <= o <= n - 2):
                                continue
                            n_fire += 1
                            if xf[0] != 'a':
                                bad.append(('KILL-e0', w, Fnm, Ynm, xp,
                                            xf, o))
                            if xf[-1] != 'a':
                                bad.append(('KILL-eL', w, Fnm, Ynm, xp,
                                             xf, o))
                            if set(xf) == {'a'}:
                                bad.append(('KILL-unif', w, Fnm, Ynm, xp,
                                             xf, o))
                            break     # one firing per output suffices
    print('PART 4 (step-D kills, uniform w): FDI outputs with beta>=n: %d'
          % n_fd)
    print('  outputs with an interior copy-pick: %d' % n_fire)
    for b in bad[:10]:
        print('   ', b)
    print('  violations: %d -- %s' % (len(bad),
                                      'VERIFIED' if not bad else 'REFUTED'))
    return not bad


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', '1'):
        ok &= part1('elim')
    if which in ('1c', 'control'):
        ok &= part1('control')
    if which in ('all', '2'):
        ok &= part2()
    if which in ('all', '3'):
        ok &= part3()
    if which in ('all', '4'):
        ok &= part4()
    if which == 'all':          # keep 'all' under 60 s: control runs apart
        print('  (mode 1c, the live control, runs as a separate '
              'invocation: verify_round11.py 1c)')
    print('ROUND 11 spot-checks:', 'ALL VERIFIED' if ok else 'REFUTED')

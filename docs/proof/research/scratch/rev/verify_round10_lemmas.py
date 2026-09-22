"""ROUND 10 spot-check, v2 (FIXED after the coordinator's verification).

v1 defect (on record): the Sandwich check read its window from the OUTPUT
and its out-adjacency precondition never fired -- VACUOUS.  v2 tracks each
output atom's t-index through the final pass and checks everything in
t-coordinates, per the coordinator's specification:

  Pick:     at most one surviving labeled atom per INSTANCE (one w-run of
            an inserted copy, or one surviving slice of an original run).
            [v1 tagged whole inserted copies; v2 tags w-runs, the form the
            proof needs; the per-copy count is also reported.]
  Slice:    at most one surviving labeled atom per ORIGINAL F1-run.
  Sandwich: survivor at t-position q whose t-predecessor t[q-1] is labeled
            and same-instance  =>  t[q-mF:q] spells the final pattern.
  Mirror:   survivor at t-position q whose t-successor t[q+1] is labeled,
            same-instance, and NOT itself a survivor
                                 =>  t[q+1:q+1+mF] spells the pattern.
  Transport: no two surviving copy-picks (inserted-copy atoms) with the
            text-earlier one at w-offset = the later one's offset + mF.

Domain (unchanged from v1, so the FDI census is comparable): all |w| <= 5
over {a,b} plus periodic families, F in {w, a.w, w.a, b.w, w.b, a.w.b,
w.w}, inner replacement Y in the labeled pf library, inner and final
patterns from the deduped pf pattern pool (depth-2 chain [eps/X].[Y/X']F).
Every output with FDI prov is checked.  Usage:
    /usr/bin/python3 -W ignore verify_round10_lemmas.py
"""
import itertools

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
    """F as atoms with original-run ids: all atoms of run r get r."""
    return [(c, i, r) for i, c in enumerate(w)]


def copy_atoms(Y, ctr):
    """One inserted copy of Y's value, tagged per w-RUN of the copy.

    Y's labeled atoms spell (0,1,...,n-1) repeated #V(Y) times; a new w-run
    starts whenever the label sequence restarts (drop after n-1, or after
    an unlabeled atom).  Constants get tag None (no instance)."""
    out = []
    n = None
    prev = None
    j = -1
    for (c, l) in Y:
        if l is None:
            out.append(((c, None), ('copy', ctr, None)))
            prev = None
            continue
        if n is None:
            n = max(l for (_, ll) in Y if ll is not None) + 1
        if prev is None or l <= prev:
            j += 1
        out.append(((c, l), ('copy', ctr, j)))
        prev = l
    return out


def inner_pass(F, xp, Y):
    """greedy [Y/xp] on tagged F; returns t with per-atom instance tags:
    ('slice', run, k) for surviving original atoms grouped into maximal
    same-run blocks, ('copy', ctr, j) for inserted-copy w-runs."""
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


def final_pass(pat, t):
    """greedy [eps/pat] on t, tracking t-indices of survivors.
    Returns (out, tidx, nmatch)."""
    m = len(pat)
    out, tidx = [], []
    i, n = 0, len(t)
    nm = 0
    while i < n:
        if ''.join(a[0][0] for a in t[i:i + m]) == pat:
            nm += 1
            i += m
        else:
            out.append(t[i])
            tidx.append(i)
            i += 1
    return out, tidx, nm


def run_id(inst):
    """original run of a slice instance, else None."""
    return inst[1] if inst[0] == 'slice' else None


def main():
    ws = [''.join(x) for n in range(2, 6)
          for x in itertools.product('ab', repeat=n)]
    fams = ['ab' * j for j in range(2, 8)] + ['aab' * j for j in range(2, 5)] + ['bba' * j for j in range(2, 4)]
    ws = list(dict.fromkeys(ws + fams))
    n_fd = 0
    fir = dict(sand=0, mir=0, sand_pc=0, mir_pc=0)
    bad = []
    pick_instances = 0
    copy_pick_pairs = 0
    for w in ws:
        pfl = pfree(w)
        pats = list(dict.fromkeys(''.join(c for c, _ in at)
                                  for _, at in pfl if any(
                                      l is not None for _, l in at) or at))
        pats = [p for p in pats if p]
        Fs = [('w', tagged_f(w, 0)),
              ('a.w', [('a', None, -1)] + tagged_f(w, 0)),
              ('w.a', tagged_f(w, 0) + [('a', None, -1)]),
              ('b.w', [('b', None, -1)] + tagged_f(w, 0)),
              ('w.b', tagged_f(w, 0) + [('b', None, -1)]),
              ('a.w.b', [('a', None, -1)] + tagged_f(w, 0)
               + [('b', None, -1)]),
              ('w.w', tagged_f(w, 0) + tagged_f(w, 1))]
        Ys = [(nm, at) for nm, at in pfl
              if any(l is not None for _, l in at)]
        for Fnm, F in Fs:
            for Ynm, Y in Ys:
                for xp in pats:
                    t = inner_pass(F, xp, Y)
                    if not any(tg is not None and tg[0] == 'copy'
                              for _, tg in t):
                        continue  # need copies for the lemma setting
                    for xf in pats:
                        out, tidx, nm = final_pass(xf, t)
                        prov = [a[0][1] for a in out
                                if a[0][1] is not None]
                        if not prov or not all(
                                prov[i] > prov[i + 1]
                                for i in range(len(prov) - 1)):
                            continue  # not FDI
                        if len(set(prov)) != len(prov):
                            continue
                        n_fd += 1
                        mF = len(xf)
                        # ---- Pick: <= 1 survivor per instance (w-run /
                        #      slice); also the stronger per-copy count
                        seen, seen_pc = {}, {}
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None:
                                continue
                            if tg in seen:
                                bad.append(('PICK', w, Fnm, Ynm, xp,
                                            xf, tg))
                            seen[tg] = s
                            pc = ('copy', tg[1]) if tg[0] == 'copy' else tg
                            if pc in seen_pc:
                                bad.append(('PICK-percopy', w, Fnm, Ynm,
                                            xp, xf, pc))
                            seen_pc[pc] = s
                        pick_instances += len(seen)
                        # ---- Slice: <= 1 survivor per ORIGINAL run
                        runs = {}
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None or tg[0] != 'slice':
                                continue
                            r = run_id(tg)
                            if r in runs:
                                bad.append(('SLICE', w, Fnm, Ynm, xp,
                                             xf, r))
                            runs[r] = s
                        # ---- Sandwich (t-based) + mirror
                        sur = set(tidx)
                        for s, (at, tg) in enumerate(out):
                            if at[1] is None:
                                continue
                            q = tidx[s]
                            # same-instance predecessor in t
                            if q >= 1 and t[q - 1][0][1] is not None \
                                    and t[q - 1][1] == tg:
                                fir['sand'] += 1
                                lo = q - mF
                                if lo < 0:
                                    bad.append(('SANDW-nofit', w, Fnm,
                                                Ynm, xp, xf, q))
                                else:
                                    seg = ''.join(a[0][0]
                                                  for a in t[lo:q])
                                    if seg != xf:
                                        bad.append(('SANDW', w, Fnm, Ynm,
                                                    xp, xf, q, seg))
                            pc = ('copy', tg[1]) if tg[0] == 'copy' else tg
                            if q >= 1 and t[q - 1][0][1] is not None \
                                    and (('copy', t[q - 1][1][1])
                                          if t[q - 1][1][0] == 'copy'
                                          else t[q - 1][1]) == pc:
                                fir['sand_pc'] += 1
                            # mirror: same-instance successor, not a survivor
                            if q + 1 < len(t) \
                                    and t[q + 1][0][1] is not None \
                                    and t[q + 1][1] == tg \
                                    and (q + 1) not in sur:
                                fir['mir'] += 1
                                hi = q + 1 + mF
                                if hi > len(t):
                                    bad.append(('MIRR-nofit', w, Fnm,
                                                Ynm, xp, xf, q))
                                else:
                                    seg = ''.join(a[0][0]
                                                  for a in t[q + 1:hi])
                                    if seg != xf:
                                        bad.append(('MIRR', w, Fnm, Ynm,
                                                    xp, xf, q, seg))
                            if q + 1 < len(t) \
                                    and t[q + 1][0][1] is not None \
                                    and (q + 1) not in sur:
                                nxt = t[q + 1][1]
                                npc = ('copy', nxt[1]) if nxt[0] == 'copy' else nxt
                                if npc == pc:
                                    fir['mir_pc'] += 1
                        # ---- Transport pairs: two surviving copy-picks,
                        #      earlier offset = later offset + mF
                        cp = [(tidx[s], at[1]) for s, (at, tg) in
                              enumerate(out)
                              if at[1] is not None and tg[0] == 'copy']
                        for i in range(len(cp)):
                            for j in range(len(cp)):
                                if i == j:
                                    continue
                                q1, o1 = cp[i]
                                q2, o2 = cp[j]
                                if q1 < q2 and o1 == o2 + mF:
                                    copy_pick_pairs += 1
                                    bad.append(('TRANSP', w, Fnm, Ynm,
                                                xp, xf, q1, o1, q2, o2))
    print('inputs: %d; FDI depth-2 outputs checked: %d' % (len(ws), n_fd))
    print('sandwich firings (per-run instances): %d' % fir['sand'])
    print('mirror-sandwich firings: %d' % fir['mir'])
    print('(per-copy convention firings: sandwich %d, mirror %d)'
          % (fir['sand_pc'], fir['mir_pc']))
    print('copy-pick instances seen: %d; transport pairs flagged: %d'
          % (pick_instances, copy_pick_pairs))
    print('violations: %d' % len(bad))
    for b in bad[:10]:
        print('  ', b)
    print('Pick/Slice/Sandwich/Mirror/Transport:',
          'VERIFIED on this domain' if not bad else 'REFUTED')


if __name__ == '__main__':
    main()

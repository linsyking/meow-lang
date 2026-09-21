"""R2: positive-construction probes for hinge 1 (del1b in L?).

Parts:
  red2  the SECOND-B-ANCHORED needle scheme, oracle-verified on the class
        C_2 (strings with <= 2 b's): with V = the first inter-b gap as an
        oracle, [V.b / b.V.b] computes delete-the-first-of-two EXACTLY on
        C_2 -- the needle b.V.b occurs exactly at the first b (uniqueness
        needs no position-0 anchor: the SECOND b is the right anchor, the
        gap V the region -- a cut, as always).
  beam  beam search over the COMBINED vocabulary (constant passes incl.
        length-4 patterns from the L+R agent's offset-1 pairing family,
        plus variable passes from the L-computable VOCAB), depths 4-10,
        scored by input-count distance to del1b on 127 strings <= 6,
        seeded with the enc-flavored near-misses.  A plateau far from 0
        is evidence for the structural circle; 0 would be a WITNESS.
"""
import random
import sys
import time

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/rec/lazy_pass')

from oncecore import (binstrings, const_passes, del1b, VOCAB, subst)

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


# ===================================================================== red2
DEL = 'b'


def Vgap(X):
    """the first inter-b gap: X = U b V b W (V b-free); '' if < 2 b's."""
    i = X.find(DEL)
    if i < 0:
        return ''
    j = X.find(DEL, i + 1)
    if j < 0:
        return ''
    return X[i + 1:j]


def part_red2():
    """Oracle-verify: [V.b / b.V.b] == del-first-of-two on all strings
    with exactly 2 b's (and the 0/1-b cases handled by if-guards)."""
    dom = [s for s in binstrings(8) if s.count('b') <= 2]
    bad = []
    for X in dom:
        nb = X.count('b')
        if nb == 2:
            V = Vgap(X)
            got = subst(V + 'b', 'b' + V + 'b', X)
        else:
            got = X.replace('b', '') if nb == 1 else X
        if got != del1b(X):
            bad.append((X, got, del1b(X)))
    log(f"red2: [V.b/b.V.b] (V oracle) + 1b/0b guards on all {len(dom)} "
        f"strings <=8 with <=2 b's: {len(bad)} failures"
        + (f", e.g. {bad[:5]}" if bad else ""))
    # also document where the needle occurs on >=3-b strings (collateral):
    coll = 0
    for X in binstrings(7):
        if X.count('b') >= 3:
            V = Vgap(X)
            if subst(V + 'b', 'b' + V + 'b', X) != del1b(X):
                coll += 1
    log(f"     collateral on >=3-b strings (<=7): {coll} failures of "
        f"{sum(1 for X in binstrings(7) if X.count('b')>=3)} -- the needle "
        f"over-deletes at later V-spaced pairs, as predicted")


# ===================================================================== beam
def build_vocab():
    """Combined pass vocabulary:
    - constant passes: patterns <= 3 over ab (incl. the offset-1 pairing
      abab/baba/abba/baab length-4 family), replacements <= 2 incl eps
    - variable passes: (rname, pname) over a trimmed VOCAB subset
    - COMPOSITE-GAP needles/replacements: s1.f(X).s2 with s1,s2 in
      {'', 'b'} (the second-b-anchored needle family [V.b/b.V.b]) and
      f in the VOCAB; and f alone.
    Each pass applied to (orig, cur) -> new cur; None if undefined."""
    import itertools
    pats3 = [''.join(t) for k in (1, 2, 3)
             for t in itertools.product('ab', repeat=k)]
    pats = pats3 + ['abab', 'abba', 'baba', 'baab', 'aabb', 'bbaa']
    repls = [''] + [''.join(t) for k in (1, 2)
                    for t in itertools.product('ab', repeat=k)]
    cpass = [(P, R) for P in pats for R in repls]
    vpat = ['a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len',
            'enc', 'tail', 'init']
    vrep = ['eps', 'a', 'b', 'X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb',
            'len', 'enc', 'tail', 'init']
    vpass = [(r, p) for p in vpat for r in vrep]
    # composite-gap family: pattern/replacement = s1 + f(X) + s2
    fs = ['X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len', 'enc', 'tail',
          'init']
    comp_pat = {}
    comp_rep = {'eps': (lambda o, c: '')}
    for f in fs:
        for s1 in ('', 'b'):
            for s2 in ('', 'b'):
                key = f"{s1}.{f}.{s2}"
                comp_pat[key] = (lambda o, c, f=f, s1=s1, s2=s2:
                                 s1 + VOCAB[f](o) + s2)
                comp_rep[key] = comp_pat[key]
    cpass2 = []          # (pattern_fn, repl_fn) as 'G' passes
    for pk, pfn in comp_pat.items():
        if pfn('', '') == '':
            continue                      # pattern would be empty on eps
        for rk, rfn in comp_rep.items():
            cpass2.append((pk, rk))
    return cpass, vpass, cpass2


def apply_pass(p, orig, cur):
    """p is ('C',(P,R)) | ('V',(rn,pn)) | ('G',(pk,rk)); new cur or None."""
    if p[0] == 'C':
        (P, R) = p[1]
        return cur.replace(P, R)
    if p[0] == 'V':
        (rn, pn) = p[1]
        P = VOCAB[pn](orig)
        if P == '':
            return None
        return cur.replace(P, VOCAB[rn](orig))
    (pk, rk) = p[1]
    P = _COMPAT[pk](orig, cur)
    if P == '':
        return None
    return cur.replace(P, _COMREP[rk](orig, cur))


_COMPAT = {}
_COMREP = {}


def part_beam(rounds=9, width=1500, seed=7, dom_maxlen=6):
    global _COMPAT, _COMREP
    rng = random.Random(seed)
    test = binstrings(dom_maxlen)
    tsig = tuple(del1b(s) for s in test)
    cpass, vpass, gpass = build_vocab()
    # materialize the composite fns as closures over VOCAB
    fs = ['X', 'Xa', 'Xb', 'aX', 'bX', 'H', 'Hb', 'len', 'enc', 'tail',
          'init']
    for f in fs:
        for s1 in ('', 'b'):
            for s2 in ('', 'b'):
                _COMPAT[f"{s1}.{f}.{s2}"] = (
                    lambda o, c, f=f, s1=s1, s2=s2: s1 + VOCAB[f](o) + s2)
                _COMREP[f"{s1}.{f}.{s2}"] = _COMPAT[f"{s1}.{f}.{s2}"]
    _COMREP['eps'] = (lambda o, c: '')
    passes = ([('C', p) for p in cpass] + [('V', p) for p in vpass]
              + [('G', p) for p in gpass])
    log(f"beam: {len(passes)} passes ({len(cpass)} const incl. length-4 "
        f"offset-1 family, {len(vpass)} atomic variable, {len(gpass)} "
        f"composite-gap [s1.f.s2]), domain {len(test)} strings <= {dom_maxlen}")

    def dist(cur_tuple):
        return sum(1 for a, b in zip(cur_tuple, tsig) if a != b)

    # seed: identity + the d=50 near-miss family + single passes
    states = {}
    ident = tuple(test)
    states[ident] = []
    for p in passes:
        ns = tuple(apply_pass(p, o, o) if apply_pass(p, o, o) is not None
                   else '\x00' for o in test)
        if '\x00' not in ns:
            states.setdefault(ns, [p])
    log(f"  seed: {len(states)} states (depth 1)")
    best = (dist(ident), [])
    for depth in range(2, rounds + 1):
        scored = []
        for sig, pl in states.items():
            d = dist(sig)
            scored.append((d, sig, pl))
            if d < best[0]:
                best = (d, pl)
        scored.sort(key=lambda t: t[0])
        top = scored[:width]
        if depth == 2:
            log(f"  depth 1 scan: best distance {best[0]}")
        newstates = {sig: pl for (d, sig, pl) in scored[:width]}
        t0 = time.time()
        cap_add = 6 * width
        for (d, sig, pl) in top:
            for p in passes:
                ns_l = []
                ok = True
                for o, c in zip(test, sig):
                    nc = apply_pass(p, o, c)
                    if nc is None:
                        ok = False
                        break
                    ns_l.append(nc)
                if not ok:
                    continue
                ns = tuple(ns_l)
                if ns not in newstates and len(newstates) < cap_add:
                    newstates[ns] = pl + [p]
                    dd = sum(1 for a, b in zip(ns, tsig) if a != b)
                    if dd < best[0]:
                        best = (dd, pl + [p])
                        log(f"  depth {depth}: new best d={dd}: "
                            f"{best[1][-4:]}")
                    if dd == 0:
                        log(f"  WITNESS at depth {depth}: {pl + [p]}")
                        return
        states = newstates
        log(f"  depth {depth}: {len(states)} states, best d={best[0]}, "
            f"{time.time()-t0:.0f}s")
        if best[0] == 0:
            break
    log(f"beam done: best distance {best[0]} on {len(test)} strings; "
        f"pipeline tail: {best[1][-6:]}")


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('red2', 'all'):
        log("=== red2: second-b-anchored needle (oracle) ===")
        part_red2()
    if which in ('beam', 'all'):
        log("=== beam: deep structured search ===")
        part_beam()
    log(f"total {time.time()-t0:.0f}s")
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/r2.log', 'w') as f:
        f.write('\n'.join(LOG))

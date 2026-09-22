"""ROUND 12 -- re-verification of the round-11 hunt's PHASE-2 (mixed-shape)
DB hits with prov.py's independent evaluator.

Reads the MIXED DB HIT lines from round11_hunt.log, rebuilds each as an
lcore expression  [eps/P](g1 . [Y/xp].f . g2)  and checks that prov is
exactly DB(w).  (Round-11 lesson: machine claims are accepted or rejected
only after an independent re-verification; transcription by hand is not
trusted.)

Usage: /usr/bin/python3 -W ignore verify_round12_mixed.py [logfile]
"""
import re
import sys

import prov as PV
from lcore import K, V, C, S

LOG = sys.argv[1] if len(sys.argv) > 1 else 'round11_hunt.log'

# form specs: "pre:X|mid:Y|suf:Z|T" (f/Y fields) or "X|Y|Z|T" (Pform field)
def form_expr(spec):
    m = re.fullmatch(r'(?:pre:)?(.*?)\|(?:mid:)?(.*?)\|(?:suf:)?(.*?)\|([01])',
                     spec)
    pre, mid, suf, two = m.group(1), m.group(2), m.group(3), int(m.group(4))
    e = C(K(pre) if pre else None, V(0)) if pre else V(0)
    if two:
        e = C(e, K(mid)) if mid else e
        e = C(e, V(0))
    if suf:
        e = C(e, K(suf))
    return e

# g-option name -> lcore expression (must mirror gbuild() in round11_hunt.c)
GN = {
    '': None, 'a': K('a'), 'b': K('b'), 'ab': K('ab'),
    'w': V(0), 'a.w': C(K('a'), V(0)), 'w.a': C(V(0), K('a')),
    'a.w.a': C(C(K('a'), V(0)), K('a')), 'w.w': C(V(0), V(0)),
    'w.a.w': C(C(V(0), K('a')), V(0)), 'b.w': C(K('b'), V(0)),
    'w.b': C(V(0), K('b')),
}

def main():
    hits = []
    for line in open(LOG):
        m = re.match(r'  MIXED DB HIT: w=(\S+) n=(\d+) f=(\S+) Y=(\S+) '
                     r'xp=(\S+) g1=(\S*) g2=(\S+) P=(\S+) Pform=(\S+)', line)
        if m:
            hits.append(m.groups())
    print('verify_round12_mixed: %d MIXED DB HIT lines parsed from %s'
          % (len(hits), LOG))
    bad = 0
    for (w, ns, fs, Ys, xp, g1s, g2s, Ps, Pf) in hits:
        n = int(ns)
        f = form_expr(fs)
        Y = form_expr(Ys)
        P = form_expr(Pf)
        g1, g2 = GN[g1s], GN[g2s]
        inner = S(Y, K(xp), f)
        scrut = inner
        if g1 is not None:
            scrut = C(g1, scrut)
        if g2 is not None:
            scrut = C(scrut, g2)
        E = S(K(''), P, scrut)
        v = PV.lden(E, (PV.lab_input(w),))
        prov = PV.labels(v)
        ok = (prov == tuple(range(n - 1, -1, -1)))
        if not ok:
            bad += 1
            print('  MISMATCH: w=%s f=%s Y=%s xp=%s g1=%s g2=%s P=%s ->'
                  ' prov=%s' % (w, fs, Ys, xp, g1s, g2s, Ps, prov))
    print('  prov.py re-verification of mixed hits: %d/%d match DB'
          % (len(hits) - bad, len(hits)))
    print('  verdict:', 'VERIFIED' if bad == 0 and hits else 'REFUTED')
    return bad == 0 and bool(hits)

if __name__ == '__main__':
    main()

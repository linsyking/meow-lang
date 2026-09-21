"""PILOT (Round 1, evidence only -- domain-limited, NOT a proof):

Do mixed constant-pattern pipelines compute functions (on the finite test
domain) that NO pure-L and NO pure-R pipeline of the same depth budget
computes?

Setup: passes (A, B, dir) with B in {a,b}^1 or {a,b}^2 (6 patterns), A in
{a,b}^{<=2} (7 replacements), dir in {L, R}  ->  84 pass types.  Test
domain: all 63 strings of length <= 5 over {a,b}.  Three reachability
computations by BFS on distinct function tables (dedup safe: equal tables
have equal extensions):  pure-L, pure-R, mixed, all at depth <= 3.

Report: mixed-only tables = mixed - L - R; whether any table equals rev on
the domain; sample witnesses.

CAVEAT (stated in REPORT.md): agreement is only on the 63-string domain;
absence of a depth-<=3 pure match is evidence, not a separation -- deeper
pure pipelines or variable patterns might match.  Any candidate that
matters gets re-verified on larger domains (the round-3 protocol).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lrcore import subst, substR, iter_strings

AB = 'ab'
DOM = tuple(iter_strings(AB, 5))                     # 63 strings
REV = tuple(s[::-1] for s in DOM)

PATTERNS = [a + b for a in AB for b in AB] + list(AB)        # 6
REPLS = [a + b for a in AB for b in AB] + list(AB) + ['']    # 7
PASSES = [(A, B, d) for A in REPLS for B in PATTERNS for d in 'LR']  # 84


def apply_pass(table, A, B, d):
    f = subst if d == 'L' else substR
    return tuple(f(A, B, s) for s in table)


def reach(passes, depth):
    """All function tables of pipelines over `passes` of length <= depth
    (run order), as a set.  BFS on distinct tables with dedup."""
    seen = {DOM}
    frontier = {DOM}
    for k in range(depth):
        new = set()
        for tab in frontier:
            for (A, B, d) in passes:
                t2 = apply_pass(tab, A, B, d)
                if t2 not in seen:
                    seen.add(t2)
                    new.add(t2)
        frontier = new
        print(f'    depth {k+1}: +{len(new)} new, {len(seen)} total tables')
    return seen


def main():
    depth = 3
    print('pure-L reachability:')
    Lset = reach([(A, B, 'L') for (A, B, d) in PASSES], depth)
    print('pure-R reachability:')
    Rset = reach([(A, B, 'R') for (A, B, d) in PASSES], depth)
    print('mixed reachability:')
    Mset = reach(PASSES, depth)

    mixed_only = Mset - Lset - Rset
    print(f'\nTOTAL: pure-L {len(Lset)}, pure-R {len(Rset)}, mixed {len(Mset)}, '
          f'mixed-only {len(mixed_only)}')
    rev_like = [t for t in Mset if t == REV]
    print(f'tables equal to rev on the domain: {len(rev_like)} '
          f'(of which mixed-only: {sum(1 for t in rev_like if t in mixed_only)})')

    # escalation: give the PURE-L side one more level (depth 4) and see how
    # much of the mixed set it absorbs; also locate the thm:subsequential
    # witness [b/aa]^R on both sides.
    print('\npure-L depth-4 escalation:')
    L4 = reach([(A, B, 'L') for (A, B, d) in PASSES], 4)
    fR = tuple(substR('b', 'aa', s) for s in DOM)
    print(f'[b/aa]^R table in pure-L depth<=3? {fR in Lset}; depth<=4? {fR in L4}')
    print(f'mixed depth<=3 tables not in pure-L depth<=4: {len(Mset - L4)}')
    print(f'pure-R depth<=3 tables not in pure-L depth<=4: {len(Rset - L4)}')

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'pilot_mixed_only.txt'), 'w') as f:
        for t in sorted(mixed_only):
            f.write(repr(t) + '\n')
    print('mixed-only tables (depth<=3 vs pure depth<=3) written to '
          'pilot_mixed_only.txt')
    return mixed_only


if __name__ == '__main__':
    main()

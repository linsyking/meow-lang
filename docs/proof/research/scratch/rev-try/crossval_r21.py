#!/usr/bin/env python3
"""Independent Python re-implementation of round21_delta.c (same
necessary constraints: collinearity, integrality, t-feasibility,
tightened early-firing window c <= Delta + 3^{s1-t1+1}, depth
monotonicity) — compared record-set-identical against the C output.
Usage: python3 crossval_r21.py K   (expects ../rev-try/dK.txt)
"""
import re
import sys
from math import gcd

k = int(sys.argv[1])
pw = [3 ** i for i in range(k + 3)]
recs = set()
for s1 in range(k):
    for s2 in range(s1 + 1, k):
        for s3 in range(s2 + 1, k):
            h1, h2 = s2 - s1, s3 - s2
            step1 = (pw[s2 + 1] - pw[s1 + 1]) // 2
            step2 = (pw[s3 + 1] - pw[s2 + 1]) // 2
            T = [(a, b) for a in range(1, k + 2) for b in range(a)]
            for (a1, b1) in T:
                if (a1, b1) == (s1 + 1, 0):
                    continue
                W1 = (pw[a1] - pw[b1] - pw[s1 + 1] + 1) // 2
                for (a2, b2) in T:
                    if (a2, b2) == (s2 + 1, 0):
                        continue
                    W2 = (pw[a2] - pw[b2] - pw[s2 + 1] + 1) // 2
                    D1 = W2 - W1
                    if D1 == 0:
                        continue
                    for (a3, b3) in T:
                        if (a3, b3) == (s3 + 1, 0):
                            continue
                        W3 = (pw[a3] - pw[b3] - pw[s3 + 1] + 1) // 2
                        D2 = W3 - W2
                        if D2 == 0 or (D1 > 0) != (D2 > 0):
                            continue
                        x, y = abs(D1), abs(D2)
                        g = gcd(x, y)
                        r1, r2 = x // g, y // g
                        n = 1
                        while r1 * n <= h1 and r2 * n <= h2:
                            q1, q2 = r1 * n, r2 * n
                            n += 1
                            if D1 % q1:
                                continue
                            delta = D1 // q1
                            if step1 + q1 * delta < 0 or step2 + q2 * delta < 0:
                                continue
                            for t1 in range(s1 + 1):
                                c = W1 - t1 * delta
                                if (c > delta + pw[s1 - t1 + 1] or
                                        c < -pw[s1 - t1]):
                                    continue
                                recs.add((s1, s2, s3, a1, b1, a2, b2,
                                          a3, b3, q1, q2, t1, delta, c))
crecs = set()
pat = re.compile(r'REC k=\d+ s=(\d+),(\d+),(\d+) ab=(\d+)/(\d+),(\d+)/'
                 r'(\d+),(\d+)/(\d+) q=(-?\d+),(-?\d+) t1=(\d+) '
                 r'D=(-?\d+) c=(-?\d+)')
for line in open('d%d.txt' % k):
    m = pat.match(line)
    crecs.add(tuple(int(v) for v in m.groups()))
print('crossval k=%d: python=%d C=%d identical=%s' %
      (k, len(recs), len(crecs), recs == crecs))
assert recs == crecs

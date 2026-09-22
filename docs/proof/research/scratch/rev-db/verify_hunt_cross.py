"""CROSS-VERIFICATION of separable_hunt.c against prov.py's lden.

Parses every CROSS line of hunt_mode*.log, rebuilds the SAME expression
(the form table below is separable_hunt.c's, index for index), evaluates
it with the independent evaluator (prov.lden / lcore), and checks:
  (S) the C simulator's prov agrees with lden's prov (prefix, length,
      weighted checksum)  -- validates the C semantics, not just the
      theorem;
  (T) the theorem's claims on the rebuilt value: prov = (0..n-1)^M,
      content = v0 w v1 ... w vM (v_j over {a,b}*), prov != DB,
      content != rev(w).

Run: /usr/bin/python3 -W ignore verify_hunt_cross.py
"""
import glob
import re
import sys

from prov import lden, labels, content, lab_input, Undefined
from lcore import K, V, C, S

X = V(0)

# separable_hunt.c's form table: value = c[0] w c[1] w c[2] w c[3]
FORMS = [
    (0, ("", "", "", "")),          # 0 eps
    (1, ("", "", "", "")),          # 1 w
    (2, ("", "", "", "")),          # 2 ww
    (3, ("", "", "", "")),          # 3 www
    (1, ("a", "", "", "")),         # 4 a.w
    (1, ("", "a", "", "")),         # 5 w.a
    (1, ("a", "a", "", "")),        # 6 a.w.a
    (1, ("b", "", "", "")),         # 7 b.w
    (1, ("", "b", "", "")),         # 8 w.b
    (1, ("a", "b", "", "")),        # 9 a.w.b
    (1, ("b", "a", "", "")),        # 10 b.w.a
    (1, ("ab", "", "", "")),        # 11 ab.w
    (1, ("", "ab", "", "")),        # 12 w.ab
    (2, ("a", "", "", "")),         # 13 a.ww
    (2, ("", "", "a", "")),         # 14 wwa
    (2, ("a", "", "a", "")),        # 15 a.w.w.a
    (2, ("", "a", "", "")),         # 16 w.a.w
    (2, ("", "b", "", "")),         # 17 w.b.w
    (2, ("a", "b", "a", "")),       # 18 a.w.b.w.a
    (0, ("a", "", "", "")),         # 19 "a"
    (0, ("b", "", "", "")),         # 20 "b"
    (0, ("aa", "", "", "")),        # 21 "aa"
    (0, ("ab", "", "", "")),        # 22 "ab"
    (0, ("ba", "", "", "")),        # 23 "ba"
]


def form_expr(fi):
    k, cst = FORMS[fi]
    parts = []
    for i in range(k + 1):
        if cst[i]:
            parts.append(K(cst[i]))
        if i < k:
            parts.append(X)
    if not parts:
        return K('')
    acc = parts[0]
    for p in parts[1:]:
        acc = C(acc, p)
    return acc


def chain_expr(passes, F1):
    """passes in RUN order (first runs first): passes[0] is the
    innermost S-node (scrutinee side), applied first."""
    acc = form_expr(F1)
    for (R, P) in passes:
        acc = S(form_expr(R), form_expr(P), acc)
    return acc


def parse_and_check(line):
    m = re.match(r'CROSS (\w+) (\d+) (.*)$', line.strip())
    kind, n, rest = m.group(1), int(m.group(2)), m.group(3)
    spec_s, prov_s = rest.split('|')
    spec = [int(x) for x in spec_s.split()]
    before, after = prov_s.split('#')
    prov = [int(x) for x in before.split()]
    plen_s = after.split()
    plen, psum = int(plen_s[0]), int(plen_s[1])
    w = ''.join(chr(ord('c') + j) for j in range(n))

    if kind == 'chain':
        d = (len(spec) - 1) // 2
        F1 = spec[0]
        passes = [(spec[1 + 2 * i], spec[2 + 2 * i]) for i in range(d)]
        e = chain_expr(passes, F1)
    elif kind in ('deepp', 'deepr'):
        F1, innerF, other = spec[0], spec[1], spec[2]
        rest_ = spec[3:]
        d1 = len(rest_) // 2
        passes = [(rest_[2 * i], rest_[2 * i + 1]) for i in range(d1)]
        inner = chain_expr(passes, innerF)
        if kind == 'deepp':
            e = S(form_expr(other), inner, form_expr(F1))
        else:
            e = S(inner, form_expr(other), form_expr(F1))
    elif kind == 'ccomp':
        F1, F2, a, b = spec[0], spec[1], spec[2], spec[3]
        lp = [(spec[4 + 2 * i], spec[5 + 2 * i]) for i in range(a)]
        rp = [(spec[4 + 2 * a + 2 * i], spec[5 + 2 * a + 2 * i])
              for i in range(b)]
        e = C(chain_expr(lp, F1), chain_expr(rp, F2))
    else:
        raise ValueError(kind)

    try:
        val = lden(e, (lab_input(w),))
    except Undefined:
        return ('undef-mismatch', line)
    provpy = list(labels(val))
    contpy = content(val)

    # (S) simulator agreement: prefix (first 48), length, checksum
    csum = sum(lb * (i + 1) for i, lb in enumerate(provpy))
    if (provpy[:48] != prov[:48] or len(provpy) != plen or csum != psum):
        return ('sim-mismatch', line)
    # (T) theorem claims
    R = list(range(n))
    if provpy != R * (len(provpy) // n) or len(provpy) % n:
        return ('bad-prov-form', line)
    if not re.fullmatch('[ab]*(?:%s[ab]*)*' % w, contpy):
        return ('bad-content-form', line)
    if n >= 2 and provpy == list(range(n - 1, -1, -1)):
        return ('DB', line)
    if contpy == w[::-1]:
        return ('rev', line)
    return ('ok', line)


def main():
    files = sorted(glob.glob('hunt_mode*.log'))
    n_lines, counts = 0, {}
    for f in files:
        for line in open(f):
            if not line.startswith('CROSS'):
                continue
            n_lines += 1
            verdict, _ = parse_and_check(line)
            counts[verdict] = counts.get(verdict, 0) + 1
            if verdict not in ('ok',):
                print(f'  {verdict}: {line.strip()}')
    print(f'cross-verified {n_lines} CROSS lines from {len(files)} logs')
    for k, v in sorted(counts.items()):
        print(f'  {k:18s} {v}')
    bad = sum(v for k, v in counts.items() if k != 'ok')
    print('VERDICT:', 'ALL CLEAN (simulator agrees with lden; theorem '
          'claims hold)' if bad == 0 else f'{bad} MISMATCHES')
    return 0 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())

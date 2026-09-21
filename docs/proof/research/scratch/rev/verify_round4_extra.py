"""ROUND 4 SUPPLEMENTARY (coordinator): the crossings evidence for the
price-of-reordering remark, measured on BUILT expressions.

Closes the three gaps between the draft remark's evidence sentence and
what verify_round4_ladder.py / verify_round4_hinges.py had measured:

1. rotR_k built expressions (k = 1..4): exact vs the content function on
   the same domains as rev-last-k; crossings at n = 14, worst of 56
   inputs, against the closed form k(n-k).
2. swap-first-last: exact on all |w| <= 9 (it enters the table as an
   L-row) -- cat(last, init o tail, head).
3. cat(X, X): crossings at n = 14, worst of 56 inputs.
4. Random pipelines (1000, variable patterns included): crossings at
   |w| = 12 (30 inputs each); the top 5 by chi re-measured at
   |w| in {8, 10, 14} to witness the growth rate.
"""
import random
import sys

import lcore as L
from lcore import K, V, C, all_strings
import r2lib as RL
from verify_round4_ladder import (init_j, _last_of, influence_of, describe,
                                  rev_last_k_fn)

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk  # noqa: E402

sg = tk.BIN
rng = random.Random(2718)

NINF = 14


def out_of(e, w):
    r = L.den_try(e, (w,))
    return None if r[0] != 'ok' else r[1]


# ---- the same 56 inputs as verify_round4_ladder (seed 2718) ---------------
ws = [''.join(rng.choice('ab') for _ in range(NINF)) for _ in range(48)]
structured = ['ab' * 7, 'ba' * 7, 'a' * 14, 'b' * 14, 'abbaababbaabba',
              'aaaabaaaaabaaa', 'baaaabaaaabaaa', 'aabbbaaabbbaaa']
ws += [s for s in structured if len(s) == NINF]


# ------------------------------------------------------------- rotR_k family
def rotr_k_expr(k):
    """cat(last o init^{k-1}, ..., last, init^k) = right rotation by k."""
    parts = [_last_of(init_j(k - 1 - j)) for j in range(k)]
    parts.append(init_j(k))
    e = parts[0]
    for q in parts[1:]:
        e = tk.cat(sg, e, q)
    return e


def rotr_k_fn(w, k):
    s = len(w) - k
    return w[s:] + w[:s]


print('=== rotR_k: expression vs function (exhaustive) ===')
kx = {}
for k in (1, 2, 3, 4):
    e = rotr_k_expr(k)
    kx[k] = e
    nmax = 10 if k <= 2 else 8
    bad = tot = 0
    for w in all_strings(nmax):
        if len(w) < k:
            continue
        tot += 1
        if out_of(e, w) != rotr_k_fn(w, k):
            bad += 1
    print(f'  k={k}: size={L.size(e):6d}  domain |w|<={nmax},|w|>=k '
          f'({tot} strings): mismatches={bad}'
          f'  {"PASS" if bad == 0 else "FAIL"}')

print('=== rotR_k crossings at n=14 (worst of 56 inputs) vs k(n-k) ===')
for k in (1, 2, 3, 4):
    best = None
    for w in ws:
        st = influence_of(kx[k], w)
        if st is None:
            continue
        if best is None or st['crossings'] > best['crossings']:
            best = st
    ok = best['crossings'] == k * (NINF - k)
    print(f'  rotR_{k}: crossings={best["crossings"]:3d}  '
          f'k(n-k)={k * (NINF - k):3d}  match={best["match"]}  '
          f'{"OK" if ok else "MISMATCH"}')

# --------------------------------------------------- swap-first-last exactness
# cat(last, init o tail, head) duplicates the character on |w| <= 1
# (last = head = the char), so the swap function's domain is |w| >= 2;
# the crossings of the table are measured at |w| = 14, where the edge
# never fires.
print('=== swap-first-last: exact on all 2 <= |w| <= 11 ===')


def swapfl_fn(w):
    return w[-1] + w[1:-1] + w[0]


bad = tot = 0
for w in all_strings(11):
    if len(w) < 2:
        continue
    tot += 1
    if out_of(RL.swapfl_expr(), w) != swapfl_fn(w):
        bad += 1
print(f'  {tot} strings: mismatches={bad}  {"PASS" if bad == 0 else "FAIL"}')

# ------------------------------------------------------------ cat(X,X) row
print('=== cat(X,X): crossings at n=14 (worst of 56 inputs) ===')
XX = C(V(0), V(0))
best = None
for w in ws:
    st = influence_of(XX, w)
    if st is None:
        continue
    if best is None or st['crossings'] > best['crossings']:
        best = st
print(f'  crossings={best["crossings"]}  match={best["match"]}  '
      f'lenrows={best["lenrows"]}  '
      f'(every row is a doubleton: both copies move together)')

# ------------------------------------------------------- random pipelines
def rand_expr(depth, cons=('', 'a', 'b', 'ab', 'ba')):
    t = rng.random()
    if depth == 0 or t < 0.3:
        return V(0) if rng.random() < 0.55 else K(rng.choice(cons))
    if t < 0.6:
        return C(rand_expr(depth - 1), rand_expr(depth - 1))
    from lcore import S
    return S(rand_expr(depth - 1), rand_expr(depth - 1),
             rand_expr(depth - 1))


def worst_chi(e, n, n_inputs=30, seed=99):
    r2 = random.Random(seed + n)
    ws2 = [''.join(r2.choice('ab') for _ in range(n)) for _ in range(n_inputs)]
    best = 0
    undef = 0
    for w in ws2:
        if out_of(e, w) is None:
            undef += 1
            continue
        st = influence_of(e, w)
        if st is not None:
            best = max(best, st['crossings'])
    return best, undef


print('=== 1000 random pipelines: crossings at |w| = 12 ===')
res = []
tot_undef = 0
for i in range(1000):
    e = rand_expr(rng.choice([1, 2, 3, 4]))
    chi, und = worst_chi(e, 12)
    tot_undef += und
    res.append((chi, e))
res.sort(key=lambda t: -t[0])
chis = [c for c, _ in res]
n_above = sum(1 for c in chis if c > 0)
print(f'  1000 exprs; chi = 0 on {1000 - n_above}; max chi = {chis[0]}, '
      f'second {chis[1]}, fifth {chis[4]};  max chi/n = {chis[0] / 12:.2f}')
print(f'  (partially undefined evaluations: {tot_undef} input-expr pairs '
      f'discarded)')

print('=== top 5 by chi: growth across |w| in {8, 10, 12, 14} ===')
for chi12, e in res[:5]:
    row = []
    for n in (8, 10, 12, 14):
        c, _ = worst_chi(e, n)
        row.append(c)
    lin = row[3] <= (14 / 8) * max(row[0], 1) + 2
    print(f'  chi12={chi12:3d}: n=8..14 crossings {row}  '
          f'{"linear-ish" if lin else "SUPERLINEAR?"}  size={L.size(e)}')

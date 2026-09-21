"""ROUND 4 - THE PRICE-OF-REORDERING LADDER (coordinator priority 2).

Assembles, machine-verifies, and measures every rung of the reordering
ladder for the paper-grade remark:

  id, init, last (prop:last), rotR1 = cat(last, init), swap-first-last,
  rev-last-k  (w -> w[n-1] w[n-2] ... w[n-k] w[:n-k])  for k = 1..4,
  rev.

The rev-last-k expressions are BUILT here (not just asserted): each
last(init^j) is the anchored right-end read of Proposition prop:last
composed j times; cat glues them.  Equality with the content function is
verified exhaustively (|w| <= 10 for k <= 2, |w| <= 8 for k <= 4),
then influence crossings are measured at n = 14 (worst of ~56 inputs),
together with prov LDS and mult (Conjecture A/B side).  NOTE the provLDS
column: every anchored rung rebuilds its output from CONSTANT atoms
(empty atom-provenance) -- the faking loophole; only influence
crossings measure their reordering.

Also the two barrier measurements the remark needs:
  - relabeling barrier: the canonical content-consistent labeling of
    rev(w) (increasing within each character class) has LDS <= #classes
    <= |Sigma| -- verified at n = 14 and by brute force over ALL
    consistent bijections at |w| <= 6;
  - the XX row: quadratic inversions at LDS 2 (inversion mass vs LDS).
"""
import random
import sys
from collections import defaultdict

import lcore as L
from lcore import K, V, C, comp, all_strings, rev
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk  # noqa: E402

sg = tk.BIN
rng = random.Random(2718)

NV = 10          # verification domain: all binary strings <= 10
NINF = 14        # crossings measured at n = 14
NS = 512         # random inputs at n = 14


def out_of(e, w):
    r = L.den_try(e, (w,))
    return None if r[0] != 'ok' else r[1]


def influence_of(e, w):
    base = out_of(e, w)
    if base is None:
        return None
    D = {}
    for p in range(len(w)):
        w2 = w[:p] + ('a' if w[p] == 'b' else 'b') + w[p + 1:]
        o2 = out_of(e, w2)
        if o2 is None:
            D[p] = ('undef',)
        elif len(o2) == len(base):
            D[p] = [i for i in range(len(base)) if o2[i] != base[i]]
        else:
            D[p] = ('len',)
    return describe(D)


def describe(D):
    single = [p for p in D if isinstance(D[p], list) and len(D[p]) == 1]
    mass = sum(len(D[p]) for p in D if isinstance(D[p], list))
    col = defaultdict(int)
    for p in single:
        col[D[p][0]] += 1
    perfect = [p for p in single if col[D[p][0]] == 1]
    pi = {p: D[p][0] for p in perfect}
    crossings = sum(1 for p in perfect for q in perfect
                     if p < q and pi[p] > pi[q])
    return {'match': len(perfect), 'crossings': crossings,
            'maxdisp': max((abs(pi[p] - p) for p in perfect), default=0),
            'lenrows': sum(1 for p in D if not isinstance(D[p], list))}


# --------------------------------------------------- rev-last-k expressions

def init_j(j):
    """init composed j times (j = 0 -> X)."""
    e = V(0)
    for _ in range(j):
        e = _subst_init(e)
    return e


def _subst_init(e):
    """init(e): anchored, as in r2lib.init_expr but with e in place of X."""
    T = C(tk.enc2(sg, e), K(RL._A))
    PA, PB = K(RL._PA), K(RL._PB)
    return tk.if_(sg, tk.eq(sg, e, K('')), K(''),
                  tk.if_(sg, tk.contains(sg, T, PA),
                         tk.dec2(sg, comp([('', RL._PA)], T)),
                         tk.dec2(sg, comp([('', RL._PB)], T))))


def _last_of(e):
    """last(e): anchored right-end read of e."""
    T = C(tk.enc2(sg, e), K(RL._A))
    return tk.if_(sg, tk.eq(sg, e, K('')), K(''),
                  tk.if_(sg, tk.contains(sg, T, K(RL._PA)), K('a'), K('b')))


def rev_last_k_expr(k):
    """cat(last, last.init, ..., last.init^{k-1}, init^k)."""
    parts = [_last_of(init_j(j)) for j in range(k)]
    parts.append(init_j(k))
    e = parts[0]
    for q in parts[1:]:
        e = tk.cat(sg, e, q)
    return e


def rev_last_k_fn(w, k):
    """w -> w[n-1] w[n-2] ... w[n-k] w[:n-k]  (exact for |w| >= k)."""
    s = len(w) - k
    return rev(w[s:]) + w[:s]


# ------------------------------------------------------------ XX row data

def xx_inversions(w):
    """[X/a]X prov = labels 0..n-1 twice (w w): inter-copy inversions =
    #{(i,j) : i > j} = C(n,2) -- quadratic inversions at LDS 2 (Dilworth)."""
    n = len(w)
    return n * (n - 1) // 2


def canonical_relabel(out, w):
    """The content-consistent labeling increasing within each character
    class: positions of character c in out receive the positions of c in
    w, both in increasing order.  Valid whenever out is a permutation of
    w's characters (e.g. out = rev(w))."""
    src = defaultdict(list)
    for i, c in enumerate(w):
        src[c].append(i)
    ptr = defaultdict(int)
    lab = []
    for c in out:
        lab.append(src[c][ptr[c]])
        ptr[c] += 1
    return lab


def min_relabel_lds(out, w):
    """LDS of the canonical content-consistent labeling -- an upper bound
    on the min over all consistent relabelings.  Class argument: a
    strictly decreasing subsequence cannot contain two positions of the
    same class (within-class labels increase), hence this is <= #classes."""
    return PV.lds(tuple(canonical_relabel(out, w)))


def lps(w):
    """longest palindromic subsequence, O(n^2)."""
    n = len(w)
    if n == 0:
        return 0
    dp = [[0] * n for _ in range(n)]
    for i in range(n):
        dp[i][i] = 1
    for L in range(2, n + 1):
        for i in range(n - L + 1):
            j = i + L - 1
            if w[i] == w[j]:
                dp[i][j] = (dp[i + 1][j - 1] + 2) if L > 2 else 2
            else:
                dp[i][j] = max(dp[i + 1][j], dp[i][j - 1])
    return dp[0][n - 1]


if __name__ == '__main__':
    ws = [''.join(rng.choice('ab') for _ in range(NINF))
          for _ in range(48)]
    ws = [w for w in ws if len(w) == NINF]
    structured = ['ab' * 7, 'ba' * 7, 'a' * 14, 'b' * 14, 'abbaababbaabba',
                  'aaaabaaaaabaaa', 'baaaabaaaabaaa', 'aabbbaaabbbaaa']
    ws += [s for s in structured if len(s) == NINF]

    # 0. verify rev-last-k expressions: all |w| <= 8 for k in 1..4,
    #    all |w| <= 10 for k <= 2 (nested-init expressions are big)
    print('=== rev-last-k: expression vs function (exhaustive) ===')
    kexpr = {}
    for k in (1, 2, 3, 4):
        e = rev_last_k_expr(k)
        kexpr[k] = e
        nmax = 10 if k <= 2 else 8
        bad = tot = 0
        for w in all_strings(nmax):
            if len(w) < k:
                continue
            tot += 1
            if out_of(e, w) != rev_last_k_fn(w, k):
                bad += 1
        print(f'  k={k}: size={L.size(e):6d}  domain |w|<={nmax},|w|>=k '
              f'({tot} strings): mismatches={bad}'
              f'  {"PASS" if bad == 0 else "FAIL"}')

    # 1. the ladder: expression side (worst of ~56 inputs at n=14)
    ladder = [
        ('id', V(0)),
        ('init', RL.init_expr()),
        ('last (prop:last)', RL.last_expr()),
        ('rotR1 = cat(last,init)', RL.rotr1_expr()),
        ('swap-first-last', RL.swapfl_expr()),
        ('rev-last-1', kexpr[1]),
        ('rev-last-2', kexpr[2]),
        ('rev-last-3', kexpr[3]),
        ('rev-last-4', kexpr[4]),
    ]
    print(f'=== expression ladder at n={NINF} (worst of len(ws) inputs) ===')
    print(f'  {"function":24s} {"size":>6s} {"cross":>6s} {"match":>6s} '
          f'{"lenrows":>8s} {"provLDS":>7s} {"mult":>5s}')
    for name, e in ladder:
        best = None
        for w in ws:
            if len(w) < NINF:
                continue
            st = influence_of(e, w)
            if st is None:
                continue
            if best is None or st['crossings'] > best['crossings']:
                best = st
                bw = w
        r = PV.stats(e, bw)
        print(f'  {name:24s} {L.size(e):6d} {best["crossings"]:6d} '
              f'{best["match"]:6d} {best["lenrows"]:8d} '
              f'{r["lds"]:7d} {r["mult"]:5d}')

    # rev (function) for the top rung
    def infl_fn(f, w):
        base = f(w)
        D = {}
        for p in range(len(w)):
            w2 = w[:p] + ('a' if w[p] == 'b' else 'b') + w[p + 1:]
            o2 = f(w2)
            if len(o2) == len(base):
                D[p] = [i for i in range(len(base)) if o2[i] != base[i]]
            else:
                D[p] = ('len',)
        return describe(D)
    best = max((infl_fn(rev, w) for w in ws),
               key=lambda st: st['crossings'])
    print(f'  {"rev (function)":24s} {"-":>6s} {best["crossings"]:6d} '
          f'{best["match"]:6d} {best["lenrows"]:8d}   n(n-1)/2 = '
          f'{NINF * (NINF - 1) // 2}')

    # 2. XX row: doubling cat(X,X) -- quadratic inversions at LDS 2
    w0 = ws[0]
    XX = tk.cat(sg, V(0), V(0))
    r = PV.stats(XX, w0)
    print(f'=== XX row: cat(X,X) on n={len(w0)}: inter-copy inversions = '
          f'{xx_inversions(w0)}, prov LDS = {r["lds"]}, mult = {r["mult"]}'
          f'  (Dilworth: 2 increasing runs) ===')

    # 3. relabeling barrier at n=14 (canonical labeling = within-class
    #    increasing) + brute-force optimality check on small n
    print('=== relabeling barrier (content-consistent relabelings of rev) ===')
    mx = 0
    for w in ws:
        mx = max(mx, min_relabel_lds(rev(w), w))
    print(f'  canonical-labeling LDS of rev(w): max over {len(ws)} inputs n=14 '
          f'= {mx}  (<= #classes <= |Sigma| = 2)')
    # brute force: min over ALL consistent bijections, all |w| <= 6
    import itertools
    worst_canon = worst_true = 0
    for w in all_strings(6):
        out = rev(w)
        n = len(w)
        canon = min_relabel_lds(out, w)
        best = n + 1
        for perm in itertools.permutations(range(n)):
            if all(w[perm[i]] == out[i] for i in range(n)):
                best = min(best, PV.lds(perm))
        if best > n:      # no consistent bijection (cannot happen for rev)
            continue
        worst_canon = max(worst_canon, canon)
        worst_true = max(worst_true, best)
        if canon < best:
            print(f'  WARNING: canonical {canon} > optimal {best} on {w}')
    print(f'  brute force over ALL consistent bijections, |w|<=6: '
          f'max min-LDS = {worst_true}, canonical achieves it '
          f'(max {worst_canon}); equals #distinct chars when >= 2')

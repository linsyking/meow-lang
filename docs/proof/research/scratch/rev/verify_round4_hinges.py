"""ROUND 4 - CROSS-HINGE TESTS (coordinator priority 1).

Question: are Conjectures A/B/C (built to exclude rev from L) REV-SPECIFIC,
or do they also exclude the other two hinges' canonical functions?

  Hinge 1 (once): P(X) = takeWhile != b  -- the longest b-free prefix.
     (once/REPORT.md R1-R3: P in L <=> del1b in L <=> delete-leftmost-b.)
  Hinge 3 (L+R): f2 = [b/aa]^R -- the R-pass A='b', B='aa'; the minimal
     hard instance of rho(A,B,C) = [A/B]^R C (lr/REPORT.md; not
     left-subsequential, so no constant-pattern L-pipeline computes it).

For each function we measure on ALL binary inputs up to length NPROV (prov
side) and a battery at length NINF (influence side):
  prov side   : LDS and mult of the natural atom-provenance,
                ratio LDS/mult (Conjecture A's per-multiplicity price),
  influence   : D(w,p) = output positions changed by flipping w at p;
                crossings of the induced partial matching (Conjecture C),
                len-changing rows, singleton rows, mass.
P's provenance is forced (its output chars are verbatim w-chars in order);
f2's provenance is computed by a labeled right-to-left substitution
lsubstR, cross-checked against lrcore.substR (rev-duality-verified, lr dir).

Predictions (coordinator): P order-preserving (crossings 0, LDS 1, mult 1);
f2 local reordering only (constant-bounded crossings).  If both hold, the
A/B/C family is rev-SPECIFIC: three hinges need three different lemmas.
If either fails, there is a unified separation theorem.
"""
import sys
from collections import defaultdict

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/lr')
import lrcore  # noqa: E402  (substR, rev-duality-verified in lr/verify_r1.py)

import prov as PV  # noqa: E402
from prov import (lab_input, lab_const, lsubst, lden, labels, mult, lds,  # noqa
                  lis, content, Undefined)

HERE = '/home/cc/projects/meow-lang/docs/proof/research/scratch/rev'
sys.path.insert(0, HERE)
import lcore as L  # noqa: E402
from lcore import K, V, C, S, all_strings, rev  # noqa: E402
import r2lib as RL  # noqa: E402

NPROV = 10      # prov side: all binary strings up to length 10
NINF = 12       # influence side: all binary strings of length 12 (4096)


# ------------------------------------------------------------- the functions

def P(w):
    """takeWhile != b: the longest b-free prefix (hinge 1 reduction)."""
    i = w.find('b')
    return w if i < 0 else w[:i]


def f2(w):
    """[b/aa]^R w (hinge 3 / rho minimal instance)."""
    return lrcore.substR('b', 'aa', w)


# ------------------------------------------- labeled provenance of each

def provP(w):
    """P's output chars are verbatim w-chars in order: forced provenance."""
    i = w.find('b')
    val = lab_input(w) if i < 0 else lab_input(w)[:i]
    return val


def lsubstR(A, B, T):
    """[A/B]^R T on labeled values (mirror of prov.lsubst, rightmost-first).

    Rightmost match of B in the unscanned prefix; the insertion A is never
    rescanned (matches of later rounds live strictly left of it).
    """
    m = len(B)
    bchars = tuple(c for c, _ in B)
    parts, end = [], len(T)
    while end >= m:
        s = -1
        for i in range(end - m, -1, -1):
            if tuple(c for c, _ in T[i:i + m]) == bchars:
                s = i
                break
        if s < 0:
            break
        parts.append(T[s + m:end])
        parts.append(A)
        end = s
    parts.append(T[:end])
    out = []
    for chunk in reversed(parts):
        out.extend(chunk)
    return tuple(out)


def provF2(w):
    """labeled evaluation of ('SR', 'b', 'aa', X) on w."""
    return lsubstR(lab_const('b'), lab_const('aa'), lab_input(w))


# ------------------------------------------------------- influence machinery

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
    disp = max((abs(pi[p] - p) for p in perfect), default=0)
    return {'rows': len(D), 'singletons': len(single), 'mass': mass,
            'match': len(perfect), 'crossings': crossings,
            'maxdisp': disp,
            'lenrows': sum(1 for p in D if not isinstance(D[p], list)),
            'empty': sum(1 for p in D if isinstance(D[p], list)
                         and not D[p])}


def influence_of(f, w):
    """D(w,p) for content function f (single flip a<->b)."""
    base = f(w)
    D = {}
    for p in range(len(w)):
        w2 = w[:p] + ('a' if w[p] == 'b' else 'b') + w[p + 1:]
        o2 = f(w2)
        if len(o2) == len(base):
            D[p] = [i for i in range(len(base)) if o2[i] != base[i]]
        else:
            D[p] = ('len',)
    return D


# ------------------------------------------------------------------ checks

def check(name):
    print(f'--- {name} ---')
    # 0. content sanity of the labeled machinery (f2 only)
    if name == 'f2':
        bad = 0
        for w in all_strings(12):
            if content(provF2(w)) != f2(w):
                bad += 1
        print(f'  lsubstR faithfulness on ALL |w|<=12: '
              f'{"PASS" if bad == 0 else f"FAIL({bad})"}')

    # 1. prov side: LDS, mult, ratio over the full battery
    mx_lds = mx_mult = mx_ratio = 0
    for w in all_strings(NPROV):
        val = provP(w) if name == 'P' else provF2(w)
        pr = labels(val)
        m_, d_ = mult(pr), lds(pr)
        mx_lds, mx_mult = max(mx_lds, d_), max(mx_mult, m_)
        if m_ >= 1:
            mx_ratio = max(mx_ratio, d_ / m_)
    print(f'  prov  (all |w|<={NPROV}): max LDS={mx_lds}  max mult={mx_mult}'
          f'  max LDS/mult={mx_ratio}')

    # 2. influence side: full battery at |w|=NINF
    tot = defaultdict(int)
    mx = defaultdict(int)
    for w in all_strings(NINF):
        D = influence_of(P if name == 'P' else f2, w)
        st = describe(D)
        for k, v in st.items():
            tot[k] += v
            mx[k] = max(mx[k], v)
    n_runs = len(list(all_strings(NINF)))
    print(f'  infl  (all {n_runs} strings |w|={NINF}): max per-input '
          f'{dict(mx)}')
    print(f'        mean per-input: '
          f'{ {k: round(tot[k]/n_runs, 2) for k in sorted(tot)} }')


# --------------------------------------------- ladder additions (priority 2)

def ladder_extra():
    """crossings for the anchor family (in L) at n=14, for the table."""
    print('--- ladder (L-expressions, n=14, worst input over 512 samples) ---')
    import random
    rng = random.Random(2718)
    ws = [''.join(rng.choice('ab') for _ in range(14)) for _ in range(512)]

    def out_of(e, w):
        r = L.den_try(e, (w,))
        return None if r[0] != 'ok' else r[1]

    def infl(e, w):
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

    exprs = {
        'lastX (prop:last)': RL.last_expr(),
        'initX': RL.init_expr(),
        'rotr1X': RL.rotr1_expr(),
        'swapflX': RL.swapfl_expr(),
    }
    for name, e in exprs.items():
        best = None
        for w in ws:
            st = infl(e, w)
            if st is None:
                continue
            if best is None or st['crossings'] > best['crossings']:
                best = st
        print(f'  {name:20s} size={L.size(e):4d}  {best}')

    # rev-last-k family on a fixed n=14 input (re-run for the table)
    def rev_last_k(w, k):
        return rev(w[-k:]) + w[:-k]
    w0 = 'abbaababbaabba'
    for k in (1, 2, 3, 4):
        D = influence_of(lambda x: rev_last_k(x, k), w0)
        st = describe(D)
        print(f'  rev-last-{k} (fn)     n=14: crossings={st["crossings"]}'
              f'  (k(n-k)={k * (14 - k)})')
    D = influence_of(rev, w0)
    st = describe(D)
    print(f'  rev (fn)              n=14: crossings={st["crossings"]}'
          f'  (C(14,2)={14 * 13 // 2})')


if __name__ == '__main__':
    check('P')
    check('f2')
    ladder_extra()

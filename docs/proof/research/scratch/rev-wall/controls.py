"""Controls for the run-level sweep.
(1) POSITIVE CONTROL (F1): E_swap = [b/w]bigsym outputs (j, i) on F1 --
    a j-dominant lead.  The F1-analogue of the dominance check MUST flag
    it; otherwise the checker is too weak to be evidence.
(2) E_asym on F1 must NOT be flagged (its length is s-dominant per cell).
(3) W2 catalogue through the full checker (ww, big2, lead-augmented w2,
    junction shaves, merge-scalings) -- all must pass.
"""
import sys
sys.path.insert(0, '.')
import sweep2 as SW
from lcore import K, V, C, S, pp
import prov as PV

X = V(0)

# ---------- F1 versions of the slope machinery ----------
def w1(i, j): return 'a' * i + 'b' + 'a' * j
def valtry(e, w):
    try:
        return PV.content(PV.lden(e, (PV.lab_input(w),)))
    except PV.Undefined:
        return None
def runs_of(v):
    out, cur = [], 0
    for c in v:
        if c == 'a': cur += 1
        else: out.append(cur); cur = 0
    out.append(cur)
    return out

def f1_lead_slopes(e, bases=[(4, 4), (2, 9), (9, 2), (5, 6), (6, 5)]):
    out = []
    for (i0, j0) in bases:
        col_i = []
        col_j = []
        ok = True
        for t in SW.TLINE:
            v = valtry(e, w1(i0 + t, j0))
            if v is None: ok = False; break
            col_i.append(runs_of(v)[0])
            v = valtry(e, w1(i0, j0 + t))
            if v is None: ok = False; break
            col_j.append(runs_of(v)[0])
        if not ok: continue
        s_i = ((col_i[6] - col_i[0]) / 12.0, (col_i[12] - col_i[6]) / 12.0)
        s_j = ((col_j[6] - col_j[0]) / 12.0, (col_j[12] - col_j[6]) / 12.0)
        out.append((s_i, s_j))
    return out

print('== control 1: E_swap on F1 (expect D1j flags) ==')
merge = S(K(''), K('b'), X)
bigsym = C(C(merge, K('b')), merge)
E_swap = S(K('b'), X, bigsym)
for (s_i, s_j) in f1_lead_slopes(E_swap):
    ai = SW.accepted(s_i); aj = SW.accepted(s_j)
    print('  i-slopes %s (acc %s)  j-slopes %s (acc %s) -> %s' %
          (tuple(round(x, 2) for x in s_i), ai,
           tuple(round(x, 2) for x in s_j), aj,
           'FLAG D1j' if ai and aj and s_i[0] < s_j[0] - SW.MARGIN
           and s_i[1] < s_j[1] - SW.MARGIN else 'no flag'))

print('== control 2: E_asym on F1 (expect no flag) ==')
dbl = S(K('aa'), K('a'), X)
diff = S(K(''), merge, dbl)
T = C(X, diff)
Q = C(K('b'), merge)
E_asym = S(K(''), K('b'), S(K(''), Q, T))
for (s_i, s_j) in f1_lead_slopes(E_asym):
    ai = SW.accepted(s_i); aj = SW.accepted(s_j)
    print('  i-slopes %s (acc %s)  j-slopes %s (acc %s)' %
          (tuple(round(x, 2) for x in s_i), ai,
           tuple(round(x, 2) for x in s_j), aj))

print('== control 3: W2 catalogue through the full checker ==')
def w2(i, j, k): return 'a' * i + 'b' + 'a' * j + 'b' + 'a' * k
merge2 = S(K(''), K('b'), X)
big2 = C(C(merge2, K('b')), merge2)
halfm = S(K('a'), K('aa'), merge2)
R_diag = C(C(halfm, K('b')), halfm)
E_aug = S(R_diag, K('b'), X)
shave = S(K('b'), K('ba'), X)             # [b/ba]w2 = (i, j-1, k) on cells
E_M_bab = S(K('bab'), X, C(C(S(K(''), K('bab'), X), K('bab')),
                            S(K(''), K('bab'), X)))
for (name, e) in [('ww C(X,X)', C(X, X)), ('big2', big2),
                  ('E_aug [R_diag/b]w2', E_aug), ('[b/ba]w2', shave),
                  ('E_M(bab)', E_M_bab)]:
    fs = SW.check(e)
    print('  %-20s -> %s' % (name, fs if fs is not None else 'NOT CLEANLY EVALUABLE'))

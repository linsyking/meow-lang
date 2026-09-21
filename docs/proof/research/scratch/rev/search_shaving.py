"""ROUND 4 - THE SHAVING LEMMA (main directive).

THE SHAVING LEMMA (v2; v1 refuted by the machine below).  A pass
consumes matched blocks by a position-based scan (def:subst: at each
position test the window, on a match jump |B|).  The scan is
memoryless.  Consider a text with m copies of the same value A at
disjoint sites (what one insertion pass produces: V_0 A V_1 ... A V_m)
and a later pass [R/B], m_pat = |B|.  V1 claimed the copy residuals are
a function of the entry offset alone (at most |B| distinct) -- FALSE:
the machine found 33 counterexamples in 3000 trials (e.g. A = 'aabb',
B = 'ba', gaps ab/baaa/ba/a: residuals {1,2,3}, {0,1,2,3}, {0,1,2}).
The exit straddles break it: matches starting inside a copy extend
into the following gap, so the residual also depends on what follows.
V2 (correct): the residual of copy c is a function of

    (o_c, h_c) = (entry offset in {0..|B|-1}, the |B|-1 text
                  characters following the copy),

hence at most |B| * |Sigma|^{|B|-1} distinct residuals -- a CONSTANT
for constant patterns, unbounded for variable ones.  Consequently,
per pass and multiplicatively over passes in sequence:

  (1v2) #distinct residuals <= |B| * |Sigma|^{|B|-1},
  (2v2) #distinct final residuals <= prod_j |B_j| * |Sigma|^{|B_j|-1},
  (3)   at final multiplicity 1 every residual class with >= 2 copies
        is empty (its atoms would be duplicated), so a strictly
        decreasing chain through former copies of A touches at most
        (number of nonempty classes) copies, <= LDS(A) atoms each:
            chain <= LDS(A) * prod_j |B_j(w)| * prod_j s^{|B_j|-1}.

For CONSTANT patterns every factor is O(1): deletion passes convert
none of the inserted structure into disorder beyond a constant.  The
gap to Conjecture B is exactly the VARIABLE patterns (|B(w)| grows
with |w|) -- the same gap as thm:subsequential's.

PART A verifies v1's failure count and v2's function property
(same (o,h) => same residual) brute-force on labeled copy-gap texts.
PART B attacks Conjecture B through that gap: 3-pass pipelines shaped
"copy, then shave", with LONG VARIABLE needles allowed (the 2-pass
exhaustive search of round 3 capped at LDS@mult1 = 3).  Includes the
double-sided-cut hand construction.  A chain at mult 1 > 3 would refute
Conjecture B; failure is evidence for the lemma's quantitative form.
"""
import random
import sys
from collections import defaultdict

import lcore as L
from lcore import K, V, C, comp, battery
import prov as PV
import r2lib as RL

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk  # noqa: E402

sg = tk.BIN
rng = random.Random(14142)

# =========================================================== PART A: lemma

def make_text(copies, gaps, A, gapstrs):
    """atoms labeled ('c', p) inside copies, ('g', j, i) inside gaps."""
    T = []
    for j in range(copies):
        for i, c in enumerate(gapstrs[j]):
            T.append((c, ('g', j, i)))
        for p, c in enumerate(A):
            T.append((c, ('c', p)))
    for i, c in enumerate(gapstrs[copies]):
        T.append((c, ('g', copies, i)))
    return tuple(T)


def make_text_tagged(gapstrs, A):
    """gap_0 A gap_1 A ... A gap_m (len(gapstrs) = m+1)."""
    T = []
    for j, g in enumerate(gapstrs[:-1]):
        for i, c in enumerate(g):
            T.append((c, ('g', j, i)))
        for p, c in enumerate(A):
            T.append((c, ('c', j, p)))
    for i, c in enumerate(gapstrs[-1]):
        T.append((c, ('g', len(gapstrs) - 1, i)))
    return tuple(T)


def copy_residuals(T, B):
    """[eps/B]T; residual of copy j = {p : ('c', j, p) survives}."""
    out = PV.lsubst((), PV.lab_const(B), T)
    res = defaultdict(set)
    for _, lab in out:
        if lab[0] == 'c':
            res[lab[1]].add(lab[2])
    return res


def scan_with_entry(T, B):
    """greedy [eps/B] on labeled atoms; returns (output, entry_offsets):
    entry_offsets[c] = first scan position landing inside copy c minus
    copy start (in {0..|B|-1}), or None if no scan position lands inside
    (copy fully consumed by straddling matches)."""
    m = len(B)
    bch = tuple(B)
    chars = [c for c, _ in T]
    starts = {}
    for idx, (_, lab) in enumerate(T):
        if lab[0] == 'c' and lab[1] not in starts:
            starts[lab[1]] = idx
    out = []
    entry = {}
    i, n = 0, len(T)
    while i < n:
        for j, st in starts.items():
            if j not in entry and i >= st:
                entry[j] = i - st
        if tuple(chars[i:i + m]) == bch:
            i += m
        else:
            out.append(T[i])
            i += 1
    return tuple(out), entry


def verify_lemma(trials=3000):
    bad1 = bad2 = badfn = 0
    for t in range(trials):
        m = rng.randrange(1, 5)
        A = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 6)))
        gapstrs = [''.join(rng.choice('ab') for _ in range(rng.randrange(0, 5)))
                   for _ in range(m + 1)]
        if t % 3 == 0:
            A = rng.choice(['ab', 'aab', 'abb', 'aaab', 'bbba', 'aabb'])[:5]
            gapstrs = [rng.choice(['', 'b', 'bb', 'bbb', 'aab', 'ba'])
                       for _ in range(m + 1)]
        T = make_text_tagged(gapstrs, A)
        B = ''.join(rng.choice('ab') for _ in range(rng.randrange(1, 5)))
        out, entry = scan_with_entry(T, B)
        res = defaultdict(set)
        for _, lab in out:
            if lab[0] == 'c':
                res[lab[1]].add(lab[2])
        nres = len({tuple(sorted(v)) for v in res.values()})
        # v1 (refuted): residuals a function of the entry offset alone
        seen = {}
        for j in res:
            o = entry.get(j)
            if o in seen and tuple(sorted(res[j])) != seen[o]:
                bad1 += 1
                seen[o] = None     # report once per trial
                if bad1 <= 3:
                    print(f'  v1 COUNTEREXAMPLE: A={A} B={B} '
                          f'gaps={gapstrs}')
                break
            seen[o] = tuple(sorted(res[j]))
        # v2: residual a function of (entry offset, following |B|-1 chars)
        content = ''.join(c for c, _ in T)
        ends = {}
        for idx, (_, lab) in enumerate(T):
            if lab[0] == 'c':
                ends[lab[1]] = idx
        grp = {}
        for j in res:
            h = content[ends[j] + 1:ends[j] + len(B)]
            key = (entry.get(j), h)
            if key in grp and tuple(sorted(res[j])) != grp[key]:
                badfn += 1
                if badfn <= 3:
                    print(f'  v2 COUNTEREXAMPLE: A={A} B={B} '
                          f'gaps={gapstrs} copy {j} key={key}')
                break
            grp[key] = tuple(sorted(res[j]))
        # count bound
        bound = len(B) * (2 ** max(0, len(B) - 1))
        if nres > bound:
            bad2 += 1
            print(f'  v2 COUNT FAIL: A={A} B={B} gaps={gapstrs} '
                  f'distinct={nres} bound={bound}')
    print(f'PART A: {trials} random copy-gap texts, |B|<=4:')
    print(f'  v1 (offset alone):       refuted, {bad1} trials with '
          f'same-offset/different-residual')
    print(f'  v2 ((o,h) function):    {"PASS" if badfn == 0 else f"FAIL({badfn})"}')
    print(f'  v2 count |B|*s^(|B|-1): '
          f'{"PASS" if bad2 == 0 else f"FAIL({bad2})"}')


# ============================== PART B: attack Conjecture B in the gap

LIB_P = dict(RL.PATTERNS)
LIB_R = dict(RL.REPLACEMENTS)
LIB_R['XX'] = lambda: C(V(0), V(0))
# extra long-needle deletion patterns (run constants up to 4)
EXTRA_P = {'b2': 'bb', 'b3': 'bbb', 'b4': 'bbbb', 'a2': 'aa',
           'a3': 'aaa', 'a4': 'aaaa', 'ab2': 'abb', 'ba2': 'baa'}

FIT_W = battery(5) + ['a' * 8 + 'b', 'b' + 'a' * 8, 'ab' * 8, 'aab' * 6,
                      'aaaaabbbb' * 2, 'bbaabbaa' * 2, 'bbbaaa' * 3,
                      'b' + 'ab' * 6, 'bb' + 'a' * 12]
FULL_W = battery(8) + FIT_W[33:]

PVals, RVals = {}, {}
for p, b in list(LIB_P.items()) + list(EXTRA_P.items()):
    ast = ('K', b) if isinstance(b, str) else b()
    PVals[p] = {}
    for w in FULL_W:
        try:
            PVals[p][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            PVals[p][w] = None
for r, b in LIB_R.items():
    ast = b()
    RVals[r] = {}
    for w in FULL_W:
        try:
            RVals[r][w] = PV.lden(ast, (PV.lab_input(w),))
        except PV.Undefined:
            RVals[r][w] = None


def run(pipeline, Ws, cap=2000):
    out = {}
    for w in Ws:
        T = PV.lab_input(w)
        for (p, r) in pipeline:
            B = PVals[p].get(w)
            A = RVals[r].get(w)
            if B is None or not B or not A:
                return None
            T = PV.lsubst(A, B, T)
            if len(T) > cap:
                return None
        out[w] = T
    return out


def fit(pipeline):
    res = run(pipeline, FIT_W)
    if res is None:
        return (-1, 0, 0)
    mB = mD = mM = 0
    for w, T in res.items():
        pr = PV.labels(T)
        if not pr:
            continue
        d, m = PV.lds(pr), PV.mult(pr)
        mD, mM = max(mD, d), max(mM, m)
        if m == 1:
            mB = max(mB, d)
    return (mB, mD, mM)


def attack():
    # copy-creating first passes: [A/sigma] for variable A
    copy_first = [(p, r) for p in ('a', 'b', 'ab', 'ba', 'bb', 'aa')
                  for r in RVals if r not in ('eps',)]
    shave = [(p, 'eps') for p in PVals
             if all(PVals[p][w] is not None for w in FIT_W)]
    space = copy_first + shave
    print(f'PART B space: {len(copy_first)} copy-passes + '
          f'{len(shave)} shave-passes')

    POP, GEN = 250, 150

    def rand_ind():
        n = rng.randrange(2, 5)
        ind = [rng.choice(copy_first)]
        for _ in range(n - 1):
            ind.append(rng.choice(shave))
        return ind

    def mutate(m):
        m = list(m)
        op = rng.random()
        if op < 0.35:
            m[rng.randrange(len(m))] = rng.choice(space)
        elif op < 0.6:
            m.insert(rng.randrange(len(m) + 1), rng.choice(shave))
        elif op < 0.75 and len(m) > 1:
            del m[rng.randrange(len(m))]
        else:
            m = rand_ind()
        if not any(p in copy_first_set for (p, _) in m):
            m[0] = rng.choice(copy_first)
        return m[:6]

    copy_first_set = {(p, r) for (p, r) in copy_first}
    pop = [rand_ind() for _ in range(POP)]
    fits = [fit(p) for p in pop]
    best = (None, (-1, 0, 0))
    for g in range(GEN):
        order = sorted(range(POP), key=lambda i: fits[i], reverse=True)
        if fits[order[0]] > best[1]:
            best = (pop[order[0]], fits[order[0]])
            print(f'  gen {g}: best {fits[order[0]]} {pop[order[0]]}',
                  flush=True)
        elite = [pop[i] for i in order[:25]]
        new = [list(x) for x in elite]
        while len(new) < POP:
            if rng.random() < 0.6:
                new.append(mutate(pop[rng.randrange(POP)]))
            else:
                a = pop[rng.randrange(POP)]
                b = pop[rng.randrange(POP)]
                cut = rng.randrange(1, min(len(a), len(b)) + 1)
                new.append(mutate(a[:cut] + b[cut:]))
        pop, fits = new, [fit(p) for p in new]

    print(f'  FINAL BEST: {best[1]} {best[0]}')
    # verify on FULL battery
    res = run(best[0], FULL_W)
    if res is not None:
        mB = mD = mM = 0
        for w, T in res.items():
            pr = PV.labels(T)
            if not pr:
                continue
            d, m = PV.lds(pr), PV.mult(pr)
            mD, mM = max(mD, d), max(mM, m)
            if m == 1:
                mB = max(mB, d)
        print(f'  re-verified on FULL (|w|<=8 + structured): '
              f'LDS@mult1={mB} maxLDS={mD} maxmult={mM}')
    return best


# ------------------- hand constructions (double-sided singleton cuts)

def hand_constructions():
    """The double-sided-cut idea: copies whose residuals shrink to
    singletons {K-j} by cutting left depths via pass 1 and right depths
    via pass 3, leaving a decreasing chain at mult 1.  Closest pipeline
    realizations over run alphabets, measured directly."""
    print('PART C: hand constructions (double-sided singleton cuts)')
    cands = [
        # A = bbbaaaa copies via [A/b] on gap-shaped w; cut left b^3;
        # kill a-tails; cut again
        [('bbbaaaa', 'b'), ('', 'bbb'), ('', 'aaaa')],
        [('bbbaaaa', 'b'), ('', 'bbb'), ('', 'baaa'), ('', 'aa')],
        [('aab', 'b'), ('', 'aa'), ('', 'ab')],
        [('baaa', 'b'), ('', 'bb'), ('', 'aaa')],
        [('abb', 'b'), ('', 'aabb'), ('', 'bb')],
        [('aabb', 'a'), ('', 'bb'), ('', 'aa')],
        # longer run copies with deeper cuts
        [('bbbaaaaaa', 'b'), ('', 'bbb'), ('', 'aaaaaa'), ('', 'baa')],
    ]
    for pipe in cands:
        # pipeline of constant passes; test on run-structured inputs
        ws = ['b' + 'ab' * 6, 'bab' * 6, 'bb' + 'ab' * 6,
              'ab' * 8, 'a' * 8 + 'b' * 4, 'b' * 4 + 'a' * 8,
              'baab' * 4, 'b' + 'a' * 16]
        best = (0, 0, 0, None)
        for w in ws:
            T = PV.lab_input(w)
            ok = True
            for (R, P) in pipe:
                if not P:
                    ok = False
                    break
                T = PV.lsubst(PV.lab_const(R), PV.lab_const(P), T)
                if len(T) > 2000:
                    ok = False
                    break
            if not ok:
                continue
            pr = PV.labels(T)
            if not pr:
                continue
            d, m = PV.lds(pr), PV.mult(pr)
            if d > best[0] or (d == best[0] and m < best[1]):
                best = (d, m, len(T), w)
        print(f'  {pipe}: best LDS={best[0]} at mult={best[1]}')


if __name__ == '__main__':
    verify_lemma()
    hand_constructions()
    attack()

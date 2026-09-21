"""ROUND 1 verification: evaluator cross-check, toolkit/rotation sanity,
constant-pattern pipelines vs rev (BFS + near-miss analysis).

Everything here is cheap re-verification of known facts (the paper's
thm:subsequential already kills constant patterns for rev) -- the point is
(a) the machinery works, (b) collect NEAR-MISS data: which output positions
do the closest constant-pattern pipelines get wrong.
"""
import itertools
import random
import sys
import time

import lcore as L
from lcore import K, V, C, S, comp, pipe, den, den_try, rev, battery

sys.path.insert(0, L._LAZY_PASS)
import core as lpc          # noqa: E402  (the cross-verified lazy_pass core)
import toolkit as tk        # noqa: E402  (paper Sec. 2 builders)

OK = []


def check(name, cond, detail=''):
    OK.append((name, cond))
    print(f"{'PASS' if cond else 'FAIL'}  {name}  {detail}")


# ---------------------------------------------------------------- 1. subst
# paper Def. def:subst examples
check('subst [ab/b]b = ab', L.subst('ab', 'b', 'b') == 'ab')
check('subst [A/A]S = S', all(L.subst(w, w, s) == s
                              for w in ('a', 'b', 'ab', 'ba', 'aab')
                              for s in ('', 'a', 'b', 'abba', 'aab', 'baab', 'bab')))
check('subst [eps/b]abab = aa (deletion, greedy)', L.subst('', 'b', 'abab') == 'aa')
check('subst [a/aa]a = a (no rescan of inserted text)', L.subst('a', 'aa', 'a') == 'a')
# greedy leftmost, non-overlap: [x/ab] on 'aab' -> a at 1? no: leftmost ab at 1 -> 'ax'
check('subst greedy leftmost', L.subst('X', 'ab', 'aab') == 'aX')

# ---------------------------------------------------------------- 2. evaluator
# cross-check lcore.den vs core.ev_eager (== def:den on call-free exprs)
rng = random.Random(20260921)


def rand_expr(depth, nvars=1, cons=('a', 'b', '', 'ab', 'ba')):
    t = rng.random()
    if depth == 0 or t < 0.25:
        return V(rng.randrange(nvars)) if rng.random() < 0.5 else K(rng.choice(cons))
    if t < 0.55:
        return C(rand_expr(depth - 1, nvars, cons), rand_expr(depth - 1, nvars, cons))
    return S(rand_expr(depth - 1, nvars, cons),
             rand_expr(depth - 1, nvars, cons),
             rand_expr(depth - 1, nvars, cons))


n_disagree = n_undef_mismatch = 0
for trial in range(4000):
    e = rand_expr(rng.choice([1, 2, 3, 4]))
    args = tuple(''.join(rng.choice('ab') for _ in range(rng.randrange(0, 7)))
                 for _ in range(1))
    mine = den_try(e, args)
    try:
        w = lpc.ev_eager({}, e, args, 0, 4000, [0], 10**7)
        theirs = ('ok', w)
    except lpc.Undefined:
        theirs = ('undef', None)
    except lpc.Diverge:
        theirs = ('diverge', None)
    if mine[0] == 'undef' and theirs[0] == 'diverge':
        continue  # depth cap on a big expression; skip
    if mine != theirs:
        if (mine[0] == 'undef') != (theirs[0] == 'undef'):
            n_undef_mismatch += 1
        else:
            n_disagree += 1
check('den == ev_eager on 4000 random exprs', n_disagree == 0 and n_undef_mismatch == 0,
      f'disagreements={n_disagree}, undef-mismatches={n_undef_mismatch}')

# ---------------------------------------------------------------- 3. toolkit
SIG = tk.BIN   # Sigma = {a,b}, b_='a', x_='b', TOP='b', BOT='a'
tests = battery(6)   # 127 strings
fails = []
for s in tests:
    for name, e, want in [
        ('enc/dec', L.comp([(L.K(SIG.b), L.K(SIG.x + SIG.b))],
                           tk.enc(SIG, V(0))), s),
        ('head', tk.head(SIG, V(0)), s[:1]),
        ('tail', tk.tail(SIG, V(0)), s[1:]),
        ('cat', tk.cat(SIG, V(0), V(0)), s + s),
        ('cat2', tk.cat(SIG, K('a'), tk.cat(SIG, V(0), K('b'))), 'a' + s + 'b'),
    ]:
        r = den_try(e, (s,))
        if r[0] != 'ok' or r[1] != want:
            fails.append((name, s, r, want))
check('toolkit head/tail/cat/enc-dec on 127 strings', not fails, f'{fails[:3]}')

eqf = if_f = 0
for x in tests[:40]:
    for y in tests[:40]:
        r = den_try(tk.eq(SIG, V(0), V(1)), (x, y))
        w = 'b' if x == y else 'a'
        if r != ('ok', w):
            eqf += 1
        r2 = den_try(tk.if_(SIG, tk.eq(SIG, V(0), V(1)), K('ab'), V(0)), (x, y))
        if r2 != ('ok', 'ab' if x == y else x):
            if_f += 1
check('eq/if 1600 pairs', eqf == 0 and if_f == 0, f'eq fails {eqf}, if fails {if_f}')

# ---------------------------------------------------------------- 4. rotation
# rotation by 1 = cat(tail X, head X);  by k via tail^k/head-chain
def rot1(w):
    return w[1:] + w[:1] if w else w


def rotk(w, k):
    if not w:
        return w
    k %= len(w)
    return w[k:] + w[:k]


e_rot1 = tk.cat(SIG, tk.tail(SIG, V(0)), tk.head(SIG, V(0)))
bad = [s for s in battery(8) if den_try(e_rot1, (s,))[1] != rot1(s)]
check('rotation by 1 (cat(tail X, head X)) on all |w|<=8', not bad, str(bad[:3]))

e_rot2 = tk.cat(SIG, tk.tail(SIG, tk.tail(SIG, V(0))),
                tk.cat(SIG, tk.head(SIG, V(0)), tk.head(SIG, tk.tail(SIG, V(0)))))
bad = [s for s in battery(8) if den_try(e_rot2, (s,))[1] != rotk(s, 2)]
check('rotation by 2 on all |w|<=8', not bad, str(bad[:3]))

# ---------------------------------------------------------------- 5. rev oracle
check('rev oracle', all(den_try(K(rev(s)), (s,))[1] == rev(s) for s in tests[:10]))

# ---------------------------------------------------------------- 6. BFS
# constant-pattern L-pipelines vs rev: exhaustive BFS in behavior space.
# (thm:subsequential says impossible; this confirms empirically + near-miss)

def sig_of(behavior):
    return tuple(behavior)


def bfs_const(target_fn, nmax=7, pat_len=2, rep_len=2, depth=3, sigma='ab',
              extra_sigma='c', verbose=True):
    """BFS over pipelines of constant passes (pattern len 1..pat_len,
    replacement len 0..rep_len, over sigma+extra_sigma for the CONSTANTS but
    evaluated on sigma inputs).  Returns (found_pipeline, seen) with the
    best near-misses."""
    tests = battery(nmax, sigma)
    target = tuple(target_fn(s) for s in tests)
    pats = [''.join(t) for k in range(1, pat_len + 1)
            for t in itertools.product(sigma + extra_sigma, repeat=k)]
    repls = [''] + [''.join(t) for k in range(1, rep_len + 1)
                    for t in itertools.product(sigma + extra_sigma, repeat=k)]
    passes = [(P, R) for P in pats for R in repls]
    ident = tuple(tests)
    seen = {ident: None}
    frontier = [ident]
    if verbose:
        print(f'  BFS: {len(passes)} passes, {len(tests)} tests', flush=True)
    found = None
    for level in range(1, depth + 1):
        t0 = time.time()
        newf = []
        for sig in frontier:
            for (P, R) in passes:
                ns = tuple(s.replace(P, R) for s in sig)
                if ns not in seen:
                    seen[ns] = (sig, (P, R))
                    newf.append(ns)
        frontier = newf
        if verbose:
            print(f'  level {level}: frontier {len(newf)}, total {len(seen)}, '
                  f'{time.time()-t0:.1f}s', flush=True)
        if target in seen:
            node, pl = target, []
            while seen[node] is not None:
                pre, last = seen[node]
                pl.append(last)
                node = pre
            found = list(reversed(pl))
            break
    return found, seen, target, tests


t0 = time.time()
found, seen, target, tests = bfs_const(rev, nmax=7, pat_len=2, rep_len=2, depth=3)
check('constant-pattern BFS depth 3 (pat,rep<=2, abc): no rev', found is None,
      f'({time.time()-t0:.0f}s, {len(seen)} behaviors)')

# near-miss analysis over the whole reachable behavior set
def mismatch_positions(out, tgt):
    """list of bad output indices, or None if lengths differ."""
    if len(out) != len(tgt):
        return None
    return [i for i in range(len(tgt)) if out[i] != tgt[i]]


def pipeline_of(sig):
    node, pl = sig, []
    while seen[node] is not None:
        pre, last = seen[node]
        pl.append(last)
        node = pre
    return list(reversed(pl))


# rank every reachable behavior by (strings wrong, total bad chars), among
# the LENGTH-PRESERVING ones (rev is length-preserving)
best = []
for sig in seen:
    ndiff = totbad = len_diff = 0
    for s, o, tg in zip(tests, sig, target):
        d = mismatch_positions(o, tg)
        if d is None:
            len_diff += 1
        elif d:
            ndiff += 1
            totbad += len(d)
    if len_diff == 0 and ndiff > 0:
        best.append((ndiff, totbad, sig))
best.sort(key=lambda x: (x[0], x[1]))
n_pal = sum(1 for s in tests if s == rev(s))
print(f'  BFS depth<=3 length-preserving near-misses: {len(best)}  '
      f'(identity: wrong on {len(tests)-n_pal}/{len(tests)}; {n_pal} palindromes)')
for nd, tot, sig in best[:3]:
    print(f'  near-miss: wrong on {nd}/{len(tests)} strings, {tot} bad chars; '
          f'pipeline(run order)={pipeline_of(sig)}')
# where do the best 3 fail? (relative position of mismatches)
for nd, tot, sig in best[:3]:
    rel = {}
    for s, o, tg in zip(tests, sig, target):
        if len(o) != len(tg) or not o:
            continue
        d = mismatch_positions(o, tg)
        for i in d:
            key = 'pos0' if i == 0 else ('last' if i == len(o) - 1 else 'mid')
            rel[key] = rel.get(key, 0) + 1
    print(f'    failure positions: {rel}')

# randomized deep constant pipelines, ranked by TOTAL mismatch over battery
tests8 = battery(8)   # 256 strings
tgt8 = [rev(s) for s in tests8]
pats = [''.join(t) for k in (1, 2) for t in itertools.product('abc', repeat=k)]
repls = [''] + [''.join(t) for k in (1, 2) for t in itertools.product('abc', repeat=k)]
passes = [(P, R) for P in pats for R in repls]
rng2 = random.Random(4242)
tried = 0
TOP = []
t0 = time.time()
while time.time() - t0 < 120:
    k = rng2.randrange(4, 8)
    pl = [rng2.choice(passes) for _ in range(k)]
    ndiff = totbad = 0
    for i, s in enumerate(tests8):
        t = s
        for (P, R) in pl:
            t = t.replace(P, R)
        if t != tgt8[i]:
            ndiff += 1
            totbad += (sum(1 for a, b in zip(t, tgt8[i]) if a != b)
                       + abs(len(t) - len(tgt8[i])))
    TOP.append((ndiff, totbad, tuple(pl)))
    tried += 1
TOP.sort()
print(f'  randomized: {tried} constant pipelines of 4-7 passes (abc, pat,rep<=2),'
      f' ranked by total mismatches over 256 inputs:')
for nd, tot, pl in TOP[:5]:
    print(f'    wrong on {nd}/256, {tot} bad chars: {list(pl)}')

print()
npass = sum(1 for _, c in OK if c)
print(f'=== ROUND 1: {npass}/{len(OK)} checks passed ===')
for n, c in OK:
    if not c:
        print('  FAILED:', n)

# ------------------------------------------------- 7. coordinator's prelim notes
# (a) [eps/b]X breaks the naive skew invariant "output[i] depends only on
#     w[0..i+c)": a late input flip moves EARLY output positions.
e_del = comp([('', 'b')], V(0))
bad = 0
for w in battery(7):
    if 'b' not in w:
        continue
    base = den(e_del, (w,))
    p = len(w) - 1                      # flip the LAST character
    w2 = w[:p] + ('a' if w[p] == 'b' else 'b')
    out2 = den(e_del, (w2,))
    # which output positions changed?
    chg = [i for i in range(min(len(base), len(out2))) if base[i] != out2[i]]
    chg += list(range(min(len(base), len(out2)),
                      max(len(base), len(out2))))
    early = [i for i in chg if i <= p - w[:p].count('b') - 2]
    if chg and min(chg) < p:            # a late flip moved an EARLIER position
        bad += 1
check('[eps/b]X: late flip moves earlier output positions (skew broken)',
      bad > 0, f'{bad} inputs exhibit it')
ex = 'abba'
print('  example: [eps/b] on abba ->', den(e_del, (ex,)), '; flip last ->',
      den(e_del, (ex[:-1] + ('b' if ex[-1] == 'a' else 'a'),)))

# (b) match-gating: [R/tail(X)]X.  tail(w) occurs in w at position 1 ALWAYS
#     (for |w|>=1), at position 0 iff w is constant.  So output[0] switches
#     between w[0] (nonconstant: pass replaces at 1) and R[0] (constant: pass
#     replaces at 0) -- a DEEP gate (constancy of the whole string) choosing
#     between two small-cone contents.
gate = S(K('XY'), tk.tail(SIG, V(0)), V(0))     # [XY / tail X] X
ok_a = ok_b = ok_c = True
for w in battery(7):
    n = len(w)
    if n <= 1:
        continue                      # tail(w) = eps: UNDEFINED pass
    r = den_try(gate, (w,))
    if len(set(w)) == 1:              # constant w: leftmost match at 0
        # match consumes w[:n-1]; leftover w[n-1] re-matches iff n-1<=1
        want = 'XYXY' if n == 2 else 'XY' + w[-1]
    else:                             # match at 1, w[0] emitted verbatim
        want = w[0] + 'XY'
    if r != ('ok', want):
        ok_a = False
        print('   gate mismatch', w, r, ('ok', want))
        break
check('[XY/tail X]X: output[0]=XY[0] iff w constant (|w|>=2), else w[0]',
      ok_a, '(deep gate selecting output[0]; n=2 leftover re-matches)')
# the gate needs the WHOLE string: flipping the LAST char of c^(n-1)d flips
# the gate and hence output[0] -- a deep causal cone reaching output[0]
fl = 0
for w in battery(7):
    n = len(w)
    if n < 3 or len(set(w)) != 2 or w[-1] == w[0]:
        continue                      # w = c^(n-1) d, c != d
    w2 = w[:-1] + w[0]                # flip last: now constant
    r1, r2 = den(gate, (w,)), den(gate, (w2,))
    if r1[0] != r2[0]:               # output[0]: w[0]=c  vs  'X'
        fl += 1
check('gate: flipping the LAST char flips output[0] (deep cone)',
      fl > 0, f'{fl} inputs (e.g. w=a^(n-1)b: output[0]=a vs X)')

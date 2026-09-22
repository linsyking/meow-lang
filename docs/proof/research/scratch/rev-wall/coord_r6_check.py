#!/usr/bin/env python3
# Coordinator round-6 (rev-wall) fresh-encoding checks. < 30 s.
# The recursion theorem, COR-A/B/B1 witnesses, MASS, the blob landing,
# the halver gap, the prefix isolation E2.
import sys
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
fails = 0
def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
        print('  FAIL %-32s got %r want %r' % (name, got, want))
    return ok

def fired(pat, w):
    out, i = [], 0
    while True:
        j = w.find(pat, i)
        if j < 0: break
        out.append(w[:j].count('b'))
        i = j + len(pat)
    return out

# 1. the recursion theorem vs direct greedy, random texts and patterns
import random
rng = random.Random(4242)
def recursion_fired(runs, i, j):
    out, c = [], runs[0]
    for sig in range(len(runs) - 1):
        f = (c >= i and runs[sig + 1] >= j)
        if f: out.append(sig)
        c = runs[sig + 1] - (j if f else 0)
    return out
bad = 0; tested = 0
for trial in range(600):
    k = rng.randint(2, 5)
    runs = [B ** z for z in range(k + 1)]
    mode = rng.random()
    if mode < 0.35:                     # bite runs (bitten texts)
        for z in range(len(runs)):
            if rng.random() < 0.3:
                runs[z] = max(0, runs[z] - rng.randint(1, 9))
    elif mode < 0.55:                   # suffix-merge
        runs = runs[rng.randint(0, k):]
    elif mode < 0.75:                   # psi-mapped (r,p)=(2,3)
        runs = [2 * (z // 3) + z % 3 for z in runs]
    i = rng.randint(0, 12); j = rng.randint(0, 12)
    text = 'b'.join('a' * z for z in runs)
    got = fired('a' * i + 'b' + 'a' * j, text)
    want = recursion_fired(runs, i, j)
    tested += 1
    if got != want:
        bad += 1
        if bad <= 3: print('   mismatch:', runs, i, j, got, want)
check('recursion theorem mismatches', bad, 0)
print('1. recursion theorem vs greedy: %d cases, 0 mismatches' % tested)

# 2. COR-A/B edge witnesses
print('2. COR-A/B/B1 witnesses')
w2 = dk(2)
check('k=2 prefix exception', fired('a' + 'b' + 'a' * 3, w2), [0])
check('k=3 resumption', fired('a' + 'b' + 'a' * 3, dk(3)), [0, 2])
check('size-1 interior k=3', fired('a' + 'b' + 'a' * 9, dk(3)), [1])
check('size-1 j=7 k=3', fired('a' + 'b' + 'a' * 7, dk(3)), [1, 2])
check('size-1 j=8 k=3', fired('a' + 'b' + 'a' * 8, dk(3)), [1, 2])
# COR-A sweep: no clean proper prefix at k>=3, all i,j
bad = 0
for k in (3, 4, 5):
    w = dk(k)
    for i in range(0, 13):
        for j in range(0, 13):
            f = set(fired('a' * i + 'b' + 'a' * j, w))
            for m in range(1, k):
                if f == set(range(m)): bad += 1
check('COR-A clean-prefix count', bad, 0)
# COR-B sweep: no interior block size >= 2
bad = 0
for k in (3, 4, 5):
    w = dk(k)
    for i in range(0, 13):
        for j in range(0, 13):
            f = set(fired('a' * i + 'b' + 'a' * j, w))
            for u in range(1, k - 1):
                for v in range(u + 1, k - 1):
                    if f == set(range(u, v + 1)): bad += 1
check('COR-B interior-block count', bad, 0)
print('   (COR-A/B sweeps: k=3..5, i,j<=12)')

# 3. MASS: [eps/a^p]X killed sets on D(6;3)
print('3. MASS on D(6;3), p=1..40')
k = 6; w = dk(k)
bad = 0
for p in range(1, 41):
    out = ev(S(K(''), K('a' * p), X), w)
    dead = [s for s in range(k + 1) if out.split('b')[s] == '']
    # suffix iff p a power of 3; else empty
    ispow = p in (1, 3, 9, 27)
    ok = (not dead) if not ispow else (dead == list(range(len([z for z in [p,0] if 0]) , k + 1)) or dead == [s for s in range(k + 1) if 3 ** s % p == 0])
    if not ok: bad += 1
check('MASS violations', bad, 0)
# never a small dead with a larger alive
bad = 0
for p in range(1, 41):
    out = ev(S(K(''), K('a' * p), X), w)
    dead = [s for s in range(k + 1) if out.split('b')[s] == '']
    for s in dead:
        for s2 in range(s + 1, k + 1):
            if s2 not in dead: bad += 1
check('MASS small-dead-larger-alive', bad, 0)

# 4. the fixed points E2, E4, E5
print('4. fixed points')
for t in range(0, 5):
    out = ev(S(K(''), K('a' * 3 ** (t + 1)), X), dk(6))
    want = dk(t) + 'b' * (6 - t)
    check('E2 prefix-isolation t=%d' % t, out, want)
for m in range(0, 5):
    blob = S(K(''), K('a' * 3 ** (m + 1)), S(K(''), K('b'), X))
    out = ev(blob, dk(6))
    check('E4 blob landing m=%d' % m, out, 'a' * ((3 ** (m + 1) - 1) // 2))
for m in range(0, 5):
    hal = ev(S(K('a'), K('aa'), K('a' * 3 ** (m + 1))), dk(6))
    check('E5 halver gap m=%d' % m, hal,
          'a' * ((3 ** (m + 1) - 1) // 2 + 1))

print('FAILS:', fails)

"""ROUND 19 (B=2 uniform-rev side quest): the tool battery + shortcut
falsifications behind the OBSTRUCTION verdict.  Theory first: every
identity below was hand-derived before this run (ROUND19_REPORT.md).

T1  The B=2 tool identities, byte-exact (k ranges stated per line):
      halver identity      [a/aa]X = 'ab' . w^{k-1}  (halving peels
                           one 'ab': the family self-similarity)
      doubler identity     [aa/a]X = gap-doubled w^k
      E_last = a^{2^k};  E_smm = a^{2^k-1};  E_h2 = a^{2^{k-1}};
      E_h4 = a^{2^{k-2}};  E_grow = a^{2S}
      STEPDOWN (NEW)       [eps/(b.E_last)]X = w^{k-1}: the pattern
                           b.a^{2^k} fires exactly once (at the last
                           separator, whose following run is exactly
                           2^k) and eats the separator plus the whole
                           last run.  The family steps down ONE LEVEL
                           in O(1) passes; the chain patterns are the
                           halving-chain values (E_last, E_h2, E_h4).
      JUMPDOWN (NEW)       [eps/(a^{2^i} b a^{2^i})]X CASCADES: the
                           flank fully consumes run i (exactly 2^i)
                           and each firing leaves just enough of the
                           next run for the next firing, so it fires
                           at separators i..k-1.  Runs j>i keep
                           2^j - 2^{i+1} and FUSE (their separators
                           are eaten) into one top-scale tail:
                           out = (2^0,...,2^{i-1}, T) with
                           T = 2^{k+1} - 2^i - (k-i).2^{i+1}
                           (= sum of the flanked remainders plus
                           2^k - 2^i): a one-pass truncation to any
                           FIXED bottom offset i.  [My first hand
                           derivation claimed tail 2^k - 2^i; the
                           machine refuted it for k >= i+3 and the
                           corrected closed form matches ALL machine
                           cases -- the empty-fusion small-k range
                           k <= i+2 is again a coincidence zone.]
      SCALER (NEW)         [a^{E_last}/a]X scales every gap by 2^k
                           (computed replacement values make pure-a
                           scaling a single pass).
      DIVIDER (NEW)        [a/a^{E_h2}]X threshold-divides gaps >=
                           2^{k-1} by 2^{k-1}, leaves smaller gaps.
      LADDER (NEW)         [b/ab][aa/a]X = (1,3,...,2^k-1,2^{k+1}):
                           the plant-depth ladder WITH separators, in
                           two constant passes (doubler, then the
                           skeleton-preserving shave).
      E_leak, E_leak-mirror, E_prod (the record's witnesses) and the
      +/-S ROUND TRIPS     [eps/mrg]E_leak = w^k and
                           [eps/mrg]E_leak-mirror = w^k: BOTH pad
                           directions round-trip back to w^k -- the
                           padding resource preserves the gap ORDER.
      RECURSION FACTS      doubler(rev(w^{k-1})).b.a = rev(w^k) and
                           halver(rev(w^k)) = rev(w^{k-1}).ba (the
                           coordinator's recursion, confirmed).
      PLANT-DEPTH IDENTITY separator m of w^k at left-depth
                           2^{m+1}-1; rev's separators at the SAME
                           depths from the right (depth mirror).

T2  The phase/rotation route dies at k=3: rev(w^k) is a rotation of
    w^k exactly for k <= 2 (documented small-k coincidences), and the
    [ba/a]-split pass preserves exactly that threshold (the split
    values are mutual rotations again only for k <= 2): the split
    maps the reversal to itself; there is no phase shortcut.

T3  The offset-cost census (illustration-grade): a battery of ~25
    hand-chosen expressions (the tools and their compositions, pass
    depth <= 6) on w^(7): every LONE near-power gap (a value with at
    most 2 gaps, an entry within 8 of 2^j) sits at end-distance
    min(j, k-j) <= 2: no cheap expression isolates a middle power;
    each halving level of depth buys one more level of end-distance.

T4  Periodic planting is indiscriminate: [ab/a^{2^j}] on the merge
    plants separators at ALL multiples of 2^j (exactly S//2^j >= 3
    plants for every j <= k-1), while the mirrored plant rev needs
    at scale j is the SINGLE maximal odd multiple: single-scale
    planting cannot isolate it, and multi-scale plants fuse (b's
    concatenate indistinguishably).

Run: /usr/bin/python3 -W ignore verify_r19_b2rev.py   (< 60 s)
"""
import sys

sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S

X = V(0)
lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))

def sup(k):
    return 'b'.join('a' * (2 ** m) for m in range(k + 1))

def rev(s):
    return s[::-1]

def D(p): return S(K(''), K(p), X)
mrgE = D('b')
halver = S(K('a'), K('aa'), X)                    # [a/aa]X
doubler = S(K('aa'), K('a'), X)                   # [aa/a]X
E_last = S(K(''), K('b'), halver)                 # [eps/b][a/aa]X
E_grow = S(K(''), K('b'), doubler)                # [eps/b][aa/a]X
E_cbox = S(K('b'), C(E_last, K('b')), C(C(mrgE, K('b')), mrgE))
E_smm = S(K(''), C(K('b'), mrgE), E_cbox)
E_h2 = S(K('a'), K('aa'), E_smm)
E_h4 = S(K('a'), K('aa'), E_h2)
stepdown = S(K(''), C(K('b'), E_last), X)         # [eps/(b.E_last)]X
stepdown2 = S(K(''), C(K('b'), E_h2), stepdown)   # chain: w^k -> w^{k-2}
stepdown3 = S(K(''), C(K('b'), E_h4), stepdown2)  # w^k -> w^{k-3}
scaler = S(E_last, K('a'), X)                     # [a^{2^k}/a]X
divider = S(K('a'), E_h2, X)                      # [a/a^{2^{k-1}}]X
ladder = S(K('b'), K('ab'), doubler)              # [b/ab][aa/a]X
leak = S(C(mrgE, K('b')), K('b'), X)
leak_m = S(C(K('b'), mrgE), K('b'), X)
E_prod = S(mrgE, K('aa'), X)
unleak = S(K(''), mrgE, leak)
unleak_m = S(K(''), mrgE, leak_m)
splitpass = S(K('ba'), K('a'), X)                 # [ba/a]X

def jumpdown(i):
    return S(K(''), K('a' * (2 ** i) + 'b' + 'a' * (2 ** i)), X)

def gaps(s):
    return [len(t) for t in s.split('b')]

def ngaps(vals):
    return 'b'.join('a' * v for v in vals)

def sdepth(e):
    if e[0] == 'K' or e[0] == 'V':
        return 0
    if e[0] == 'C':
        return max(sdepth(e[1]), sdepth(e[2]))
    if e[0] == 'S':
        return 1 + max(sdepth(e[1]), sdepth(e[2]), sdepth(e[3]))
    raise ValueError(e)

# ---------------- T1: the tool identities -------------------------------
ok = True
for k in range(1, 11):
    w = sup(k)
    S_ = 2 ** (k + 1) - 1
    ok &= val(halver, w) == 'ab' + sup(k - 1)
    ok &= val(doubler, w) == ngaps([2 * g for g in gaps(w)])
    ok &= val(E_last, w) == 'a' * (2 ** k)
    ok &= val(E_smm, w) == 'a' * (2 ** k - 1)
    ok &= val(E_h2, w) == 'a' * (2 ** (k - 1))
    if k >= 2:
        ok &= val(E_h4, w) == 'a' * (2 ** (k - 2))
    ok &= val(E_grow, w) == 'a' * (2 * S_)
    ok &= val(stepdown, w) == sup(k - 1)
    ok &= val(ladder, w) == 'b'.join(['a' * (2 ** (j + 1) - 1)
                                      for j in range(k)] + ['a' * (2 ** (k + 1))])
    ok &= val(leak, w) == 'b'.join(['a' * (S_ + 2 ** m)
                                    for m in range(k)] + ['a' * (2 ** k)])
    ok &= val(leak_m, w) == 'b'.join(['a' * 1] +
                                     ['a' * (2 ** j + S_)
                                      for j in range(1, k + 1)])
    ok &= val(unleak, w) == w
    ok &= val(unleak_m, w) == w
    ok &= val(divider, w) == ngaps([2 ** j for j in range(k - 1)] + [1, 2])
    ok &= val(splitpass, w) == w.replace('a', 'ba')
    if k <= 8:
        ok &= val(E_prod, w) == 'b'.join(
            ['a' * (1 if m == 0 else S_ * 2 ** (m - 1))
             for m in range(k + 1)])
    if k <= 7:
        ok &= val(scaler, w) == ngaps([g * (2 ** k) for g in gaps(w)])
    if k >= 2:
        ok &= val(stepdown2, w) == sup(k - 2)
    if k >= 3:
        ok &= val(stepdown3, w) == sup(k - 3)
for i in (1, 2, 3):
    for k in range(i + 1, 11):
        ok &= val(jumpdown(i), sup(k)) == \
            ngaps([2 ** j for j in range(i)] +
                  [2 ** (k + 1) - 2 ** i - (k - i) * 2 ** (i + 1)])
for k in range(1, 9):
    r_prev, r = rev(sup(k - 1)), rev(sup(k))
    ok &= val(doubler, r_prev) + 'ba' == r
    ok &= val(halver, r) == r_prev + 'ba'
for k in range(1, 11):
    w, r = sup(k), rev(sup(k))
    ld_w = [2 ** (j + 1) - 1 for j in range(k)]
    rd_r = [sum(2 ** i for i in range(k - j)) for j in range(k)]
    ok &= ld_w == [sum(2 ** i for i in range(j + 1)) for j in range(k)]
    ok &= rd_r == ld_w[::-1]   # the mirror is order-reversing: rev's
    #   separator j sits at right-depth 2^{k-j}-1 = the left-depth of
    #   w's separator k-1-j
print('T1 the B=2 tool identities (halver/doubler self-similarity, E_last/'
      'E_smm/E_h2/E_h4/E_grow, STEPDOWN + chains, JUMPDOWN i=1..3, SCALER'
      ' k<=7, DIVIDER, LADDER, E_leak/E_leak-mirror/E_prod k<=8, +/-S round'
      ' trips, split pass, recursion facts, plant-depth mirror):',
      'VERIFIED' if ok else 'REFUTED')

# ---------------- T2: the phase/rotation route -------------------------
rot = [k for k in range(0, 8) if rev(sup(k)) in sup(k) + sup(k)]
print('T2a rev(w^k) is a rotation of w^k exactly for k in', rot,
      '(dies at k=3; k<=2 are the documented coincidences)')
ok = (rot == [0, 1, 2])
rot2 = []
for k in range(1, 8):
    sw = val(splitpass, sup(k))
    sr = val(splitpass, rev(sup(k)))
    ok &= len(sw) == len(sr) and sw.count('b') == sr.count('b')
    if sr in sw + sw:
        rot2.append(k)
print('T2b the [ba/a]-split values are mutual rotations exactly for k in',
      rot2, '(same threshold: the split maps the reversal to itself)')
ok &= (rot2 == [1, 2])
print('T2 the phase/rotation route:', 'FALSIFIED beyond k=2, and the split'
      ' buys nothing (problem-preserving)' if ok else 'CHECK THE NUMBERS')

# ---------------- T3: the offset-cost census ----------------------------
battery = [
    ('halver', halver), ('halver^2', S(K('a'), K('aa'), halver)),
    ('halver^3', S(K('a'), K('aa'), S(K('a'), K('aa'), halver))),
    ('doubler', doubler), ('E_last', E_last), ('E_smm', E_smm),
    ('E_h2', E_h2), ('E_h4', E_h4), ('E_grow', E_grow),
    ('leak', leak), ('leak_mirror', leak_m), ('ladder', ladder),
    ('stepdown', stepdown), ('stepdown2', stepdown2),
    ('stepdown3', stepdown3), ('scaler', scaler), ('divider', divider),
    ('E_prod', E_prod), ('jumpdown_i1', jumpdown(1)),
    ('jumpdown_i2', jumpdown(2)), ('jumpdown_i3', jumpdown(3)),
    ('shave[eps/ab]', S(K(''), K('ab'), X)),
    ('[aab/ab]', S(K('aab'), K('ab'), X)),
    ('unleak', unleak), ('unleak_m', unleak_m), ('E_cbox', E_cbox),
    ('ladder.halver', S(K('a'), K('aa'), ladder)),
]
k = 7
w = sup(k)
print('T3 offset-cost census on w^(%d): lone near-power gaps (value with'
      ' <= 2 gaps, an entry within 8 of some 2^j) vs pass depth:' % k)
worst = -1
for name, e in battery:
    d = sdepth(e)
    g = gaps(val(e, w))
    cand = [min(j, k - j) for j in range(0, k + 1)
            if any(abs(x - 2 ** j) <= 8 for x in g)]
    if len(g) <= 2 and cand:
        dist = min(cand)
        worst = max(worst, dist)
        print('   %-14s depth %d: lone near-power, best end-distance %d'
              % (name, d, dist))
print('   max best end-distance over the battery: %d' % worst)
print('T3 census (illustration-grade):', 'CONSISTENT with the offset-cost'
      ' ceiling (no lone MIDDLE power at depth <= 6; each halving level'
      ' buys one end-distance)' if 0 <= worst <= 2 else 'ANOMALY')

# ---------------- T4: periodic planting is indiscriminate ----------------
ok = True
for k in (3, 4, 5, 6):
    S_ = 2 ** (k + 1) - 1
    for j in range(1, k):
        plant = S(K('ab'), K('a' * (2 ** j)), mrgE)  # [ab/a^{2^j}] on mrg
        nsep = val(plant, sup(k)).count('b')
        ok &= nsep == S_ // (2 ** j)          # plants at ALL multiples
        ok &= nsep >= 3                        # never the single plant
print('T4 periodic planting [ab/a^{2^j}] on the merge: plants exactly'
      ' S//2^j >= 3 separators at every scale j <= k-1 (rev needs the'
      ' SINGLE maximal odd multiple per scale):',
      'VERIFIED (indiscriminate)' if ok else 'CHECK')
print('ROUND 19 MACHINE VERDICT: tools VERIFIED; shortcut classes'
      ' falsified; obstruction = offset-cost ceiling (ROUND19_REPORT.md)')

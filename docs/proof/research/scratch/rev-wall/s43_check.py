#!/usr/bin/env python3
# rev-wall round 7 battery: S4.3-GENERAL (the compensation channel) —
# the arithmetic core.  Theory first; the machine CONFIRMS hand
# derivations; every run < 60 s.
import sys, time, os
sys.path.insert(0, '.')
print('INVOCATION: /usr/bin/python3 -W ignore %s/s43_check.py  (cwd: %s)' %
      (os.path.dirname(os.path.abspath(__file__)),
       os.path.dirname(os.path.abspath(__file__))), flush=True)
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S
X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def Sde(e):
    t = e[0]
    if t in ('K', 'V'): return 0
    if t == 'C': return max(Sde(e[1]), Sde(e[2]))
    return 1 + max(Sde(e[1]), Sde(e[2]), Sde(e[3]))
fails = 0
def bad(msg):
    global fails; fails += 1; print('  FAIL: ' + msg)
def I(u, v):   return (3 ** (v + 1) - 3 ** u) // 2
def v3(n):
    n = abs(n); c = 0
    while n and n % 3 == 0: n //= 3; c += 1
    return c

# ---------------------------------------------------------------------------
print('== A: THE 3-ADIC VALUATION LEMMA (v_3(I(u,v)) = u) ==')
n = 0
for u in range(0, 15):
    for v in range(u, 15):
        n += 1
        if v3(I(u, v)) != u: bad('v3(%d,%d) != %d' % (u, v, u))
print('  A v_3(I(u,v)) = u (the bottom exponent dominates the valuation;'
      ' I(u,v)/3^u = (3^{v-u+1}-1)/2 is a 3-ADIC UNIT, = 1 mod 3): %d '
      'checks, %s' % (n, 'VERIFIED' if fails == 0 else 'FAILED'))
MARK('A done')

# ---------------------------------------------------------------------------
print('== B: THE COUNT-SHIFT CATALOG (c*I(u,v) = I(U,V): the shifts and '
      'the length-divisibility channel) ==')
sols = []
for c in range(1, 82):
    for u in range(0, 8):
        for v in range(u, 8):
            w = c * I(u, v)
            for U in range(0, 9):
                for V in range(U, 9):
                    if w == I(U, V):
                        sols.append((c, u, v, U, V))
shifts = [z for z in sols
          if z[0] == 3 ** (z[3] - z[1]) and z[4] - z[2] == z[3] - z[1]]
others = [z for z in sols if z not in shifts]
okdiv = 0
for (c, u, v, U, V) in others:
    L, Lp = v - u + 1, V - U + 1
    if (Lp % L == 0 and
            c == 3 ** (U - u) * (3 ** Lp - 1) // (3 ** L - 1)
            and U >= u):
        okdiv += 1
    else:
        bad('count-shift unclassified c=%d I(%d,%d)=I(%d,%d)'
            % (c, u, v, U, V))
print('  B c*I(u,v)=I(U,V), c<=81, u,v<=7: %d solutions = %d SHIFTS '
      '(c=3^j, (U,V)=(u+j,v+j): Lane C K(c)) + %d LENGTH-DIVISIBILITY '
      '(c=3^{U-u}(3^{L\'}-1)/(3^L-1) with L | L\'): %s'
      % (len(sols), len(shifts), len(others),
         'ALL CLASSIFIED' if fails == 0 else 'UNCLASSIFIED REMAIN'))
print('  (the count channel is arithmetic-rich — the counts c are '
      'interval-rationals; their EXACT supply routes through the fired '
      'structure: the tiling counts carry remainders (corrections) and '
      'the junction counts separate the insertions (corrections) — the '
      'corrections machinery of part C)')
MARK('B done')

# ---------------------------------------------------------------------------
print('== C: THE CORRECTION-EQUATION CATALOG (the span/copy/bite '
      'decompositions) ==')
# Solutions of  sum_a s_a*I(ua,va) + t = I(u,v)  with <= 3 signed interval
# pieces and one small bite |t| <= 12, the bite STRICTLY BELOW the
# target's bottom digit scale (|t| < 3^u: the piece at scale u IS the
# target's bottom digit — a bite >= 3^u is material, not junk; the
# degenerate solutions where t = the target are thereby excluded).
# CLAIM (the OBLIGATION LEMMA): after cancelling +/- pairs, for every
# k > v some piece I(c,d) of EITHER SIGN satisfies
#   min(d, k-c) >= m*(k) - 1,  m*(k) = max_{sigma in [u..v]} min(sigma, k-sigma)
# (the target's worst scale).  A positive piece = span/copy material;
# a negative piece = a bite whose flank value is itself an interval
# obligation for the P-subtree; EITHER WAY the piece's own supply
# obligation min(d, k-c) reaches within 1 of the target's worst
# scale — the downward induction's step: the assembly pays the worst
# scale through strictly smaller subproblems.  The uncovered-scale
# solutions are the COUNT channel (top-segment gaps: c*I(u',v') =
# I(u,v), Lane C K(c) shifts/length-divisibility — paid by the
# fired-set walk or the R-atom at the target scale) and the CARRY
# channel (middle gaps filled from three units below).
SP = [(0, None)] + [(s, (a, b)) for s in (1, -1)
                    for a in range(0, 7) for b in range(a, 7)]
def pval(sp):
    s, p = sp
    return 0 if s == 0 else s * I(p[0], p[1])
singles = {}
for sp in SP:
    singles.setdefault(pval(sp), []).append(sp)
def canon(pieces):
    # cancel the +/- pairs (net-zero junk), keep the signed multiset
    ps = sorted(pieces, key=lambda sp: (sp[1], sp[0]))
    out = []
    for sp in ps:
        if out and out[-1][1] == sp[1] and out[-1][0] == -sp[0]:
            out.pop()
        else:
            out.append(sp)
    return out
catsol = viol = span = 0
for u in range(1, 7):
    for v in range(u + 1, 7):
        tgt = I(u, v)
        for t in range(-12, 13):
            if abs(t) >= 3 ** u: continue
            want = tgt - t
            for sp1 in SP:
                for sp2 in SP:
                    if pval(sp1) + pval(sp2) > want: continue
                    rem = want - pval(sp1) - pval(sp2)
                    if rem == 0:
                        cand = [sp1, sp2]
                    elif rem in singles:
                        cand = [sp1, sp2, singles[rem][0]]
                    else:
                        continue
                    pieces = canon([sp for sp in cand if sp[0] != 0])
                    if not pieces: continue
                    catsol += 1
                    # THE OBLIGATION LEMMA: for every text size k > v,
                    # some piece (c,d) carries its own obligation
                    # min(d, k-c) >= m*(k) - 1, where m*(k) is the
                    # target's worst scale max_{sigma in [u..v]}
                    # min(sigma, k-sigma).  (Covered scales route
                    # directly; top-segment gaps are the COUNT channel
                    # (c = 3^j shift / length-divisibility: paid by the
                    # fired-set walk or the R-atom at the target scale);
                    # middle gaps are CARRIES from below (the carriers
                    # sit at scales <= sigma-1, off by at most 1).)
                    okk = True
                    for kk in range(v + 1, 17):
                        ms = max(min(sig, kk - sig)
                                 for sig in range(u, v + 1))
                        if not any(min(d, kk - c) >= ms - 1
                                   for (s, (c, d)) in pieces):
                            okk = False
                            if viol <= 8:
                                print('     C obligation gap: %s + %d = '
                                      'I(%d,%d) at k=%d (m*=%d)'
                                      % (pieces, t, u, v, kk, ms))
                            break
                    if okk: span += 1
                    else: viol += 1
print('  C correction equations (<=3 signed pieces, |bite| < 3^u, targets '
      'I(u,v) MERGED, u>=1, u,v<=6): %d solutions; obligation lemma '
      'min(d, k-c) >= m*(k)-1 for some piece, all k in (v, 16]: %d pass, '
      'VIOLATIONS %d' % (catsol, span, viol))
if viol:
    bad('C obligation-lemma violations: %d' % viol)
MARK('C done')

# ---------------------------------------------------------------------------
print('== D: THE psi-LANDING SWEEP (the classification of the b-free '
      'landings on interval sums) ==')
sing = del_nonsing = repl_nonsing = 0
ex = []; struct_bad = []
for r in range(0, 41):
    for p in range(1, 41):
        for s in range(0, 7):
            U = 3 ** s
            w = r * (U // p) + U % p
            for a in range(0, 9):
                for b in range(a, 9):
                    if w == I(a, b):
                        if a == b: sing += 1
                        elif r == 0: del_nonsing += 1
                        else:
                            repl_nonsing += 1
                            ex.append((r, p, s, a, b))
                            if b - s > 3:
                                struct_bad.append((r, p, s, a, b))
print('  D psi-map landings on interval sums: %d singleton landings (the '
      'powers, incl. the ASCENTS a=b=s+log_3 r: J(V)-cheap); NON-singleton: '
      '%d with r=0 (the MOD-DELETION channel U mod p = I(a,b) — S4.4, '
      'priced by the pattern supply at scale ~p), %d with r>=1 (the '
      'replacing maps: the COPY+REMNANT split r*floor(U/p) + U mod p; the '
      'TRIPLER [a^3/a^2]: (3U-1)/2 = I(0,s) — a DEEP-WIDE landing)' %
      (sing, del_nonsing, repl_nonsing))
print('  D top-scale bound: every replacing-map landing of 3^s satisfies '
      'b - s <= 3 = floor(log_3 40) for the swept r <= 40 (general law: '
      'b <= s + ceil(log_3(r/p)) + O(1), the amplification paid by the '
      'R-atom a^r at scale log_3 r): %s (%d violations %s)'
      % ('VERIFIED' if not struct_bad else 'FAILED', len(struct_bad),
         struct_bad[:4]))
print('  (channel cost: [isolate run s; amplify] pays the head-mass '
      'walk — every run 0..s-1 must be FULLY eaten, so the eating '
      'pattern carries an atom matching each run scale (fixed flanks '
      'zero at most 2 runs: 3^sigma = i, j, or i+j), max supply at the '
      'middle sigma ~ s/2: Omega(min(s, k-s)) — which covers the bound '
      'min(b, k-a) <= min(s+O(1), k) up to a constant C ~ 2)')
if struct_bad:
    bad('D top-scale violations: %d' % len(struct_bad))
MARK('D done')

# ---------------------------------------------------------------------------
print('== E: THE E_last-PREFIX CHANNEL (the halver over the isolated '
      'prefix) ==')
def topower(s, k):
    e = S(K('aa'), K('aaa'), S(K(''), K('b'), X))
    for _ in range(k - s): e = S(K('a'), K('aaa'), e)
    return e
for t in range(0, 5):
    k = t + 2
    e = S(K(''), K('b'),
          S(K('a'), K('aa'), S(K(''), topower(t + 1, k), X)))
    want = 'a' * ((I(0, t) + t + 1) // 2)
    got = ev(e, dk(k))
    if got != want:
        bad('E1 prefix-halver t=%d: got len %d want %d'
            % (t, len(got), len(want)))
print('  E1 [e/b][a/aa][e/a^{3^{t+1}}]X = a^{(I(0,t)+t+1)/2} (the halver '
      'over the isolated prefix, k=t+2): OK t=0..4')
hits = []
for t in range(0, 41):
    w = (I(0, t) + t + 1) // 2
    for a in range(0, 44):
        for b in range(a, 44):
            if w == I(a, b): hits.append((t, a, b))
merged = [h for h in hits if h[1] < h[2]]
if merged:
    bad('E2 E_last-prefix MERGED landings: %s' % merged)
print('  E2 (I(0,t)+t+1)/2 in {I(a,b)}: only SINGLETON landings %s — the '
      'k-affine junk (the +t+1) blocks every MERGED landing: %s'
      % (hits, 'VERIFIED' if not merged else 'FAILED'))
for m in range(1, 6):
    e = S(K('a'), K('aa'), topower(m + 1, m + 2))
    got = len(ev(e, dk(m + 2)))
    if got != (3 ** (m + 1) + 1) // 2:
        bad('E3 halver gap m=%d' % m)
    if (3 ** (m + 1) + 1) // 2 in [I(a, b) for a in range(9)
                                   for b in range(a, 9)]:
        bad('E3 halver lands on an interval sum at m=%d!' % m)
print('  E3 [a/aa]a^{3^{m+1}} = (3^{m+1}+1)/2: NEVER an interval sum (the '
      '+1 gap): OK m=1..5')
MARK('E done')

# ---------------------------------------------------------------------------
print('== F: THE FIXED-BOX INTERIOR MERGE (the J(V) absorption, concrete) '
      '==')
# [b.a^3.b.a^9.b / b.a^12.b]X on D(4;3): one SD window spans b_0..b_2
# (interiors exact), R plants the merged run I(1,2)=12 in place; the
# runs AFTER the window survive untouched.
Ebox = S(K('b' + 'a' * 12 + 'b'), K('b' + 'a' * 3 + 'b' + 'a' * 9 + 'b'), X)
wantF = 'a' + 'b' + 'a' * 12 + 'b' + 'a' * 27 + 'b' + 'a' * 81
if ev(Ebox, dk(4)) != wantF:
    bad('F fixed box: %r' % ev(Ebox, dk(4))[:30])
print('  F [b.a^3.b.a^9.b / b.a^12.b]X on D(4;3) = a.b.a^12.b.a^27.b.a^81:'
      ' the run I(1,2)=12 realized in ONE pass at S-depth 1 — the FIXED '
      '(u,v) absorption (J(V)); the GROWING-(u,v) version needs the '
      'computed D-fragment pattern (the prefix isolation: the threshold '
      'walk) and a computed R (the obligation itself: the IH)')
for (t, kk) in ((2, 4), (3, 5)):
    e = S(K(''), K('bb'), S(K(''), topower(t + 1, kk), X))
    if ev(e, dk(kk)) != dk(t):
        bad('F2 prefix isolation t=%d k=%d' % (t, kk))
print('  F2 the prefix-isolation route [e/bb][e/a^{3^{t+1}}]X = D(t;3) '
      '(k=4,5 verified): S-depth %d at k=5,t=3 — the computed-fragment '
      'route pays the threshold walk' % Sde(S(K(''), K('bb'),
      S(K(''), topower(3, 5), X))))
MARK('F done')

print('== G: THE MIDDLE-MERGE WITNESS ==')
# [b.a^9.b.a^27.b / b.a^36.b]X on D(5;3): the window spans b_1..b_3
# (interior runs 2,3 exact), planting I(2,3)=36; runs 0,1 and 4,5
# survive around it.
Ebox2 = S(K('b' + 'a' * 36 + 'b'),
          K('b' + 'a' * 9 + 'b' + 'a' * 27 + 'b'), X)
wantG = ('a' + 'b' + 'a' * 3 + 'b' + 'a' * 36 + 'b' + 'a' * 81 + 'b'
         + 'a' * 243)
if ev(Ebox2, dk(5)) != wantG:
    bad('G middle box: %r' % ev(Ebox2, dk(5))[:40])
print('  G [b.a^9.b.a^27.b / b.a^36.b]X on D(5;3): the run I(2,3)=36 in '
      'one pass (fixed (u,v) again); the computed version pays the '
      'head-split (the material [0..1] before the interval: its own '
      'supply) + the threshold (the tail) — consistent with the bound '
      'min(v, k-u) = min(3, 3)')
print('== H: THE TRIPLER COMPOSITIONS (the value-level cheapness and its '
      'atom-level pricing) ==')
# [a^3/a^2]X: every run 3^sigma -> (3^{sigma+1}-1)/2 = I(0,sigma) at
# S-depth 1 with V-FIXED atoms — the prefix interval values are CHEAP
# EMBEDDED.  This REFUTES the value-level reading of the round-5/6
# obligation set (the end-anchored intervals as run VALUES); the
# obligations are ATOM-LEVEL (standalone a-blocks demanded in R/P
# positions), where the extraction/isolation pays the walk.
for kk in (2, 3, 4, 5):
    e = S(K('aaa'), K('aa'), X)
    want = 'b'.join('a' * I(0, sig) for sig in range(kk + 1))
    if ev(e, dk(kk)) != want:
        bad('H1 tripler k=%d: %r' % (kk, ev(e, dk(kk))[:30]))
print('  H1 [a^3/a^2]X = a^{I(0,0)}.b.a^{I(0,1)}.b...a^{I(0,k)} (EVERY '
      'run a prefix interval, S-depth 1, V-fixed atoms): OK k=2..5 — '
      'the EMBEDDED prefix values are cheap; the ATOM (the standalone '
      'block demanded in an R/P position) pays the isolation walk (part '
      'D) or the blob threshold walk Omega(k-m) — the round-5/6 '
      'obligation set holds at the ATOM level, not the value level')
for kk in (2, 3, 4, 5, 6, 7, 8):
    v = sum(I(0, sig) for sig in range(kk + 1))
    if v != (3 ** (kk + 2) - 2 * kk - 5) // 4:
        bad('H2 formula k=%d' % kk)
    if any(v == I(a, b) for a in range(kk + 4) for b in range(a, kk + 4)):
        bad('H2 tripler b-kill lands an interval at k=%d!' % kk)
e2 = S(K(''), K('b'), S(K('aaa'), K('aa'), X))
for kk in (2, 3, 4):
    if len(ev(e2, dk(kk))) != sum(I(0, s) for s in range(kk + 1)):
        bad('H2 b-kill k=%d' % kk)
print('  H2 [e/b][a^3/a^2]X = a^{Sum_sigma I(0,sigma)} = '
      'a^{(3^{k+2}-2k-5)/4}: the k-affine junk (the -2k-5) blocks every '
      'interval landing (k=2..8 checked, the E2-type obstruction) — the '
      'merged tripler block is NOT an obligation value')
print('== H3: THE JUNCTION-EATING MERGES (the free boundary and the '
      'stopping flank) ==')
# [a^3/abaa]X: every junction fires (c_sigma = 3^sigma - 2 >= 1 for
# sigma >= 1... and at 0: c_0 = 1 >= 1), each fire eats 1+2 atoms and
# plants 3: NET 0: the WHOLE TEXT merges to a^{I(0,k)} at S-depth 1
# with V-FIXED atoms — the degenerate FREE boundary of the atom
# obligation (v = k: no stopping flank needed; the partial prefixes
# I(0,m), m < k, need the blocking flank i+j > 3^m with i <= 3^0 = 1:
# only m <= 1: the stopping pays Omega(min(m, k-m))).
for kk in (2, 3, 4, 5):
    e = S(K('aaa'), K('ab' + 'aa'), X)
    if ev(e, dk(kk)) != 'a' * I(0, kk):
        bad('H3a full merge k=%d: %r' % (kk, ev(e, dk(kk))[:30]))
print('  H3a [a^3/abaa]X = a^{I(0,k)} (the FULL prefix as ONE block, '
      'S-depth 1, V-fixed atoms: the fires never stop — the free '
      'boundary v=k of the atom obligation; the PARTIAL prefixes pay '
      'the stopping flank): OK k=2..5')
# [a^{i+j}/a^i b a^j]: the fired set is the round-6 RECURSION
# THEOREM's (fire_sigma iff c_sigma >= i and R_{sigma+1} >= j;
# c_{sigma+1} = R_{sigma+1} - j*[fire_sigma]).  The width-1 atom
# I(u,u+1) arises when i <= 3^u (fire_u fits) and the window
# max(3^u, 3^{u+1}-i) < j <= 3^{u+1}: j > 3^u blocks every sigma <=
# u-1 (right flank), j > 3^{u+1}-i blocks u+1 (the shrunken remnant
# c_{u+1} = 3^{u+1}-j < i), j <= 3^{u+1} allows fire_u; the fires
# above u+1 CHAIN to the top (c_{sigma+1} = 3^{sigma+1}-j >= i),
# merging the tail; the atom is bounded by the surviving junctions
# b_{u-1}, b_{u+1}.  The right flank a^j sits at scale u+1 — the
# STOPPING FLANK, paying Omega(min(u+1, k-u-1)).  [Erratum vs the
# round-7 text: the earlier "fires exactly at the junctions with
# 3^{sigma+1} >= j" is FALSE (the coordinator's probes: (1,27) at
# k=7 fires {2,4,5,6}; (1,20) fires {2,3,4}, chaining runs 2..5 into
# one run); see R8.0.]
u_ = 2; i_ = 1; j_ = 27
e3b = S(K('a' * (i_ + j_)), K('a' * i_ + 'b' + 'a' * j_), X)
want3b = ('a' + 'b' + 'a' * 3 + 'b' + 'a' * I(2, 3) + 'b'
          + 'a' * I(4, 5))
if ev(e3b, dk(5)) != want3b:
    bad('H3b pair merge: %r' % ev(e3b, dk(5))[:40])
print('  H3b [a^28/a.b.a^27]X on D(5;3) = a.b.a^3.b.a^36.b.a^324: the '
      'width-1 interior intervals I(2,3), I(4,5) as MERGED RUNS at '
      'S-depth 1 (fired set {u} + the chain {u+2..k-1} by the round-6 '
      'recursion theorem; window max(3^u, 3^{u+1}-i) < j <= 3^{u+1}; '
      'ERRATUM vs the round-7 text: the fires do NOT sit at all '
      'junctions with 3^{sigma+1} >= j — junction u+1 is blocked by '
      'the remnant, the upper junctions chain, and the interior of the '
      'old window (e.g. j=20) chains runs 2..5 into ONE run) — '
      'embedded cheap; the ATOM a^{I(u,u+1)} demands the stopping '
      'flank a^j at scale u+1, paying Omega(min(u+1, k-u-1)): the '
      'interval bound minus 1')
print('ROUND 7 BATTERY COMPLETE — FAILS: %d' % fails)
MARK('done')

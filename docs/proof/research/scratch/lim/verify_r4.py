"""
verify_r4.py -- R4: machine verification for the lim section draft
(lim_section.tex).  Every number that the draft states is produced or
re-verified here, on the domain stated in each part's header.

Conventions.  Paper notation [A/B] = replace the pattern B by A:
throughout this file a rule is the pair (A, B) with B the PATTERN, so
(A, B) = ('baab', 'aba') is the paper's [baak/aba] = [baab/aba].
lim([A/B])(w): iterate the sweep s -> s.replace(B, A) to its first fixed
point.  restart: Definition def:markov (leftmost one at a time).

Domains (summary for the REPORT):
  (0) cross-check: direct sweep orbit == lim_core evaluator, 400 random pairs.
  (1) fixed-point set: all 930 binary rules |A|,|B| <= 4 (B != eps, A != B),
      all 2^8-1 = 255 inputs |w| <= 7.
  (2) strategies: same 930 rules, all inputs |w| <= 6, restart cap 2000;
      the draft's witnesses at restart cap 10^5.
  (3) growth: (a) amplifier: all binary inputs <= 12, 200 random 13..16,
      tallies a b^{n-1} for n <= 14, invariants per sweep on 50 traces;
      (b) towers through lim: t=1 n<=7, t=2 n<=6 + block grid m<=3 K<=14,
      t=3 n<=4; (c) Fibonacci orbits [aabb/ba] k <= 28 (length ~10^6),
      witness 'bbaa' k <= 28, mirror rule k <= 16; sort remark <= 12.

Run from this directory:  python3 verify_r4.py
"""

from lim_core import (K, V, C, S, L, restart, run, ev, subst_fast,
                      orbit_pass, Budget)
import itertools
import random
import time

random.seed(20260921)

FAILS = []
N = 0


def check(name, ok, detail=''):
    global N
    N += 1
    if not ok:
        FAILS.append((name, detail))
        print('FAIL', name, detail)


def horner(S):
    """v(S): a adds 1, b doubles, read left to right (thm:amplifier)."""
    v = 0
    for c in S:
        v = v + 1 if c == 'a' else 2 * v
    return v


def rules():
    """All 930 binary (A, B), B the pattern, 1 <= |B| <= 4, |A| <= 4, A != B."""
    for la in range(5):
        for lb in range(1, 5):
            for ta in itertools.product('ab', repeat=la):
                for tb in itertools.product('ab', repeat=lb):
                    A, B = ''.join(ta), ''.join(tb)
                    if A != B:
                        yield (A, B)


def strs(maxlen):
    for n in range(maxlen + 1):
        for t in itertools.product('ab', repeat=n):
            yield ''.join(t)


FIB = [0, 1, 1]           # F[1] = F[2] = 1
while len(FIB) < 40:
    FIB.append(FIB[-1] + FIB[-2])


# ===========================================================================
# PART 0 -- the direct sweep orbit is the calculus: cross-check against the
# lim_core evaluator (expression L(S(K(A), K(B), V(0)), E0)) on a sample.

def part0():
    t0 = time.time()
    pairs = []
    rs = list(rules())
    for _ in range(400):
        A, B = rs[random.randrange(len(rs))]
        w = ''.join(random.choice('ab')
                    for _ in range(random.randrange(0, 13)))
        pairs.append((A, B, w))
    for (A, B, w) in pairs:
        d = orbit_pass(A, B, w, capsteps=3000, caplen=1 << 16)
        r = run(L(S(K(A), K(B), V(0)), V(0)), (w,), 400_000, 1 << 16)
        ok = (d[0] == 'val' and r[0] == 'val' and d[1] == r[1]) or \
             (d[0] == 'div' and r[0] in ('div', 'undef'))
        check('p0-direct-vs-evaluator', ok, (A, B, w, d, r))
    print(f"(0) direct sweep orbit == lim_core evaluator on "
          f"{len(pairs)} random (rule, input) pairs: "
          f"{'OK' if not FAILS else 'FAIL'}  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 1 -- the fixed-point set of a pass (Lemma lem:fpsweep):
# for B != eps and A != B:  [A/B]w = w  iff  B not in w.

def part1():
    t0 = time.time()
    bad = 0
    for (A, B) in rules():
        for w in strs(7):
            p = subst_fast(A, B, w)          # the single pass [A/B]w
            fp = (p == w)
            occ = (B in w)
            check('p1-fpset', fp == (not occ), (A, B, w, p))
            if fp == occ:                    # must be fp iff NOT occ
                bad += 1
    print(f"(1) fixed-point set: [A/B]w = w iff B not in w, all 930 rules x "
          f"all 255 inputs |w| <= 7: "
          f"{'OK' if bad == 0 else str(bad) + ' FAILS'}  "
          f"[{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 2 -- the two normalizers of one rule: sweep-lim vs leftmost-restart.

def part2():
    t0 = time.time()
    # (a) census at inputs <= 6, restart cap 2000: classify each pair.
    cls = {'vv': 0, 'vd': 0, 'dl': 0, 'dr': 0, 'dd': 0}
    vd_small = None                          # shortest value-mismatch input
    dr_seen = None
    for (A, B) in rules():
        for w in strs(6):
            d = orbit_pass(A, B, w, capsteps=3000, caplen=4096)
            r = restart(A, B, w, cap=2000, caplen=1 << 22)
            dv, rv = d[0] == 'val', r is not None
            if dv and rv:
                c = 'vv' if d[1] == r else 'vd'
                if c == 'vd' and (vd_small is None or
                                  (len(w), len(A) + len(B)) < vd_small[:2]):
                    vd_small = (len(w), len(A) + len(B), A, B, w, d[1], r)
            elif dv and not rv:
                c = 'dl'
            elif not dv and rv:
                c = 'dr'
                dr_seen = (A, B, w)
            else:
                c = 'dd'
            cls[c] += 1
            check('p2-census', not (not dv and rv), (A, B, w, d, r))
    tot = sum(cls.values())
    check('p2-no-reverse', cls['dr'] == 0,
          ('lim diverges & restart converges', dr_seen))
    print(f"(2a) census, 930 rules x all inputs |w| <= 6 ({tot} pairs, "
          f"restart cap 2000): agree {cls['vv']}, value-mismatch {cls['vd']}, "
          f"lim-conv/restart-div {cls['dl']}, lim-div/restart-conv {cls['dr']}"
          f", both div {cls['dd']}")
    print(f"     shortest value-mismatch witness: "
          f"[{vd_small[2]}/{vd_small[3]}] on {vd_small[4]!r}: "
          f"lim {vd_small[5]!r} vs restart {vd_small[6]!r}")
    print(f"     [{time.time()-t0:.1f}s]")

    # (b) the draft's witnesses, recomputed at restart cap 10^5 and
    # cross-checked through the lim_core evaluator.
    # find the smallest [abba/bab] input where lim converges, restart diverges
    best = None
    for w in strs(9):
        d = orbit_pass('abba', 'bab', w, capsteps=4000, caplen=1 << 16)
        r = restart('abba', 'bab', w, cap=2000, caplen=1 << 22)
        if d[0] == 'val' and r is None and d[1] != w:
            best = (w, d[1], d[2] - 1)
            break
    check('p2-abba-bab-witness', best is not None, 'no witness found')
    print(f"(2b) [abba/bab]: smallest input with lim converging "
          f"(restart diverging): {best[0]!r} -> lim {best[1]!r} "
          f"in {best[2]} sweeps")
    s = best[0]
    orbit_list = [s]
    for _ in range(6):
        s = subst_fast('abba', 'bab', s)
        orbit_list.append(s)
    rr = run(L(S(K('abba'), K('bab'), V(0)), V(0)), (best[0],),
             4_000_000, 1 << 22)
    r10 = restart('abba', 'bab', best[0], cap=100_000, caplen=1 << 26)
    check('p2-abba-bab-orbit',
          orbit_list[best[2]] == best[1] == orbit_list[best[2] + 1]
          and rr[0] == 'val' and rr[1] == best[1] and r10 is None,
          (orbit_list, rr, r10))
    print(f"     [abba/bab] orbit on {best[0]!r}: "
          f"{' -> '.join(orbit_list[:best[2] + 1])} (fixed); restart "
          f"diverges at cap 10^5; evaluator agrees")

    t0 = time.time()
    wit = [
        # (A, B, w, what): value witnesses -- both converge, differently
        ('ab', 'bb', 'bbbb', 'value: lim abab, restart aaab'),
        ('babb', 'bbbb', 'abbbbbbbb', 'value: lim ababbbabb, restart ababababb'),
        ('ab', 'abba', 'abbababba', 'value: lim abb, restart abbba'),
        # verdict witnesses -- restart diverges, lim converges
        ('baab', 'aba', 'aaaba', 'verdict: lim baabbaabb in 3 sweeps'),
    ]
    for (A, B, w, what) in wit:
        d = orbit_pass(A, B, w, capsteps=4000, caplen=1 << 22)
        r = restart(A, B, w, cap=100_000, caplen=1 << 26)
        rr = run(L(S(K(A), K(B), V(0)), V(0)), (w,), 4_000_000, 1 << 22)
        print(f"     [{A}/{B}] on {w!r}: lim {d[1]!r} ({d[2]-1} sweeps), "
              f"restart {'DIVERGED at cap 10^5' if r is None else repr(r)}  "
              f"[{what}]")
        check('p2-witness-lim', d[0] == 'val' and rr[0] == 'val'
              and d[1] == rr[1], (A, B, w, d, rr))
        if 'value' in what:
            check('p2-witness-value', r is not None and d[1] != r,
                  (A, B, w, d, r))
        else:
            check('p2-witness-verdict', r is None, (A, B, w, d, r))

    # the [baab/aba] orbit, sweep by sweep (stated in the draft)
    s = 'aaaba'
    orbit_list = [s]
    for _ in range(6):
        s = subst_fast('baab', 'aba', s)
        orbit_list.append(s)
    check('p2-baab-aba-orbit',
          orbit_list[:5] == ['aaaba', 'aabaab', 'abaabab', 'baabbaabb',
                             'baabbaabb'],
          orbit_list)
    print(f"     [baab/aba] orbit on aaaba: "
          f"{' -> '.join(orbit_list[:4])} (fixed)")
    print(f"     [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 3 -- growth (Proposition prop:limgrowth and the remark after it).

def amp_f(S):
    return 'b' * S.count('b') + 'a' * horner(S)


def half_f(bmaK):
    m = len(bmaK) - len(bmaK.lstrip('b'))
    K = len(bmaK) - m
    return 'b' * m + 'ab' * (K // 2) + 'a' * (K % 2)


def AMP(E0):
    return L(S(K('baa'), K('ab'), V(0)), E0)


def HALF(E0):
    return L(S(K('ab'), K('aa'), V(0)), E0)


def part3a():
    t0 = time.time()
    # amplifier law + sweep bound, exhaustive small + random
    bad = 0
    dom = list(strs(12))
    dom += [''.join(random.choice('ab') for _ in range(random.randrange(13, 17)))
            for _ in range(200)]
    for w in dom:
        d = orbit_pass('baa', 'ab', w, capsteps=100_000, caplen=1 << 22)
        exp = amp_f(w)
        ok = d[0] == 'val' and d[1] == exp and (d[2] - 1) <= horner(w) - w.count('a')
        check('p3a-amplifier', ok, (w, d, exp))
        if not ok:
            bad += 1
    print(f"(3a) lim([baa/ab])(w) = b^#b a^v(w), sweeps <= v(w) - #a(w): "
          f"all {len(dom)} binary inputs <= 12 + 200 random 13..16: "
          f"{'OK' if bad == 0 else str(bad) + ' FAILS'}")

    # per-sweep invariants (#b, v preserved by every sweep) on 50 traces
    bad = 0
    for _ in range(50):
        w = ''.join(random.choice('ab')
                    for _ in range(random.randrange(8, 17)))
        s = w
        for _ in range(400):
            t = subst_fast('baa', 'ab', s)
            if t == s:
                break
            ok = t.count('b') == s.count('b') and horner(t) == horner(s)
            check('p3a-invariants', ok, (s, t))
            if not ok:
                bad += 1
            s = t
    print(f"     #b and v invariant under every sweep, 50 random traces: "
          f"{'OK' if bad == 0 else 'FAIL'}")

    # the exponential witness: a b^{n-1} -> b^{n-1} a^{2^{n-1}}, n <= 14
    bad = 0
    for n in range(1, 15):
        w = 'a' + 'b' * (n - 1)
        d = orbit_pass('baa', 'ab', w, capsteps=200_000, caplen=1 << 22)
        exp = 'b' * (n - 1) + 'a' * (2 ** (n - 1))
        r = run(AMP(V(0)), (w,), 4_000_000, 1 << 22)
        ok = (d[0] == 'val' and d[1] == exp and len(exp) == 2 ** (n - 1) + n - 1
              and r[0] == 'val' and r[1] == exp)
        check('p3a-witness', ok, (n, d, exp, r[0]))
        if not ok:
            bad += 1
    print(f"     lim([baa/ab])(a b^(n-1)) = b^(n-1) a^(2^(n-1)), length "
          f"2^(n-1)+n-1, n <= 14 (also via the AMP expression): "
          f"{'OK' if bad == 0 else 'FAIL'}")
    print(f"     [{time.time()-t0:.1f}s]")


def part3b():
    t0 = time.time()
    # t = 1: n <= 7; t = 2: n <= 6 and the block grid; t = 3: n <= 4
    bad = 0
    for n in range(1, 8):
        w = 'a' + 'b' * (n - 1)
        exp = amp_f(w)
        r = run(AMP(V(0)), (w,), 4_000_000, 1 << 22)
        check('p3b-t1', r[0] == 'val' and r[1] == exp
              and len(exp) == 2 ** (n - 1) + n - 1, (n, r[0], exp))
        if not (r[0] == 'val' and r[1] == exp
                and len(exp) == 2 ** (n - 1) + n - 1):
            bad += 1
    print(f"(3b) tower t=1 (1 lim node) on a b^(n-1), n <= 7, output length "
          f"2^(n-1)+n-1: {'OK' if bad == 0 else 'FAIL'}")

    bad = 0
    for n in range(1, 7):
        w = 'a' + 'b' * (n - 1)
        exp = amp_f(half_f(amp_f(w)))
        r = run(AMP(HALF(AMP(V(0)))), (w,), 8_000_000, 1 << 23)
        check('p3b-t2', r[0] == 'val' and r[1] == exp, (n, r[0], len(exp)))
        if not (r[0] == 'val' and r[1] == exp):
            bad += 1
    print(f"     tower t=2 (3 lim nodes) on a b^(n-1), n <= 6, == closed form "
          f"(height-2 tower in the input length): "
          f"{'OK' if bad == 0 else 'FAIL'}; "
          f"n=6 output length {len(amp_f(half_f(amp_f('abbbbb'))))}")

    bad = 0
    for m in range(4):
        for K in range(15):
            w = 'b' * m + 'a' * K
            exp = 'b' * (m + K // 2) + 'a' * (2 ** (K // 2 + 1) - 2 + K % 2)
            r = run(AMP(HALF(V(0))), (w,), 8_000_000, 1 << 23)
            check('p3b-block', r[0] == 'val' and r[1] == exp, (m, K, r[0], exp))
            if not (r[0] == 'val' and r[1] == exp):
                bad += 1
    print(f"     block AMP(HALF): b^m a^K -> b^(m+K/2) a^(2^(K/2+1)-2+K%2), "
          f"grid m <= 3, K <= 14: {'OK' if bad == 0 else 'FAIL'}")

    bad = 0
    for n in range(1, 5):
        w = 'a' + 'b' * (n - 1)
        exp = amp_f(half_f(amp_f(half_f(amp_f(w)))))
        r = run(AMP(HALF(AMP(HALF(AMP(V(0)))))), (w,), 16_000_000, 1 << 23)
        check('p3b-t3', r[0] == 'val' and r[1] == exp, (n, r[0], len(exp)))
        if not (r[0] == 'val' and r[1] == exp):
            bad += 1
    print(f"     tower t=3 (5 lim nodes) on a b^(n-1), n <= 4, == closed form: "
          f"{'OK' if bad == 0 else 'FAIL'}; n=4 output length "
          f"{len(amp_f(half_f(amp_f(half_f(amp_f('abbb'))))))}")
    print(f"     [{time.time()-t0:.1f}s]")


def part3c():
    t0 = time.time()
    # the Fibonacci orbit of [aabb/ba] from aabbaabb: |s_k| = 2 F_{k+1} + 2k + 6
    s = 'aabbaabb'
    lens = [len(s)]
    for k in range(1, 29):
        s = subst_fast('aabb', 'ba', s)
        lens.append(len(s))
    bad = 0
    for k, L in enumerate(lens):
        check('p3c-fib-aabbaabb', L == 2 * FIB[k + 1] + 2 * k + 6,
              (k, L, 2 * FIB[k + 1] + 2 * k + 6))
        if L != 2 * FIB[k + 1] + 2 * k + 6:
            bad += 1
    inc = all(lens[i + 1] > lens[i] for i in range(len(lens) - 1))
    check('p3c-increasing-aabbaabb', inc, lens)
    print(f"(3c) [aabb/ba] orbit of aabbaabb: |s_k| = 2F_(k+1)+2k+6 for "
          f"k <= 28 (|s_28| = {lens[28]:,}, strictly increasing: {inc}): "
          f"{'OK' if bad == 0 else 'FAIL'}")

    # from bbaa: |s_k| = 2 F_{k+1} + 2k + 2
    s = 'bbaa'
    lens2 = [len(s)]
    for k in range(1, 29):
        s = subst_fast('aabb', 'ba', s)
        lens2.append(len(s))
    bad = 0
    for k, L in enumerate(lens2):
        check('p3c-fib-bbaa', L == 2 * FIB[k + 1] + 2 * k + 2,
              (k, L, 2 * FIB[k + 1] + 2 * k + 2))
        if L != 2 * FIB[k + 1] + 2 * k + 2:
            bad += 1
    print(f"     [aabb/ba] orbit of bbaa: |s_k| = 2F_(k+1)+2k+2 for k <= 28 "
          f"(|s_28| = {lens2[28]:,}): {'OK' if bad == 0 else 'FAIL'}")

    # the calculus tie-in: first 16 sweeps through the lim_core evaluator
    s_direct = 'aabbaabb'
    s_eval = 'aabbaabb'
    E = S(K('aabb'), K('ba'), V(0))
    bud = Budget(2_000_000, 1 << 20)
    bad = 0
    for k in range(16):
        s_direct = subst_fast('aabb', 'ba', s_direct)
        s_eval = ev(E, (s_eval,), bud)
        check('p3c-evaluator-tie', s_direct == s_eval,
              (k, len(s_direct), len(s_eval)))
        if s_direct != s_eval:
            bad += 1
    print(f"     first 16 sweeps of the orbit == evaluator trace: "
          f"{'OK' if bad == 0 else 'FAIL'}")

    # the mirror rule [bbaa/ab] from bbaabbaa = reversal, k <= 16
    s1 = 'aabbaabb'          # [aabb/ba]
    s2 = 'bbaabbaa'          # [bbaa/ab]
    bad = 0
    for k in range(16):
        s1 = subst_fast('aabb', 'ba', s1)
        s2 = subst_fast('bbaa', 'ab', s2)
        check('p3c-mirror', s1[::-1] == s2, (k, len(s1), len(s2)))
        if s1[::-1] != s2:
            bad += 1
    print(f"     mirror rule [bbaa/ab] on bbaabbaa = reversal of the "
          f"[aabb/ba] orbit on aabbaabb, k <= 16 (same Fibonacci law): "
          f"{'OK' if bad == 0 else 'FAIL'}")

    # the sort remark: lim([ba/ab]) sorts to b^#b a^#a
    bad = 0
    dom = list(strs(12)) + [''.join(random.choice('ab')
                                     for _ in range(random.randrange(13, 17)))
                            for _ in range(100)]
    for w in dom:
        d = orbit_pass('ba', 'ab', w, capsteps=100_000, caplen=1 << 20)
        exp = 'b' * w.count('b') + 'a' * w.count('a')
        check('p3c-sort', d[0] == 'val' and d[1] == exp, (w, d, exp))
        if not (d[0] == 'val' and d[1] == exp):
            bad += 1
    print(f"     lim([ba/ab]) sorts to b^#b a^#a: all inputs <= 12 + 100 "
          f"random 13..16: {'OK' if bad == 0 else 'FAIL'}")
    print(f"     [{time.time()-t0:.1f}s]")


def main():
    print("verify_r4.py -- the lim section draft, machine verification")
    print("=" * 70)
    part0()
    part1()
    part2()
    part3a()
    part3b()
    part3c()
    print("=" * 70)
    print(f"TOTAL: {N} checks, {len(FAILS)} failures")
    if FAILS:
        for f in FAILS[:20]:
            print('  FAIL', f)
        raise SystemExit(1)
    print("ALL GREEN")


if __name__ == '__main__':
    main()

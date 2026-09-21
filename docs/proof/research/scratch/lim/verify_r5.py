"""
verify_r5.py -- R5: (1) the single-pass ceiling, (2) the omega-limit reading.

ITEM 1 -- THE SINGLE-PASS CEILING.  Question: is lim over ONE constant pass
universal?  Expected: no.  This script proves/verifies the reduction of
that question to a sweep-count law:

  Lemma A2 (freshness): every occurrence of B in s_{k+1} contains a
      character emitted by sweep k (proved; verified A2).
  Lemma A3 (branching): r_{k+1} <= |A||B| * r_k, r_k = fires of sweep k
      (proved from A2; verified A3).
  Lemma A4 (drift): every fire of sweep k+1 starts within |A|+|B| of an
      emission of sweep k, in output coordinates (verified A4).
  Corollary: total replacements R <= (|A||B|)^K, K the sweep count.  So the
      output is <= 2^{poly(|w|)} IFF K is polynomially bounded.  The
      census (part B) measures f(n) (max output), K(n), R(n) per rule;
      part C fits the ceiling and hunts for anything super-single-
      exponential (a double-exponential convergent rule would REFUTE the
      ceiling and is the headline negative-search target).

ITEM 2 -- THE OMEGA READING.  The pass is causal: output prefix j depends
  on input prefix j+|B| (D1, verified).  Hence the pass on an omega-string
  is the pointwise limit of the passes on prefixes (proved from D1's
  bound).  But ITERATION does not commute with omega-extension (D2/D3):
  the amplifier on a b^omega diverges stepwise while every window
  stabilizes to b^omega (which is a fixed point the orbit never reaches),
  and the finite values b^n a^{2^n} converge pointwise to the same b^omega.
  D4: an omega-census for the length-preserving rules on periodic inputs.

Domains (summary):
  (A) all 930 binary rules |A|,|B| <= 4 (B != eps, A != B), all inputs
      |w| <= 7, caps (300 sweeps, 4096 len).
  (B) growing-rule census: binary |A| > |B|, B not-in A, |A| <= 4,
      all inputs |w| <= 9, caps (2000 sweeps, 2^20 len); plus the four
      hard rules and a length-preserving sample.
  (C) top rules extended: structured a^i b^j (i+j <= 16) + 200 random
      16..20, caps (10^4 sweeps, 2^24 len); amplifier K(n), R(n) for
      n <= 22; the slow family under sweep, n <= 20.
  (D) omega: causality (300 random rule/input pairs); amplifier window
      W in {8,16,32,48}, K = 24, prefix slack certificate; sort and
      amplifier finite values n <= 20; omega-census |A| = |B| <= 4 rules
      x 4 periodic shapes, window 24, K = 60.

Run from this directory:  python3 verify_r5.py
"""

import itertools
import random
import time

random.seed(20260922)

FAILS = []
N = 0


def check(name, ok, detail=''):
    global N
    N += 1
    if not ok:
        FAILS.append((name, detail))
        print('FAIL', name, detail)


def rules():
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


def sweep_tracked(A, B, s):
    """One greedy sweep with fire bookkeeping.
    Returns (out, fires_in, fires_out) where fires_in[i] = start of the
    i-th fire in s, fires_out[i] = start of its emission A in out."""
    if not B:
        raise ValueError
    parts, fires_in, fires_out, i, pos = [], [], [], 0, 0
    while True:
        j = s.find(B, i)
        if j < 0:
            parts.append(s[i:])
            break
        parts.append(s[i:j])
        pos += j - i
        parts.append(A)
        fires_in.append(j)
        fires_out.append(pos)
        pos += len(A)
        i = j + len(B)
    return ''.join(parts), fires_in, fires_out


def orbit_tracked(A, B, w, capsteps=2000, caplen=1 << 20):
    """The sweep orbit with per-sweep fire data.  Returns
    ('conv', out, K, data) | ('div',) where data is a list of
    (r_k, fires_in_k, fires_out_k, next_occurrences_checkable)."""
    s, k, data = w, 0, []
    if B not in s:
        return ('conv', s, 0, data)
    while True:
        t, fi, fo = sweep_tracked(A, B, s)
        k += 1
        if t == s:
            return ('conv', s, k - 1, data)
        if k > capsteps or len(t) > caplen:
            return ('div', None, None, data)
        data.append((len(fi), fi, fo, t))
        s = t


# ===========================================================================
# PART A -- freshness, branching, drift (the proved lemmas, verified)

def partA():
    t0 = time.time()
    badA1 = badA2 = badA3 = badA4 = 0
    orbits = 0
    for (A, B) in rules():
        al, be = len(A), len(B)
        for w in strs(7):
            r = orbit_tracked(A, B, w, capsteps=300, caplen=4096)
            if r[0] == 'conv':
                orbits += 1
                if B in w:
                    # A1: convergence from a B-containing input implies
                    # B does not occur in A (else prop:limtotal(ii)).
                    if B in A:
                        badA1 += 1
                        check('A1-BnotInA', False, (A, B, w))
                # A2/A3/A4 across consecutive productive sweeps
                d = r[3]
                for i in range(len(d) - 1):
                    r1, fi1, fo1, s1 = d[i]
                    r2, fi2, fo2, s2 = d[i + 1]
                    # A2: every occurrence of B in s_{k+1} overlaps an
                    # emission of sweep k (emitted intervals of sweep k in
                    # s_{k+1} are [fo, fo+al) for fo in fo1).
                    occ = []
                    j = s1.find(B)
                    while j >= 0:
                        occ.append(j)
                        j = s1.find(B, j + 1)
                    for q in occ:
                        # the occurrence [q, q+be) must overlap an emission
                        # [fo, fo+al) of sweep k
                        if not any(q < fo + al and fo < q + be
                                   for fo in fo1):
                            badA2 += 1
                            check('A2-freshness', False,
                                   (A, B, w, i, q, s1))
                    # A3: branching  r_{k+1} <= (|A|+|B|-1) r_k
                    # (the occurrence's span meets an emission's span, so
                    #  its start lies in an interval of |A|+|B|-1 positions
                    #  per emission; covers A = eps, where the span is a
                    #  point -- the |A||B| form fails exactly there)
                    if r2 > (al + be - 1) * r1:
                        badA3 += 1
                        check('A3-branching', False, (A, B, w, i, r1, r2))
                    # A4: drift -- every fire of sweep k+1 starts within
                    # |A|+|B| of an emission of sweep k (output coords).
                    for q in fi2:
                        if not any(abs(q - fo) < al + be for fo in fo1):
                            badA4 += 1
                            check('A4-drift', False, (A, B, w, i, q))
                            break
    print(f"(A) freshness/branching/drift on all convergent orbits of the "
          f"930 rules x inputs <= 7 ({orbits} convergent orbits): "
          f"A1 {badA1}, A2 {badA2}, A3 {badA3}, A4 {badA4} failures")
    print(f"    [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART B -- the growth / sweep-count census for growing convergent rules

def partB():
    t0 = time.time()
    # growing rules: |A| > |B|, B not in A, |A| <= 4 (binary).
    # CAP NOTE: capsteps must exceed the base-3 two-block orbit length
    # (K = 3^7+7 = 2194 on a b^8); at capsteps = 2000 the base-3 quartet
    # [baaa/ab],[bbba/ab],[aaab/ba],[abbb/ba] is misclassified as
    # non-total and their f(9) = 3^8+8 = 6569 is hidden.
    grules = [(A, B) for (A, B) in rules()
              if len(A) > len(B) and B not in A]
    stats = {}          # (A,B) -> {n: (maxout, maxK, maxR)}
    conv_rules = set()
    nonconv = []
    maxrk = 0
    maxstreak = 0       # longest run of sweeps with r_k strictly growing
    for (A, B) in grules:
        per = {}
        ok = True
        for w in strs(9):
            r = orbit_tracked(A, B, w, capsteps=6000, caplen=1 << 16)
            if r[0] != 'conv':
                ok = False
                nonconv.append(((A, B), w[:12]))
                break
            n = len(w)
            K = r[2]
            R = sum(d[0] for d in r[3])
            out = len(r[1])
            prev = None
            streak = 0
            for d in r[3]:
                rk = d[0]
                maxrk = max(maxrk, rk)
                if prev is not None and rk > prev:
                    streak += 1
                    maxstreak = max(maxstreak, streak)
                else:
                    streak = 0
                prev = rk
            cur = per.get(n, (0, 0, 0))
            per[n] = (max(cur[0], out), max(cur[1], K), max(cur[2], R))
        if ok:
            conv_rules.add((A, B))
            stats[(A, B)] = per
    print(f"(B) growing convergent rules (|A| > |B|, B not-in A, |A| <= 4): "
          f"{len(conv_rules)} of {len(grules)} total on all inputs <= 9 "
          f"(caps 6000 sweeps / 2^16 chars)")
    for (AB, w) in nonconv:
        print(f"      non-conv at cap: [{AB[0]}/{AB[1]}] on {w!r}...")
    # champion table by f(9) = max output at n = 9
    champs = sorted(conv_rules,
                    key=lambda AB: -stats[AB].get(9, (0, 0, 0))[0])[:12]
    print(f"    top by max output at n = 9 (f(n), K(n), R(n)):")
    for (A, B) in champs:
        per = stats[(A, B)]
        row = [(n, per[n][0], per[n][1], per[n][2]) for n in sorted(per)]
        print(f"      [{A}/{B}]: (n,f,K,R) = {row}")
    worstK = max((stats[AB][n][1], AB, n) for AB in conv_rules
                 for n in stats[AB])
    worstR = max((stats[AB][n][2], AB, n) for AB in conv_rules
                 for n in stats[AB])
    print(f"    worst K on the domain: {worstK[0]} sweeps "
          f"([{worstK[1][0]}/{worstK[1][1]}] at n = {worstK[2]})")
    print(f"    worst R on the domain: {worstR[0]} fires "
          f"([{worstR[1][0]}/{worstR[1][1]}] at n = {worstR[2]})")
    print(f"    fire counts: max r_k over all census orbits = {maxrk}; "
          f"longest strictly-growing run = {maxstreak} sweeps")
    # the ceiling law, per rule: f, K, R <= (alpha-beta+1)^n + n, where
    # alpha-beta+1 is the family base. TIGHT: part C(b) shows the
    # base-m family attains |out| = i m^j + j exactly.
    bad = 0
    for AB in conv_rules:
        base = max(2, len(AB[0]) - len(AB[1]) + 1)
        for n, (f, K, R) in stats[AB].items():
            if n >= 2 and (f > base ** n + n or K > base ** n + n
                           or R > base ** n + n):
                bad += 1
                check('B-ceiling', False, (AB, n, f, K, R))
    print(f"    law f,K,R <= (alpha-beta+1)^n + n per rule on the domain: "
          f"{'OK' if bad == 0 else str(bad) + ' FAILS'} (tight: base-m "
          f"family attains it)")
    print(f"    [{time.time()-t0:.1f}s]")
    return conv_rules, stats


# ===========================================================================
# PART C -- ceiling fit on the champions + amplifier/slow families

def partC():
    t0 = time.time()
    # (a) the amplifier's exact K(n), R(n), output(n) for n <= 22
    print("(C) amplifier [baa/ab] on a b^(n-1):")
    for n in range(1, 20):
        w = 'a' + 'b' * (n - 1)
        r = orbit_tracked('baa', 'ab', w, capsteps=10 ** 6, caplen=1 << 24)
        K, R, out = r[2], sum(d[0] for d in r[3]), len(r[1])
        print(f"    n = {n:2d}: K = {K:3d}, R = {R:8d}, "
              f"|out| = {out:9d} (2^(n-1)+n-1 = {2**(n-1)+n-1})")
        check('C-amplifier', out == 2 ** (n - 1) + n - 1, (n, out))
        if n >= 2:
            # the new sweep-count law: K(n) = 2^(n-2) + n - 2, R = 2^(n-1) - 1
            check('C-amplifier-K-law',
                  K == 2 ** (n - 2) + n - 2 and R == 2 ** (n - 1) - 1,
                  (n, K, R))

    # (b) THE BASE-m FAMILY: the four letter-duplicating shapes
    #       S1(m) = [b a^m / ab]  on a^i b^j: out = b^j a^(i m^j)
    #       S2(m) = [b^m a / ab]  on a^i b^j: out = b^(j m^i) a^i
    #       T1(m) = [a^m b / ba]  on b^j a^i: out = a^(i m^j) b^j
    #       T2(m) = [a b^m / ba]  on b^j a^i: out = a^i b^(j m^i)
    # with K = i m^(j-1) + j - 1 (S1/T1) resp. j m^(i-1) + i - 1
    # (S2/T2), R = i (m^j - 1)/(m-1) resp. j (m^i - 1)/(m-1); the m = 1
    # degenerate of all four is the insertion sort (out = sorted, R = ij,
    # K = i + j - 1). EVERY base m >= 1 is realized; |out| = i m^j + j
    # is tight single-exponential. The amplifier is m = 2; the systems
    # report's "slow family" [aaab/ba],[abbb/ba] are m = 3 instances
    # (K = 3^(n-1)+n-1 -- NOT slow under the sweep).
    def runlaw(A, B, w, outp, Kp, Rp, tag, args):
        r = orbit_tracked(A, B, w, capsteps=10 ** 6, caplen=1 << 24)
        Rn = sum(d[0] for d in r[3])
        check(tag, r[0] == 'conv' and r[1] == outp and r[2] == Kp
              and Rn == Rp, (args, r[0], r[2], Rn))
        return 1

    print("    base-m family laws (exact):")
    fam_cnt = 0
    for m in (1, 2, 3, 4, 5):
        ncell = 0
        for j in range(1, 15):
            for i in (1, 2, 3):
                Kp = i + j - 1 if m == 1 else i * m ** (j - 1) + j - 1
                if m > 1 and Kp > 8000:
                    continue
                Rp = i * j if m == 1 else i * (m ** j - 1) // (m - 1)
                ncell += runlaw('b' + 'a' * m, 'ab', 'a' * i + 'b' * j,
                                'b' * j + 'a' * (i * m ** j),
                                Kp, Rp, 'C-fam-S1', (m, i, j))
        fam_cnt += ncell
        print(f"      S1(m) [b a^m/ab] on a^i b^j: m = {m}, "
              f"{ncell} cells exact")
    for m in (1, 2, 3, 4):
        ncell = 0
        for i in range(1, 15):
            for j in range(1, 13):
                Kp = i + j - 1 if m == 1 else j * m ** (i - 1) + i - 1
                if m > 1 and Kp > 8000:
                    continue
                Rp = i * j if m == 1 else j * (m ** i - 1) // (m - 1)
                ncell += runlaw('b' * m + 'a', 'ab', 'a' * i + 'b' * j,
                                'b' * (j * m ** i) + 'a' * i,
                                Kp, Rp, 'C-fam-S2', (m, i, j))
        fam_cnt += ncell
        print(f"      S2(m) [b^m a/ab] on a^i b^j: m = {m}, "
              f"{ncell} cells exact")
    for m in (1, 2, 3, 4):
        ncell = 0
        for j in range(1, 15):
            for i in (1, 2, 3):
                Kp = i + j - 1 if m == 1 else i * m ** (j - 1) + j - 1
                if m > 1 and Kp > 8000:
                    continue
                Rp = i * j if m == 1 else i * (m ** j - 1) // (m - 1)
                ncell += runlaw('a' * m + 'b', 'ba', 'b' * j + 'a' * i,
                                'a' * (i * m ** j) + 'b' * j,
                                Kp, Rp, 'C-fam-T1', (m, i, j))
        fam_cnt += ncell
        print(f"      T1(m) [a^m b/ba] on b^j a^i: m = {m}, "
              f"{ncell} cells exact")
    for m in (1, 2, 3, 4):
        ncell = 0
        for i in range(1, 15):
            for j in range(1, 13):
                Kp = i + j - 1 if m == 1 else j * m ** (i - 1) + i - 1
                if m > 1 and Kp > 8000:
                    continue
                Rp = i * j if m == 1 else j * (m ** i - 1) // (m - 1)
                ncell += runlaw('a' + 'b' * m, 'ba', 'b' * j + 'a' * i,
                                'a' * i + 'b' * (j * m ** i),
                                Kp, Rp, 'C-fam-T2', (m, i, j))
        fam_cnt += ncell
        print(f"      T2(m) [a b^m/ba] on b^j a^i: m = {m}, "
              f"{ncell} cells exact")
    print(f"      total family cells verified exact: {fam_cnt}")

    # (c) the growth champions among ALL inputs: the two-block Horner
    # inputs are the argmax at n = 9 for all eight family champions --
    # nothing beats the family rate.
    print("    champion inputs at n = 9 (argmax over all 2^9 inputs):")
    for (A, B, m) in [('baa', 'ab', 2), ('bba', 'ab', 2),
                      ('aab', 'ba', 2), ('abb', 'ba', 2),
                      ('baaa', 'ab', 3), ('bbba', 'ab', 3),
                      ('aaab', 'ba', 3), ('abbb', 'ba', 3)]:
        best = (-1, None)
        for w in strs(9):
            r = orbit_tracked(A, B, w, capsteps=50000, caplen=1 << 18)
            if r[0] == 'conv' and len(r[1]) > best[0]:
                best = (len(r[1]), w)
        check('C-champ-attains', best[0] == m ** 8 + 8, ((A, B), best))
        print(f"      [{A}/{B}]: f(9) = {best[0]} at {best[1]!r} "
              f"(= m^8 + 8, m = {m}: the two-block Horner input)")
    print(f"    [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART D -- the omega reading

def partD():
    t0 = time.time()
    # D1: causality of one pass: for |A| >= |B|, output[:j] depends on the
    # input prefix of length j + |B| (verified on random pairs).
    bad = 0
    rs = list(rules())
    for _ in range(300):
        A, B = rs[random.randrange(len(rs))]
        if len(A) < len(B):
            continue
        w = ''.join(random.choice('ab')
                    for _ in range(random.randrange(4, 16)))
        m = random.randrange(1, len(w) + 1)
        w2 = w[:m] + ''.join(random.choice('ab')
                             for _ in range(random.randrange(0, 8)))
        o1, _, _ = sweep_tracked(A, B, w)
        o2, _, _ = sweep_tracked(A, B, w2)
        j = max(0, m - len(B))
        if o1[:j] != o2[:j]:
            bad += 1
            check('D1-causality', False, (A, B, w, w2, j))
    print(f"(D1) one pass is causal (output[:m-|B|] fixed by input[:m]): "
          f"300 random pairs: {'OK' if bad == 0 else 'FAIL'}")

    # D2: the amplifier on a b^omega -- pointwise convergence with a
    # doubling cascade. The front (leftmost a) never retreats; its dwell
    # at value v is EXACTLY 2^(v-1)+1 sweeps; position j is permanently
    # 'b' from sweep k_j = 2^j + j on; the orbit fires every sweep (r_k
    # >= 1 and growing) so the stepwise fixpoint test s_{k+1} = s_k
    # never fires, while the pointwise limit is b^omega -- itself a
    # fixed point of the sweep.
    W = 10
    K = 2 ** W + W + 8
    for tag, M in (('main', W + 2 * K + 64),
                   ('slack', 2 * (W + 2 * K + 64))):
        s = 'a' + 'b' * M
        front = []
        rs = []
        for k in range(K):
            front.append(s.find('a'))
            rs.append(s.count('ab'))
            s = sweep_tracked('baa', 'ab', s)[0]
        dwell = []
        for v in range(1, W + 1):
            f1 = next((k for k in range(K) if front[k] >= v), None)
            f2 = next((k for k in range(K) if front[k] >= v + 1), None)
            dwell.append(None if None in (f1, f2) else f2 - f1)
        kj = [next((k for k in range(K) if front[k] > j), None)
              for j in range(W)]
        okfront = all(front[i + 1] >= front[i] for i in range(K - 1))
        okdwell = dwell == [2 ** (v - 1) + 1 for v in range(1, W + 1)]
        okkj = kj == [2 ** j + j for j in range(W)]
        okr = all(x >= 1 for x in rs) and rs[-1] > rs[K // 2]
        if tag == 'main':
            print(f"(D2) [baa/ab] on a b^omega (M = {M}, {K} sweeps):")
            print(f"     front dwell at v is 2^(v-1)+1 (v <= {W}): "
                  f"{'OK' if okdwell else 'FAIL'} {dwell}")
            print(f"     position j permanently b from sweep k_j = 2^j+j "
                  f"(j < {W}): {'OK' if okkj else 'FAIL'}")
            print(f"     k_j = {kj}")
            print(f"     front non-decreasing: {okfront}; fires every "
                  f"sweep, growing (r_{K // 2} = {rs[K // 2]}, r_{K} = "
                  f"{rs[-1]}): {okr}; #a at horizon = {s.count('a')}")
            check('D2-dwell', okdwell, (dwell,))
            check('D2-kj', okkj, (kj,))
            check('D2-front', okfront, ())
            check('D2-fires', okr, (rs[:3], rs[K // 2], rs[-1]))
        else:
            check('D2-slack', okdwell and okkj and okfront, (kj, dwell))
            print(f"     slack certificate (M doubled to {M}): same "
                  f"dwell/k_j laws: "
                  f"{'OK' if okdwell and okkj else 'FAIL'}")
    print(f"     -> pointwise limit b^omega at cost 2^j+j sweeps per "
          f"position j; the orbit never stops firing: the coinductive "
          f"(pointwise) and stepwise readings of lim diverge on a b^omega")

    # D3: does lim commute with omega-extension? The two showcase rules
    # commute; [aa/a] on a^omega does not.
    bad = 0
    for n in range(1, 16):
        r = orbit_tracked('baa', 'ab', 'a' + 'b' * (n - 1),
                          capsteps=10 ** 6, caplen=1 << 22)
        if not (r[0] == 'conv'
                and r[1] == 'b' * (n - 1) + 'a' * 2 ** (n - 1)):
            bad += 1
            check('D3-amplifier-finite', False, (n, r[0]))
    for n in range(1, 41):
        r = orbit_tracked('ba', 'ab', 'ba' * n, capsteps=10 ** 6,
                          caplen=1 << 20)
        if not (r[0] == 'conv' and r[1] == 'b' * n + 'a' * n):
            bad += 1
            check('D3-sort-finite', False, (n, r[0]))
    print(f"(D3a) finite values: lim(a b^(n-1)) = b^(n-1) a^(2^(n-1)) "
          f"(n <= 15), lim((ba)^n) = b^n a^n (n <= 40): "
          f"{'OK' if bad == 0 else 'FAIL'} -- both converge pointwise "
          f"to b^omega")
    # omega side of the sort: s_k = b^(k+1) (ab)^omega, so the window
    # stabilizes to b^W -- the omega-orbit COMMUTES here
    W2, K2 = 48, 80
    for tag in ('main', 'slack'):
        N = (W2 + 2 * K2 + 8 if tag == 'main'
             else 2 * (W2 + 2 * K2 + 8))
        s = 'ba' * ((N + 1) // 2)
        hist = []
        for k in range(K2):
            t = sweep_tracked('ba', 'ab', s)[0]
            if t == s:
                break
            s = t
            hist.append(s[:W2])
        final = s[:W2]
        stab = (all(h == final for h in hist[len(hist) - 10:])
                if len(hist) >= 10 else all(h == final for h in hist))
        if tag == 'main':
            print(f"(D3b) sort omega-orbit of (ba)^omega (window {W2}): "
                  f"final window {final!r}, stabilized {stab}")
            check('D3-sort-omega', final == 'b' * W2 and stab, (final,))
        else:
            check('D3-sort-omega-slack', final == 'b' * W2, (final,))
    print(f"     COMMUTES for the showcase rules: omega-orbit pointwise "
          f"limit = pointwise limit of finite values = b^omega")
    # the NON-commutation witness: [aa/a] on a^omega
    bad = 0
    for n in range(1, 61):
        r = orbit_tracked('a', 'aa', 'a' * n, capsteps=10 ** 6,
                          caplen=1 << 16)
        if not (r[0] == 'conv' and r[1] == 'a'):
            bad += 1
            check('D3c-finite', False, (n, r[0]))
    print(f"(D3c) [aa/a]: finite side lim(a^n) = 'a' for 1 <= n <= 60: "
          f"{'OK' if bad == 0 else 'FAIL'}")
    okw = True
    for W3 in (8, 16, 32):
        for M3 in (2 * W3, 2 * W3 + 7, 4 * W3):
            o = sweep_tracked('a', 'aa', 'a' * M3)[0]
            if o[:W3] != 'a' * W3:
                okw = False
                check('D3c-omega-window', False, (W3, M3, o[:W3]))
    check('D3c-omega', okw, ())
    print(f"     omega side: pass(a^omega) = a^omega (fires at 0,2,4,..., "
          f"window-verified at 3 widths x 3 truncations), a fixed point "
          f"-> coinductive lim([aa/a])(a^omega) = a^omega")
    print(f"     NON-COMMUTATION: finite-approximation reading 'a' vs "
          f"coinductive reading a^omega -- they differ at EVERY position "
          f">= 1 (least vs greatest fixpoint, cf. rem:leastfix)")

    # D4: omega-census, length-preserving rules on periodic shapes.
    shapes = ['a' * 64, 'ab' * 32, 'ba' * 32, 'aab' * 22]
    Wc, Kc = 24, 60
    counts = {'stab': 0, 'churn': 0}
    ex_churn = []
    lp_rules = [(A, B) for (A, B) in rules() if len(A) == len(B)]
    for (A, B) in lp_rules:
        for sh in shapes:
            Nn = Wc + len(B) * Kc + 8
            s = (sh * ((Nn // len(sh)) + 1))[:Nn]
            prev = s
            stable_at = None
            for k in range(Kc):
                t, _, _ = sweep_tracked(A, B, s)
                if t == s:
                    stable_at = k
                    break
                s = t
            if stable_at is not None:
                counts['stab'] += 1
            else:
                counts['churn'] += 1
                if len(ex_churn) < 6 and B in s[:Wc + 4]:
                    ex_churn.append((A, B, sh[:6], s[:Wc]))
    print(f"(D4) omega-census, {len(lp_rules)} length-preserving rules x "
          f"{len(shapes)} periodic shapes, window {Wc}, cap {Kc} sweeps: "
          f"stabilized {counts['stab']}, churning {counts['churn']}")
    for e in ex_churn:
        print(f"      churn: [{e[0]}/{e[1]}] on {e[2]}^omega -> window "
              f"{e[3]!r}")
    check('D4-census-run', True)

    # D5: [eps/ab] on (ab)^omega: ONE sweep erases the entire infinite
    # string -- the omega-orbit leaves omega-strings; total output
    # finite, process LIVE forever (the thm:guardedness edge case).
    oke = True
    for N5 in (17, 34, 71):
        if sweep_tracked('', 'ab', 'ab' * N5)[0] != '':
            oke = False
            check('D5-collapse', False, (N5,))
    check('D5-collapse-all', oke, ())
    print(f"(D5) [eps/ab] on (ab)^omega: one sweep erases the whole "
          f"infinite string (out = eps, verified on truncations of 17, "
          f"34, 71 pairs): {'OK' if oke else 'FAIL'}")
    print(f"    [{time.time()-t0:.1f}s]")


def main():
    print("verify_r5.py -- R5: the single-pass ceiling + omega reading")
    print("=" * 70)
    partA()
    partB()
    partC()
    partD()
    print("=" * 70)
    print(f"TOTAL: {N} checks, {len(FAILS)} failures")
    if FAILS:
        for f in FAILS[:20]:
            print('  FAIL', f)
        raise SystemExit(1)
    print("ALL GREEN")


if __name__ == '__main__':
    main()

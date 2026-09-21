"""verify_r1.py -- Round 1 of the L+lim study.

PART 0  infrastructure cross-checks:
       (a) subst (paper def:subst, char-for-char from core.py) vs
           CPython str.replace (subst_fast) -- they must agree everywhere.
       (b) the AST evaluator's lim node vs the direct orbit_pass.

PART 1  the fixed-point-set lemma for a single pass: for B != eps and
       A != B,  [A/B]w == w  iff  B not-in w.  (All 930 census rules,
       all inputs of length <= 8.)

PART 2  the fixed-point lemma proper: lim([A/B]) = the restart variant
       [A/B]^m (paper def:markov) as partial functions, on the paper's
       census domain: all 930 binary rules (|A|,|B| <= 4, B != eps,
       A possibly eps) x all inputs of length <= 9.
         - A == B is EXCLUDED from the lemma (lim converges to the
           identity, restart diverges: expected mismatch, reported).
         - B in A (proper): both diverge on every B-containing input --
           proved by one-step facts + operational confirmation on a
           subsample (this is thm:termination(iii) both ways).
         - otherwise: full operational comparison, verdict AND value.
       Also reproduces the paper's census numbers (170 divergent rules,
       the 8 non-B-in-A divergent rules) as a check on restart().

PART 3  re-verification on strictly larger domains (the house discipline):
       (a) the 8 hard rules: all inputs of length <= 10 + 150 random of
           length 12..16;
       (b) all 930 rules: 100 random inputs of length 12..16;
       (c) every rule with |A| <= |B| (all provably convergent both ways):
           all inputs of length <= 10, values compared.

PART 4  tower growth through lim (cor:towers carried over):
       (a) lim([baa/ab]) = the amplifier thm:amplifier: b^#b(S) a^v(S)
           on all binary strings of length <= 9 + 40 random of length 10..12;
       (b) the half node: lim([ab/aa]): b^m a^K -> b^m (ab)^{K/2} a^{K%2};
       (c) the block and the towers: 2t-1 constant-pattern lim-nodes,
           t = 1, 2, 3, verified against the composed closed forms AND
           against the composed restart nodes.

PART 5  demos: nested lim; a branching iterand (if/contains, the power
       source for universality); exponential growth by lim([XX/X]).
"""

import random
import time
import sys

from lim_core import (K, V, C, S, L, subst, subst_fast, restart, ev, run,
                      orbit, orbit_pass, Undefined, Diverge, Budget, pp)

random.seed(20260921)

FAILS = []
NCHECK = [0]


def check(name, ok, detail=''):
    NCHECK[0] += 1
    if not ok:
        FAILS.append((name, detail))
        print(f"  FAIL {name}: {detail}")
    return ok


def all_strings(maxlen, alpha='ab'):
    """all strings over alpha of length 0..maxlen, in shortlex order."""
    for n in range(maxlen + 1):
        for t in _prod(alpha, n):
            yield t


def _prod(alpha, n):
    if n == 0:
        yield ''
        return
    for t in _prod(alpha, n - 1):
        for c in alpha:
            yield t + c


def rules_census():
    """all (A,B), |A| <= 4, 1 <= |B| <= 4, over {a,b}: 31 * 30 = 930."""
    out = []
    for lb in range(1, 5):
        for B in _prod('ab', lb):
            for la in range(0, 5):
                for A in _prod('ab', la):
                    out.append((A, B))
    return out


def horner(S):
    """v(S): a adds 1, b doubles, read left to right (thm:amplifier)."""
    v = 0
    for c in S:
        v = v + 1 if c == 'a' else 2 * v
    return v


# ===========================================================================
# PART 0 -- infrastructure cross-checks

def part0():
    print("== (0) infrastructure cross-checks ==")
    t0 = time.time()
    # (a) subst vs str.replace
    n = 0
    for la in range(0, 4):
        for A in _prod('ab', la):
            for lb in range(1, 4):
                for B in _prod('ab', lb):
                    for w in all_strings(8):
                        n += 1
                        if subst(A, B, w) != subst_fast(A, B, w):
                            check('subst-vs-replace', False, (A, B, w))
                            break
    print(f"  subst == str.replace on {n} triples "
          f"(|A|<=3 incl eps, |B|<=3, |w|<=8): "
          f"{'OK' if not FAILS else 'FAIL'}")

    # (b) evaluator lim node vs direct orbit
    n = 0
    for A, B in [('', 'b'), ('a', 'b'), ('ba', 'ab'), ('baa', 'ab'),
                 ('aab', 'ba'), ('ab', 'a'), ('', 'ab'), ('bb', 'ab')]:
        expr = L(S(K(A), K(B), V(0)), V(0))       # lim([A/B])(X)
        for w in all_strings(7):
            r1 = run(expr, (w,), maxsteps=3000, maxlen=200000)
            r2 = orbit_pass(A, B, w, 3000, 200000)
            n += 1
            ok = (r1[0] == r2[0] and (r1[0] != 'val' or r1[1] == r2[1]))
            if not ok:
                check('ev-vs-orbit', False, (A, B, w, r1, r2))
    print(f"  evaluator L-node == direct orbit on {n} runs (8 rules, |w|<=7): "
          f"{'OK' if not [f for f in FAILS if f[0]=='ev-vs-orbit'] else 'FAIL'}")
    print(f"  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 1 -- fixed-point-set lemma

def part1():
    print("== (1) fixed-point-set lemma: fp([A/B]) = B-free strings ==")
    t0 = time.time()
    n = mism = 0
    for A, B in rules_census():
        for w in all_strings(8):
            n += 1
            t = subst_fast(A, B, w)
            isfp = (t == w)
            expect = (B not in w) if A != B else True   # A==B: identity pass
            if A != B and isfp != expect:
                mism += 1
                check('fp-set', False, (A, B, w, t))
            if A == B and not isfp:
                mism += 1
                check('fp-identity', False, (A, B, w, t))
    print(f"  930 rules x 255 inputs = {n} checks, "
          f"{'OK: [A/B]w==w iff B-free (A!=B); [A/A]=identity' if mism == 0 else str(mism)+' FAILS'}")
    print(f"  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 2 -- lim(pass) vs restart on the census domain.
#
# FINDING (this round): the fixed-point lemma as conjectured --
# lim([A/B]) = the restart variant -- is FALSE in general.  The two are
# two different deterministic strategies for the one-rule system B -> A
# (leftmost-one-at-a-time vs all-greedy-matches-per-sweep), one-rule
# systems are not confluent, and the strategies separate.  This part
# therefore CATALOGUES the mismatches and verifies the corrected facts:
#   (F1) A == B:  lim = total identity, restart diverges (thm:termination
#       iii) -- the mismatch is an artifact of restart's "stop only when
#       B-free" rule; lim's fixed-point test detects stabilization.
#   (F2) B in A (proper): both diverge on every B-containing input (proved
#       by one-step facts + operational spot checks).
#   (F3) on all other rules: agreement is the default; the exceptions are
#       catalogued.  Verdict mismatches occur ONLY in the direction
#       restart-diverges & lim-converges (0 cases of the reverse).
#   (F4) census cross-check against the paper's own script: exactly FOUR
#       rules diverge under restart on inputs <= 9 with B not-in A
#       (the paper's TEXT says eight and lists [aaab/ba], [abbb/ba],
#       which terminate on <= 9 and diverge only from length 10 up --
#       a text bug; the paper's script verify_extra.py has the FOUR).

def bordered(W):
    """W has a proper border: some 0 < |u| < |W| with u prefix and suffix."""
    for k in range(1, len(W)):
        if W[:k] == W[len(W) - k:]:
            return True
    return False


def part2():
    print("== (2) lim([A/B]) vs restart [A/B]^m, census domain ==")
    t0 = time.time()
    stats = {'agree_val': 0, 'agree_div': 0, 'A=B': 0,
             'verdict-restart-div-lim-val': 0, 'verdict-lim-div-restart-val': 0,
             'value-mismatch': 0}
    val_rules = {}
    verd_rules = {}
    div_rules_restart = set()
    for A, B in rules_census():
        if A == B:
            for w in all_strings(9):
                if B not in w:
                    r = run(L(S(K(A), K(B), V(0)), V(0)), (w,), 100, 1000)
                    check('A=B-free', r[0] == 'val' and r[1] == w, (A, w, r))
                else:
                    o = orbit_pass(A, B, w, 10, 1000)
                    rr = restart(A, B, w, 10)
                    check('A=B-lim-identity', o == ('val', w, 1), (A, w, o))
                    check('A=B-restart-div', rr is None, (A, w, rr))
                    stats['A=B'] += 1
            div_rules_restart.add((A, B))
            continue
        if B in A:
            for w in all_strings(9):
                if B not in w:
                    check('BinA-free', restart(A, B, w, 5) == w
                          and orbit_pass(A, B, w, 5, 100)[0] == 'val',
                          (A, B, w))
                else:
                    i = w.find(B)
                    s1 = w[:i] + A + w[i + len(B):]
                    if B not in s1 or B not in subst_fast(A, B, w):
                        check('BinA-fact', False, (A, B, w))
                    if len(w) <= 6:
                        rr = restart(A, B, w, 120)
                        oo = orbit_pass(A, B, w, 120, 30000)
                        if rr is not None or oo[0] != 'div':
                            check('BinA-ops', False, (A, B, w, rr, oo))
                    stats['agree_div'] += 1
            div_rules_restart.add((A, B))
            continue
        for w in all_strings(9):
            rr = restart(A, B, w, 4000, 2_000_000)
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            if rr is None:
                div_rules_restart.add((A, B))
                if oo[0] == 'div':
                    stats['agree_div'] += 1
                else:
                    stats['verdict-restart-div-lim-val'] += 1
                    verd_rules.setdefault((A, B), 0)
                    verd_rules[(A, B)] += 1
            else:
                if oo[0] == 'div':
                    stats['verdict-lim-div-restart-val'] += 1
                    check('reverse-verdict', False, (A, B, w, rr))
                elif oo[1] != rr:
                    stats['value-mismatch'] += 1
                    val_rules[(A, B)] = val_rules.get((A, B), 0) + 1
                else:
                    stats['agree_val'] += 1
    hard4 = sorted(r for r in div_rules_restart if r[1] not in r[0])
    # F3: verdict mismatches only in one direction, and only on rules of
    # the hard four where the SWEEP terminates and leftmost does not.
    check('verd-direction',
          stats['verdict-lim-div-restart-val'] == 0
          and set(verd_rules) <= set(hard4),
          (verd_rules, hard4))
    allb = [B for A, B in rules_census()]
    unb_mismatch = [r for r in list(val_rules) + list(verd_rules)
                    if not bordered(r[1])]
    print(f"  agreement: {stats['agree_val']} converging + {stats['agree_div']}"
          f" diverging pairs; {stats['A=B']} A=B pairs "
          f"(lim=total identity, restart=div)")
    print(f"  MISMATCHES: {stats['value-mismatch']} value pairs across "
          f"{len(val_rules)} rules; verdict: "
          f"{stats['verdict-restart-div-lim-val']} pairs (restart div, lim"
          f" converges) across {len(verd_rules)} rules, "
          f"{stats['verdict-lim-div-restart-val']} reverse (expected 0)")
    print(f"  verdict-mismatch rules: {[f'[{a}/{b}]' for a, b in verd_rules]}")
    bstats = (sum(1 for A, B in val_rules if bordered(B)),
              len(val_rules), sum(1 for A, B in verd_rules if bordered(B)),
              len(verd_rules),
              sum(1 for A, B in rules_census() if bordered(B)))
    print(f"  bordered-B among value-mismatch rules: {bstats[0]}/{bstats[1]};"
          f" among verdict rules: {bstats[2]}/{bstats[3]}; "
          f"among all 930 rules: {bstats[4]} (bordered B is necessary for "
          f"a mismatch so far: {'CONFIRMED' if not unb_mismatch else 'REFUTED ' + str(unb_mismatch)})")
    print(f"  census cross-check vs paper: {len(div_rules_restart)} rules "
          f"diverge under restart on inputs <= 9 (paper text says 170; the "
          f"paper's own verify_extra.py and this census say 166), of these "
          f"{len(hard4)} with B not-in A: {[f'[{a}/{b}]' for a, b in hard4]}")
    print(f"  [{time.time()-t0:.1f}s]")
    return hard4, verd_rules, val_rules


# ===========================================================================
# PART 3 -- larger domains (house discipline: re-verify every phenomenon on
# strictly larger domains; short-domain artifacts are real).

def rand_strings(count, lo, hi, alpha='ab'):
    out = set()
    while len(out) < count:
        n = random.randint(lo, hi)
        out.add(''.join(random.choice(alpha) for _ in range(n)))
    return sorted(out)


def part3(hard4, verd_rules):
    print("== (3) re-verification on strictly larger domains ==")
    t0 = time.time()

    # (a) the hard four on inputs <= 10 + 150 random 12..16: per-rule
    # behavior catalog.  The verified claims: NO input where lim diverges
    # while restart converges (the reverse of the R1 finding); every input
    # where lim converges while restart diverges has a value STABLE at
    # 10x caps.  CAP DISCIPLINE (learned this round, see report): a cap
    # 'divergence' can be a slow termination -- [aaab/ba]-family rules
    # terminate after >6000 steps on 10-char inputs -- so the two
    # lim-wins rules' witnesses are re-run at restart cap 50000 (a
    # subsample) and the counts are stated at the caps used.
    for A, B in hard4:
        cat = {'bothdiv': 0, 'rdiv-lval': 0, 'bothval-agree': 0,
               'bothval-differ': 0, 'reverse': 0}
        unstable = 0
        lval_witnesses = []
        for w in list(all_strings(10)) + rand_strings(150, 12, 16):
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            rr = restart(A, B, w, 4000, 2_000_000)
            if rr is None:
                if oo[0] == 'div':
                    cat['bothdiv'] += 1
                else:
                    cat['rdiv-lval'] += 1
                    lval_witnesses.append(w)
                    oo2 = orbit_pass(A, B, w, 40000, 20_000_000)
                    if oo2[0] != 'val' or oo2[1] != oo[1]:
                        unstable += 1
                        check('hard-stable', False, (A, B, w, oo, oo2))
            else:
                if oo[0] == 'div':
                    cat['reverse'] += 1
                    check('hard-reverse', False, (A, B, w, rr))
                elif oo[1] == rr:
                    cat['bothval-agree'] += 1
                else:
                    cat['bothval-differ'] += 1
        # re-verify a subsample of the lim-wins witnesses at restart cap
        # 50000 (true separation vs slow termination)
        still = slow = 0
        for w in lval_witnesses[::max(1, len(lval_witnesses) // 15)][:15]:
            r2 = restart(A, B, w, 50000, 4_000_000)
            if r2 is None:
                still += 1
            else:
                slow += 1
        check('hard-reverse-0', cat['reverse'] == 0, (A, B, cat))
        print(f"  [{A}/{B}] on <= 10 + 150 random 12..16: {cat}"
              f"; of {len(lval_witnesses)} lim-wins witnesses, a 15-input"
              f" subsample at restart cap 50000: {still} still divergent, "
              f"{slow} slow-converging"
              + (f"  UNSTABLE={unstable}" if unstable else ""))

    # (b) all 930 rules on random inputs of length 12..16: NO reverse
    # verdict mismatch (lim div where restart converges) may appear.
    rs = rand_strings(100, 12, 16)
    nrev = 0
    nvalmis = 0
    for A, B in rules_census():
        if A == B or B in A:
            continue
        for w in rs:
            rr = restart(A, B, w, 4000, 2_000_000)
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            if rr is not None and oo[0] == 'div':
                nrev += 1
                check('reverse-verdict-16', False, (A, B, w, rr))
            elif rr is not None and oo[0] == 'val' and oo[1] != rr:
                nvalmis += 1
    print(f"  930 rules x 100 random inputs 12..16: reverse verdict "
          f"mismatches {nrev} (expected 0); value mismatches {nvalmis} "
          f"(the non-confluence persists at length)")

    # (c) every rule with |A| <= |B| (both provably convergent): values on
    # all inputs <= 10; verdicts must ALWAYS agree (both converge), values
    # may differ (catalogued: non-confluence of the strategies).
    npairs = nvalmis = 0
    mism_rules = set()
    for A, B in rules_census():
        if A == B or len(A) > len(B):
            continue
        for w in all_strings(10):
            npairs += 1
            rr = restart(A, B, w, 4000, 2_000_000)
            oo = orbit_pass(A, B, w, 4000, 2_000_000)
            if rr is None or oo[0] == 'div':
                check('le-verdict', False, (A, B, w, rr, oo))
            elif oo[1] != rr:
                nvalmis += 1
                mism_rules.add((A, B))
    print(f"  all |A|<=|B| rules, {npairs} pairs on all inputs <= 10: "
          f"verdicts always agree (both converge); value mismatches "
          f"{nvalmis} across {len(mism_rules)} rules (non-confluence)")

    # (d) the unbordered-B conjecture on bigger rules: every mismatch rule
    # in the census has BORDERED B.  Stress: all rules with UNBORDERED B,
    # |A| <= 6, |B| <= 6 (beyond the census' 4), A != B, B not in A, on
    # 100 random inputs of length 8..14.  CAP DISCIPLINE: apparent
    # verdict mismatches at cap 6000 are RE-VERIFIED at restart cap
    # 60000 and classified: 'still-div' (true verdict mismatch) or
    # 'slow' (restart terminates late; then its VALUE is compared with
    # lim's -- agreement kills the mismatch, disagreement is a genuine
    # unbordered-B VALUE mismatch).
    unb_rules = []
    for lb in range(1, 7):
        for B in _prod('ab', lb):
            if bordered(B):
                continue
            for la in range(0, 7):
                for A in _prod('ab', la):
                    if A == B or B in A:
                        continue
                    unb_rules.append((A, B))
    rs2 = rand_strings(100, 8, 14)
    raw_mis = []
    for A, B in unb_rules:
        for w in rs2:
            rr = restart(A, B, w, 6000, 8_000_000)
            oo = orbit_pass(A, B, w, 6000, 8_000_000)
            bad = ((rr is None) != (oo[0] == 'div')
                   or (rr is not None and oo[0] == 'val' and rr != oo[1]))
            if bad:
                raw_mis.append((A, B, w, rr, oo))
    cls = {'apparent-verdict->still-div': 0,   # restart still None at 60k
           'apparent-verdict->slow-agree': 0,  # restart late, value = lim's
           'apparent-verdict->slow-differ': 0,  # restart late, value differs
           'value-mismatch': 0}                # both returned, different
    for A, B, w, rr, oo in raw_mis:
        if rr is not None and oo[0] == 'val':
            cls['value-mismatch'] += 1
            continue
        r2 = restart(A, B, w, 60000, 4_000_000)
        o2 = orbit_pass(A, B, w, 60000, 8_000_000)
        if r2 is None:
            cls['apparent-verdict->still-div'] += 1
        elif r2 == o2[1]:
            cls['apparent-verdict->slow-agree'] += 1
        else:
            cls['apparent-verdict->slow-differ'] += 1
    print(f"  unbordered-B stress: {len(unb_rules)} rules (|A|,|B| <= 6, B"
          f" unbordered, B not-in A) x 100 random inputs 8..14 = "
          f"{len(unb_rules)*100} pairs at cap 6000 -> {len(raw_mis)} raw "
          f"mismatches; classified at restart cap 60000: {cls}")
    for A, B, w, rr, oo in raw_mis[:5]:
        tag = ('val-mismatch' if (rr is not None and oo[0] == 'val')
               else 'verdict')
        print(f"    e.g. [{A}/{B}] {w!r}: {tag}")
    check('unbordered-differ',
          cls['apparent-verdict->slow-differ'] == 0 and cls['value-mismatch'] == 0,
          [m for m in raw_mis[:10]])
    print(f"  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 2b -- the agreement class: A, B nonempty with disjoint alphabets.
# Paper prop:restart-agree says restart = the plain pass there; one sweep
# inserts only characters that cannot occur in B, so no new B can appear:
# lim([A/B]) converges in ONE nontrivial sweep and equals the pass, and
# all three (pass / restart / lim) coincide.

def part2b():
    print("== (2b) agreement class: A,B nonempty, disjoint alphabets ==")
    t0 = time.time()
    n = 0
    for A, B in rules_census():
        if not A or set(A) & set(B):
            continue
        for w in all_strings(9):
            n += 1
            one = subst_fast(A, B, w)
            rr = restart(A, B, w, 2000, 1_000_000)
            oo = orbit_pass(A, B, w, 2000, 1_000_000)
            # one firing sweep (+ one confirming sweep) if B occurs, else
            # the fixed point is detected at the first comparison
            ksweeps = 2 if B in w else 1
            if not (rr == one and oo[0] == 'val' and oo[1] == one
                    and oo[2] == ksweeps):
                check('disjoint', False, (A, B, w, one, rr, oo))
    print(f"  {n} pairs (rules with disjoint nonempty A,B x inputs <= 9): "
          f"pass = restart = lim, orbit stabilizes after the single firing "
          f"sweep: "
          f"{'OK' if not [f for f in FAILS if f[0] == 'disjoint'] else 'FAIL'}")
    print(f"  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 4 -- tower growth through lim

def amp_f(S):
    return 'b' * S.count('b') + 'a' * horner(S)


def half_f(bmaK):
    """b^m a^K -> b^m (ab)^{K//2} a^{K%2}"""
    m = len(bmaK) - len(bmaK.lstrip('b'))
    K = len(bmaK) - m
    return 'b' * m + 'ab' * (K // 2) + 'a' * (K % 2)


def blk_f(bmaK):
    """the block: b^m a^K -> b^{m+K//2} a^{2^{K//2+1}-2+K%2}"""
    m = len(bmaK) - len(bmaK.lstrip('b'))
    K = len(bmaK) - m
    return 'b' * (m + K // 2) + 'a' * (2 ** (K // 2 + 1) - 2 + K % 2)


def AMP(E0):  return L(S(K('baa'), K('ab'), V(0)), E0)
def HALF(E0): return L(S(K('ab'), K('aa'), V(0)), E0)


def part4():
    print("== (4) tower growth through lim (cor:towers) ==")
    t0 = time.time()
    # (a) the amplifier
    bad = 0
    for w in list(all_strings(9)) + rand_strings(40, 10, 12):
        r = run(AMP(V(0)), (w,), 2_000_000, 1 << 22)
        if r[0] != 'val' or r[1] != amp_f(w):
            bad += 1
            check('amplifier', False, (w, r, amp_f(w)))
    print(f"  lim([baa/ab])(S) = b^#b a^v(S): all binary S <= 9 + 40 random "
          f"10..12: {'OK' if bad == 0 else str(bad)+' FAILS'}")

    # (b) the half node
    bad = 0
    for m in range(0, 4):
        for K in range(0, 13):
            w = 'b' * m + 'a' * K
            r = run(HALF(V(0)), (w,), 100000, 1 << 20)
            if r[0] != 'val' or r[1] != half_f(w):
                bad += 1
                check('half', False, (w, r, half_f(w)))
    print(f"  lim([ab/aa]): b^m a^K -> b^m (ab)^(K/2) a^(K%2), m<=3, K<=12: "
          f"{'OK' if bad == 0 else str(bad)+' FAILS'}")

    # (c) towers, against closed forms AND against the restart composition
    def rAmp(w):  return restart('baa', 'ab', w, 1 << 22, 1 << 26)
    def rHalf(w): return restart('ab', 'aa', w, 1 << 22, 1 << 26)

    # t = 1 on ab^(n-1): output length 2^(n-1)+n-1  (paper: n <= 5+)
    bad = 0
    for n in range(1, 7):
        w = 'a' + 'b' * (n - 1)
        r = run(AMP(V(0)), (w,), 2_000_000, 1 << 22)
        exp = amp_f(w)
        if r[0] != 'val' or r[1] != exp or len(exp) != 2 ** (n - 1) + n - 1:
            bad += 1
            check('t1', False, (n, r, exp))
    print(f"  tower t=1: lim([baa/ab])(ab^(n-1)) length = 2^(n-1)+n-1, n<=6: "
          f"{'OK' if bad == 0 else str(bad)+' FAILS'}")

    # t = 2: AMP(HALF(AMP(X))) on ab^(n-1), n <= 5; and the block on the grid
    bad = 0
    for n in range(1, 6):
        w = 'a' + 'b' * (n - 1)
        exp = amp_f(half_f(amp_f(w)))          # closed-form composition
        r = run(AMP(HALF(AMP(V(0)))), (w,), 2_000_000, 1 << 22)
        rr = rAmp(rHalf(rAmp(w)))             # restart composition
        if r[0] != 'val' or r[1] != exp or rr != exp:
            bad += 1
            check('t2', False, (n, r, exp, rr))
    for m in range(0, 4):
        for K in range(0, 13):
            w = 'b' * m + 'a' * K
            exp = blk_f(w)
            r = run(AMP(HALF(V(0))), (w,), 2_000_000, 1 << 22)
            rr = rAmp(rHalf(w))
            if r[0] != 'val' or r[1] != exp or rr != exp:
                bad += 1
                check('t2grid', False, (m, K, r, exp, rr))
    print(f"  tower t=2 (block): grid m<=3, K<=12 + ab^(n-1) n<=5 = tower "
          f"height 2 in the input length; lim == closed form == restart: "
          f"{'OK' if bad == 0 else str(bad)+' FAILS'}")

    # t = 3: five nodes, on ab^(n-1) for n <= 4 (output a^(2^16-2) at n=4)
    bad = 0
    for n in range(1, 5):
        w = 'a' + 'b' * (n - 1)
        exp = amp_f(half_f(amp_f(half_f(amp_f(w)))))
        r = run(AMP(HALF(AMP(HALF(AMP(V(0)))))), (w,), 4_000_000, 1 << 23)
        rr = rAmp(rHalf(rAmp(rHalf(rAmp(w)))))
        if r[0] != 'val' or r[1] != exp or rr != exp:
            bad += 1
            check('t3', False, (n, r[0], len(r[1]) if r[0]=='val' else None,
                                len(exp), None if rr is None else len(rr)))
    print(f"  tower t=3 (5 lim-nodes) on ab^(n-1), n<=4: output lengths "
          f"{[len(amp_f(half_f(amp_f(half_f(amp_f('a'+'b'*(n-1))))))) for n in range(1,5)]}; "
          f"lim == closed form == restart: {'OK' if bad == 0 else str(bad)+' FAILS'}")
    print(f"  [{time.time()-t0:.1f}s]")


# ===========================================================================
# PART 5 -- demos

def mk_if(cond, xt, xf):
    """the paper's Selection, binary alphabet b='a', x='b', top='b', bot='a':
       if(C,X,Y) = dec([enc(Y)/bb]([enc(X)/top][bb/bot]C))"""
    def enc(E): return S(K('ba'), K('a'), E)
    def dec(E): return S(K('a'), K('ba'), E)
    return dec(S(enc(xf), K('aa'),
                 S(enc(xt), K('b'), S(K('aa'), K('a'), cond))))


def mk_contains(E, B):
    """contains(X,B) = top iff the constant B != eps occurs in X.
    changed = [M/B]X (M a single char != B): changed == X iff B absent
    (the fixed-point-set lemma); then eq(X, changed) via the paper's
    Equality (b='a', x='b', top='b', bot='a') and Selection."""
    M = 'a' if B[0] != 'a' else 'b'
    assert M not in (B,) and len(M) == 1
    changed = S(K(M), K(B), E)

    def benc(Z): return C(C(K('baa'), S(K('ba'), K('a'), Z)), K('baa'))
    # eq(X,Y) = [bot/benc(X)][top/benc(Y)](benc(X)); rightmost runs first.
    eqx = S(K('a'), benc(E), S(K('b'), benc(changed), benc(E)))
    return mk_if(eqx, K('a'), K('b'))       # eq true (=absent) -> bot


def part5():
    print("== (5) demos: nesting, branching iterands, growth ==")
    # (a) nested lim: lim(lim([eps/ba])).  NOTE: a single deletion sweep is
    # NOT idempotent -- deleting 'ba' from 'bbaa' merges the neighbors into a
    # fresh 'ba' -- so lim([eps/ba]) itself iterates; the expected value is
    # the true fixed point (a 'ba'-free string, by the fixed-point-set lemma).
    E2 = S(K(''), K('ba'), V(0))
    nest = L(L(E2, V(0)), V(0))
    bad = 0
    for w in all_strings(8):
        r = run(nest, (w,), 100000, 1 << 20)
        exp = w
        while 'ba' in exp:
            exp = exp.replace('ba', '')
        if r[0] != 'val' or r[1] != exp or 'ba' in r[1]:
            bad += 1
            check('nest', False, (w, r))
    print(f"  nested lim(lim([eps/ba])): all |w|<=8: "
          f"{'OK' if bad == 0 else str(bad)+' FAILS'}")

    # (b) branching iterand: E(x) = if(contains(x,'bb'), x, x·b) -- the
    # iterand does data-dependent work (Selection + Equality + the
    # occurrence test), the power source for universality.  The appended b
    # uses the concatenation node (grammar sugar, eliminable by thm:core).
    body = mk_if(mk_contains(V(0), 'bb'), V(0), C(V(0), K('b')))
    bad = 0
    for w in all_strings(6):
        r = run(L(body, V(0)), (w,), 100000, 1 << 20)
        exp = w
        while 'bb' not in exp:
            exp = exp + 'b'
        if r[0] != 'val' or r[1] != exp:
            bad += 1
            check('branch', False, (w, r, exp))
    print(f"  branching iterand if(contains(x,bb), x, xb) under lim: "
          f"all |w|<=6 -> first bb-suffix: "
          f"{'OK' if bad == 0 else str(bad)+' FAILS'}")

    # (c) growth: lim([XX/X]) doubles; orbit lengths 1,2,4,8,...
    g = L(S(C(V(0), V(0)), V(0), V(0)), V(0))
    bud = Budget(20, 1 << 20)
    lens = []
    s = 'a'
    try:
        for _ in range(10):
            lens.append(len(s))
            s = ev(S(C(V(0), V(0)), V(0), V(0)), (s,), bud)
    except Diverge:
        lens.append(len(s))
    print(f"  growth lim([X1X1/X1])('a'): orbit lengths {lens} -> diverges, "
          f"{'OK' if lens[:6] == [1, 2, 4, 8, 16, 32] else 'FAIL'}")
    r = run(g, ('a',), 100, 1 << 20)
    print(f"    verdict on 'a': {r[0]} (expected div)")


# ===========================================================================

def main():
    print("L + lim -- Round 1 verification\n")
    part0()
    part1()
    hard4, verd_rules, val_rules = part2()
    part2b()
    part3(hard4, verd_rules)
    part4()
    part5()
    print()
    print(f"R1 RESULT: {NCHECK[0]} checks, {len(FAILS)} failures")
    if FAILS:
        for name, detail in FAILS[:20]:
            print(f"  FAIL {name}: {detail}")
        sys.exit(1)


if __name__ == '__main__':
    main()

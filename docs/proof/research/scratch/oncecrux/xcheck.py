"""xcheck.py -- cross-validation of the C search harness (search.c).

Everything here is INDEPENDENT of the C code:
  * pass application  vs  Python str.replace (prior art R1: subst == replace
    for constant patterns, cross-checked against the paper semantics);
  * oracle targets    vs  direct implementations of def:once / tau;
  * world generator   vs  DP re-segmentation of dumped texts into tokens,
    plus the freshness property (every M-occurrence at a mark-token start);
  * pair enumeration  vs  the prior art's token_fresh / find_constants
    (ported from ../once/verify_marking.py, the paper's supporting code).

Inputs: selftest_W.txt / selftest_C3.txt (from `./search selftest <cls>`).
Run: /usr/bin/python3 xcheck.py          (light loops only; a few seconds)
"""
import itertools
import sys

ONCE = '../once'


def unescape(s):
    return '' if s == '<e>' else s


# ---------------------------------------------------------------- targets
def tgt_sanity(T):
    i = T.find('b')
    return T if i < 0 else T[:i] + 'a' + T[i + 1:]


def tgt_crux(T):
    i = T.find('baa')
    return T if i < 0 else T[:i] + 'babba' + T[i + 3:]


def tgt_trunc(T):
    i = T.find('aa')
    return T if i < 0 else T[:i]


def tgt_pair(M, A0):
    def f(T):
        i = T.find(M)
        return T if i < 0 else T[:i] + A0 + T[i + len(M):]
    return f


# ---------------------------------------------------- prior art pair check
def token_fresh(M, A0, cells, ntok=4):
    """verbatim port of verify_marking.token_fresh"""
    toks = cells + [M, A0]
    for k in range(1, ntok + 1):
        for prod_t in itertools.product(toks, repeat=k):
            T = ''.join(prod_t)
            for marker in (M, A0):
                start = 0
                while True:
                    i = T.find(marker, start)
                    if i < 0:
                        break
                    pos, ok = 0, False
                    for t in prod_t:
                        if pos == i and t == marker:
                            ok = True
                        pos += len(t)
                    if not ok:
                        return False
                    start = i + 1
    return True


def find_constants(sigma, x, maxlen=5):
    """verbatim port of verify_marking.find_constants"""
    cells = [x + c for c in sigma]
    cand = []
    letters = sorted(set(sigma))
    for lm in range(2, maxlen + 1):
        for M in (''.join(t) for t in itertools.product(letters, repeat=lm)):
            if M in cells:
                continue
            for la in range(2, maxlen + 1):
                for A0 in (''.join(t) for t in
                           itertools.product(letters, repeat=la)):
                    if A0 == M or A0 in cells:
                        continue
                    if token_fresh(M, A0, cells):
                        cand.append((M, A0))
        if cand:
            return cand
    return cand


# --------------------------------------------------------- token machinery
def segmentable(T, toks):
    """is T a product of tokens (DP)?"""
    n = len(T)
    reach = [False] * (n + 1)
    reach[0] = True
    for i in range(n):
        if not reach[i]:
            continue
        for t in toks:
            if T.startswith(t, i):
                reach[i + len(t)] = True
    return reach[n]


def token_starts(T, toks, M):
    """all positions where an M-token can start in SOME segmentation, plus
    a check that every M-occurrence starts at a possible M-token start."""
    n = len(T)
    fwd = [False] * (n + 1)      # reachable from 0
    fwd[0] = True
    for i in range(n):
        if fwd[i]:
            for t in toks:
                if T.startswith(t, i):
                    fwd[i + len(t)] = True
    bwd = [False] * (n + 1)      # can reach the end
    bwd[n] = True
    for i in range(n - 1, -1, -1):
        for t in toks:
            if T.startswith(t, i) and bwd[i + len(t)]:
                bwd[i] = True
                break
    # positions where an M-token can sit in a full segmentation
    ok_starts = set()
    for i in range(n - len(M) + 1):
        if (fwd[i] and T.startswith(M, i) and bwd[i + len(M)]
                and any(fwd[j] and T.startswith(M, j) and bwd[j + len(M)]
                        is not None for j in [i])):
            ok_starts.add(i)
    # every occurrence of M must be a possible M-token start
    pos = T.find(M)
    while pos >= 0:
        if pos not in ok_starts:
            return False, pos
        pos = T.find(M, pos + 1)
    return True, None


# ------------------------------------------------------------------ main
def main():
    fails = 0

    for fn in ('selftest_W.txt', 'selftest_C3.txt'):
        lines = open(fn).read().splitlines()
        i = 0
        npass, passes = 0, []
        napply = 0
        pairs = []
        # world tables
        world = None      # (name, M, A0, target fn, tokens)
        nbat = nfb = 0
        while i < len(lines):
            L = lines[i]
            f = L.split()
            if f[0] == 'CLASS':
                npass = int(f[3])
                assert int(f[3]) >= 1
            elif f[0] == 'PASS':
                passes.append((unescape(f[1]), unescape(f[2])))
            elif f[0] == 'APPLY':
                R, P, T, O = (unescape(f[1]), unescape(f[2]),
                              unescape(f[3]), unescape(f[4]))
                if T.replace(P, R) != O:
                    print(f"APPLY FAIL: [{R}/{P}] {T} -> {O} (want "
                          f"{T.replace(P, R)})")
                    fails += 1
                napply += 1
            elif f[0] == 'PAIRS':
                pass
            elif f[0] == 'PAIR':
                pairs.append((f[1], f[2]))
            elif f[0] == 'BATW':
                # BATW <name> <M> <A0> n <nb>
                name, M, A0 = f[1], f[2], f[3]
                if name == 'sanity':
                    world = ('sanity', tgt_sanity, None, None)
                elif name == 'crux':
                    world = ('crux', tgt_crux, 'baa', ['ba', 'bb', 'baa'])
                elif name == 'trunc':
                    world = ('trunc', tgt_trunc, 'baa', ['ba', 'bb', 'baa'])
                else:
                    world = ('pair', tgt_pair(M, A0), M, ['ba', 'bb', M])
            elif f[0] == 'BAT' or f[0] == 'FB':
                T, O = unescape(f[1]), unescape(f[2])
                name, tf, M, toks = world
                if tf(T) != O:
                    print(f"TARGET FAIL [{name}]: {T} -> {O} (want {tf(T)})")
                    fails += 1
                if toks is not None:
                    if not segmentable(T, toks):
                        print(f"NOT A TOKEN PRODUCT [{name}]: {T}")
                        fails += 1
                    ok, pos = token_starts(T, toks, M)
                    if not ok:
                        print(f"FRESHNESS FAIL [{name}]: M at {pos} in {T}")
                        fails += 1
                    # target output must ALSO be consistent: crux target ==
                    # tau(T) + 'abba' + rest-after-mark
                    if name == 'crux':
                        m = T.find('baa')
                        if m >= 0:
                            want = T[:m + 1] + 'abba' + T[m + 3:]
                            if want != O:
                                print(f"CRUX/TAU FORMULATION FAIL: {T}")
                                fails += 1
                if f[0] == 'BAT':
                    nbat += 1
                else:
                    nfb += 1
            i += 1
        # class sanity: no identity passes, counts
        if len(passes) != npass:
            print(f"PASS COUNT MISMATCH in {fn}: {len(passes)} vs {npass}")
            fails += 1
        for (R, P) in passes:
            if R == P or not P or len(P) > 3 or len(R) > 3:
                print(f"BAD PASS in {fn}: [{R}/{P}]")
                fails += 1
        # pair-table cross-check (identical in both files; check once)
        if fn == 'selftest_W.txt':
            cells = ['ba', 'bb']
            bad = 0
            for (M, A0) in pairs:
                if not (2 <= len(M) <= 6 and 2 <= len(A0) <= 6):
                    print(f"PAIR LEN FAIL: {M} {A0}")
                    fails += 1
                    continue
                if M in cells or A0 in cells or A0 == M:
                    print(f"PAIR BASIC FAIL: {M} {A0}")
                    fails += 1
                if not token_fresh(M, A0, cells, 4):
                    print(f"PAIR FRESHNESS FAIL: {M} {A0}")
                    fails += 1
            # exhaustive negative check on the full |M|,|A0| <= 4 space
            strs4 = [''.join(t) for n in (2, 3, 4)
                     for t in itertools.product('ab', repeat=n)]
            cands = [s for s in strs4 if s not in cells]
            for M in cands:
                for A0 in cands:
                    if A0 == M:
                        continue
                    fresh = token_fresh(M, A0, cells, 4)
                    inc = (M, A0) in set(pairs)
                    if fresh != inc:
                        print(f"PAIR DISAGREEMENT: {M} {A0} py={fresh} c={inc}")
                        fails += 1
            # prior-art find_constants comparison (|M|=3 minimal, |A0| <= 5)
            prior = find_constants(list('ab'), 'b', 5)
            mine3 = [(M, A0) for (M, A0) in pairs
                     if len(M) == 3 and len(A0) <= 5]
            if sorted(prior) != sorted(mine3):
                print(f"FIND_CONSTANTS MISMATCH: py {sorted(prior)} vs "
                      f"c {sorted(mine3)}")
                fails += 1
            print(f"[pairs] C pairs total {len(pairs)}; prior-art "
                  f"find_constants(|M|=3,|A0|<=5) = {len(prior)} -> "
                  f"{'AGREE' if sorted(prior) == sorted(mine3) else 'DIFFER'}")
        print(f"[{fn}] {napply} APPLY checks, {nbat} BAT checks, "
              f"{nfb} FB checks, {len(pairs)} pairs -- "
              f"{'ALL GREEN' if fails == 0 else str(fails) + ' FAILURES'}")
    print("ALL GREEN" if fails == 0 else f"FAILURES: {fails}")
    return 0 if fails == 0 else 1


if __name__ == '__main__':
    sys.exit(main())

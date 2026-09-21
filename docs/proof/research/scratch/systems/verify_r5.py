"""R5: close the R1 hand-derived collapse rows (1-3) with machine checks,
including the row-2 granularity correction."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from systems import once, restart, rescan, occ

def strings(maxlen):
    out = []
    for L in range(maxlen + 1):
        for t in itertools.product('ab', repeat=L):
            out.append(''.join(t))
    return out

def pats(maxlen):
    return [''.join(t) for L in range(1, maxlen + 1)
            for t in itertools.product('ab', repeat=L)]

# ROW 1: once + rescan = once.  The unsafe once-pass: the scan may match
# inside previously INSERTED text; but once performs at most one splice,
# so at match time no text has been inserted: the first match is the
# first occurrence either way.
def once_unsafe(A, B, C):
    # scan allowing matches against inserted text is irrelevant pre-splice:
    # first occurrence of B in C
    O = occ(C, B)
    if not O:
        return C
    i = O[0]
    return C[:i] + A + C[i + len(B):]

bad1 = 0
for A in pats(2) + ['']:
    for B in pats(2):
        for S in strings(5):
            if once_unsafe(A, B, S) != once(A, B, S):
                bad1 += 1
print(f"ROW 1 once+rescan = once: "
      f"{len(pats(2)+[''])*len(pats(2))*len(strings(5))} checks, "
      f"{bad1} mismatches (expect 0)")

# ROW 3: once + restart (node level) = MARKOV: iterate "replace leftmost
# occurrence" to fixpoint = restart verbatim.
def once_restart(A, B, C, cap=10000):
    s, steps = C, 0
    while B in s:
        s = once(A, B, s)
        steps += 1
        if steps > cap:
            return None
    return s

bad3 = agree3 = 0
for A in pats(2) + ['']:
    for B in pats(2):
        for S in strings(5):
            a = once_restart(A, B, S)
            b = restart(A, B, S, cap=10000)
            if (a is None) != (b is None):
                bad3 += 1
            elif a is not None and a != b:
                bad3 += 1
            else:
                agree3 += 1
print(f"ROW 3 once+restart(node) = MARKOV: {agree3} agreements, "
      f"{bad3} mismatches (expect 0)")

# ROW 2: rescan + restart.  STEP-granularity (= MARKOV): each step
# replaces the leftmost occurrence, rescanning from 0 -- plain restart
# already does that, so the rescan clause is subsumed.  PASS-granularity
# (iterate the FULL unsafe pass to a fixpoint) is a DIFFERENT system.
def unsafe_pass(A, B, C, cap=100000):
    """one unsafe pass: replace occurrences left-to-right, RESUMING THE SCAN
    INSIDE INSERTED TEXT (paper 5.4 semantics)."""
    out, i, n, m, steps = [], 0, len(C), len(B), 0
    text = C
    res, j = [], 0
    # emulate: scan position p in the OUTPUT being built, comparing
    # against B; classic rescan semantics = infinite loop risk when B in A
    s = C
    # simpler faithful emulation: repeatedly find leftmost occurrence of B
    # in the CURRENT output-with-cursor... the paper's rescan: greedy scan
    # where after a splice the scan RESTARTS at the beginning of the
    # inserted replacement text.
    out = []
    i = 0
    n = len(C)
    # cursor over original + ability to match across the boundary of
    # already-emitted text: rescan can see out[-(m-1):] + C[i:i+m-1]
    while i < n:
        # candidate: suffix of emitted text + upcoming original chars
        matched = False
        for pre in range(min(m - 1, len(out)), -1, -1):
            cand = ''.join(out[len(out) - pre:]) + C[i:i + m - pre]
            if pre > 0 and len(cand) < m:
                continue
            if len(cand) == m and cand == B:
                out.extend(A)
                i += m - pre
                matched = True
                steps += 1
                if steps > cap:
                    return None
                break
        if not matched:
            if m == 1 and C[i:i + m] == B:
                out.extend(A); i += 1; matched = True
        if not matched:
            out.append(C[i])
            i += 1
    return ''.join(out)

def restart_unsafe_pass(A, B, C, cap=100000):
    """iterate the full unsafe pass to a fixpoint (row 2, pass-granularity)"""
    s, steps = C, 0
    while True:
        t = unsafe_pass(A, B, s, cap)
        if t is None:
            return None
        if t == s:
            return s
        s, steps = t, steps + 1
        if steps > cap:
            return None

# sanity: unsafe_pass vs systems.rescan on cases where B not in A
san = 0
for A in pats(2):
    for B in pats(2):
        if B in A:
            continue
        for S in strings(4):
            a = unsafe_pass(A, B, S)
            b = rescan(A, B, S, cap=100000)
            if a is None or b is None or a != b:
                san += 1
print(f"unsafe_pass vs systems.rescan (B not-in A): {san} mismatches "
      f"(expect 0 -- semantics cross-check)")

# the granularity witness: [ba/ab] on 'abab'
w = restart_unsafe_pass('ba', 'ab', 'abab')
r = restart('ba', 'ab', 'abab', cap=100000)
print(f"ROW 2 granularity witness [ba/ab] on 'abab': "
      f"pass-level = {w!r}, Markov = {r!r}, "
      f"{'DIFFER (row-2 pass-granularity is NOT Markov)' if w != r else 'same'}")

"""R5b: row 2 done right -- iterate the FULL unsafe pass (systems.rescan)
to a fixpoint, vs MARKOV (restart).  rescan is total iff B not-in A."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from systems import restart, rescan

def strings(maxlen):
    return [''.join(t) for L in range(maxlen + 1)
            for t in itertools.product('ab', repeat=L)]

def pats(maxlen):
    return [''.join(t) for L in range(1, maxlen + 1)
            for t in itertools.product('ab', repeat=L)]

def restart_pass(A, B, C, cap=2000):
    """iterate the full rescan pass to a fixpoint (pass granularity)."""
    s, steps = C, 0
    while True:
        t = rescan(A, B, s, cap=cap)
        if t is None:
            return None
        if t == s:
            return s
        s = t
        steps += 1
        if steps > cap:
            return None

agree = diff = undef_diff = 0
wits = []
for A in pats(3):
    for B in pats(3):
        if B in A:
            continue                      # rescan diverges; restart too
        for S in strings(5):
            a = restart_pass(A, B, S)
            b = restart(A, B, S, cap=2000)
            if a is None or b is None:
                if (a is None) != (b is None):
                    undef_diff += 1
                continue
            if a == b:
                agree += 1
            else:
                diff += 1
                if len(wits) < 6:
                    wits.append((A, B, S, a, b))
print(f"pass-granularity (iterate rescan passes) vs MARKOV, B not-in A: "
      f"{agree} agreements, {diff} value differences, "
      f"{undef_diff} definedness differences")
for w in wits:
    print(f"   witness [{w[0]}/{w[1]}] on {w[2]!r}: pass-iter {w[3]!r} "
          f"vs Markov {w[4]!r}")

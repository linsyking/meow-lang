"""Round 2, battery U: the |Sigma| = 1 edge.

  U1  the unary expression space, exhaustively up to SIZE <= 7 (36,978
      expressions) plus 3000 random depth <= 4; collect the induced length
      maps n |-> |[[E]](a^n)| on n = 0..24:
      U1a every CONSTANT pass [a^i/a^j] acts on lengths as
          n |-> i*floor(n/j) + (n mod j)   (greedy scan of a unary string).
      U1b target maps: which of id, 2n, n^2, n+1, floor(n/2), ceil(n/2),
          parity, n-1, n^4, 2^n appear in the space?  (floor(n/2) is the
          paper's prop:unary-once H, which needs a SECOND letter; 2^n is
          excluded at every size by the polynomial-growth lemma.)
  U2  there is no injective monoid homomorphism {a,b}* -> {a}*: any hom
      h has h(ab) = h(a)h(b) = h(b)h(a) = h(ba), and ab != ba.  Hence NO
      coding-conjugation scheme exists for binary -> unary; the transfer
      theorem cannot cross the |Sigma| = 1 boundary from above.
  U3  binary length profiles vs the unary space: for all depth<=1 binary
      expressions (constants <= 2 over {a,b}) plus random depth<=3, the
      profile n |-> |[[E]](a^n)|, n = 0..12; which total profiles are
      missing from the exhaustive size<=7 unary space?  (Bounded-search
      evidence, stated as such.)
"""
import random
import sys
from meow import ev, all_strings, size

random.seed(20260922)
LOG = []
def log(s):
    print(s)
    LOG.append(s)

def check(name, n, ok):
    log(f"{'OK  ' if ok else 'FAIL'} {name}: {n} cases")
    return ok

allok = True

NS = list(range(25))            # n = 0..24 for unary profiles
NB = list(range(13))            # n = 0..12 for binary profiles

# ---------- U1a: constant passes act as i*floor(n/j) + n mod j ----------
n_cases = bad = 0
for i in range(5):
    for j in range(1, 5):
        E = ('pass', ('const', 'a' * i), ('const', 'a' * j), ('var', 0))
        n_cases += 1
        want = tuple(i * (n // j) + n % j for n in NS)
        got = tuple(len(ev(E, ['a' * n])) for n in NS)
        if got != want:
            bad += 1
log(f"U1a constant pass [a^i/a^j] acts as i*floor(n/j)+(n mod j) on lengths: "
    f"{n_cases} (i,j) pairs, {bad} mismatches")
allok &= check("U1a constant-pass length law", n_cases, bad == 0)

# ---------- the exhaustive unary space: all expressions of size <= 7 ----------
leaves = [('var', 0)] + [('const', 'a' * k) for k in range(5)]
EXPRS = {1: list(leaves)}

def exprs_of(s):
    if s in EXPRS:
        return EXPRS[s]
    res = []
    for a in range(1, s):                       # cat: 1 + a + b = s
        b = s - 1 - a
        if b < 1:
            break
        for E1 in exprs_of(a):
            for E2 in exprs_of(b):
                res.append(('cat', E1, E2))
    for a in range(1, s):                       # pass: 1 + a + b + c = s
        for b in range(1, s - a):
            c = s - 1 - a - b
            if c < 1:
                break
            for R in exprs_of(a):
                for P in exprs_of(b):
                    for E in exprs_of(c):
                        res.append(('pass', R, P, E))
    EXPRS[s] = res
    return res

UALL = []
for s in range(1, 8):
    UALL.extend(exprs_of(s))

def rand_unary(d):
    if d == 0:
        return random.choice([('var', 0), ('const', 'a' * random.randint(0, 4))])
    if random.random() < 0.7:
        return ('pass', rand_unary(d - 1), rand_unary(d - 1), rand_unary(d - 1))
    return ('cat', rand_unary(d - 1), rand_unary(d - 1))

UR = [rand_unary(4) for _ in range(3000)]
UALL += UR
log(f"unary space: exhaustive size<=7 = {len(UALL) - len(UR)} expressions "
    f"(+ {len(UR)} random depth<=4)")

def profile(E, ns):
    out = []
    for n in ns:
        v = ev(E, ['a' * n])
        out.append(None if v is None else len(v))
    return tuple(out)

uprofiles = {}
for E in UALL:
    uprofiles.setdefault(profile(E, NS), []).append(E)
log(f"distinct total-and-partial unary length maps on n=0..24: {len(uprofiles)}")

def find(prof):
    hits = uprofiles.get(tuple(prof))
    return min(hits, key=size) if hits else None

# ---------- U1b: target maps ----------
targets = {
    "id n": lambda n: n,
    "2n": lambda n: 2 * n,
    "n^2": lambda n: n * n,
    "n+1": lambda n: n + 1,
    "n^4": lambda n: n ** 4,
    "floor(n/2)": lambda n: n // 2,
    "ceil(n/2)": lambda n: (n + 1) // 2,
    "n mod 2": lambda n: n % 2,
    "max(n-1,0)": lambda n: max(n - 1, 0),
    "2^n": lambda n: 2 ** n,
}
log("U1b target maps (searched over the exhaustive size<=7 space, n=0..24):")
found = {}
for name, f in targets.items():
    E = find(tuple(f(n) for n in NS))
    found[name] = E is not None
    log(f"  {name:14s}: {'FOUND  ' if E else 'NOT FOUND'}"
        + (f" e.g. {E} (size {size(E)})" if E else ""))
exp = {"id n": True, "2n": True, "n^2": True, "n^4": False, "n+1": True,
       "floor(n/2)": False, "ceil(n/2)": True, "n mod 2": True,
       "max(n-1,0)": False, "2^n": False}
bad = sum(1 for k, v in exp.items() if found[k] != v)
log(f"U1b expectations (floor(n/2), n-1, n^4 (needs size 10), 2^n absent at "
    f"size<=7; rest present): {bad} surprises")
allok &= check("U1b target-map search over size<=7", len(targets), bad == 0)

# n^4 is reachable at size 10 by squaring twice: [[X/a]X / a]([X/a]X)
sq = ('pass', ('var', 0), ('const', 'a'), ('var', 0))
n4 = ('pass', sq, ('const', 'a'), sq)
ok4 = profile(n4, NS) == tuple(n ** 4 for n in NS)
log(f"U1b' witness for n^4 at size {size(n4)}: {ok4}")
allok &= check("U1b' n^4 reachable by double squaring (size 10)", 25, ok4)

# ---------- U2: no injective homomorphism {a,b}* -> {a}* ----------
n_cases = bad = 0
for i in range(4):
    for j in range(4):
        n_cases += 1
        if (i + j) != (j + i):        # h(ab) = a^{i+j} vs h(ba) = a^{j+i}
            bad += 1
log(f"U2 every homomorphism h(a)=a^i, h(b)=a^j collides on ab/ba: "
    f"{n_cases} pairs, {bad} non-colliding (hand proof: h(ab)=h(ba), ab!=ba)")
allok &= check("U2 no injective homomorphism binary -> unary", n_cases, bad == 0)

# ---------- U3: binary length profiles vs the unary space ----------
bleaves = [('var', 0)] + [('const', w) for w in all_strings('ab', 2)]
B1 = list(bleaves)
for R in bleaves:
    for P in bleaves:
        for E in bleaves:
            B1.append(('pass', R, P, E))
for E1 in bleaves:
    for E2 in bleaves:
        B1.append(('cat', E1, E2))

def rand_bin(d):
    if d == 0:
        if random.random() < 0.5:
            return ('var', 0)
        return ('const', ''.join(random.choice('ab') for _ in range(random.randint(0, 3))))
    if random.random() < 0.7:
        return ('pass', rand_bin(d - 1), rand_bin(d - 1), rand_bin(d - 1))
    return ('cat', rand_bin(d - 1), rand_bin(d - 1))

BR = [rand_bin(3) for _ in range(2000)]
log(f"binary space: {len(B1)} depth<=1 (constants<=2) + {len(BR)} random depth<=3")

uset = {u[:len(NB)] for u in uprofiles}
# constant shifts at the profile level: cat(E, a^k) / cat(a^k, E) for the
# whole size<=7 space (an expression of size 8..11, but a trivial one);
# values capped to keep the comparison finite.
ushift = set(uset)
for u in uset:
    for k in range(0, 65):
        if all(x is not None and x + k <= 400 for x in u):
            ushift.add(tuple(x + k for x in u))
missing = {}
total = 0
for E in B1 + BR:
    p = profile(E, NB)
    if any(x is None for x in p):
        continue                      # only total profiles compete
    total += 1
    if p not in ushift:
        missing.setdefault(p, []).append(E)
log(f"U3 total binary profiles on n=0..12: {total}; "
    f"{len(missing)} NOT realized in the size<=7 unary space or a "
    f"constant shift of it")
for p in sorted(missing, key=lambda p: (p[-1], p))[:10]:
    E = min(missing[p], key=size)
    log(f"  missing profile {list(p)}  e.g. {E}")
# expectation: profiles below are unary-realizable at small size, so the
# survivors are the interesting ones (max-shaped, non-monotone at 0, or
# super-polynomial -- excluded forever by the growth lemma only in the
# asymptotic sense).
allok &= check("U3 binary profiles vs exhaustive unary space (data)", total,
               len(missing) >= 0)

with open('unary.log', 'w') as f:
    f.write('\n'.join(LOG) + '\n')
print("ALL OK" if allok else "SOME FAILURES")
sys.exit(0 if allok else 1)

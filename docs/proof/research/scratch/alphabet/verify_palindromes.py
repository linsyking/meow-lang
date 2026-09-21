"""Round 2, battery P: palindromic comma-free dictionaries.

Reversal is the one equivariance that character-wise codings do NOT enjoy:
c(rev S) = rev(c(S)) holds iff every codeword is a palindrome (the machine
caught the naive claim false in round 1).  The reversal payoff therefore
runs through a retraction q = c o e whose e has PALINDROMIC comma-free
codewords.  This battery checks the dictionaries that make that possible.

  P1  the middle-marker family  D = {alpha mu rev(alpha) : alpha over
      Gamma\\{mu}, |alpha| = m}  is palindromic and comma-free.  Proof:
      mu occurs in each codeword only at the exact middle, so an occurrence
      of any codeword in u*v has its mu at p+m, and the mu positions of
      u*v are m and 3m+1; hence p in {0, 2m+1} -- aligned.  Unbounded for
      |Gamma| >= 3; size 1 for |Gamma| = 2 (the binary wall).
  P2  binary dictionaries of size 3 exist: {aabaa, ababa, abbba} and
      {aabaa, babab, bbabb} (found by search, both comma-free).  A size-3
      binary palindromic comma-free dictionary is what lets the reversal
      payoff escape the binary alphabet (P4 route (a)).
  P3  exact maxima of palindromic comma-free sets over binary for small
      lengths (branch and bound): observed 1, 1, 3, 2, 7, ?, 14 for
      ell = 3..9.  Recorded as data; the payoff needs only size >= 3.
  P4  composition (L3): for every reversal route, the q-codewords
      {c(e(gamma))} form a comma-free dictionary.
      (a) Sigma = binary source: c = aa-family (ell=5), e = any 2 of the
          size-3 binary palindromic dictionary.
      (b) Sigma = ternary source: c = aa-family (ell=6), e = middle-marker
          {bab, cac} over abc.
"""
import sys
from itertools import product
from meow import comma_free, make_coding, enc

LOG = []
def log(s):
    print(s)
    LOG.append(s)

def check(name, n, ok):
    log(f"{'OK  ' if ok else 'FAIL'} {name}: {n} cases")
    return ok

allok = True

def palindromes(gamma, ell):
    res = set()
    if ell % 2 == 1:
        for a in product(gamma, repeat=(ell - 1) // 2):
            for mid in gamma:
                res.add(''.join(a) + mid + ''.join(reversed(a)))
    else:
        for a in product(gamma, repeat=ell // 2):
            res.add(''.join(a) + ''.join(reversed(a)))
    return sorted(res)

def max_pal_cf(gamma, ell):
    P = palindromes(gamma, ell)
    n = len(P)
    best = []
    def search(i, cur):
        nonlocal best
        if len(cur) + (n - i) <= len(best):
            return
        if i == n:
            best = list(cur)
            return
        if comma_free(cur + [P[i]]):
            search(i + 1, cur + [P[i]])
        search(i + 1, cur)
    search(0, [])
    return best

# ---------- P1: middle-marker family ----------
n = bad = 0
for gamma, mu in [('abc', 'a'), ('abcd', 'a'), ('abc', 'b'), ('abcd', 'c')]:
    for m in range(1, 6):
        D = [''.join(alpha) + mu + ''.join(reversed(alpha))
             for alpha in product([c for c in gamma if c != mu], repeat=m)]
        n += 1
        if not (all(w == w[::-1] for w in D) and comma_free(D)
                and len(D) == (len(gamma) - 1) ** m):
            bad += 1
log(f"P1 middle-marker family palindromic+comma-free+size (q-1)^m: "
    f"{n} dictionaries, {bad} failures")
allok &= check("P1 middle-marker family (q>=3, m=1..5)", n, bad == 0)

# ---------- P2: size-3 binary dictionaries ----------
n = bad = 0
for D in [['aabaa', 'ababa', 'abbba'], ['aabaa', 'babab', 'bbabb']]:
    n += 1
    if not (all(w == w[::-1] for w in D) and comma_free(D) and len(set(D)) == 3):
        bad += 1
log(f"P2 binary size-3 palindromic comma-free dictionaries: {n} checked, {bad} failures")
allok &= check("P2 binary size-3 dictionaries", n, bad == 0)

# ---------- P3: exact maxima over binary ----------
sizes = {}
for ell in [3, 4, 5, 6, 7, 9]:
    best = max_pal_cf('ab', ell)
    sizes[ell] = len(best)
    assert comma_free(best) and all(w == w[::-1] for w in best)
log(f"P3 exact maxima of palindromic comma-free sets over binary: {sizes} "
    f"(ell=3..7,9; 2^ceil(ell/2) palindromes each)")
allok &= check("P3 binary maxima computed (data)", len(sizes), True)

# ---------- P4: composition for the reversal routes ----------
cmap2, Dc2, ellc2 = make_coding('ab', 'xy')          # c: ab -> xy, ell=5
cmap3, Dc3, ellc3 = make_coding('abc', 'xy')         # c: abc -> xy, ell=6
n = bad = 0
for e_map in [{'x': 'aabaa', 'y': 'ababa'}, {'x': 'aabaa', 'y': 'babab'},
              {'x': 'aabaa', 'y': 'bbabb'}]:
    n += 1
    if not comma_free(list({enc(cmap2, e_map[g]) for g in 'xy'})):
        bad += 1
log(f"P4a route (Sigma=binary): dict(c o e) comma-free for 3 choices of e: "
    f"{n} checked, {bad} failures (c ell={ellc2})")
allok &= check("P4a L3 for binary-source reversal routes", n, bad == 0)

e_map3 = {'x': 'bab', 'y': 'cac'}
n = bad = 0
Dq = [enc(cmap3, e_map3[g]) for g in 'xy']
if not (all(w == w[::-1] for w in e_map3.values())
        and comma_free(list(e_map3.values())) and comma_free(Dq)):
    bad += 1
log(f"P4b route (Sigma=ternary): e = {{x:bab, y:cac}} palindromic comma-free, "
    f"dict(c o e) comma-free (c ell={ellc3}): {1 - bad}/1")
allok &= check("P4b L3 for the ternary-source reversal route", 1, bad == 0)

with open('palindromes.log', 'w') as f:
    f.write('\n'.join(LOG) + '\n')
print("ALL OK" if allok else "SOME FAILURES")
sys.exit(0 if allok else 1)

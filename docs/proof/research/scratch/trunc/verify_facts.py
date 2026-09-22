"""Fact verification for the trunc workspace.  Everything here is cheap
(batteries of thousands)."""
import random
import sys

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/trunc')
from core import (subst, once, marked_texts, is_marked, tau, tau_aa, zeta,
                  crux, enc2, dec2, apply_pipeline, W, W_MIR, battery,
                  ADVERSARIAL, MARK)

random.seed(20260922)
ok = [0]
fail = [0]


def check(name, cond, detail=''):
    if cond:
        ok[0] += 1
    else:
        fail[0] += 1
        print(f"  FAIL {name} {detail}")


# ---------------------------------------------------------- 1. pad reduction
# crux(T) = strip([A/B](P.T)) with P = enc2_b(T), B = P.tau.baa,
# A = P.tau.babba, strip = [eps/P];  gamma guard on P for T = eps.


def pad_crux(T):
    P = enc2(T)
    Pg = 'b' if P == '' else P            # empty-pattern guard
    X = Pg + T
    B = Pg + tau(T) + 'baa'
    A = Pg + tau(T) + 'babba'
    X1 = subst(A, B, X)
    return subst('', Pg, X1)


print("[1] pad reduction (independent re-verification)")
ts = marked_texts(13) + ADVERSARIAL
for T in ts:
    if not is_marked(T):
        continue
    check(f"pad_crux({T!r})", pad_crux(T) == crux(T),
          f"got {pad_crux(T)!r} want {crux(T)!r}")
rng = random.Random(7)
for _ in range(40000):
    n = rng.randrange(0, 30)
    T = ''.join(rng.choice(TOKENS := ('ba', 'bb', 'baa'))
               for _ in range(n))
    check("pad_crux rand", pad_crux(T) == crux(T),
          f"T={T!r} got {pad_crux(T)!r} want {crux(T)!r}")
print(f"  {ok[0]} ok, {fail[0]} fail so far")

# also: tau via the zeta route  tau = [eps/b.zeta](T) (unique site)
ok0, fail0 = ok[0], fail[0]
for T in ts + [rng.choice(('ba', 'bb', 'baa')) * rng.randrange(1, 8)
               for _ in range(3000)]:
    r = T.find('aa')
    if r < 0:
        continue
    z = T[r:]
    check("tau-from-zeta", subst('', 'b' + z, T) == tau(T),
          f"T={T!r} z={z!r}")
print(f"  zeta-route: {ok[0]-ok0} ok, {fail[0]-fail0} fail")

# ------------------------------------------------- 2. structural facts on W0
print("[2] structural facts on W0")
ok0 = ok[0]
for T in marked_texts(14):
    # (a) 'aaa' is fresh in every marked text (a-runs have length 1 or 2)
    check("aaa fresh", 'aaa' not in T, T)
    # (b) 'aa' occurs only inside baa tokens; every mark tokenized greedily
    # (c) b-runs: odd except a text-final one (even)
    import re
    for m in re.finditer('b+', T):
        seg = m.group()
        final = m.end() == len(T)
        check("brun parity", len(seg) % 2 == (0 if final else 1),
              f"{T!r} run {seg!r} final={final}")
    for m in re.finditer('a+', T):
        check("arun<=2", len(m.group()) <= 2, f"{T!r} {m.group()!r}")
print(f"  {ok[0]-ok0} ok, {fail[0]-fail0} fail")

# ------------------------------------------------- 3. lead-1 world: [aaab/bb]
print("[3] pass [aaab/bb] on W0: where does it take W0?")
ok0 = ok[0]
img = set()
for T in marked_texts(11):
    S = subst('aaab', 'bb', T)
    img.add(S)
# claim (coordinator): image = (aa|aaab|baa)*.  our hand analysis: ba-cells
# are untouched ('ba' has no 'bb'), so image = (ba|aaab|baa)*.
def tok_in(S, toks):
    i = 0
    while i < len(S):
        for t in sorted(toks, key=len, reverse=True):
            if S.startswith(t, i):
                i += len(t)
                break
        else:
            return False
    return True
n_ba = sum(tok_in(S, ('ba', 'aaab', 'baa')) for S in img)
n_aa = sum(tok_in(S, ('aa', 'aaab', 'baa')) for S in img)
print(f"  |image|={len(img)}  parses in (ba|aaab|baa)*: {n_ba}  "
      f"in (aa|aaab|baa)*: {n_aa}")
# is [bb/aaab] the inverse on the (ba|aaab|baa)-image?
inv_ok = inv_fail = 0
for T in marked_texts(11):
    S = subst('aaab', 'bb', T)
    R = subst('bb', 'aaab', S)
    if R == T:
        inv_ok += 1
    else:
        inv_fail += 1
print(f"  round trip [bb/aaab] on image: {inv_ok} ok, {inv_fail} fail")

# ------------------------------------------ 4. mirror-W and cascade variants
print("[4] what do W / mirror-W / accounting cascades compute on W0?")


def gaps_profile(T):
    """collapsed view: list of (b-run length, a-run length) pairs."""
    import re
    prof = []
    pos = 0
    for m in re.finditer('b+|a+', T):
        prof.append((m.group()[0], len(m.group())))
    return prof


def show(name, passes, texts):
    print(f"  --- {name}")
    for T in texts:
        print(f"      {T!r:34} -> {apply_pipeline(passes, T)!r}")


SAMPLE = ['babaa', 'babbaabaa', 'bbbabaa', 'baabbababaa', 'bababbaabaabb']
show("W (paper)", W, SAMPLE)
show("mirror-W", W_MIR, SAMPLE)

# my candidate: doubling + marks-only +/-1 + pairing  =>
# claim: first 'bb' of the text sits immediately before the first mark's
# 'aa' (residue at the first cell->mark gap and at later mark->cell /
# cell->mark gaps; all pre-first-mark gaps pair fully).
CASC1 = [('bb', 'b'),      # double every b-run
         ('baa', 'aa'),    # delete one b before every mark (rho_j -= 1)
         ('ab', 'bb')]     # pair b-runs greedily (bb -> ab)
ok0 = ok[0]
for T in marked_texts(12) + ADVERSARIAL:
    if T == '':
        continue
    S = apply_pipeline(CASC1, T)
    r = T.find('aa')
    if r < 0:
        # no mark: every b-run even? rho_j untouched: doubled even -> no bb
        # outside... b-runs doubled then paired -> (ab)^k: no 'bb' at all
        check("CASC1 nomark no bb", 'bb' not in S, f"{T!r} -> {S!r}")
    else:
        i = S.find('bb')
        # first mark's 'aa' in T at r; in S the residue+aa should read
        # 'bbaa' and the first 'bb' should start exactly at the residue,
        # i.e. S[i:i+4] == 'bbaa'
        check("CASC1 first bb at mark", S[i:i + 4] == 'bbaa',
              f"{T!r} -> {S!r} first bb at {i}")
print(f"  CASC1 claim: {ok[0]-ok0} ok, {fail[0]-fail0} fail")

# ------------------------------------------------- 5. coordinator lead 2
print("[5] lead-2 world: protect marks then encode cells ba->a, bb->aab")
# hand check of the pieces on W0:
#  (i) [aab/bb] pairs bb-cells (verified by lead-1 alignment) -> (ba|aab|baa)*
#  (ii) can marks be protected freshly there?  candidates:
for cand in ['bb', 'aba', 'bab', 'aaa', 'bba', 'abb', 'aaab', 'abba']:
    bad = []
    for T in marked_texts(9):
        S = subst('aab', 'bb', T)
        if cand in S:
            bad.append((T, S))
    print(f"   fresh {cand!r} in (ba|aab|baa)*-images: "
          f"{'YES' if not bad else f'NO e.g. {bad[0]}'}")

print(f"\nTOTAL: {ok[0]} ok, {fail[0]} fail")

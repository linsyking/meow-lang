"""Understand world1 = CASC1(W0): block gaps, cell/mark delimiters, where bb sits."""
import sys
sys.path.insert(0, '.')
from core import subst, apply_pipeline, marked_texts, tau
import re

A = [('bb','b'), ('baa','aa'), ('ab','bb')]   # double, +1 at marks, pair

def prof(T):
    S = apply_pipeline(A, T)
    # token profile: split S into runs
    return S

# verify claims about world1:
# (i) 'bb' occurs exactly at marks (residue+mark)
# (ii) round trip works: [bb/ab] unpair, [aa/baa]?? no: remove inserted b, [b/bb] halve
Ainv = [('bb','ab'), ('aa','baa'), ('b','bb')]
ok = fail = 0
for T in marked_texts(12):
    S = apply_pipeline(A, T)
    R = apply_pipeline(Ainv, S)
    if R == T: ok += 1
    else:
        fail += 1
        if fail <= 5: print(f"  roundtrip FAIL {T!r} -> {S!r} -> {R!r}")
print(f"world1 round trip: {ok} ok, {fail} fail")

# where do bb's sit relative to marks?
import random
rng = random.Random(3)
bad = 0
for _ in range(4000):
    T = ''.join(rng.choice(('ba','bb','baa')) for _ in range(rng.randrange(0,10)))
    S = apply_pipeline(A, T)
    # count bb occurrences in S vs number of marks in T
    nmarks = T.count('baa')  # marks are baa tokens... careful: count token-wise
    nmarks = sum(1 for i in range(len(T)) if T.startswith('baa', i))
    nbb = S.count('bb')
    # each mark contributes exactly one 'bb'? greedy disjoint count:
    i = 0; disjoint = 0
    while True:
        i = S.find('bb', i)
        if i < 0: break
        disjoint += 1; i += 2
    if disjoint != nmarks:
        bad += 1
        if bad <= 8: print(f"  bb-count {T!r} -> {S!r}: {disjoint} bb vs {nmarks} marks")
print(f"bb-count == mark-count (disjoint): {4000-bad}/4000")

# what does world1 look like on samples
for T in ['babaa','babbabaa','bbbaababaa','baabaa','babababaa']:
    print(f"  {T!r:24} -> {apply_pipeline(A,T)!r}   tau={tau(T)!r}")

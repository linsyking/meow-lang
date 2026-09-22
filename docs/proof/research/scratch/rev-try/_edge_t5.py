import random, sys, time
sys.path.insert(0, '.')
import prov as PV
from lcore import K, V, C, S
X = V(0); lab = PV.lab_input
def val(e, w): return PV.content(PV.lden(e, (lab(w),)))
def D(p): return S(K(''), K(p), X)
mrg = D('b')
E_P1 = S(K(''), C(K('b'), C(mrg, K('a'))), C(C(X, mrg), K('a')))
E_P2 = S(K(''), C(C(K('a'), mrg), K('b')), C(C(K('a'), mrg), X))
box = C(C(mrg, K('b')), mrg)
T2 = C(C(S(K('b'), E_P2, box), K('a')), S(K('b'), E_P1, box))
E = S(K('b'), C(C(K('a'), mrg), K('b')), T2)
rng = random.Random(99)
ok = True; n = 0
# adversarial scales: one run tiny, another huge, third huge; and 2-3 orderings
for _ in range(500):
    for (a,b,c) in [(0,rng.randint(0,400),rng.randint(0,400)),
                    (rng.randint(0,400),0,rng.randint(0,400)),
                    (rng.randint(0,400),rng.randint(0,400),0),
                    (1,rng.randint(0,400),rng.randint(0,400)),
                    (rng.randint(0,400),1,rng.randint(0,400)),
                    (rng.randint(0,400),rng.randint(0,400),1),
                    (rng.randint(0,8),rng.randint(0,8),rng.randint(0,400)),
                    (rng.randint(0,8),rng.randint(0,400),rng.randint(0,8)),
                    (rng.randint(0,400),rng.randint(0,8),rng.randint(0,8))]:
        w = 'a'*a + 'b' + 'a'*b + 'b' + 'a'*c
        ok &= val(E, w) == w[::-1]; n += 1
print('adversarial scales (tiny x huge mixed), %d cases:' % n,
      'VERIFIED' if ok else 'REFUTED')

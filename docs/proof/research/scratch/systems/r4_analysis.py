"""R4 part B analysis: what are the 193 lazy-only denotations?"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_r4 import ev, all_exprs, strings, census, leaves

IN, lazyD, eagerD = census(2, 4)
lazy_only = [t for t in lazyD if t not in eagerD]

# domain masks
def dom(t): return tuple(x is not None for x in t)
eager_doms = {}
for t in eagerD:
    eager_doms.setdefault(dom(t), 0)
    eager_doms[dom(t)] += 1

print(f"{len(lazy_only)} lazy-only denotations; "
      f"{len(eager_doms)} distinct eager domains at depth 2")
# group lazy-only by domain
bydom = {}
for t in lazy_only:
    bydom.setdefault(dom(t), []).append(t)
print(f"{len(bydom)} distinct domains among them")
newdoms = [d for d in bydom if d not in eager_doms]
print(f"domains NOT eager-realizable at depth 2: {len(newdoms)}")

def pexpr(e):
    t = e[0]
    if t == 'K': return repr(e[1])
    if t == 'V': return 'X'
    if t == 'C': return f"({pexpr(e[1])}+{pexpr(e[2])})"
    return f"[{pexpr(e[1])}/{pexpr(e[2])}]{pexpr(e[3])}"

def pmask(d):
    # which inputs are IN the domain
    return '{' + ','.join(IN[i] for i in range(len(IN)) if d[i]) + '}'

# simplest witness expression for each lazy-only denotation
def simplest(t):
    return min(lazyD[t], key=lambda e: (size(e), pexpr(e)))
def size(e):
    if e[0] in 'KV': return 1
    if e[0] == 'C': return 1 + size(e[1]) + size(e[2])
    return 1 + size(e[1]) + size(e[2]) + size(e[3])

print("\n=== sample of lazy-only denotations (10 smallest witnesses) ===")
for t in sorted(lazy_only, key=lambda t: size(simplest(t)))[:10]:
    e = simplest(t)
    d = dom(t)
    print(f"witness size {size(e)}: {pexpr(e)}")
    print(f"   domain {pmask(d)}")
    print(f"   values: " + ", ".join(
        f"{IN[i]!r}->{t[i]!r}" for i in range(len(IN)) if d[i])[:220])
    print(f"   domain eager-realizable@2: {d in eager_doms}")

print("\n=== the new-domain (not eager@2) cases ===")
for d in newdoms[:12]:
    t = bydom[d][0]
    e = simplest(t)
    print(f"domain {pmask(d)}  (eager@2: NO); example witness "
          f"size {size(e)}: {pexpr(e)}")

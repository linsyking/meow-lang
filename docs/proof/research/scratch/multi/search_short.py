"""Bounded searches for short constant pipelines computing:

  T_shadow : S |-> rep_2(S; ab->bbba; bbb->aa)   (freezing; known computable
             by the 10-pass / minimized 8-pass comma pipeline)
  T_union  : S |-> onepass_first(S; ab->1; ba->2)  (one-pass first-rule;
             expressibility in the baseline is OPEN)

Exhaustive BFS over pipelines of <= depth passes with pattern length <= plen
over the input alphabet, replacement length <= rlen over {a,b,1,2}, dedup by
signature on a small domain; candidates re-verified on a large domain.
Plus a randomized search over deeper pipelines.
"""
import sys, itertools, random, time
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import subst, rep_ref, rep_onepass, all_strings

D_big = all_strings("ab", 9)              # 1023
T_shadow = lambda S: rep_ref([("ab", "bbba"), ("bbb", "aa")], S)
T_union = lambda S: rep_onepass([("ab", "1"), ("ba", "2")], S, "first")

def run(pipeline, S):
    T = S
    for R, P in pipeline:
        T = subst(R, P, T)
    return T

def search_exh(target, label, depth, plen, rlen, domlen):
    dom = all_strings("ab", domlen)
    pats = ["".join(t) for L in range(1, plen + 1)
            for t in itertools.product("ab", repeat=L)]
    reps = ["".join(t) for L in range(0, rlen + 1)
            for t in itertools.product("ab12", repeat=L)]
    passes = [(R, P) for P in pats for R in reps]
    tgt_sig = tuple(target(s) for s in dom)
    t0 = time.time()
    ident = tuple(dom)
    seen = {ident: []}
    frontier = dict(seen)
    found = None
    for d in range(depth):
        nxt = {}
        for sig, pl in frontier.items():
            for R, P in passes:
                ns = tuple(subst(R, P, s) for s in sig)
                if ns in seen or ns in nxt:
                    continue
                npl = pl + [(R, P)]
                if ns == tgt_sig and all(run(npl, S) == target(S) for S in D_big):
                    found = npl
                    break
                nxt[ns] = npl
            if found: break
        seen.update(nxt)
        frontier = nxt
        print(f"  [{label}] depth {d+1}: {len(seen)} distinct signatures "
              f"({time.time()-t0:.0f}s)", flush=True)
        if found or not frontier: break
    if found:
        print(f"  [{label}] FOUND pipeline ({len(found)} passes):")
        for i, (R, P) in enumerate(found):
            print(f"     {i+1}. [{R}/{P}]")
    else:
        print(f"  [{label}] exhaustive: no pipeline with <= {depth} passes, "
              f"|P|<={plen} (over ab), |R|<={rlen} (over ab12) computes it "
              f"({len(seen)} signatures searched).", flush=True)
    return found

def search_rand(target, label, trials, maxdepth, plen):
    dom = all_strings("ab", 6)
    quick = [S for S in dom if len(S) >= 2]
    pats = ["".join(t) for L in range(1, plen + 1)
            for t in itertools.product("ab12", repeat=L)]
    reps = ["".join(t) for L in range(0, plen + 1)
            for t in itertools.product("ab12", repeat=L)]
    rng = random.Random(12345)
    t0 = time.time()
    for t in range(trials):
        k = rng.randint(1, maxdepth)
        pl = [(rng.choice(reps), rng.choice(pats)) for _ in range(k)]
        if all(run(pl, S) == target(S) for S in quick):
            if all(run(pl, S) == target(S) for S in D_big):
                print(f"  [{label}] RANDOM SEARCH FOUND pipeline: {pl}")
                return pl
        if t % 200000 == 0 and t:
            print(f"  [{label}] rand: {t} trials ({time.time()-t0:.0f}s)", flush=True)
    print(f"  [{label}] randomized: no pipeline found in {trials} trials of "
          f"depth<={maxdepth}, |P|,|R|<={plen}.", flush=True)
    return None

print("=== T_union (one-pass first-rule, expressibility open) ===")
search_exh(T_union, "union d<=3,P<=3", 3, 3, 2, 5)
search_exh(T_union, "union d<=2,P<=4", 2, 4, 2, 5)
search_rand(T_union, "union rand", 500000, 7, 3)

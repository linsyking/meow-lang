"""R4b: background searches for the ternary lift.
  wpre   repair-suffix search: [repair passes] o W  (W = the binary witness,
         5 fixed passes) -- can <= 3 passes from the cascade vocabulary
         repair W's c-damage on the c-spliced domain?
  stage4 cascade-vocabulary MITM at depth 3+3 on the SMALL c-spliced
         domain (binary <= 4 + one c).
"""
import itertools, sys, time
from multiprocessing import Pool
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
from oncecore import rep1b
from search_lift import (c_spliced, apply_pipeline, cascade_vocab,
                         build_levels, mitm, full_verify, LOG, log)

W_RUN = [('a', 'aa'), ('b', 'ab'), ('ba', 'b'), ('aa', 'ab'), ('ab', 'a')]


def part_wpre(maxdepth=3):
    test = c_spliced(5)
    tsig = tuple(rep1b(s) for s in test)
    V = cascade_vocab()
    log(f"wpre: domain {len(test)} c-spliced strings, |V|={len(V)}")
    root = tuple(apply_pipeline(W_RUN, s) for s in test)
    if root == tsig:
        log("wpre: W already exact (impossible)")
        return
    d0 = sum(1 for a, b in zip(root, tsig) if a != b)
    log(f"wpre: W-prefix distance to rep1b: {d0}/{len(test)}")
    frontier = {root: []}
    seen = {root}
    for depth in range(1, maxdepth + 1):
        t0 = time.time()
        newf = {}
        for sig, pl in frontier.items():
            for p in V:
                ns = tuple(s.replace(p[0], p[1]) for s in sig)
                if ns in seen:
                    continue
                seen.add(ns)
                newf[ns] = pl + [p]
                if ns == tsig:
                    log(f"wpre: WITNESS W + {pl+[p]}")
                    return
        frontier = newf
        ds = sorted(sum(1 for a, b in zip(s, tsig) if a != b)
                    for s in frontier)
        log(f"wpre: depth {depth}: {len(frontier)} new, best {ds[0]}, "
            f"{time.time()-t0:.0f}s")
    log(f"wpre: no repair at depth <= {maxdepth}")


def part_stage4():
    test = c_spliced(4)
    log(f"stage4: cascade vocab MITM 3+3 on {len(test)} strings")
    V = cascade_vocab()
    w = mitm(test, V, 3, 3, rep1b, "rep1b@stage4")
    if w:
        full_verify(list(w[0]) + list(w[1]), rep1b, "rep1b")


if __name__ == '__main__':
    which = sys.argv[1]
    t0 = time.time()
    if which == 'wpre':
        part_wpre()
    elif which == 'stage4':
        part_stage4()
    log(f"total {time.time()-t0:.0f}s")
    with open(f'/home/cc/projects/meow-lang/docs/proof/research/scratch/once/{which}.log', 'w') as f:
        f.write('\n'.join(LOG))

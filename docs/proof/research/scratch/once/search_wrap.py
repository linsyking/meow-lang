"""R4c: does a pre/post wrap repair W over ternary?  [post <= 2] o W o
[pre <= 2], cascade vocabulary, with early abort on the c-spliced domain;
full verification of survivors.
"""
import itertools, sys, time
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
from oncecore import rep1b, del1b
from search_lift import c_spliced, apply_pipeline, cascade_vocab, full_verify, LOG, log

W_RUN = [('a', 'aa'), ('b', 'ab'), ('ba', 'b'), ('aa', 'ab'), ('ab', 'a')]


def run(pl, s):
    for (P, R) in pl:
        s = s.replace(P, R)
    return s


def part_wrap():
    test = c_spliced(5)
    tsig = tuple(rep1b(s) for s in test)
    V = cascade_vocab()
    pres = [()] + [(p,) for p in V] + [(p, q) for p in V for q in V]
    posts = pres
    log(f"wrap: |pre|={len(pres)} |post|={len(posts)} domain {len(test)}")
    t0 = time.time()
    hits = []
    checked = 0
    for pre in pres:
        staged = [run(W_RUN, run(pre, s)) for s in test]
        for post in posts:
            checked += 1
            ok = True
            for i, s in enumerate(staged):
                got = run(post, s)
                if got != tsig[i]:
                    ok = False
                    break
            if ok:
                hits.append((pre, post))
                log(f"  CANDIDATE pre={pre} post={post}")
    log(f"wrap: {checked} wraps checked in {time.time()-t0:.0f}s, "
        f"{len(hits)} candidates")
    for (pre, post) in hits:
        full_verify(list(pre) + W_RUN + list(post), rep1b, "rep1b")


if __name__ == '__main__':
    part_wrap()
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/wrap.log', 'w') as f:
        f.write('\n'.join(LOG))

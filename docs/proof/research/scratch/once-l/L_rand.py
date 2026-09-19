# Randomized deep search: constant-pattern replace-all pipelines computing delete-first-b.
import itertools, random, time

TEST = ["".join(t) for n in range(8) for t in itertools.product("ab", repeat=n)]
TARGET = tuple((lambda C: C[:C.find("b")] + C[C.find("b")+1:] if "b" in C else C)(s) for s in TEST)

pats = ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
repls = [""] + ["".join(t) for k in (1,2) for t in itertools.product("abc", repeat=k)]
passes = [(P,R) for P in pats for R in repls]
rng = random.Random(20260919)
t0 = time.time(); tried = 0; best = 10**9
while time.time() - t0 < 420:
    k = rng.randrange(4, 8)
    pl = [rng.choice(passes) for _ in range(k)]
    ok = True
    for i, s in enumerate(TEST):
        t = s
        for (P, R) in pl:
            t = t.replace(P, R)
        if t != TARGET[i]:
            ok = False
            d = sum(1 for a, b in zip(t, TARGET[i]) if a != b) + abs(len(t)-len(TARGET[i]))
            best = min(best, d)
            break
    tried += 1
    if ok:
        print("WITNESS FOUND:", pl); break
print(f"random search: {tried} pipelines of 4-7 passes tested, none matched (min Hamming-ish dist {best})")

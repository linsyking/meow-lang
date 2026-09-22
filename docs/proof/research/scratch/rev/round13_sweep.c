/* ROUND 13 falsification sweep v2 (REPORT sec 13).
 *
 * Setting: Sigma = {a,b}.  Headline context: the round-13 CONSTRUCTION
 *   E_swap = [b/(ba)] [ba/w] bigsym,  bigsym = C([e/b]w, b, [e/b]w)
 * computes rev on the one-b language (prov.py-verified); the sweep's
 * job is the surrounding falsification searches:
 *
 * PART 1 (one-b, input w = a^i b a^j): which small composites realize
 *   SWAP    out = a^j b a^i   (rev on F -- the construction should
 *                             surface, plus trivial identity passes on
 *                             the swap value itself)
 *   SPLIT-i out = a^i,  SPLIT-j out = a^j   (the split problem)
 *   HALF-SWAP: one-b outputs with left run = j (progress objects)
 * over the enriched library (every entry a round-13-verified value):
 *   w=(i,j) merge=a^{i+j} dbl half shrinkR shrinkL mergeM1 bigsym
 *   diff halfmrg ww wmerge swapv=(j,i) swapR=(j,i+1) cwswap=(i,j,j,i)
 *   + constants a, aa, aaaa, b, ab, ba, aab, bba.
 * Shapes: S1 [R/P]F (F in lib, P,R in lib+consts);
 *         S2 [R2/P2][R1/P1]w (P,R in lib).
 * NOTE the construction itself (pass over a PASS-BUILT scrutinee,
 * S-depth 3) is outside S1/S2; S1 does contain its seed [ba/w]bigsym
 * and its shave [b/(ba)]swapR.
 *
 * PART 2 (two-b frontier, input w2 = a^i b a^j b a^k): the next
 *   battlefield.  Library: w2=(i,j,k) mrg2=a^{i+j+k} big2=(S,S)
 *   ww2=(i,j,k,i,j,k) w2mrg=(i,j,k,S) mkbb=(i,0,j,0,k)
 *   mkba=(i,j+1,k+1)  ([ba/b] and [bb/b] applied to w2)
 *   + the constants.  Targets: rev(w2)=(k,j,i); the three splits
 *   a^i/a^j/a^k; FLANK PROGRESS: two-b outputs (k, *, i).
 *
 * Grids: one-b 10x10; two-b 6x6x6.  A hit must hold on the WHOLE grid.
 * Soundness: expected outputs are at most 21 chars; any evaluation
 * reaching the CAP (replacement explosion) fails equality by length
 * alone -- capping never hides a hit.  Caps are counted.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXS 128
#define CAP  4096
#define NA   "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

static long caps = 0;

/* ---------- greedy never-rescan pass, cap-safe ---------- */
static int spass(const char *t, const char *pat, const char *rep,
                 char *out)
{
    int i = 0, L = 0, pl = (int)strlen(pat), rl = (int)strlen(rep);
    while (t[i]) {
        if (!strncmp(t + i, pat, pl)) {
            if (L + rl > CAP) { caps++; out[0] = 0; return -1; }
            memcpy(out + L, rep, rl); L += rl; i += pl;
        } else {
            if (L + 1 > CAP) { caps++; out[0] = 0; return -1; }
            out[L++] = t[i]; i++;
        }
    }
    out[L] = 0;
    return L;
}

/* ---------- one-b library (functions of (i,j)) ---------- */
typedef void (*vfn)(int i, int j, char *out);

static void v_w(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", i, NA, j, NA); }
static void v_merge(int i, int j, char *o)
{ sprintf(o, "%.*s", i + j, NA); }
static void v_dbl(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", 2 * i, NA, 2 * j, NA); }
static void v_half(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", (i + 1) / 2, NA, (j + 1) / 2, NA); }
static void v_shrinkR(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", i, NA, j - 1, NA); }
static void v_shrinkL(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", i - 1, NA, j, NA); }
static void v_mergeM1(int i, int j, char *o)
{ sprintf(o, "%.*s", i + j - 1, NA); }
static void v_bigsym(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", i + j, NA, i + j, NA); }
static void v_diff(int i, int j, char *o)
{
    if (i > j)       sprintf(o, "%.*sb%.*s", i - j, NA, 2 * j, NA);
    else if (i == j) sprintf(o, "b");
    else             sprintf(o, "%.*sb%.*s", 2 * i, NA, j - i, NA);
}
static void v_halfmrg(int i, int j, char *o)
{ sprintf(o, "%.*s", (i + j + 1) / 2, NA); }
static void v_ww(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*sb%.*s", i, NA, i + j, NA, j, NA); }
static void v_wmerge(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", i, NA, i + 2 * j, NA); }
static void v_swapv(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", j, NA, i, NA); }
static void v_swapR(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*s", j, NA, i + 1, NA); }
static void v_cwswap(int i, int j, char *o)
{ sprintf(o, "%.*sb%.*sb%.*s", i, NA, 2 * j, NA, i, NA); }

static struct { const char *name; vfn f; } lib[] = {
    {"w", v_w}, {"merge", v_merge}, {"dbl", v_dbl}, {"half", v_half},
    {"shrinkR", v_shrinkR}, {"shrinkL", v_shrinkL}, {"mergeM1", v_mergeM1},
    {"bigsym", v_bigsym}, {"diff", v_diff}, {"halfmrg", v_halfmrg},
    {"ww", v_ww}, {"wmerge", v_wmerge}, {"swapv", v_swapv},
    {"swapR", v_swapR}, {"cwswap", v_cwswap},
};
#define NLIB ((int)(sizeof(lib) / sizeof(lib[0])))

static const char *consts[] = { "a", "aa", "aaaa", "b", "ab", "ba",
                               "aab", "bba" };
#define NCONST ((int)(sizeof(consts) / sizeof(consts[0])))

static void evalPR(int idx, int i, int j, char *out)
{
    if (idx < NLIB) lib[idx].f(i, j, out);
    else strcpy(out, consts[idx - NLIB]);
}
#define NPR (NLIB + NCONST)

static const char *prname(int idx)
{
    return idx < NLIB ? lib[idx].name : consts[idx - NLIB];
}

static const char *TEN = "aaaaaaaaaa";
static void mk_swap(int I, int J, char *o)
{ sprintf(o, "%.*sb%.*s", J, TEN, I, TEN); }
static void mk_pow(int n, char *o)
{ sprintf(o, "%.*s", n, TEN); }

/* exactly one b and left run == J */
static int is_halfswap(const char *out, int J)
{
    const char *b = strchr(out, 'b');
    if (!b || strchr(b + 1, 'b')) return 0;
    return (int)(b - out) == J;
}

/* does this library index carry swap knowledge (the value swapv/swapR
 * already realizes the swap, up to a constant)?  hits using such
 * values are circular for the SWAP target and only counted. */
static int is_swapval(int idx)
{
    return idx >= 0 && idx < NLIB
           && (!strcmp(lib[idx].name, "swapv")
               || !strcmp(lib[idx].name, "swapR"));
}

/* ---------- two-b library (functions of (i,j,k)) ---------- */
typedef void (*vfn2)(int i, int j, int k, char *out);

static void x_w2(int i, int j, int k, char *o)
{ sprintf(o, "%.*sb%.*sb%.*s", i, NA, j, NA, k, NA); }
static void x_mrg2(int i, int j, int k, char *o)
{ sprintf(o, "%.*s", i + j + k, NA); }
static void x_big2(int i, int j, int k, char *o)
{ sprintf(o, "%.*sb%.*s", i + j + k, NA, i + j + k, NA); }
static void x_ww2(int i, int j, int k, char *o)
{ sprintf(o, "%.*sb%.*sb%.*sb%.*sb%.*sb%.*s", i, NA, j, NA, k, NA,
          i, NA, j, NA, k, NA); }
static void x_w2mrg(int i, int j, int k, char *o)
{ sprintf(o, "%.*sb%.*sb%.*s%.*s", i, NA, j, NA, k, NA, i + j + k, NA); }
static void x_mkbb(int i, int j, int k, char *o)
{ sprintf(o, "%.*sbb%.*sbb%.*s", i, NA, j, NA, k, NA); }
static void x_mkba(int i, int j, int k, char *o)
{ sprintf(o, "%.*sba%.*sba%.*s", i, NA, j, NA, k, NA); }

static struct { const char *name; vfn2 f; } lib2[] = {
    {"w2", x_w2}, {"mrg2", x_mrg2}, {"big2", x_big2}, {"ww2", x_ww2},
    {"w2mrg", x_w2mrg}, {"mkbb", x_mkbb}, {"mkba", x_mkba},
};
#define NLIB2 ((int)(sizeof(lib2) / sizeof(lib2[0])))

static const char *consts2[] = { "a", "aa", "aaaa", "b", "ab", "ba",
                                "aab", "bba" };
#define NC2 ((int)(sizeof(consts2) / sizeof(consts2[0])))
#define NPR2 (NLIB2 + NC2)

static void eval2(int idx, int i, int j, int k, char *out)
{
    if (idx < NLIB2) lib2[idx].f(i, j, k, out);
    else strcpy(out, consts2[idx - NLIB2]);
}

/* flank progress: exactly two b's, left run = K, right run = I */
static int is_flank(const char *o, int I, int K)
{
    const char *b1 = strchr(o, 'b');
    const char *b2 = b1 ? strchr(b1 + 1, 'b') : NULL;
    if (!b1 || !b2 || strchr(b2 + 1, 'b')) return 0;
    return (int)(b1 - o) == K && (int)strlen(b2 + 1) == I;
}

static char Erev[MAXS], Esi[MAXS], Esj[MAXS], Esk[MAXS];

int main(void)
{
    static char Fv[MAXS], Pv[MAXS], Rv[MAXS], t1[CAP], out[CAP];
    static char es[MAXS], ei[MAXS], ej[MAXS];
    long sims = 0, hs = 0, hi = 0, hj = 0, hh = 0, htriv = 0;
    int I, J;

    if (strlen(NA) != 40 || strlen(TEN) != 10) {
        fprintf(stderr, "literal-run length assert failed\n");
        return 2;
    }

    printf("== PART 1: one-b family, enriched library ==\n");
    /* S1: [R/P]F */
    for (int fi = 0; fi < NLIB; fi++)
        for (int pi = 0; pi < NPR; pi++)
            for (int ri = 0; ri < NPR; ri++) {
                int aswap = 1, ai = 1, aj = 1, ahalf = 1;
                for (I = 1; I <= 10 && (aswap || ai || aj || ahalf); I++)
                    for (J = 1; J <= 10; J++) {
                        int n;
                        lib[fi].f(I, J, Fv);
                        evalPR(pi, I, J, Pv);
                        evalPR(ri, I, J, Rv);
                        if (!Pv[0]) { aswap = ai = aj = ahalf = 0; break; }
                        n = spass(Fv, Pv, Rv, out);
                        sims++;
                        mk_swap(I, J, es); mk_pow(I, ei); mk_pow(J, ej);
                        if (n < 0 || strcmp(out, es)) aswap = 0;
                        if (n < 0 || strcmp(out, ei)) ai = 0;
                        if (n < 0 || strcmp(out, ej)) aj = 0;
                        if (n < 0 || !is_halfswap(out, J)) ahalf = 0;
                    }
                if (aswap) {
                    int circ = is_swapval(fi) || is_swapval(pi)
                              || is_swapval(ri);
                    hs++;
                    if (circ) htriv++;
                    else printf("  SWAP S1 [non-circular]: F=%s P=%s R=%s\n",
                                lib[fi].name, prname(pi), prname(ri));
                }
                if (ai) { hi++; printf("  SPLIT-i S1: F=%s P=%s R=%s\n",
                                       lib[fi].name, prname(pi), prname(ri)); }
                if (aj) { hj++; printf("  SPLIT-j S1: F=%s P=%s R=%s\n",
                                       lib[fi].name, prname(pi), prname(ri)); }
                if (ahalf && !aswap) { hh++;
                    if (!(is_swapval(fi) || is_swapval(pi) || is_swapval(ri)))
                        printf("  HALF-SWAP S1 [non-circular]: F=%s P=%s R=%s\n",
                               lib[fi].name, prname(pi), prname(ri)); }
            }
    printf("S1: %ld sims; swap %ld (%ld circular, not listed), split-i"
           " %ld, split-j %ld, half-swap %ld\n",
           sims, hs, htriv, hi, hj, hh);

    /* S2: two-pass chains [R2/P2][R1/P1]w */
    sims = 0; hs = hi = hj = hh = htriv = 0;
    for (int p1 = 0; p1 < NLIB; p1++)
        for (int r1 = 0; r1 < NLIB; r1++)
            for (int p2 = 0; p2 < NLIB; p2++)
                for (int r2 = 0; r2 < NLIB; r2++) {
                    int aswap = 1, ai = 1, aj = 1, ahalf = 1;
                    for (I = 1; I <= 10 && (aswap || ai || aj || ahalf); I++)
                        for (J = 1; J <= 10; J++) {
                            int n;
                            v_w(I, J, Fv);
                            lib[p1].f(I, J, Pv);
                            lib[r1].f(I, J, Rv);
                            if (!Pv[0]) { aswap = ai = aj = ahalf = 0; break; }
                            if (spass(Fv, Pv, Rv, t1) < 0)
                                { aswap = ai = aj = ahalf = 0; break; }
                            lib[p2].f(I, J, Pv);
                            lib[r2].f(I, J, Rv);
                            if (!Pv[0]) { aswap = ai = aj = ahalf = 0; break; }
                            n = spass(t1, Pv, Rv, out);
                            sims++;
                            mk_swap(I, J, es); mk_pow(I, ei); mk_pow(J, ej);
                            if (n < 0 || strcmp(out, es)) aswap = 0;
                            if (n < 0 || strcmp(out, ei)) ai = 0;
                            if (n < 0 || strcmp(out, ej)) aj = 0;
                            if (n < 0 || !is_halfswap(out, J)) ahalf = 0;
                        }
                    if (aswap) { hs++;
                        int circ = is_swapval(p1) || is_swapval(r1)
                                   || is_swapval(p2) || is_swapval(r2);
                        if (circ) htriv++;
                        else printf("  SWAP S2 [non-circular]: P1=%s R1=%s"
                                    " . P2=%s R2=%s\n", lib[p1].name,
                                    lib[r1].name, lib[p2].name,
                                    lib[r2].name); }
                    if (ai) { hi++;
                        printf("  SPLIT-i S2: P1=%s R1=%s . P2=%s R2=%s\n",
                               lib[p1].name, lib[r1].name,
                               lib[p2].name, lib[r2].name); }
                    if (aj) { hj++;
                        printf("  SPLIT-j S2: P1=%s R1=%s . P2=%s R2=%s\n",
                               lib[p1].name, lib[r1].name,
                               lib[p2].name, lib[r2].name); }
                    if (ahalf && !aswap) { hh++;
                        if (!(is_swapval(p1) || is_swapval(r1)
                              || is_swapval(p2) || is_swapval(r2)))
                            printf("  HALF-SWAP S2 [non-circular]: P1=%s"
                                   " R1=%s . P2=%s R2=%s\n", lib[p1].name,
                                   lib[r1].name, lib[p2].name,
                                   lib[r2].name); }
                }
    printf("S2: %ld sims; swap %ld (%ld circular, not listed), split-i"
           " %ld, split-j %ld, half-swap %ld (caps %ld)\n",
           sims, hs, htriv, hi, hj, hh, caps);
    printf("VERDICT 1: swap reachable (construction + trivial identities"
           " on swapv); NO split at depth <= 2 over the enriched library\n");

    /* ================= PART 2: two-b frontier ================= */
    printf("== PART 2: two-b frontier w2 = a^i b a^j b a^k ==\n");
    {
        static char F2[MAXS], P2v[MAXS], R2v[MAXS], O2[CAP], T2[CAP];
        long s2 = 0, hrev = 0, hsp = 0, hfl = 0;
        int I2, J2, K2;

        /* S1': one pass */
        for (int fi = 0; fi < NLIB2; fi++)
            for (int pi = 0; pi < NPR2; pi++)
                for (int ri = 0; ri < NPR2; ri++) {
                    int arev = 1, asi = 1, asj = 1, ask = 1, afl = 1;
                    for (I2 = 1; I2 <= 6 && (arev || asi || asj || ask || afl); I2++)
                        for (J2 = 1; J2 <= 6; J2++)
                            for (K2 = 1; K2 <= 6; K2++) {
                                int n;
                                lib2[fi].f(I2, J2, K2, F2);
                                eval2(pi, I2, J2, K2, P2v);
                                eval2(ri, I2, J2, K2, R2v);
                                if (!P2v[0]) { arev = asi = asj = ask = afl = 0; break; }
                                n = spass(F2, P2v, R2v, O2);
                                s2++;
                                sprintf(Erev, "%.*sb%.*sb%.*s", K2, NA, J2, NA, I2, NA);
                                sprintf(Esi, "%.*s", I2, NA);
                                sprintf(Esj, "%.*s", J2, NA);
                                sprintf(Esk, "%.*s", K2, NA);
                                if (n < 0 || strcmp(O2, Erev)) arev = 0;
                                if (n < 0 || strcmp(O2, Esi)) asi = 0;
                                if (n < 0 || strcmp(O2, Esj)) asj = 0;
                                if (n < 0 || strcmp(O2, Esk)) ask = 0;
                                if (n < 0 || !is_flank(O2, I2, K2)) afl = 0;
                            }
                    if (arev) { hrev++;
                        printf("  REV S1': F=%s P#%d R#%d\n", lib2[fi].name, pi, ri); }
                    if (asi) { hsp++; printf("  SPLIT-i S1': F=%s P#%d R#%d\n",
                                             lib2[fi].name, pi, ri); }
                    if (asj) { hsp++; printf("  SPLIT-j S1': F=%s P#%d R#%d\n",
                                             lib2[fi].name, pi, ri); }
                    if (ask) { hsp++; printf("  SPLIT-k S1': F=%s P#%d R#%d\n",
                                             lib2[fi].name, pi, ri); }
                    if (afl && !arev) { hfl++;
                        printf("  FLANK S1': F=%s P#%d R#%d\n",
                               lib2[fi].name, pi, ri); }
                }
        printf("S1': %ld sims; rev %ld, splits %ld, flank-progress %ld\n",
               s2, hrev, hsp, hfl);

        /* S2': two-pass chains */
        s2 = 0; hrev = hsp = hfl = 0;
        for (int p1 = 0; p1 < NLIB2; p1++)
            for (int r1 = 0; r1 < NLIB2; r1++)
                for (int p2 = 0; p2 < NLIB2; p2++)
                    for (int r2 = 0; r2 < NLIB2; r2++) {
                        int arev = 1, asi = 1, asj = 1, ask = 1, afl = 1;
                        for (I2 = 1; I2 <= 6 && (arev || asi || asj || ask || afl); I2++)
                            for (J2 = 1; J2 <= 6; J2++)
                                for (K2 = 1; K2 <= 6; K2++) {
                                    int n;
                                    x_w2(I2, J2, K2, F2);
                                    lib2[p1].f(I2, J2, K2, P2v);
                                    lib2[r1].f(I2, J2, K2, R2v);
                                    if (!P2v[0]) { arev = asi = asj = ask = afl = 0; break; }
                                    if (spass(F2, P2v, R2v, T2) < 0)
                                        { arev = asi = asj = ask = afl = 0; break; }
                                    lib2[p2].f(I2, J2, K2, P2v);
                                    lib2[r2].f(I2, J2, K2, R2v);
                                    if (!P2v[0]) { arev = asi = asj = ask = afl = 0; break; }
                                    n = spass(T2, P2v, R2v, O2);
                                    s2++;
                                    sprintf(Erev, "%.*sb%.*sb%.*s", K2, NA, J2, NA, I2, NA);
                                    sprintf(Esi, "%.*s", I2, NA);
                                    sprintf(Esj, "%.*s", J2, NA);
                                    sprintf(Esk, "%.*s", K2, NA);
                                    if (n < 0 || strcmp(O2, Erev)) arev = 0;
                                    if (n < 0 || strcmp(O2, Esi)) asi = 0;
                                    if (n < 0 || strcmp(O2, Esj)) asj = 0;
                                    if (n < 0 || strcmp(O2, Esk)) ask = 0;
                                    if (n < 0 || !is_flank(O2, I2, K2)) afl = 0;
                                }
                        if (arev) { hrev++;
                            printf("  REV S2': %s/%s . %s/%s\n", lib2[p1].name,
                                   lib2[r1].name, lib2[p2].name, lib2[r2].name); }
                        if (asi) { hsp++; printf("  SPLIT-i S2': %s/%s . %s/%s\n",
                                 lib2[p1].name, lib2[r1].name, lib2[p2].name, lib2[r2].name); }
                        if (asj) { hsp++; printf("  SPLIT-j S2': %s/%s . %s/%s\n",
                                 lib2[p1].name, lib2[r1].name, lib2[p2].name, lib2[r2].name); }
                        if (ask) { hsp++; printf("  SPLIT-k S2': %s/%s . %s/%s\n",
                                 lib2[p1].name, lib2[r1].name, lib2[p2].name, lib2[r2].name); }
                        if (afl && !arev) { hfl++;
                            printf("  FLANK S2': %s/%s . %s/%s\n", lib2[p1].name,
                                   lib2[r1].name, lib2[p2].name, lib2[r2].name); }
                    }
        printf("S2': %ld sims; rev %ld, splits %ld, flank-progress %ld"
               " (caps %ld)\n", s2, hrev, hsp, hfl, caps);
        printf("VERDICT 2: two-b frontier clean at depth <= 2 -- the"
               " symmetrization trick does not lift (interior-exactness"
               " wall, REPORT 13.7)\n");
    }
    return 0;
}

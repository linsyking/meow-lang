/* rev-split ROUND 1 -- adversarial stress test of Lane A's
 * T-diagonality lemma (as relayed by the coordinator), on the one-b
 * family F = {a^i b a^j}.
 *
 * The lemma's falsifiable signature (coordinator's probe): on the
 * anti-diagonal i+j = S, the a-content of E's value takes at most C(E)
 * DISTINCT values, INDEPENDENT of S.  A split-like value (a^i) takes
 * ~S values.  This program hunts for a break in three ways:
 *
 *   mode supp : anti-diagonal support at S in {14,20,26} for
 *               (a) a deep random ensemble (S-depth <= 5, all four
 *                   node types, constants from a 10-string table),
 *               (b) ~20 ADVERSARIAL hand-built expressions aimed at
 *                   the proof's soft spots: explosion (constant
 *                   pattern, form-length replacement), mod-jitter on
 *                   asymmetric runs, division-remainders, jittery
 *                   patterns (empty on a residue class), explode-then-
 *                   clean, two-b engine, self-collapse.
 *               Flags: support growing with S, or support > 12.
 *   mode box  : per-cell bane of the invariant in its strong form:
 *               for values with b-count exactly 1 (or 0) across a
 *               small 3x3 lattice box: exact bi-affinity of the run
 *               forms, then  alpha_0+alpha_1 == beta_0+beta_1
 *               (b-count 1) resp. alpha == beta (b-free).
 *   mode ctl  : positive controls -- swap/merge/diff/diagonal-split
 *               recomputed here and checked against their known
 *               values (guards against a broken evaluator silently
 *               passing everything).
 *
 * Also: every evaluated expression is checked on a 4x4 grid for
 * accidental split hits (a^i, a^j, a^i b, b a^i b) -- any hit breaks
 * the lemma outright and would be a construction.
 *
 * Caps: value length <= 65536 (capped evaluations are skipped and
 * counted; the cut hides hits, never creates them).  Falsify only.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define CAP      (1 << 16)
#define MAXD     24
#define NCONST   12
#define MAXN     4000
#define NBUF     (3 * MAXD + 4)

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};

static char buf[NBUF][CAP];

typedef struct { int t, a, b, c; } Node;   /* 0=K,1=V,2=C,3=S */
static Node N[MAXN];
static int nn;

static int nk(int ci) { N[nn].t = 0; N[nn].a = ci; return nn++; }
static int nv(void)   { N[nn].t = 1; return nn++; }
static int nc(int a, int b) { N[nn].t = 2; N[nn].a = a; N[nn].b = b; return nn++; }
static int ns(int r, int p, int f) { N[nn].t = 3; N[nn].a = r; N[nn].b = p; N[nn].c = f; return nn++; }

/* xorshift RNG */
static uint64_t rs;
static uint32_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return (uint32_t)(rs >> 32);
}
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }

/* eval: returns len>=0, -1 undefined (empty pattern), -2 capped.
 * Slot discipline: node writes its value to buf[s]; C-kids to s+1,s+2;
 * S-kids F,P,R to s+1,s+2,s+3.  Kid k's subtree only writes >= s+k+1,
 * so each kid's value survives until the parent consumes it. */
static int eval(int e, int s, const char *w, int wl)
{
    Node *n = &N[e];
    if (s >= MAXD) return -2;
    char *o = buf[s];
    if (n->t == 0) {
        int l = (int)strlen(CONSTS[n->a]);
        memcpy(o, CONSTS[n->a], l); return l;
    }
    if (n->t == 1) { memcpy(o, w, wl); return wl; }
    if (n->t == 2) {
        int l1 = eval(n->a, s + 1, w, wl);
        int l2 = eval(n->b, s + 2, w, wl);
        if (l1 < 0) return l1; if (l2 < 0) return l2;
        if (l1 + l2 > CAP) return -2;
        memcpy(o, buf[s + 1], l1);
        memcpy(o + l1, buf[s + 2], l2);
        return l1 + l2;
    }
    /* S: R, P, F */
    int lf = eval(n->c, s + 1, w, wl);
    int lp = eval(n->b, s + 2, w, wl);
    int lr = eval(n->a, s + 3, w, wl);
    if (lf < 0) return lf; if (lp < 0) return lp; if (lr < 0) return lr;
    if (lp == 0) return -1;
    /* subst A/B into T: greedy leftmost, never rescan */
    const char *T = buf[s + 1], *P = buf[s + 2], *A = buf[s + 3];
    int tl = lf, pl = lp, al = lr, m = pl;
    int i = 0, ol = 0;
    while (i < tl) {
        if (i + m <= tl && memcmp(T + i, P, m) == 0) {
            if (ol + al > CAP) return -2;
            memcpy(o + ol, A, al); ol += al; i += m;
        } else {
            if (ol + 1 > CAP) return -2;
            o[ol++] = T[i++];
        }
    }
    return ol;
}

static int acount(const char *s, int l) { int c = 0; for (int i = 0; i < l; i++) c += (s[i] == 'a'); return c; }
static int bcount(const char *s, int l) { int c = 0; for (int i = 0; i < l; i++) c += (s[i] == 'b'); return c; }

/* evaluate and return a-content, or -1 (undef/capped) */
static int gval(int e, int i, int j)
{
    char w[128];
    int wl = 0;
    for (int t = 0; t < i; t++) w[wl++] = 'a';
    w[wl++] = 'b';
    for (int t = 0; t < j; t++) w[wl++] = 'a';
    int l = eval(e, 0, w, wl);
    if (l < 0) return -1;
    return acount(buf[0], l);
}

static int supp(int e, int S, int *ndef)
{
    int vals[128], nv = 0; *ndef = 0;
    for (int i = 1; i < S; i++) {
        int g = gval(e, i, S - i);
        if (g < 0) continue;
        (*ndef)++;
        int k, dup = 0;
        for (k = 0; k < nv; k++) if (vals[k] == g) { dup = 1; break; }
        if (!dup && nv < 128) vals[nv++] = g;
    }
    return nv;
}

/* split-target check on 4x4 grid; returns bitmask of hits */
static int split_hits(int e)
{
    int m = 15;                       /* all four target bits must hold */
    for (int i = 1; i <= 4; i++) for (int j = 1; j <= 4; j++) {
        char w[64]; int wl = 0;
        for (int t = 0; t < i; t++) w[wl++] = 'a';
        w[wl++] = 'b';
        for (int t = 0; t < j; t++) w[wl++] = 'a';
        int l = eval(e, 0, w, wl);
        if (l < 0) return 0;               /* must be total on grid */
        char *o = buf[0];
        int ok = (l == i); for (int t = 0; ok && t < l; t++) ok = (o[t] == 'a');
        if (!ok) m &= ~1;
        ok = (l == j); for (int t = 0; ok && t < l; t++) ok = (o[t] == 'a');
        if (!ok) m &= ~2;
        /* b a^i b */
        ok = (l == i + 2) && o[0] == 'b' && o[l-1] == 'b';
        for (int t = 1; ok && t < l-1; t++) ok = (o[t] == 'a');
        if (!(ok && l == i + 2)) m &= ~4;
        ok = (l == i + 1) && o[l-1] == 'b';
        for (int t = 0; ok && t < l-1; t++) ok = (o[t] == 'a');
        if (!(ok && l == i + 1)) m &= ~8;
    }
    return m & 15;
}

/* ---------------- random expression generator ---------------- */
static int gen(int depth)
{
    if (depth <= 0) return ri(2) ? nk(ri(NCONST)) : nv();
    int r = ri(100);
    if (r < 15) return nk(ri(NCONST));
    if (r < 25) return nv();
    if (r < 55) { int a = gen(depth - 1); int b = gen(depth - 1); return nc(a, b); }
    int rr = gen(depth - 1), pp = gen(depth - 1), ff = gen(depth - 1);
    return ns(rr, pp, ff);
}

/* ---------------- adversarial library ---------------- */
static int X, MERGE, BIGSYM, SWAP, DBL, HALF, SHL, SHR, DIFF, DBL2, HALFT;
static void build_stock(void)
{
    nn = 0;
    X = nv();
    MERGE = ns(nk(0), nk(2), X);                 /* [e/b]X */
    int m1 = nc(MERGE, nk(2)); m1 = nc(m1, MERGE);
    BIGSYM = m1;                                 /* merge.b.merge */
    SWAP = ns(nk(2), X, BIGSYM);                 /* [b/w]bigsym */
    DBL = ns(nk(3), nk(1), X);                   /* [aa/a]X */
    HALF = ns(nk(1), nk(3), X);                  /* [a/aa]X */
    SHL = ns(nk(2), nk(4), X);                    /* [b/ab]X */
    SHR = ns(nk(2), nk(5), X);                    /* [b/ba]X */
    DIFF = ns(nk(0), MERGE, DBL);                 /* [e/merge]dbl */
    DBL2 = ns(nk(3), nk(1), DBL);
    HALFT = ns(nk(1), nk(3), MERGE);              /* [a/aa]merge */
}

int main(int argc, char **argv)
{
    rs = (argc > 1) ? strtoull(argv[1], 0, 10) : 88172645ULL;
    if (!rs) rs = 88172645ULL;

    /* ---------------- controls ---------------- */
    if (argc > 1 && !strcmp(argv[1], "ctl")) {
        printf("[ctl] positive controls (evaluator must reproduce them)\n");
        struct { const char *name; int e; } cs[] = {
            {"merge", MERGE}, {"swap", SWAP}, {"diff", DIFF},
            {"half", HALF}, {"halft(diag split)", HALFT}, {"dbl2", DBL2},
        };
        build_stock();
        for (unsigned k = 0; k < sizeof cs / sizeof cs[0]; k++) {
            int okm = 1, nd = 0;
            for (int i = 1; i <= 6; i++) for (int j = 1; j <= 6; j++) {
                char w[64]; int wl = 0;
                for (int t = 0; t < i; t++) w[wl++] = 'a';
                w[wl++] = 'b';
                for (int t = 0; t < j; t++) w[wl++] = 'a';
                int l = eval(cs[k].e, 0, w, wl);
                if (l < 0) { okm = -1; break; }
                char *o = buf[0];
                if (cs[k].e == MERGE) { okm &= (l == i + j); }
                else if (cs[k].e == SWAP) {
                    int ok2 = (l == i + j + 1) && o[j] == 'b';
                    for (int t = 0; ok2 && t < j; t++) ok2 &= (o[t] == 'a');
                    for (int t = 0; ok2 && t < i; t++) ok2 &= (o[j + 1 + t] == 'a');
                    okm &= ok2;
                }
                else if (cs[k].e == DIFF) { okm &= (l == i + j + 1 || (i == j && l == 1)); }
                else if (cs[k].e == HALF) { okm &= (l == (i + 1) / 2 + (j + 1) / 2 + 1); }
                else if (cs[k].e == HALFT) { okm &= (l == (i + j + 1) / 2); }
                else if (cs[k].e == DBL2) { okm &= (l == 4 * i + 4 * j + 1); }
            }
            int s14 = supp(cs[k].e, 14, &nd), s15 = supp(cs[k].e, 15, &nd);
            printf("  %-20s content ok:%s  supports S=14/15: %d/%d\n",
                   cs[k].name, okm == 1 ? "yes" : (okm == -1 ? "UNDEF" : "NO"),
                   s14, s15);
        }
        return 0;
    }

    int NRAND = (argc > 2) ? atoi(argv[2]) : 30000;
    int growing = 0, big = 0, computed = 0, skipped = 0, hits = 0, maxs = 0;
    static const int SS[6] = {14, 15, 20, 21, 26, 27};
    printf("[supp] random ensemble: %d exprs, S-depth <= 5, S in {14,15,20,21,26,27}\n",
           NRAND);
    for (int t = 0; t < NRAND; t++) {
        nn = 0; X = nv();
        int e = gen(5);
        int mx = 0, ndtot = 0;
        for (int q = 0; q < 6; q++) {
            int nd;
            int s = supp(e, SS[q], &nd);
            ndtot += nd;
            if (s > mx) mx = s;
        }
        if (ndtot == 0) {
            /* small-S rescue pass for double explosions (cap 65536) */
            int nd, mx2 = 0, any = 0;
            static const int SS2[3] = {8, 9, 12};
            for (int q = 0; q < 3; q++) {
                int s = supp(e, SS2[q], &nd);
                if (nd) any = 1;
                if (s > mx2) mx2 = s;
            }
            if (!any) { skipped++; continue; }
            mx = mx2;
        }
        computed++;
        if (mx > maxs) maxs = mx;
        if (mx > 12) {
            big++;
            if (big <= 10) printf("  BIG-SUPPORT idx=%d max=%d\n", t, mx);
        }
        int h = split_hits(e);
        if (h) { hits++; printf("  SPLIT HIT idx=%d mask=%d\n", t, h); }
    }
    printf("  computed %d, all-capped/undef %d, max support %d, big(>12) %d, "
           "split hits %d\n", computed, skipped, maxs, big, hits);

    /* ---------------- adversarial ensemble ---------------- */
    printf("[supp] adversarial ensemble (labels aligned)\n");
    build_stock();
    {
        int adv[40]; const char *an[40]; int na = 0;
        #define ADD(ex, nm) do { adv[na] = (ex); an[na] = (nm); na++; } while (0)
        ADD(SWAP, "swap");
        ADD(DIFF, "diff");
        ADD(HALFT, "halft");
        ADD(ns(nk(0), nk(3), DIFF), "[e/aa]diff");
        ADD(ns(nk(0), nk(11), DIFF), "[e/aaa]diff");
        ADD(ns(DIFF, nk(1), X), "[diff/a]w explode");
        ADD(ns(nk(0), nk(3), ns(DIFF, nk(1), X)), "[e/aa][diff/a]w");
        ADD(ns(nk(0), nk(11), ns(DIFF, nk(1), X)), "[e/aaa][diff/a]w");
        ADD(ns(nk(0), MERGE, DBL2), "[e/merge]dbl2");
        ADD(ns(nk(0), MERGE, ns(nk(0), MERGE, DBL2)), "[e/merge]^2 dbl2");
        ADD(ns(nk(0), ns(nk(0), nk(3), MERGE), X), "[e/[e/aa]merge]w");
        ADD(ns(nk(0), ns(nk(0), nk(11), MERGE), X), "[e/[e/aaa]merge]w");
        ADD(ns(nk(0), nk(6), ns(nk(3), nk(1), X)), "[e/bb][ab/a]w");
        ADD(ns(nk(0), nk(10), ns(nk(3), nk(1), X)), "[e/abba][ab/a]w");
        ADD(ns(nk(0), nk(7), DIFF), "[e/aab]diff");
        ADD(ns(SWAP, nk(1), X), "[swap/a]w explode");
        ADD(ns(nk(0), SWAP, ns(SWAP, nk(1), X)), "[e/swap][swap/a]w");
        ADD(ns(nk(0), nk(4), ns(DIFF, nk(1), X)), "[e/ab][diff/a]w");
        ADD(ns(nk(0), nc(X, SWAP), nc(X, SWAP)), "self-collapse");
        ADD(ns(nk(0), nc(SHL, SHR), nc(X, X)), "two-b-engine");
        ADD(nc(nc(SWAP, SWAP), SWAP), "triple-cat");
        ADD(ns(nk(2), X, nc(nc(MERGE, nk(2)), MERGE)), "swap-again");
        ADD(ns(HALFT, X, X), "[halft/w]w");
        ADD(ns(nk(0), HALFT, X), "[e/halft]w");
        ADD(ns(ns(nk(1), nk(2), X), nk(1), ns(nk(2), nk(3), X)), "mixed");
        ADD(ns(ns(nk(0), nk(2), ns(DIFF, nk(1), X)), nk(0), MERGE), "nested-expl");
        int awin = 0;
        for (int k = 0; k < na; k++) {
            int mx = 0, ndtot = 0;
            for (int q = 0; q < 6; q++) {
                int nd; int s = supp(adv[k], SS[q], &nd); ndtot += nd;
                if (s > mx) mx = s;
            }
            if (ndtot == 0) {
                int nd, mx2 = 0, any = 0;
                static const int SS2[3] = {8, 9, 12};
                for (int q = 0; q < 3; q++) {
                    int s = supp(adv[k], SS2[q], &nd);
                    if (nd) any = 1;
                    if (s > mx2) mx2 = s;
                }
                mx = any ? mx2 : -1; ndtot = any ? 1 : 0;
            }
            int h = split_hits(adv[k]);
            if (h) printf("  SPLIT HIT adversarial '%s' mask=%d\n", an[k], h);
            if (mx > 12) { awin++; printf("  BIG '%s' max support %d\n", an[k], mx); }
            printf("  %-24s max support %s%d\n", an[k], ndtot ? "" : "ALL-UNDEF ", mx);
        }
        printf("  adversarial big(>12): %d\n", awin);
    }

    /* ---------------- mode box (strong-form invariant) ---------------- */
    printf("[box] bi-affine box + alpha==beta check (aggregate a-content)\n");
    rs = 424242424242ULL;
    int tried = 0, boxed = 0, nonaff = 0, viol = 0;
    for (int t = 0; t < NRAND; t++) {
        nn = 0; X = nv();
        int e = gen(4);
        for (int rep = 0; rep < 2; rep++) {
            int i0 = 12 + ri(30), j0 = 12 + ri(30), h = 5;
            char w[128]; int wl;
            int g[5];
            int pts[5][2] = {{i0,j0},{i0+h,j0},{i0+2*h,j0},{i0,j0+h},{i0,j0+2*h}};
            int bad = 0, bn = -1;
            for (int q = 0; q < 5; q++) {
                wl = 0;
                for (int z = 0; z < pts[q][0]; z++) w[wl++]='a';
                w[wl++]='b';
                for (int z = 0; z < pts[q][1]; z++) w[wl++]='a';
                int l = eval(e, 0, w, wl);
                if (l < 0) { bad = 1; break; }
                int b = bcount(buf[0], l);
                if (q == 0) bn = b; else if (b != bn) { bad = 1; break; }
                g[q] = acount(buf[0], l);
            }
            if (bad) continue;
            tried++;
            /* bi-affine check on the aggregate a-content (the invariant
               itself: slope along i must equal slope along j) */
            if ((g[1]-g[0]) != (g[2]-g[1]) || (g[3]-g[0]) != (g[4]-g[3])) {
                nonaff++; continue;
            }
            boxed++;
            int ai = g[1] - g[0], aj = g[3] - g[0];
            if (ai != aj) {
                viol++;
                if (viol <= 10) printf("  VIOLATION idx=%d base=(%d,%d) ai=%d aj=%d\n",
                                      t, i0, j0, ai, aj);
            }
        }
    }
    printf("  boxes tried %d, bi-affine: %d, non-affine: %d, "
           "alpha!=beta violations: %d\n", tried, boxed, nonaff, viol);
    return 0;
}

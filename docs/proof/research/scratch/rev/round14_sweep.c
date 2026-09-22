/* ROUND 14 sweep: the ALL-VARYING two-b family
 *   W2 = { a^i b a^j b a^k : i, j, k >= 1 }
 * with the ENRICHED library that round 13's sweep lacked (its blind
 * spot): C-shaped scrutinees, shave-type values, one-b intermediates,
 * junction-shifted w2's.
 *
 * Falsification/discovery only -- the machine never proves.
 *
 * Library (16 values, all computed from w2 by real single passes or
 * concatenations at each grid point -- no hand-derived formulas):
 *   w2   = a^i b a^j b a^k            (input)
 *   mrg  = [e/b]w2 = a^{i+j+k}          (b-free)
 *   js1  = [b/ba]w2 = (i, j-1, k-1)     (junction shave)
 *   js2  = [b/ab]w2 = (i-1, j-1, k)     (junction shave)
 *   del1 = [e/ab]w2 = a^{S-2}          (both-fire shave, b-free)
 *   onbA = [e/(aabaa)]w2               (one-b window, piecewise)
 *   onbB = [e/(baa)]w2                 (one-b window, piecewise)
 *   dbl2 = [aa/a]w2  half2 = [a/aa]w2  (affine)
 *   cw2  = w2.w2  cws = w2.js1         (C-shaped scrutinees, 4 b's)
 *   big2 = mrg.b.mrg                    (one-b, bigsym form)
 *   midb = b.mrg.b                      (2-b, interior S)
 *   sym3 = mrg.b.mrg.b.mrg              (2-b, runs (S,S,S))
 *   sand = mrg.b.w2.b.mrg               (merge-sandwich, 4 b's)
 *   dupb = [bab/b]w2                    (junction duplication, 4 b's)
 * Constants (8): e, a, b, aa, ab, ba, bb, aab.
 *
 * S1: [R/P]F, F in lib (16), P and R in the full 24-pool.
 * S2: [R2/P2][R1/P1]w2 with P*, R* from the 18-value short pool
 *     (consts + w2, mrg, js1, js2, del1, onbA, onbB, half2, midb,
 *     dupb); first-pass results longer than CAP2 = 200 are skipped
 *     (documented completeness cut: blow-up-then-shrink chains).
 *
 * Targets (must hold on ALL grid points, [1..NI]^3):
 *   rev = a^k b a^j b a^i;  splits ai, aj, ak;  sums aik, aij, ajk.
 * Progress counters (full grid): flank (x1,x3) = (k,i) with middle
 * arbitrary; midstrict x2 = j with output != w2; identity.
 * Best partial fraction tracked per target.  Circularity proxy for
 * hits: pattern or replacement contains the substring b.a^j.b.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXS  4096
#define CAP   4096
#define CAP2  200
#define NI    5                /* grid [1..NI]^3 */
#define NGRID (NI * NI * NI)
#define NLIB  16
#define NCONST 8
#define NPOOL (NLIB + NCONST)  /* 24 */
#define NTGT 7
#define S2POOLSZ 18

static char pool[NPOOL][MAXS];
static int plen[NPOOL];
static int capped;

static const char *libn[NLIB] = {
    "w2", "mrg", "js1", "js2", "del1", "onbA", "onbB", "dbl2",
    "half2", "cw2", "cws", "big2", "midb", "sym3", "sand", "dupb"
};
static const char *constn[NCONST] = {
    "e", "a", "b", "aa", "ab", "ba", "bb", "aab"
};
static const char *pname(int x) {
    return x < NLIB ? libn[x] : constn[x - NLIB];
}

/* S2 short pool: consts + 10 short library values */
static const int s2idx[S2POOLSZ] = {
    0, 1, 2, 3, 4, 5, 6, 8, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23
};

static void spass(const char *in, int n, const char *pat, int m,
                  const char *rep, int rl, char *out) {
    int oi = 0, i = 0;
    if (m == 0) { memcpy(out, in, n); out[n] = 0; return; }
    while (i < n) {
        if (i + m <= n && memcmp(in + i, pat, m) == 0) {
            if (oi + rl > CAP) { capped = 1; break; }
            memcpy(out + oi, rep, rl); oi += rl; i += m;
        } else {
            if (oi + 1 > CAP) { capped = 1; break; }
            out[oi++] = in[i++];
        }
    }
    out[oi] = 0;
}

static void rep_a(char *s, int n) {
    for (int t = 0; t < n; t++) s[t] = 'a';
    s[n] = 0;
}

static char t_rev[MAXS], t_ai[32], t_aj[32], t_ak[32];
static char t_aik[32], t_aij[32], t_ajk[32];
static int gi, gj, gk;

static void build_point(int i, int j, int k) {
    char a[64], ab[64], w2c[MAXS];
    gi = i; gj = j; gk = k;
    rep_a(a, i); strcat(a, "b");
    rep_a(ab, j); strcat(ab, "b");
    rep_a(t_ak, k);
    strcpy(w2c, a); strcat(w2c, ab); strcat(w2c, t_ak);   /* w2 */
    strcpy(pool[0], w2c);
    spass(w2c, strlen(w2c), "b", 1, "", 0, pool[1]);
    spass(w2c, strlen(w2c), "ba", 2, "b", 1, pool[2]);
    spass(w2c, strlen(w2c), "ab", 2, "b", 1, pool[3]);
    spass(w2c, strlen(w2c), "ab", 2, "", 0, pool[4]);
    spass(w2c, strlen(w2c), "aabaa", 5, "", 0, pool[5]);
    spass(w2c, strlen(w2c), "baa", 3, "", 0, pool[6]);
    spass(w2c, strlen(w2c), "a", 1, "aa", 2, pool[7]);
    spass(w2c, strlen(w2c), "aa", 2, "a", 1, pool[8]);
    strcpy(pool[9], w2c); strcat(pool[9], w2c);           /* cw2 */
    strcpy(pool[10], w2c); strcat(pool[10], pool[2]);     /* cws */
    strcpy(pool[11], pool[1]); strcat(pool[11], "b");
    strcat(pool[11], pool[1]);                            /* big2 */
    strcpy(pool[12], "b"); strcat(pool[12], pool[1]);
    strcat(pool[12], "b");                                /* midb */
    strcpy(pool[13], pool[1]); strcat(pool[13], "b");
    strcat(pool[13], pool[1]); strcat(pool[13], "b");
    strcat(pool[13], pool[1]);                            /* sym3 */
    strcpy(pool[14], pool[1]); strcat(pool[14], "b");
    strcat(pool[14], w2c); strcat(pool[14], "b");
    strcat(pool[14], pool[1]);                            /* sand */
    spass(w2c, strlen(w2c), "b", 1, "bab", 3, pool[15]); /* dupb */
    strcpy(pool[16], "");  strcpy(pool[17], "a");  strcpy(pool[18], "b");
    strcpy(pool[19], "aa"); strcpy(pool[20], "ab"); strcpy(pool[21], "ba");
    strcpy(pool[22], "bb"); strcpy(pool[23], "aab");
    for (int t = 0; t < NPOOL; t++) plen[t] = strlen(pool[t]);
    /* targets */
    rep_a(t_ai, i); rep_a(t_aj, j);
    rep_a(t_aik, i + k); rep_a(t_aij, i + j); rep_a(t_ajk, j + k);
    strcpy(t_rev, t_ak); strcat(t_rev, "b"); rep_a(ab, j);
    strcat(t_rev, ab); strcat(t_rev, "b"); rep_a(a, i); strcat(t_rev, a);
}

static int parse2b(const char *s, int *x1, int *x2, int *x3) {
    int n = strlen(s), p = 0;
    *x1 = 0; while (p < n && s[p] == 'a') { (*x1)++; p++; }
    if (p >= n || s[p] != 'b') return 0; p++;
    *x2 = 0; while (p < n && s[p] == 'a') { (*x2)++; p++; }
    if (p >= n || s[p] != 'b') return 0; p++;
    *x3 = 0; while (p < n && s[p] == 'a') { (*x3)++; p++; }
    return p == n;
}

static const char *tgtn[NTGT] = { "rev", "ai", "aj", "ak", "aik", "aij", "ajk" };

#define NS1 (NLIB * NPOOL * NPOOL)
#define NS2 (S2POOLSZ * S2POOLSZ * S2POOLSZ * S2POOLSZ)

static int cnt1[NS1][NTGT], fl1[NS1], ms1[NS1], id1[NS1];
static int ex1[NS1][3];
static int cnt2[NS2][NTGT], fl2[NS2], ms2[NS2], id2[NS2];
static int ex2[NS2][3];
static char first[S2POOLSZ][S2POOLSZ][CAP2 + 2];
static int flen[S2POOLSZ][S2POOLSZ];

static void tally(const char *out, int *cnt, int *fl, int *ms, int *id,
                  int *ex) {
    char *tv[NTGT] = { t_rev, t_ai, t_aj, t_ak, t_aik, t_aij, t_ajk };
    int sum = 0;
    for (int t = 0; t < NTGT; t++)
        if (strcmp(out, tv[t]) == 0) { cnt[t]++; sum++; }
    int x1, x2, x3;
    if (parse2b(out, &x1, &x2, &x3)) {
        if (x1 == gk && x3 == gi) (*fl)++;
        if (x2 == gj && strcmp(out, pool[0]) != 0) (*ms)++;
        if (strcmp(out, pool[0]) == 0) (*id)++;
    }
    if (sum == 1) { ex[0] = gi; ex[1] = gj; ex[2] = gk; }
}

/* circularity proxy: does s contain b.a^gj.b (exact-interior window)? */
static int pins_middle(const char *s) {
    char midj[NI + 4];
    midj[0] = 'b';
    for (int t = 0; t < gj; t++) midj[1 + t] = 'a';
    midj[1 + gj] = 'b'; midj[2 + gj] = 0;
    return strstr(s, midj) != NULL;
}

int main(void) {
    clock_t t0 = clock();
    char out[MAXS];
    long sims = 0;
    int ncut = 0;

    for (int i = 1; i <= NI; i++)
        for (int j = 1; j <= NI; j++)
            for (int k = 1; k <= NI; k++) {
                build_point(i, j, k);
                /* ---- S1: [R/P]F ---- */
                for (int f = 0; f < NLIB; f++)
                    for (int p = 0; p < NPOOL; p++) {
                        if (plen[p] == 0) continue;
                        for (int r = 0; r < NPOOL; r++) {
                            int c = (f * NPOOL + p) * NPOOL + r;
                            spass(pool[f], plen[f], pool[p], plen[p],
                                  pool[r], plen[r], out);
                            sims++;
                            tally(out, cnt1[c], &fl1[c], &ms1[c],
                                  &id1[c], ex1[c]);
                        }
                    }
                /* ---- S2: first passes [R1/P1]w2 ---- */
                for (int a = 0; a < S2POOLSZ; a++)
                    for (int b = 0; b < S2POOLSZ; b++) {
                        int pi = s2idx[a], ri = s2idx[b];
                        if (plen[pi] == 0) { flen[a][b] = -1; continue; }
                        spass(pool[0], plen[0], pool[pi], plen[pi],
                              pool[ri], plen[ri], out);
                        if (strlen(out) > CAP2) {
                            flen[a][b] = -2;
                            continue;
                        }
                        strcpy(first[a][b], out);
                        flen[a][b] = strlen(out);
                    }
                for (int a = 0; a < S2POOLSZ; a++)            /* P1 */
                    for (int b = 0; b < S2POOLSZ; b++) {       /* R1 */
                        if (flen[a][b] < 0) continue;
                        for (int c2 = 0; c2 < S2POOLSZ; c2++) { /* P2 */
                            if (plen[s2idx[c2]] == 0) continue;
                            for (int d = 0; d < S2POOLSZ; d++) { /* R2 */
                                int c = ((a * S2POOLSZ + b) * S2POOLSZ
                                         + c2) * S2POOLSZ + d;
                                spass(first[a][b], flen[a][b],
                                      pool[s2idx[c2]], plen[s2idx[c2]],
                                      pool[s2idx[d]], plen[s2idx[d]], out);
                                sims++;
                                tally(out, cnt2[c], &fl2[c], &ms2[c],
                                      &id2[c], ex2[c]);
                            }
                        }
                    }
            }

    for (int a = 0; a < S2POOLSZ; a++)
        for (int b = 0; b < S2POOLSZ; b++)
            if (flen[a][b] == -2) ncut++;
    printf("sims: %ld\n", sims);
    printf("grid: [1..%d]^3 = %d points\n", NI, NGRID);
    printf("S1 combos: %d   S2 combos: %d\n", NS1, NS2);
    printf("S2 first-pass results skipped (len > %d): %d of %d "
           "(documented completeness cut)\n", CAP2, ncut,
           S2POOLSZ * S2POOLSZ);

    /* ---- report S1 ---- */
    int best[NTGT]; char bestc[NTGT][160];
    for (int t = 0; t < NTGT; t++) best[t] = 0;
    for (int c = 0; c < NS1; c++) {
        int f = c / (NPOOL * NPOOL), p = (c / NPOOL) % NPOOL, r = c % NPOOL;
        char nm[160];
        snprintf(nm, sizeof nm, "[%s/%s]%s", pname(r), pname(p), libn[f]);
        for (int t = 0; t < NTGT; t++)
            if (cnt1[c][t] > best[t]) {
                best[t] = cnt1[c][t];
                snprintf(bestc[t], 160, "%s", nm);
                if (cnt1[c][t] == NGRID) {
                    printf("HIT  %-4s  %s", tgtn[t], nm);
                    if (ex1[c][0]) {
                        build_point(ex1[c][0], ex1[c][1], ex1[c][2]);
                        printf("   [proxy: P%s R%s]",
                               pins_middle(pool[p]) ? " pins-middle" : "",
                               pins_middle(pool[r]) ? " pins-middle" : "");
                    }
                    printf("\n");
                }
            }
        if (fl1[c] == NGRID) printf("HIT  flank   %s\n", nm);
        if (ms1[c] == NGRID) printf("HIT  midstr  %s\n", nm);
    }
    printf("\nS1 best partial (of %d):\n", NGRID);
    for (int t = 0; t < NTGT; t++)
        printf("  %-4s %3d  %s\n", tgtn[t], best[t], bestc[t]);

    /* ---- report S2 ---- */
    for (int t = 0; t < NTGT; t++) best[t] = 0;
    for (int c = 0; c < NS2; c++) {
        int a = c / (S2POOLSZ * S2POOLSZ * S2POOLSZ);
        int b = (c / (S2POOLSZ * S2POOLSZ)) % S2POOLSZ;
        int c2 = (c / S2POOLSZ) % S2POOLSZ, d = c % S2POOLSZ;
        char nm[160];
        snprintf(nm, sizeof nm, "[%s/%s][%s/%s]w2", pname(s2idx[d]),
                 pname(s2idx[c2]), pname(s2idx[b]), pname(s2idx[a]));
        for (int t = 0; t < NTGT; t++)
            if (cnt2[c][t] > best[t]) {
                best[t] = cnt2[c][t];
                snprintf(bestc[t], 160, "%s", nm);
                if (cnt2[c][t] == NGRID) {
                    printf("HIT  %-4s  %s", tgtn[t], nm);
                    if (ex2[c][0]) {
                        build_point(ex2[c][0], ex2[c][1], ex2[c][2]);
                        printf("   [proxy: P1%s R1%s P2%s R2%s]",
                               pins_middle(pool[s2idx[a]]) ? " pins" : "",
                               pins_middle(pool[s2idx[b]]) ? " pins" : "",
                               pins_middle(pool[s2idx[c2]]) ? " pins" : "",
                               pins_middle(pool[s2idx[d]]) ? " pins" : "");
                    }
                    printf("\n");
                }
            }
        if (fl2[c] == NGRID) printf("HIT  flank   %s\n", nm);
        if (ms2[c] == NGRID) printf("HIT  midstr  %s\n", nm);
    }
    printf("\nS2 best partial (of %d):\n", NGRID);
    for (int t = 0; t < NTGT; t++)
        printf("  %-4s %3d  %s\n", tgtn[t], best[t], bestc[t]);

    printf("\ncapped evaluations (len > %d): %s\n", CAP,
           capped ? "occurred (sound: expected outputs are short)" : "none");
    printf("elapsed: %.1fs\n", (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}

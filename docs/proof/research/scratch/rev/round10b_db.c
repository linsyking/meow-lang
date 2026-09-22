/* ROUND 10 (continued) - the descending-bijection (DB) hunt, v2.
 *
 * Supersedes round10_hunt.c (which over-ran the 55 s budget).  Domains
 * are shrunk to fit, and - unlike the previous version - ALL depth-2
 * shapes are covered, not just chains:
 *
 *   shape "chain"  : [eps/x] ([y'/x'] F)      F,y',x' pass-free
 *   shape "deepR"  : [t1/x]  F                t1 a 1-pass output
 *   shape "deepP"  : [eps/x1] F               x1 a 1-pass output
 *   shape "C"      : cat of two depth<=1 parts
 *   (depth-3 probe: chain3 / deepR3 / C3 / Ctarget)
 *
 * Justified restrictions (T1, proved in the round-10 fragment):
 *   - the FINAL pass's replacement may be assumed label-free for n>=2
 *     (c>=2 sites + labeled replacement => mult>=2; c=1 => the block
 *     prov(y)=R^rho is not FDI; c=0 => vacuous), so the outer
 *     replacement is eps and only prov matters: [eps/x] suffices;
 *   - deepR replacements are filtered to label-free or FDI provs
 *     (anything else dies by T1 for n >= 2 at c in {>=2, 1}).
 *
 * DB(w): prov = strictly decreasing permutation of {0..n-1}.
 * FDI:   prov strictly decreasing and injective (length, or -1).
 *
 * Build: gcc -O2 -o round10b_db round10b_db.c
 * Usage: ./round10b_db 1|2|3   (1=depth<=1, 2=depth-2, 3=depth-3)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXW 24
#define MAXATOMS 4096
#define POOL_CAP 20000
#define POOL_CAP2 4000

typedef struct { char c; int lb; } atom;

static long sims = 0, undef = 0;
static long db_hits = 0;
static int db_maxn = 0;
static int fdi_max = -1;
static char fdi_shape[64], fdi_w[64];
static char db_shape[64], db_w[64];

/* ---------------------------------------------------------------- pass */

static int pass_(const atom *repl, int rn, const char *pat, int plen,
                 const atom *t, int tn, atom *out, int *on)
{
    int i, o = 0;
    if (plen == 0) return 1;
    i = 0;
    while (i < tn) {
        if (i + plen <= tn) {
            int k, eq = 1;
            for (k = 0; k < plen; k++)
                if (t[i + k].c != pat[k]) { eq = 0; break; }
            if (eq) {
                if (o + rn > MAXATOMS) return 2;
                if (rn) memcpy(out + o, repl, rn * sizeof(atom));
                o += rn; i += plen; sims++;
                continue;
            }
        }
        if (o >= MAXATOMS) return 2;
        out[o++] = t[i++]; sims++;
    }
    *on = o;
    return 0;
}

/* ------------------------------------------------------------ checks */

static int fdi_len(const atom *t, int tn)
{
    int prev = 0, first = 1, len = 0, i;
    for (i = 0; i < tn; i++) {
        int lb = t[i].lb;
        if (lb < 0) continue;
        if (first) { prev = lb; first = 0; len = 1; continue; }
        if (prev <= lb) return -1;
        prev = lb; len++;
    }
    return first ? 0 : len;
}

static int is_db(const atom *t, int tn, int n)
{
    int seen[MAXW], prev = 0, first = 1, cnt = 0, i;
    if (n < 2 || n > MAXW) return 0;
    memset(seen, 0, sizeof(seen));
    for (i = 0; i < tn; i++) {
        int lb = t[i].lb;
        if (lb < 0) continue;
        if (lb >= n) return 0;
        if (seen[lb]) return 0;
        seen[lb] = 1;
        if (!first && prev <= lb) return 0;
        prev = lb; first = 0; cnt++;
    }
    return cnt == n;
}

static void check(const atom *t, int tn, int n, const char *shape,
                  const char *w)
{
    int len = fdi_len(t, tn);
    if (len > fdi_max) {
        fdi_max = len;
        snprintf(fdi_shape, sizeof(fdi_shape), "%s", shape);
        snprintf(fdi_w, sizeof(fdi_w), "%s", w);
    }
    if (is_db(t, tn, n)) {
        db_hits++;
        if (n > db_maxn) {
            db_maxn = n;
            snprintf(db_shape, sizeof(db_shape), "%s", shape);
            snprintf(db_w, sizeof(db_w), "%s", w);
        }
        if (1)
            printf("  DB HIT: shape=%s w=%s n=%d prov-len=%d\n",
                   shape, w, n, len);
    }
}

/* --------------------------------------------------------- hash pool */

typedef struct entry { atom *a; int n; struct entry *next; } entry;
#define HSIZE (1 << 16)
static entry *htab[HSIZE];

static uint64_t hash_text(const atom *a, int n)
{
    uint64_t h = 1469598103934665603ULL;
    int i;
    for (i = 0; i < n; i++) {
        h ^= (uint64_t)(unsigned char)a[i].c; h *= 1099511628211ULL;
        h ^= (uint64_t)(uint32_t)a[i].lb;    h *= 1099511628211ULL;
    }
    return h;
}

static int pool_has(const atom *a, int n)
{
    uint64_t h = hash_text(a, n);
    entry *e = htab[h % HSIZE];
    while (e) {
        if (e->n == n && !memcmp(e->a, a, n * sizeof(atom))) return 1;
        e = e->next;
    }
    return 0;
}

static void pool_add(const atom *a, int n)   /* no dedup check */
{
    uint64_t h = hash_text(a, n);
    entry *e = malloc(sizeof(entry));
    e->a = malloc(n ? n * sizeof(atom) : 1);
    if (n) memcpy(e->a, a, n * sizeof(atom));
    e->n = n;
    e->next = htab[h % HSIZE];
    htab[h % HSIZE] = e;
}

static void pool_free(void)
{
    int i;
    for (i = 0; i < HSIZE; i++) {
        entry *e = htab[i];
        while (e) { entry *nx = e->next; free(e->a); free(e); e = nx; }
        htab[i] = NULL;
    }
}

/* dynamic vector of (atom*, len) */
typedef struct { atom **a; int *l; int n, cap; } vec;
static void vec_push(vec *v, const atom *a, int n)
{
    if (v->n == v->cap) {
        v->cap = v->cap ? v->cap * 2 : 64;
        v->a = realloc(v->a, v->cap * sizeof(atom *));
        v->l = realloc(v->l, v->cap * sizeof(int));
    }
    v->a[v->n] = malloc(n ? n * sizeof(atom) : 1);
    if (n) memcpy(v->a[v->n], a, n * sizeof(atom));
    v->l[v->n] = n;
    v->n++;
}
static void vec_free(vec *v)
{
    int i;
    for (i = 0; i < v->n; i++) free(v->a[i]);
    free(v->a); free(v->l);
    v->a = NULL; v->l = NULL; v->n = v->cap = 0;
}

/* ------------------------------------------------------- pass-free lib */

typedef struct { char name[16]; atom a[3 * MAXW + 8]; int n; } val;

static void mkval(val *v, const char *pre, const char *w,
                  const char *suf, int wruns)
{
    int i, j, pos = 0;
    for (i = 0; pre[i]; i++) { v->a[pos].c = pre[i]; v->a[pos].lb = -1; pos++; }
    for (i = 0; i < wruns; i++)
        for (j = 0; w[j]; j++) { v->a[pos].c = w[j]; v->a[pos].lb = j; pos++; }
    for (i = 0; suf[i]; i++) { v->a[pos].c = suf[i]; v->a[pos].lb = -1; pos++; }
    v->n = pos;
}

static int pfree(const char *w, val *vals)
{
    static const char *consts[] = { "a", "b", "aa", "ab", "ba", "bb",
                                    "aaa", "aab", "aba", "abb",
                                    "baa", "bab", "bba", "bbb" };
    int k = 0, i;
    mkval(&vals[k++], "", w, "", 0);                    /* eps */
    for (i = 0; i < 14; i++) mkval(&vals[k++], consts[i], w, "", 0);
    mkval(&vals[k++], "", w, "", 1);                    /* w   */
    mkval(&vals[k++], "a", w, "", 1);                    /* a.w */
    mkval(&vals[k++], "", w, "a", 1);                    /* w.a */
    mkval(&vals[k++], "b", w, "", 1);                    /* b.w */
    mkval(&vals[k++], "", w, "b", 1);                    /* w.b */
    mkval(&vals[k++], "a", w, "b", 1);                   /* a.w.b */
    mkval(&vals[k++], "b", w, "a", 1);                   /* b.w.a */
    mkval(&vals[k++], "ab", w, "", 1);                   /* ab.w */
    mkval(&vals[k++], "", w, "ab", 1);                   /* w.ab */
    mkval(&vals[k++], "", w, "", 2);                     /* w.w */
    return k;
}

/* ---------------------------------------------------------- w domains */

static char wdom[512][MAXW + 1];
static int nws = 0;

static void add_w(const char *s)
{
    int i;
    if (strlen(s) > MAXW) return;
    for (i = 0; i < nws; i++) if (!strcmp(wdom[i], s)) return;
    if (nws < 512) snprintf(wdom[nws++], MAXW + 1, "%s", s);
}

static void gen_all(int maxlen)
{
    int n, i, total;
    char buf[MAXW + 1];
    for (n = 1; n <= maxlen; n++) {
        total = 1 << n;
        for (i = 0; i < total; i++) {
            int j;
            for (j = 0; j < n; j++)
                buf[j] = ((i >> (n - 1 - j)) & 1) ? 'b' : 'a';
            buf[n] = 0;
            add_w(buf);
        }
    }
}

static void gen_families(int jmax, int maxw)
{
    static const char *pats[] = { "ab", "ba", "aab", "aba", "abb",
                                  "baa", "bab", "bba", "aa", "bb" };
    int p, j;
    for (p = 0; p < 10; p++)
        for (j = 2; j <= jmax; j++) {
            char buf[MAXW + 1];
            int L = 0, k;
            for (k = 0; k < j; k++) {
                int pl = (int)strlen(pats[p]);
                if (L + pl > maxw) break;
                memcpy(buf + L, pats[p], pl); L += pl;
            }
            buf[L] = 0;
            add_w(buf);
        }
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void)
{
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static void gen_random(int cnt, int minlen, int maxlen)
{
    int i;
    for (i = 0; i < cnt; i++) {
        char buf[MAXW + 1];
        int L = minlen + (int)(rnd() % (maxlen - minlen + 1)), j;
        for (j = 0; j < L; j++) buf[j] = (rnd() & 1) ? 'b' : 'a';
        buf[L] = 0;
        add_w(buf);
    }
}

/* --------------------------------------------------------------- main */

int main(int argc, char **argv)
{
    int mode = argc > 1 ? atoi(argv[1]) : 2;
    int i;
    static char pats[64][3 * MAXW + 8];
    int npats;
    atom *outbuf = malloc(sizeof(atom) * MAXATOMS);
    atom *outbuf2 = malloc(sizeof(atom) * MAXATOMS);

    if (mode == 1) { gen_all(6); gen_families(6, 18); }
    else if (mode == 2) { gen_all(7); gen_families(8, 24); gen_random(80, 6, 20); }
    else { gen_all(5); gen_families(6, 18); gen_random(30, 5, 12); }
    if (mode == 4) { gen_all(4); gen_families(4, 12); gen_random(10, 4, 8); }
    printf("mode %d: %d inputs\n", mode, nws);

    for (i = 0; i < nws; i++) {
        const char *w = wdom[i];
        val vals[32];
        int nvals;
        int n = (int)strlen(w);
        atom *lab = malloc(sizeof(atom) * n);
        int z, v, p, r, on, rc;
        vec L1, D2, R1, RD, R2, RD2, D3;

        for (z = 0; z < n; z++) { lab[z].c = w[z]; lab[z].lb = z; }
        nvals = pfree(w, vals);
        npats = 0;
        for (v = 0; v < nvals; v++) {
            int dup = 0, q;
            if (vals[v].n == 0) continue;
            for (q = 0; q < npats; q++)
                if ((int)strlen(pats[q]) == vals[v].n &&
                    !memcmp(pats[q], vals[v].a, vals[v].n)) { dup = 1; break; }
            if (!dup) {
                for (z = 0; z < vals[v].n; z++) pats[npats][z] = vals[v].a[z].c;
                pats[npats][vals[v].n] = 0;
                npats++;
            }
        }
        pool_free();
        memset(&L1, 0, sizeof(L1)); memset(&D2, 0, sizeof(D2));
        memset(&R1, 0, sizeof(R1)); memset(&RD, 0, sizeof(RD));
        memset(&R2, 0, sizeof(R2)); memset(&RD2, 0, sizeof(RD2));
        memset(&D3, 0, sizeof(D3));

        /* ---- level-1 pool: all 1-pass outputs [y'/x']F ---- */
        for (v = 0; v < nvals; v++) {           /* F (scrutinee) */
            for (p = 0; p < npats; p++) {       /* x' */
                int plen = (int)strlen(pats[p]);
                for (r = 0; r < nvals; r++) {   /* y' */
                    rc = pass_(vals[r].a, vals[r].n, pats[p], plen,
                               vals[v].a, vals[v].n, outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    if (mode == 1) check(outbuf, on, n, "depth1", w);
                    if (!pool_has(outbuf, on)) {
                        pool_add(outbuf, on);
                        if (L1.n < POOL_CAP) vec_push(&L1, outbuf, on);
                    }
                }
            }
        }

        if (mode == 1) {
            /* C-compositions of two depth-1 parts */
            vec parts; memset(&parts, 0, sizeof(parts));
            for (z = 0; z < L1.n; z++) {
                int fl = fdi_len(L1.a[z], L1.l[z]);
                if (fl >= 0) vec_push(&parts, L1.a[z], L1.l[z]);
            }
            for (z = 0; z < parts.n && z < 400; z++)
                for (v = 0; v < parts.n && v < 400; v++) {
                    int tn = parts.l[z] + parts.l[v];
                    if (tn > MAXATOMS) continue;
                    memcpy(outbuf, parts.a[z], parts.l[z] * sizeof(atom));
                    memcpy(outbuf + parts.l[z], parts.a[v],
                           parts.l[v] * sizeof(atom));
                    check(outbuf, tn, n, "C(1,1)", w);
                }
            vec_free(&parts);
        }

        if (mode >= 2) {
            /* ---- depth-2 chains: [eps/x] t, t in L1 ---- */
            for (z = 0; z < L1.n; z++)
                for (p = 0; p < npats; p++) {
                    int plen = (int)strlen(pats[p]);
                    rc = pass_(NULL, 0, pats[p], plen, L1.a[z], L1.l[z],
                               outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    check(outbuf, on, n, "chain2", w);
                    if (!pool_has(outbuf, on)) {
                        pool_add(outbuf, on);
                        if (D2.n < POOL_CAP2) vec_push(&D2, outbuf, on);
                    }
                }
            /* ---- deepR: [t1/x] F, t1 label-free or FDI ---- */
            for (z = 0; z < L1.n; z++) {
                int fl = fdi_len(L1.a[z], L1.l[z]);
                int labfree = 1, q;
                for (q = 0; q < L1.l[z]; q++)
                    if (L1.a[z][q].lb >= 0) { labfree = 0; break; }
                if (!labfree && fl < 0) continue;
                vec_push(&R1, L1.a[z], L1.l[z]);
            }
            for (z = 0; z < R1.n && z < 600; z++)
                for (v = 0; v < nvals; v++)
                    for (p = 0; p < npats; p++) {
                        int plen = (int)strlen(pats[p]);
                        rc = pass_(R1.a[z], R1.l[z], pats[p], plen,
                                   vals[v].a, vals[v].n, outbuf, &on);
                        if (rc == 1) { undef++; continue; }
                        if (rc == 2) continue;
                        check(outbuf, on, n, "deepR2", w);
                    }
            /* ---- deepP: [eps/x1] F, x1 = content of a 1-pass output ---- */
            {
                vec PC; memset(&PC, 0, sizeof(PC));
                for (z = 0; z < L1.n && PC.n < 1200; z++) {
                    int q, dup = 0;
                    for (v = 0; v < PC.n; v++)
                        if (PC.l[v] == L1.l[z] &&
                            !memcmp(PC.a[v], L1.a[z], L1.l[z])) { dup = 1; break; }
                    if (!dup) vec_push(&PC, L1.a[z], L1.l[z]);
                }
                for (z = 0; z < PC.n; z++) {
                    /* PC entries stored as atoms; use content as pattern */
                    static char cbuf[3 * MAXW + 8];
                    int q, cl = 0;
                    for (q = 0; q < PC.l[z]; q++) cbuf[cl++] = PC.a[z][q].c;
                    for (v = 0; v < nvals; v++) {
                        rc = pass_(NULL, 0, cbuf, cl, vals[v].a, vals[v].n,
                                   outbuf, &on);
                        if (rc == 1) { undef++; continue; }
                        if (rc == 2) continue;
                        check(outbuf, on, n, "deepP2", w);
                    }
                }
                vec_free(&PC);
            }
            /* ---- C-shapes at depth 2 ---- */
            for (z = 0; z < R1.n && z < 400; z++)
                for (v = 0; v < R1.n && v < 400; v++) {
                    int tn = R1.l[z] + R1.l[v];
                    if (tn > MAXATOMS) continue;
                    memcpy(outbuf, R1.a[z], R1.l[z] * sizeof(atom));
                    memcpy(outbuf + R1.l[z], R1.a[v], R1.l[v] * sizeof(atom));
                    check(outbuf, tn, n, "C(2)", w);
                }
            for (z = 0; z < R1.n && z < 400; z++)
                for (v = 0; v < nvals; v++) {
                    int tn = R1.l[z] + vals[v].n;
                    if (tn > MAXATOMS) continue;
                    memcpy(outbuf, R1.a[z], R1.l[z] * sizeof(atom));
                    memcpy(outbuf + R1.l[z], vals[v].a,
                           vals[v].n * sizeof(atom));
                    check(outbuf, tn, n, "C(2,pf)", w);
                    memcpy(outbuf, vals[v].a, vals[v].n * sizeof(atom));
                    memcpy(outbuf + vals[v].n, R1.a[z],
                           R1.l[z] * sizeof(atom));
                    check(outbuf, tn, n, "C(pf,2)", w);
                }
        }

        if (mode == 3) {
            /* ---- depth-3 probe ---- */
            /* (a) chain3: [eps/x] on depth-2 outputs */
            for (z = 0; z < D2.n; z++)
                for (p = 0; p < npats; p++) {
                    int plen = (int)strlen(pats[p]);
                    rc = pass_(NULL, 0, pats[p], plen, D2.a[z], D2.l[z],
                               outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    check(outbuf, on, n, "chain3", w);
                }
            /* (b) deepR3: [d/x] w with d = depth-2 output, label-free/FDI */
            for (z = 0; z < D2.n; z++) {
                int fl = fdi_len(D2.a[z], D2.l[z]);
                int labfree = 1, q;
                for (q = 0; q < D2.l[z]; q++)
                    if (D2.a[z][q].lb >= 0) { labfree = 0; break; }
                if (!labfree && fl < 0) continue;
                vec_push(&RD2, D2.a[z], D2.l[z]);
            }
            for (z = 0; z < RD2.n && z < 400; z++)
                for (p = 0; p < npats; p++) {
                    int plen = (int)strlen(pats[p]);
                    rc = pass_(RD2.a[z], RD2.l[z], pats[p], plen,
                               lab, n, outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    check(outbuf, on, n, "deepR3", w);
                }
            /* (c) Ctarget: [d/x] (w.a.w) */
            {
                atom *targ = malloc(sizeof(atom) * (2 * n + 1));
                int tn = 0;
                memcpy(targ, lab, n * sizeof(atom));
                targ[tn].c = 'a'; targ[tn].lb = -1; tn++;
                memcpy(targ + tn, lab, n * sizeof(atom)); tn += n;
                for (z = 0; z < RD2.n && z < 400; z++)
                    for (p = 0; p < npats; p++) {
                        int plen = (int)strlen(pats[p]);
                        rc = pass_(RD2.a[z], RD2.l[z], pats[p], plen,
                                   targ, tn, outbuf, &on);
                        if (rc == 1) { undef++; continue; }
                        if (rc == 2) continue;
                        check(outbuf, on, n, "Ctarget3", w);
                    }
                free(targ);
            }
            /* (d) C3: cat of depth-2 and depth-1 parts (FDI/empty only) */
            for (z = 0; z < RD2.n && z < 200; z++)
                for (v = 0; v < R1.n && v < 200; v++) {
                    int tn = RD2.l[z] + R1.l[v];
                    if (tn > MAXATOMS) continue;
                    memcpy(outbuf, RD2.a[z], RD2.l[z] * sizeof(atom));
                    memcpy(outbuf + RD2.l[z], R1.a[v], R1.l[v] * sizeof(atom));
                    check(outbuf, tn, n, "C(3,1)", w);
                }
        }
        if (mode == 4) {
            /* D3 pool: outputs of [eps/x] on depth-2 outputs */
            for (z = 0; z < D2.n; z++)
                for (p = 0; p < npats; p++) {
                    int plen = (int)strlen(pats[p]);
                    rc = pass_(NULL, 0, pats[p], plen, D2.a[z], D2.l[z],
                               outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    if (!pool_has(outbuf, on)) {
                        pool_add(outbuf, on);
                        if (D3.n < POOL_CAP2) vec_push(&D3, outbuf, on);
                    }
                }
            /* chain4 */
            for (z = 0; z < D3.n; z++)
                for (p = 0; p < npats; p++) {
                    int plen = (int)strlen(pats[p]);
                    rc = pass_(NULL, 0, pats[p], plen, D3.a[z], D3.l[z],
                               outbuf, &on);
                    if (rc == 1) { undef++; continue; }
                    if (rc == 2) continue;
                    check(outbuf, on, n, "chain4", w);
                }
            /* deepR4: [d/x] w with d = depth-3 output, label-free/FDI */
            {
                vec RD3; memset(&RD3, 0, sizeof(RD3));
                for (z = 0; z < D3.n; z++) {
                    int fl = fdi_len(D3.a[z], D3.l[z]);
                    int labfree = 1, q;
                    for (q = 0; q < D3.l[z]; q++)
                        if (D3.a[z][q].lb >= 0) { labfree = 0; break; }
                    if (!labfree && fl < 0) continue;
                    vec_push(&RD3, D3.a[z], D3.l[z]);
                }
                for (z = 0; z < RD3.n && z < 600; z++)
                    for (p = 0; p < npats; p++) {
                        int plen = (int)strlen(pats[p]);
                        rc = pass_(RD3.a[z], RD3.l[z], pats[p], plen,
                                   lab, n, outbuf, &on);
                        if (rc == 1) { undef++; continue; }
                        if (rc == 2) continue;
                        check(outbuf, on, n, "deepR4", w);
                    }
                vec_free(&RD3);
            }
        }
        vec_free(&L1); vec_free(&D2); vec_free(&R1); vec_free(&RD);
        vec_free(&R2); vec_free(&RD2); vec_free(&D3);
        free(lab);
    }
    printf("sims=%ld undef=%ld\n", sims, undef);
    printf("max FDI length: %d (shape %s, w %s)\n", fdi_max, fdi_shape,
           fdi_w);
    printf("DB realizations (n>=2): %ld; max n: %d (shape %s, w %s)\n",
           db_hits, db_maxn, db_shape, db_w);
    free(outbuf); free(outbuf2);
    return 0;
}

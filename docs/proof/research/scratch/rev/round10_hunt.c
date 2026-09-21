/* ROUND 10 - the descending-bijection (DB) hunt, C port.
 *
 * Semantics identical to prov.py / lcore.py (cross-checked):
 *   - a pass [A/B]T replaces greedy-leftmost non-overlapping B-sites
 *     of T by A, never rescanning inserted text (scan resumes after
 *     the matched pattern span);
 *   - empty pattern => undefined (skipped, counted);
 *   - pass-free labeled values are FULL identity runs (V(0) and cats
 *     with constants), exactly as in verify_round10_db.py:pfree().
 *
 * DB(w): prov = labels (None stripped) is a strictly decreasing
 * permutation of {0..n-1}.  FDI: strictly decreasing, injective.
 *
 * Caps (printed at runtime): MAXATOMS per text (overflow -> skipped,
 * counted); pool caps per level/shape (counted).  Modes:
 *   12 : depth-1 battery  (cross-check vs Python part 2)
 *   23 : depth-2 chains   (cross-check vs Python part 3)
 *   3  : depth-3 hunt (chain3, deepR, Ctarget, C-compositions)
 *
 * Build: gcc -O2 -o round10_hunt round10_hunt.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXW 40
#define MAXATOMS (1 << 17)
#define POOL1_CAP 8000
#define POOL2_CAP 300000

typedef struct { char c; int lb; } atom;

static long sims = 0, skipped_undef = 0, skipped_overflow = 0;
static long capped_pool = 0;

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
                memcpy(out + o, repl, rn * sizeof(atom));
                o += rn;
                i += plen;
                sims++;
                continue;
            }
        }
        if (o >= MAXATOMS) return 2;
        out[o++] = t[i++];
        sims++;
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
    if (n < 1 || n > MAXW) return 0;
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

/* --------------------------------------------------------- hash pool */

typedef struct entry { atom *a; int n; struct entry *next; } entry;
#define HSIZE (1 << 18)
static entry *htab[HSIZE];

static uint64_t hash_text(const atom *a, int n)
{
    uint64_t h = 1469598103934665603ULL;
    int i;
    for (i = 0; i < n; i++) {
        h ^= (uint64_t)(unsigned char)a[i].c;
        h *= 1099511628211ULL;
        h ^= (uint64_t)(uint32_t)a[i].lb;
        h *= 1099511628211ULL;
    }
    return h;
}

/* returns the canonical entry for this text, creating if new */
static entry *pool_intern(const atom *a, int n, int *isnew)
{
    uint64_t h = hash_text(a, n);
    entry *e = htab[h % HSIZE];
    *isnew = 0;
    while (e) {
        if (e->n == n && !memcmp(e->a, a, n * sizeof(atom))) return e;
        e = e->next;
    }
    e = malloc(sizeof(entry));
    e->a = malloc(n ? n * sizeof(atom) : 1);
    if (n) memcpy(e->a, a, n * sizeof(atom));
    e->n = n;
    e->next = htab[h % HSIZE];
    htab[h % HSIZE] = e;
    *isnew = 1;
    return e;
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

/* ------------------------------------------------------- pass-free lib */

typedef struct { char name[16]; atom a[2 * MAXW + 4]; int n; } val;

static void mkval(val *v, const char *nm, const char *pre,
                  const char *w, const char *suf, int wruns)
{
    int i, j, pos = 0, run;
    snprintf(v->name, sizeof(v->name), "%s", nm);
    for (i = 0; pre[i]; i++) { v->a[pos].c = pre[i]; v->a[pos].lb = -1; pos++; }
    for (run = 0; run < wruns; run++)
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
    char nm[16];
    mkval(&vals[k++], "eps", "", w, "", 0);
    for (i = 0; i < 14; i++) {
        snprintf(nm, sizeof(nm), "K:%s", consts[i]);
        mkval(&vals[k++], nm, consts[i], w, "", 0);
    }
    mkval(&vals[k++], "w", "", w, "", 1);
    mkval(&vals[k++], "a.w", "a", w, "", 1);
    mkval(&vals[k++], "w.a", "", w, "a", 1);
    mkval(&vals[k++], "b.w", "b", w, "", 1);
    mkval(&vals[k++], "w.b", "", w, "b", 1);
    mkval(&vals[k++], "a.w.b", "a", w, "b", 1);
    mkval(&vals[k++], "b.w.a", "b", w, "a", 1);
    mkval(&vals[k++], "ab.w", "ab", w, "", 1);
    mkval(&vals[k++], "w.ab", "", w, "ab", 1);
    mkval(&vals[k++], "w.w", "", w, "", 2);
    return k;
}

/* ---------------------------------------------------------- w domains */

static char wdom[1024][MAXW + 1];
static int nws = 0;

static void add_w(const char *s)
{
    int i;
    if (strlen(s) > MAXW) return;
    for (i = 0; i < nws; i++) if (!strcmp(wdom[i], s)) return;
    if (nws < 1024) snprintf(wdom[nws++], MAXW + 1, "%s", s);
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

static void gen_families(int jmax)
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
                if (L + pl > MAXW) break;
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

/* ---------------------------------------------------------- reporting */

static long db_hits = 0;
static int db_maxn = 0;
static int fdi_max = -1;
static char fdi_shape[64], fdi_w[64];
static int db_seen_n[MAXW + 1];

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
        if (n > db_maxn) db_maxn = n;
        db_seen_n[n] = 1;
    }
}

/* --------------------------------------------------------------- main */

int main(int argc, char **argv)
{
    int mode = argc > 1 ? atoi(argv[1]) : 3;
    int i, n;
    val vals[32];
    int nvals;
    static char pats[64][MAXW + 1];
    int npats;
    atom *outbuf, *tbuf;
    int Fidx[8], nF;
    int Rfinal[12], nRf;
    static const char *RFIN[] = { "eps", "K:a", "K:b", "K:ab", "w",
                                  "a.w", "w.a", "b.w", "w.b", "a.w.b" };
    static const char *FN[] = { "w", "a.w", "w.a", "b.w", "w.b",
                                "a.w.b", "b.w.a", "w.w" };

    outbuf = malloc(sizeof(atom) * MAXATOMS);
    tbuf = malloc(sizeof(atom) * MAXATOMS);

    if (mode == 12) { gen_all(6); gen_families(8); }
    else if (mode == 23) { gen_all(5); gen_families(8); }
    else { gen_all(5); gen_families(8); gen_random(12, 6, 16);
           add_w("aaba"); add_w("abaa"); add_w("baab"); }
    printf("mode %d: %d inputs\n", mode, nws);

    for (i = 0; i < nws; i++) {
        const char *w = wdom[i];
        atom *lab;
        entry **lvl1, **lvl2;
        int lvl1c = 0, lvl2c = 0;
        n = (int)strlen(w);
        nvals = pfree(w, vals);
        npats = 0;
        { int v, q, dup, z;
          for (v = 0; v < nvals; v++) {
              if (vals[v].n == 0) continue;
              dup = 0;
              for (q = 0; q < npats; q++)
                  if ((int)strlen(pats[q]) == vals[v].n &&
                      !memcmp(pats[q], vals[v].a, vals[v].n)) {
                      dup = 1; break; }
              if (!dup) {
                  for (z = 0; z < vals[v].n; z++)
                      pats[npats][z] = vals[v].a[z].c;
                  pats[npats][vals[v].n] = 0;
                  npats++;
              }
          } }
        nF = 0;
        { int q, v;
          for (q = 0; q < 8; q++)
              for (v = 0; v < nvals; v++)
                  if (!strcmp(vals[v].name, FN[q])) { Fidx[nF++] = v; break; } }
        lab = malloc(sizeof(atom) * n);
        { int z; for (z = 0; z < n; z++) { lab[z].c = w[z]; lab[z].lb = z; } }
        pool_free();
        lvl1 = malloc(sizeof(entry *) * POOL1_CAP);
        lvl2 = malloc(sizeof(entry *) * POOL2_CAP);

        /* ---- level-1 pool (and mode-12 battery) ---- */
        { int fi, p, r, on;
          for (fi = 0; fi < nF; fi++)
              for (p = 0; p < npats; p++) {
                  int plen = (int)strlen(pats[p]);
                  for (r = 0; r < nvals; r++) {
                      int rc, isnew;
                      entry *e;
                      rc = pass_(vals[r].a, vals[r].n, pats[p], plen,
                                 vals[Fidx[fi]].a, vals[Fidx[fi]].n,
                                 outbuf, &on);
                      if (rc == 1) { skipped_undef++; continue; }
                      if (rc == 2) { skipped_overflow++; continue; }
                      if (mode == 12) check(outbuf, on, n, "depth1", w);
                      e = pool_intern(outbuf, on, &isnew);
                      if (isnew && lvl1c < POOL1_CAP) lvl1[lvl1c++] = e;
                      else if (isnew) capped_pool++;
                  }
              } }
        /* ---- level-2 pool (and mode-23 battery) ---- */
        { int t, p, r, on;
          for (t = 0; t < lvl1c; t++)
              for (p = 0; p < npats; p++) {
                  int plen = (int)strlen(pats[p]);
                  for (r = 0; r < nvals; r++) {
                      int rc, isnew;
                      entry *e;
                      rc = pass_(vals[r].a, vals[r].n, pats[p], plen,
                                 lvl1[t]->a, lvl1[t]->n, outbuf, &on);
                      if (rc == 1) { skipped_undef++; continue; }
                      if (rc == 2) { skipped_overflow++; continue; }
                      if (mode == 23) check(outbuf, on, n, "depth2", w);
                      e = pool_intern(outbuf, on, &isnew);
                      if (isnew && lvl2c < POOL2_CAP) lvl2[lvl2c++] = e;
                      else if (isnew) capped_pool++;
                  }
              } }
        if (mode == 3) {
            nRf = 0;
            { int q, v;
              for (q = 0; q < 10; q++)
                  for (v = 0; v < nvals; v++)
                      if (!strcmp(vals[v].name, RFIN[q])) {
                          Rfinal[nRf++] = v; break; } }
            /* (a) 3-chains */
            { int t, r, p, on;
              for (t = 0; t < lvl2c; t++)
                  for (r = 0; r < nRf; r++)
                      for (p = 0; p < npats; p++) {
                          int plen = (int)strlen(pats[p]);
                          int rc = pass_(vals[Rfinal[r]].a,
                                         vals[Rfinal[r]].n, pats[p],
                                         plen, lvl2[t]->a, lvl2[t]->n,
                                         outbuf, &on);
                          if (rc == 1) { skipped_undef++; continue; }
                          if (rc == 2) { skipped_overflow++; continue; }
                          check(outbuf, on, n, "chain3", w);
                      } }
            /* (b) deepR: 2-pass block spliced into V(0) */
            { int t, p, on;
              for (t = 0; t < lvl2c; t++)
                  for (p = 0; p < npats; p++) {
                      int plen = (int)strlen(pats[p]);
                      int rc = pass_(lvl2[t]->a, lvl2[t]->n, pats[p],
                                     plen, lab, n, outbuf, &on);
                      if (rc == 1) { skipped_undef++; continue; }
                      if (rc == 2) { skipped_overflow++; continue; }
                      check(outbuf, on, n, "deepR", w);
                  } }
            /* (c) Ctarget: 2-pass block into C(V0,K:a,V0) */
            { atom *targ; int tn = 0, t, p, on;
              targ = malloc(sizeof(atom) * (2 * n + 1));
              memcpy(targ, lab, n * sizeof(atom));
              targ[tn].c = 'a'; targ[tn].lb = -1; tn++;
              memcpy(targ + tn, lab, n * sizeof(atom)); tn += n;
              for (t = 0; t < lvl2c; t++)
                  for (p = 0; p < npats; p++) {
                      int plen = (int)strlen(pats[p]);
                      int rc = pass_(lvl2[t]->a, lvl2[t]->n, pats[p],
                                     plen, targ, tn, outbuf, &on);
                      if (rc == 1) { skipped_undef++; continue; }
                      if (rc == 2) { skipped_overflow++; continue; }
                      check(outbuf, on, n, "Ctarget", w);
                  }
              free(targ); }
            /* (d) C-compositions: 2-pass . 1-pass, both orders */
            { int t2, t1, on;
              for (t2 = 0; t2 < lvl2c && t2 < 200; t2++)
                  for (t1 = 0; t1 < lvl1c && t1 < 100; t1++) {
                      on = lvl2[t2]->n + lvl1[t1]->n;
                      if (on > MAXATOMS) continue;
                      memcpy(tbuf, lvl2[t2]->a,
                             lvl2[t2]->n * sizeof(atom));
                      memcpy(tbuf + lvl2[t2]->n, lvl1[t1]->a,
                             lvl1[t1]->n * sizeof(atom));
                      check(tbuf, on, n, "C(2,1)", w);
                      memcpy(tbuf, lvl1[t1]->a,
                             lvl1[t1]->n * sizeof(atom));
                      memcpy(tbuf + lvl1[t1]->n, lvl2[t2]->a,
                             lvl2[t2]->n * sizeof(atom));
                      check(tbuf, on, n, "C(1,2)", w);
                  } }
        }
        free(lvl1); free(lvl2); free(lab);
    }
    printf("sims=%ld undef-skipped=%ld overflow-skipped=%ld "
           "pool-capped=%ld\n", sims, skipped_undef, skipped_overflow,
           capped_pool);
    printf("max FDI length: %d (shape %s, w %s)\n", fdi_max,
           fdi_shape, fdi_w);
    printf("DB realizations: %ld; max |w|: %d; sizes: ",
           db_hits, db_maxn);
    { int z, first = 1;
      for (z = 0; z <= MAXW; z++)
          if (db_seen_n[z]) {
              printf("%s%d", first ? "" : ",", z); first = 0;
          }
      printf("\n"); }
    free(outbuf); free(tbuf);
    return 0;
}

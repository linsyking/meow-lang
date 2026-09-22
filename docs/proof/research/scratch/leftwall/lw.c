/* lw.c -- leftwall round 1: reduction-chain machine verification.
 *
 * Semantics: def:subst (greedy leftmost-first, never rescanning).
 * Oracles: tau (truncate at leftmost "aa"), used ONLY inside composites that
 *          are supposed to be L-expressions given the oracle.
 *
 * Modes (argv[1]):
 *   chainA   -- tau in L  ==> P_b in L   (letter reduction; the day's new bridge)
 *   chainB   -- tau in L  ==> crux in L  (coordination: pad + anchored needle + strip)
 *   chainC   -- P_b equivalence cluster ([eps/S(w)]w == P_b, S = suffix from 1st b)
 *   honestyW -- W == [a/b]_1 on all binary; and W's a-count on W_2 == S+1 (equal-slope witness)
 *   marking  -- paper thm:marking with crux-oracle == once-node [X/Y]_1 (semantics calibration)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static long FAIL = 0, OK = 0;

static char *xstrdup(const char *s){ char *r = malloc(strlen(s)+1); strcpy(r,s); return r; }
static char *cat3(const char*a,const char*b,const char*c){
    char *r = malloc(strlen(a)+strlen(b)+strlen(c)+1);
    strcpy(r,a); strcat(r,b); strcat(r,c); return r;
}

/* ---- def:subst: [A/B]C, greedy leftmost-first, never rescans inserted text ---- */
static char *subst(const char *A, const char *B, const char *C){
    size_t la=strlen(A), lb=strlen(B), lc=strlen(C);
    if(lb==0){ fprintf(stderr,"subst: empty pattern\n"); exit(1); }
    size_t cap = lc*(la+1)+la+1;
    char *out = malloc(cap); size_t op=0, p=0;
    while(p<lc){
        if(p+lb<=lc && memcmp(C+p,B,lb)==0){ memcpy(out+op,A,la); op+=la; p+=lb; }
        else out[op++]=C[p++];
    }
    out[op]=0; return out;
}

/* ---- once-node [A/B]_1 (def:once) ---- */
static char *once(const char *A, const char *B, const char *C){
    size_t la=strlen(A), lb=strlen(B), lc=strlen(C);
    if(lb==0){ fprintf(stderr,"once: empty pattern\n"); exit(1); }
    for(size_t p=0; p+lb<=lc; p++){
        if(memcmp(C+p,B,lb)==0){
            char *out = malloc(lc-lb+la+1);
            memcpy(out,C,p); memcpy(out+p,A,la); memcpy(out+p+la,C+p+lb,lc-p-lb);
            out[lc-lb+la]=0; return out;
        }
    }
    return xstrdup(C);
}

/* ---- comma code, x = 'b' (enc^2 : c |-> block 'bc') ---- */
static char *enc2(const char *w){ return subst("ba","a", subst("bb","b", w)); }
static char *dec2(const char *w){ return subst("b","bb", subst("a","ba", w)); }

/* ---- W (prop:del-leftmost), run order right-to-left of the paper's display ---- */
static char *W(const char *w){
    char *t1 = subst("aa","a",  w);        /* a -> aa        */
    char *t2 = subst("ab","b",  t1);        /* b -> ab        */
    char *t3 = subst("b", "ba", t2);        /* ba -> b        */
    char *t4 = subst("ab","aa", t3);        /* aa -> ab       */
    char *t5 = subst("a", "ab", t4);        /* ab -> a        */
    free(t1);free(t2);free(t3);free(t4); return t5;
}

/* ---- targets / oracles ---- */
static char *tau(const char *T){                 /* prefix before leftmost "aa" */
    const char *q = strstr(T,"aa");
    if(!q) return xstrdup(T);
    char *r = malloc(q-T+1); memcpy(r,T,q-T); r[q-T]=0; return r;
}
static char *pb(const char *w){                  /* longest b-free prefix */
    const char *q = strchr(w,'b');
    if(!q) return xstrdup(w);
    char *r = malloc(q-w+1); memcpy(r,w,q-w); r[q-w]=0; return r;
}
static char *crux(const char *T){ return once("babba","baa",T); }  /* [babba/baa]_1 */

/* ---- batteries ---- */
static char **all_binary(int maxlen, int *n_out){
    int cap = 1; for(int i=0;i<=maxlen;i++) cap*=2;
    char **v = malloc(sizeof(char*)*cap); int n=0;
    for(int L=0; L<=maxlen; L++){
        for(int m=0;m<(1<<L);m++){
            char *s = malloc(L+1);
            for(int i=0;i<L;i++) s[i] = (m>>(L-1-i))&1 ? 'b':'a';
            s[L]=0; v[n++]=s;
        }
    }
    *n_out=n; return v;
}
/* marked texts: products of tokens ba|bb|baa, <= k tokens (DFS, short first) */
static void mark_enum(int k, char ***arr, int *n){
    int cap = 4000000;
    char **v = malloc(sizeof(char*)*cap); int n_=0;
    char *buf = malloc(3*k+1);
    // BFS by token count
    v[n_++]=xstrdup("");
    int lvl_start=0, lvl_end=1;
    for(int t=0;t<k;t++){
        for(int i=lvl_start;i<lvl_end;i++){
            const char *toks[3] = {"ba","bb","baa"};
            for(int j=0;j<3;j++){
                if(n_>=cap){fprintf(stderr,"mark_enum overflow\n");exit(1);}
                char *s = malloc(strlen(v[i])+4);
                strcpy(s,v[i]); strcat(s,toks[j]);
                v[n_++]=s;
            }
        }
        lvl_start=lvl_end; lvl_end=n_;
    }
    *arr=v; *n=n_;
}
static void rand_str(char *s, int L){ for(int i=0;i<L;i++) s[i] = (rand()>>5)&1 ? 'b':'a'; s[L]=0; }

/* ================= mode: chainA -- tau ==> P_b ================= */
/* F(w) = [eps/b]( tau( [baa/bb]( enc2(w) ) ) )   must equal  longest-b-free-prefix(w) */
static void chainA(void){
    int n; char **v = all_binary(11, &n);
    for(int i=0;i<n;i++){
        char *e  = enc2(v[i]);
        char *m  = subst("baa","bb", e);
        char *tr = tau(m);
        char *f  = subst("", "b", tr);
        char *p  = pb(v[i]);
        if(strcmp(f,p)){ FAIL++; if(FAIL<=5) printf("chainA FAIL w=%s got=%s want=%s\n", v[i], f, p); }
        else OK++;
        free(e);free(m);free(tr);free(f);free(p);
    }
    for(int i=0;i<200000;i++){
        int L = 1 + rand()%50; char s[64]; rand_str(s,L);
        char *e  = enc2(s); char *m = subst("baa","bb", e);
        char *tr = tau(m);   char *f = subst("", "b", tr);
        char *p  = pb(s);
        if(strcmp(f,p)){ FAIL++; if(FAIL<=5) printf("chainA FAIL(rand) w=%s got=%s want=%s\n", s, f, p); }
        else OK++;
        free(e);free(m);free(tr);free(f);free(p);
    }
    printf("[chainA] tau => P_b : %ld ok, %ld FAIL\n", OK, FAIL);
}

/* ================= mode: chainB -- tau ==> crux ================= */
/* crux(T) = dec2( [eps/aa]( [R'/N']( 'aa' . enc2(T) ) ) )
 * N' = 'aa' . enc2(tau(T)) . enc2('aa')            ('aa' fresh in enc2-images)
 * R' = 'aa' . enc2(tau(T)) . enc2('abba')
 * no-site case: needle longer than scrutinee => inert; pad stripped => identity. */
static void chainB(void){
    int n; char **v; mark_enum(5, &v, &n);
    // battery: all marked texts <= 5 tokens
    for(int i=0;i<n;i++){
        const char *T = v[i];
        char *e  = enc2(T);
        char *S  = cat3("aa", e, "");
        char *tr = tau(T);
        char *etr= enc2(tr);
        char *N  = cat3("aa", etr, "baba");       /* enc2("aa") = "baba"  */
        char *R  = cat3("aa", etr, "babbbba");   /* enc2("abba")         */
        char *o1 = subst(R, N, S);
        char *o2 = subst("", "aa", o1);
        char *f  = dec2(o2);
        char *c  = crux(T);
        if(strcmp(f,c)){ FAIL++; if(FAIL<=8) printf("chainB FAIL T=%s got=%s want=%s\n", T, f, c); }
        else OK++;
        free(e);free(S);free(tr);free(etr);free(N);free(R);free(o1);free(o2);free(f);free(c);
    }
    // random longer marked texts (6..10 tokens)
    for(int i=0;i<50000;i++){
        int k = 6 + rand()%5;
        char T[64]; T[0]=0;
        const char *toks[3] = {"ba","bb","baa"};
        for(int j=0;j<k;j++) strcat(T, toks[rand()%3]);
        char *e  = enc2(T);
        char *S  = cat3("aa", e, "");
        char *tr = tau(T);
        char *etr= enc2(tr);
        char *N  = cat3("aa", etr, "baba");
        char *R  = cat3("aa", etr, "babbbba");
        char *o1 = subst(R, N, S);
        char *o2 = subst("", "aa", o1);
        char *f  = dec2(o2);
        char *c  = crux(T);
        if(strcmp(f,c)){ FAIL++; if(FAIL<=8) printf("chainB FAIL(rand) T=%s got=%s want=%s\n", T, f, c); }
        else OK++;
        free(e);free(S);free(tr);free(etr);free(N);free(R);free(o1);free(o2);free(f);free(c);
    }
    printf("[chainB] tau => crux : %ld ok, %ld FAIL\n", OK, FAIL);
}

/* ================= mode: chainC -- P_b cluster ================= */
/* [eps/S(w)]w == P_b(w), S(w) = suffix from first b (inclusive). */
static void chainC(void){
    int n; char **v = all_binary(11, &n);
    for(int i=0;i<n;i++){
        const char *w = v[i];
        const char *q = strchr(w,'b');
        if(!q) continue;                 /* S undefined; guarded by if-node in L */
        char *S = xstrdup(q);
        char *f = subst("", S, w);
        char *p = pb(w);
        if(strcmp(f,p)){ FAIL++; if(FAIL<=5) printf("chainC FAIL w=%s got=%s want=%s\n", w, f, p); }
        else OK++;
        free(S);free(f);free(p);
    }
    for(int i=0;i<100000;i++){
        int L = 1 + rand()%40; char s[64]; rand_str(s,L);
        if(!strchr(s,'b')) continue;
        char *f = subst("", strchr(s,'b'), s);
        char *p = pb(s);
        if(strcmp(f,p)){ FAIL++; if(FAIL<=5) printf("chainC FAIL(rand) w=%s\n", s); }
        else OK++;
        free(f);free(p);
    }
    printf("[chainC] [eps/S]w == P_b : %ld ok, %ld FAIL\n", OK, FAIL);
}

/* ================= mode: honestyW ================= */
static void honestyW(void){
    int n; char **v = all_binary(11, &n);
    for(int i=0;i<n;i++){
        char *f = W(v[i]);
        char *c = once("a","b",v[i]);
        if(strcmp(f,c)){ FAIL++; if(FAIL<=5) printf("honestyW FAIL w=%s got=%s want=%s\n", v[i], f, c); }
        else OK++;
        free(f);free(c);
    }
    for(int i=0;i<100000;i++){
        int L = 1 + rand()%49; char s[64]; rand_str(s,L);
        char *f = W(s); char *c = once("a","b",s);
        if(strcmp(f,c)){ FAIL++; if(FAIL<=5) printf("honestyW FAIL(rand) w=%s\n", s); }
        else OK++;
        free(f);free(c);
    }
    printf("[honestyW] W == [a/b]_1 : %ld ok, %ld FAIL\n", OK, FAIL);
    /* equal-slope witness: a-count of W(a^i b a^j b a^k) == S+1 (function of S alone) */
    long ok2=0, bad2=0;
    for(int i=1;i<=12;i++)for(int j=1;j<=12;j++)for(int k=1;k<=12;k++){
        char s[128]; snprintf(s,sizeof s,"%.*s", i, "aaaaaaaaaaaa");
        char b2[3]={ 'b',0,0 };
        s[i]='b'; int p=i+1;
        for(int t=0;t<j;t++) s[p++]='a'; s[p++]='b';
        for(int t=0;t<k;t++) s[p++]='a'; s[p]=0;
        char *f = W(s);
        int na=0; for(int t=0;f[t];t++) if(f[t]=='a') na++;
        if(na != i+j+k+1){ bad2++; if(bad2<=5) printf("honestyW slope FAIL (%d,%d,%d): #a=%d\n",i,j,k,na); }
        else ok2++;
        free(f);
    }
    printf("[honestyW] W a-count on W_2 == S+1 : %ld ok, %ld FAIL\n", ok2, bad2);
}

/* ================= mode: marking (paper thm:marking, crux as oracle) ================= */
/* [X/Y]_1 Z == dec2( [X'/A0] [N/M] [A0/M]_1 [N... wait: [N/M]] enc2(Z) )
 * run order: enc2(Z); [M/N]; [A0/M]_1 (=crux oracle); [N/M]; [X'/A0]; dec2 */
static void marking(void){
    /* random X,Y,Z over {a,b}, Y != eps; compare against once(X,Y,Z) */
    for(int it=0; it<4000; it++){
        char X[16],Y[16],Z[32];
        int lx = rand()%5, ly = 1+rand()%3, lz = rand()%8;
        rand_str(X,lx); rand_str(Y,ly); rand_str(Z,lz);
        char *Ez = enc2(Z);
        char *N  = enc2(Y);
        char *t1 = subst("baa", N, Ez);                   /* [M/N]: pattern N, repl M */
        /* order per paper: [M/N] then oracle [A0/M]_1 then [N/M] then [X'/A0].
         * t1 = [M/N] enc2(Z).  Oracle [A0/M]_1 = crux: */
        char *t2 = crux(t1);
        char *t3 = subst(N, "baa", t2);                   /* [N/M] */
        char *Xp = enc2(X);
        char *t4 = subst(Xp, "babba", t3);                /* [X'/A0] */
        char *f  = dec2(t4);
        char *c  = once(X, Y, Z);
        if(strcmp(f,c)){ FAIL++; if(FAIL<=8) printf("marking FAIL X=%s Y=%s Z=%s got=%s want=%s\n",X,Y,Z,f,c); }
        else OK++;
        free(Ez);free(t1);free(N);free(t2);free(t3);free(Xp);free(t4);free(f);free(c);
    }
    printf("[marking] paper pipeline(+crux oracle) == [X/Y]_1 : %ld ok, %ld FAIL\n", OK, FAIL);
}

int main(int argc, char **argv){
    if(argc<2){ fprintf(stderr,"usage: %s chainA|chainB|chainC|honestyW|marking\n", argv[0]); return 1; }
    srand(20260922);
    if(!strcmp(argv[1],"chainA")) chainA();
    else if(!strcmp(argv[1],"chainB")) chainB();
    else if(!strcmp(argv[1],"chainC")) chainC();
    else if(!strcmp(argv[1],"honestyW")) honestyW();
    else if(!strcmp(argv[1],"marking")) marking();
    else { fprintf(stderr,"unknown mode\n"); return 1; }
    return FAIL?1:0;
}

/* rev-split ROUND 6 -- THE PO WRITE-OUT + THE CROSS-K RECURRENCE BATTERY
 * (charter CHARTER_po.md).  Family D(k;3).
 *
 * Modes:
 *  [po1]  window-anatomy + fired-set machine checks for Lemma PO:
 *         (A) greedy-leftmost == max-disjoint occurrences (Lane D's
 *             firing-count lemma) on random scrutinees incl. replicated
 *             ones, random multi-b patterns;
 *         (B) replica-translate pinning: on T = [X/'b']X (k copies of
 *             the input), multi-b patterns with interior runs matching
 *             a site value fire once per copy at the SAME offset
 *             relative to the copy start (boundary-spanning allowed)
 *             -- PO-3's per-copy translate, verified exactly.
 *  [rec]  the cross-k recurrence battery: per run SLOT (matched across
 *         k by left-index / right-index / absolute-label-signature /
 *         top-relative-label-signature), the value sequence over
 *         consecutive k must be annihilated by a recurrence from
 *             char = (x-1)^a . prod_{d in S}(x^{L_d} - 3^{d L_d})
 *                    . [(x^{L_a}-1)/(x-1)]
 *         a in {1,2}, S subset of {1,2,3,4}, L in {1..6} (periods of
 *         V-fixed moduli: ord_p(3)); suffix-testing for eventual
 *         pre-periods.  Battery + adversarial teeth + blind-spot
 *         demos + random compositions (calm ones; selection bias
 *         disclosed).  The recurrence ORDER is the degree-family
 *         count: a LOWER bound probe of the ledger bound M_V.
 *
 * Every log's first line is the full invocation (discipline).
 * Machine checks CONFIRM hand derivations; they do not replace them.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP      (1 << 21)
#define SBCAP    (1 << 16)
#define MAXD     12
#define NBUF     (3 * MAXD + 4)
#define NCONST   12

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aaa", "abb", "bab", "abba", "aaa"};

static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci) { N[nn].t=0; N[nn].a=ci; return nn++; }
static int nv(void)   { N[nn].t=1; return nn++; }
static int nc(int a,int b){ N[nn].t=2; N[nn].a=a; N[nn].b=b; return nn++; }
static int ns(int r,int p,int f){ N[nn].t=3; N[nn].a=r; N[nn].b=p; N[nn].c=f; return nn++; }

static uint64_t rs;
static uint32_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (uint32_t)(rs>>32); }
static int ri(int n){ return (int)(rnd()%(uint64_t)n); }

static int eval(int e,int s,const char*w,int wl){
    Node*n=&N[e]; if(s>=MAXD) return -2; char*o=buf[s];
    if(n->t==0){int l=strlen(CONSTS[n->a]);memcpy(o,CONSTS[n->a],l);return l;}
    if(n->t==1){memcpy(o,w,wl);return wl;}
    if(n->t==2){int l1=eval(n->a,s+1,w,wl);int l2=eval(n->b,s+2,w,wl);
        if(l1<0)return l1; if(l2<0)return l2; if(l1+l2>CAP)return -2;
        memcpy(o,buf[s+1],l1); memcpy(o+l1,buf[s+2],l2); return l1+l2;}
    int lf=eval(n->c,s+1,w,wl), lp=eval(n->b,s+2,w,wl), lr=eval(n->a,s+3,w,wl);
    if(lf<0)return lf; if(lp<0)return lp; if(lr<0)return lr; if(lp==0)return -1;
    const char*T=buf[s+1],*P=buf[s+2],*A=buf[s+3];
    int tl=lf,pl=lp,al=lr,m=pl,i=0,ol=0;
    while(i<tl){ if(i+m<=tl&&memcmp(T+i,P,m)==0){ if(ol+al>CAP)return -2;
        memcpy(o+ol,A,al);ol+=al;i+=m;} else { if(ol+1>CAP)return -2; o[ol++]=T[i++];}}
    return ol;
}
static int runs_of(const char*s,int l,long long*out,long maxr){
    long n=0; long long cur=0;
    for(long i=0;i<=(long)l;i++){
        if(i<(long)l&&s[i]=='a') cur++;
        else { if(n<maxr) out[n]=cur; n++; cur=0; }
    }
    return (int)n;
}
static long long pw(int B,int e){ long long r=1; for(int i=0;i<e;i++) r*=B; return r; }
static void mkwk(char*w,int*wl,int k,int B){
    *wl=0;
    for(int t=0;t<=k;t++){
        long long len = t?pw(B,t):1;
        for(long long q=0;q<len;q++) w[(*wl)++]='a';
        if(t<k) w[(*wl)++]='b';
    }
}
static long long checks, fails;
static void ck(const char*what,long long pred,long long act,const char*det){
    checks++;
    if(pred!=act){ fails++;
        if(fails<=20) printf("  FAIL %s: pred %lld act %lld [%s]\n",
                             what,pred,act,det?det:""); }
}
static void ck_le(const char*what,long long act,long long lim,const char*det){
    checks++;
    if(act>lim){ fails++;
        if(fails<=20) printf("  FAIL %s: act %lld > lim %lld [%s]\n",
                             what,act,lim,det?det:""); }
}

/* ---------- battery construction (from ledger3) ---------- */
typedef struct { int e; const char*name; } Ent;
static int build_battery(Ent*Es){
    int n=0; nn=0; int X=nv();
    int mrg   = ns(nk(0), nk(2), X);
    int halv  = ns(nk(1), nk(3), X);
    int third = ns(nk(1), nk(7), X);
    int dbl   = ns(nk(3), nk(1), X);
    int shv   = ns(nk(2), nk(4), X);
    int drp   = ns(nk(0), nc(nk(1),nk(2)), X);
    int Rl    = nc(mrg, nk(2));
    int Elek  = ns(Rl, nk(2), X);
    int Eprod = ns(mrg, nk(3), X);
    int patL = nc(nk(2), nc(mrg, nk(1)));
    int Dlast= ns(nk(0), patL, nc(nc(X,mrg),nk(1)));
    int patF = nc(nc(nk(1), mrg), nk(2));
    int Dfirst=ns(nk(0), patF, nc(nc(nk(1),mrg),X));
    int Elast = ns(nk(0), nk(2), halv);
    int mrgbmrg = nc(nc(mrg,nk(2)),mrg);
    int Ecbox = ns(nk(2), nc(Elast,nk(2)), mrgbmrg);
    int Esmm  = ns(nk(0), nc(nk(2),mrg), Ecbox);
    int Eh2   = ns(nk(1), nk(3), Esmm);
    int DblM  = ns(nk(0), nk(2), dbl);
    int X1=nv(), X2=nv();
    int decb  = ns(X1, nk(2), X2);            /* [X/'b']X */
    Es[n].e=mrg;    Es[n++].name="mrg";
    Es[n].e=halv;   Es[n++].name="half";
    Es[n].e=third;  Es[n++].name="third";
    Es[n].e=dbl;    Es[n++].name="dbl";
    Es[n].e=shv;    Es[n++].name="shave";
    Es[n].e=drp;    Es[n++].name="dropab";
    Es[n].e=Elek;   Es[n++].name="Eleak";
    Es[n].e=Eprod;  Es[n++].name="Eprod";
    Es[n].e=Dlast;  Es[n++].name="dlast";
    Es[n].e=Dfirst; Es[n++].name="dfirst";
    Es[n].e=Elast;  Es[n++].name="Elast";
    Es[n].e=Ecbox;  Es[n++].name="Ecbox";
    Es[n].e=Esmm;   Es[n++].name="Esmm";
    Es[n].e=Eh2;    Es[n++].name="Eh2";
    Es[n].e=DblM;   Es[n++].name="dblmerge";
    Es[n].e=decb;   Es[n++].name="decb";
    return n;
}
static int gen_expr(int d){
    if(d<=0){ return ri(2)? nv() : nk(ri(7)); }
    int t=ri(12);
    if(t<2) return nv();
    if(t<4) return nk(ri(7));
    if(t<8) return nc(gen_expr(d-1),gen_expr(d-1));
    return ns(gen_expr(d-1),gen_expr(d-1),gen_expr(d-1));
}

/* ---------- [po1] window machinery ---------- */
/* find greedy leftmost disjoint occurrences of p (length L) in T;
   returns count, fills pos[] */
static int greedy_occ(const char*T,int tl,const char*p,int pl,int*pos,int maxw){
    int n=0,i=0;
    while(i+pl<=tl){
        if(!memcmp(T+i,p,pl)){ if(n<maxw)pos[n]=i; n++; i+=pl; }
        else i++;
    }
    return n;
}
/* max # disjoint occurrences, DP over occurrence start positions */
static int max_disjoint(const char*T,int tl,const char*p,int pl){
    int occ[8192], noc=0;
    for(int i=0;i+pl<=tl;i++) if(!memcmp(T+i,p,pl)) occ[noc++]=i;
    /* dp over positions: best[j] = max disjoint using occurrences >= j */
    if(!noc) return 0;
    /* greedy-by-start IS optimal for equal lengths; but compute DP
       independently: process occurrences sorted (already), dp[i] =
       max( dp[i+1], 1 + dp[next i' with occ[i'] >= occ[i]+pl] ) */
    int dp[8193];
    dp[noc]=0;
    for(int i=noc-1;i>=0;i--){
        /* binary search first occurrence start >= occ[i]+pl */
        int lo=i+1,hi=noc,target=occ[i]+pl;
        while(lo<hi){ int mid=(lo+hi)/2; if(occ[mid]<target)lo=mid+1; else hi=mid; }
        int cont = dp[lo]+1;
        dp[i] = dp[i+1] > cont ? dp[i+1] : cont;
    }
    return dp[0];
}
static void mode_po1(uint64_t seed,int trials){
    printf("=== [po1] window anatomy + fired-set checks (Lemma PO) ===\n");
    rs=seed;
    static char w[8192];
    /* (A) greedy == max-disjoint on random scrutinees/patterns */
    {
        int bad=0, tot=0;
        int pos[8192];
        for(int t=0;t<trials;t++){
            nn=0;
            int F=gen_expr(2+ri(2));            /* scrutinee */
            int k=3+ri(3);
            int wl; mkwk(w,&wl,k,3);
            int tl=eval(F,0,w,wl); if(tl<0||tl<8) continue;
            char pat[24]; int pl=0;
            /* random multi-b pattern from small constants: 2-3 b's */
            int nb=2+ri(2);
            for(int b=0;b<nb;b++){
                int a0=ri(3);
                for(int q=0;q<a0;q++) pat[pl++]='a';
                pat[pl++]='b';
            }
            int aT=ri(3);
            for(int q=0;q<aT;q++) pat[pl++]='a';
            if(!pl) continue;
            int g=greedy_occ(buf[0],tl,pat,pl,pos,8192);
            int m=max_disjoint(buf[0],tl,pat,pl);
            tot++;
            if(g!=m){ bad++;
                printf("  MISMATCH greedy=%d maxdisjoint=%d (tl=%d pl=%d)\n",
                       g,m,tl,pl); }
        }
        ck("greedy==max-disjoint",0,bad,"random multi-b");
        printf("  (A) greedy == max-disjoint: %d cases, %d mismatches\n",tot,bad);
    }
    /* (B) replica-translate + threshold pinning on T = [X/'b']X.
       OUT = a^{3^0} X a^{3^1} X ... X a^{3^k}, k copies of X; copy
       edges merge (round-7 correction, coordinator's derivation):
       the run before copy c's separator 0 is 2 at c = 0 (site-0 run
       + copy head) and 3^k + 3^c + 1 for c >= 1 (copy (c-1)'s tail
       + site-c run + copy c's head); interior runs of a copy are its
       own site runs 3^j.  A multi-b pattern a^{c0} b a^{c1} b a^{c2}
       with c1 = 3^si fires at (sep si, sep si+1) of copy c iff the
       flanks hold: run before beta_0 >= c0 (for si=0: c=0 fires iff
       2 >= c0; c>=1 always fires: 3^k+3^c+1 >= 3^k -- a threshold
       set in the replica index; for si>=1: 3^si >= c0,
       k-independent) and run after >= c2.  Expected fired set is
       computed by this hand analysis; the machine verifies the
       GREEDY windows equal it exactly. */
    {
        static char w[SBCAP];
        int tot=0, bad=0;
        struct { const char*pat; int c0,c1,c2,si; } P[]={
            {"abaaab",     1,3,0, 0},
            {"aabaaab",    2,3,0, 0},
            {"abaaaba",    1,3,1, 0},
            {"aaabaaab",   3,3,0, 0},
            {"aaabaaaaaaaaab", 3,9,0, 1},
            {"aaaabaaab",   4,3,0, 0},
        };
        for(int pi=0;pi<(int)(sizeof P/sizeof P[0]);pi++){
            const char*pat=P[pi].pat; int pl=strlen(pat);
            int c0=P[pi].c0, c1=P[pi].c1, c2=P[pi].c2, si=P[pi].si;
            for(int k=4;k<=7;k++){
                nn=0; int X1=nv(),X2=nv();
                int decb=ns(X1,nk(2),X2);
                int wl; mkwk(w,&wl,k,3);
                int tl=eval(decb,0,w,wl); if(tl<0) continue;
                int pos[8192];
                int g=greedy_occ(buf[0],tl,pat,pl,pos,8192);
                /* copy geometry */
                long long cstart[64]; int nc_=0;
                long long site[16]; for(int j=0;j<=k;j++) site[j]= j?pw(3,j):1;
                long long xlen=0;
                for(int j=0;j<=k;j++){ xlen+=site[j]; if(j<k)xlen++; }
                long long posx=0;
                for(int j=0;j<k;j++){
                    posx+=site[j];
                    cstart[nc_++]=posx;
                    posx+=xlen;
                }
                /* expected: copy c fires iff k >= si+2 (seps si,si+1
                   exist) and run-before >= c0 and run-after >= c2.
                   run before beta_0: si==0 ? merged 3^c+1 : copy run
                   3^si.  run after beta_1: copy run 3^(si+1) (si+1<k)
                   -- the tail flank.  Window start = beta_0 - c0,
                   beta_0 = cstart[c] + offset of sep si in X. */
                long long sepoff=0;
                for(int j=0;j<=si;j++){ sepoff+=site[j]; sepoff++; }
                /* sepoff = chars from copy start to just past sep si:
                   runs 0..si plus (si+1) b's. beta_0 sits at
                   cstart[c]+sepoff-1. */
                long long exp_[64]; int ne=0;
                for(int c=0;c<nc_;c++){
                    long long before = (si==0)
                        ? ((c==0)? 2 : (site[k]+site[c]+1))
                        : site[si];
                    long long after  = site[si+1];
                    if(before>=c0 && after>=c2) exp_[ne++]=cstart[c]+sepoff-1-c0;
                }
                tot++;
                int ok = (ne==g);
                for(int i=0;i<ne&&ok;i++) ok=(pos[i]==exp_[i]);
                if(!ok){ bad++;
                    printf("  (B) FAIL pat=%s k=%d: greedy g=%d expected %d",
                           pat,k,g,ne);
                    if(g==ne){ printf(" [");
                        for(int i=0;i<g;i++) printf(" %d/%lld",pos[i],exp_[i]);
                        printf(" ]"); }
                    printf("\n");
                } else
                    printf("  (B) pat=%-22s k=%d: %d windows == expected "
                           "(copies fired: %s, offset %lld)\n",
                           pat,k,g, ne==nc_?"all":"threshold",
                           ne? exp_[0]-cstart[0] : 0);
            }
        }
        ck("replica-translate",0,bad,"[X/'b']X multi-b");
        printf("  (B) replica-translate pinning: %d cases, %d failures\n",tot,bad);
    }
}

/* ---------- [rec] recurrence machinery ---------- */
#define MAXORD 14
typedef struct { int n; long long c[MAXORD+1]; } Poly;   /* c[0..n], c[n]=1 */
static Poly POL[16384]; static int NPOL;
static void pmul(Poly*r,const Poly*a,const Poly*b){
    Poly t; memset(&t,0,sizeof t);
    t.n=a->n+b->n;
    for(int i=0;i<=a->n;i++)for(int j=0;j<=b->n;j++)
        t.c[i+j]+=a->c[i]*b->c[j];
    *r=t;
}
static void build_family(void){
    NPOL=0;
    Poly x1; x1.n=1; x1.c[0]=-1; x1.c[1]=1;               /* x-1 */
    for(int a=1;a<=2;a++){
        Poly aff;                                          /* (x-1)^a */
        if(a==1) aff=x1;
        else { Poly t=x1; pmul(&aff,&t,&x1); }
        for(int S=0;S<16;S++){                            /* S subset {1,2,3,4} */
            int ds[4],nd=0;
            for(int d=1;d<=4;d++) if(S&(1<<(d-1))) ds[nd++]=d;
            /* enumerate L_d in 1..6 with sum <= 9 (|S|>=1) */
            int Ls[4];
            /* iterate over L assignments */
            int total=1;
            for(int i=0;i<nd;i++) total*=6;
            for(int asg=0;asg<total;asg++){
                int x=asg,sumL=0;
                for(int i=0;i<nd;i++){ Ls[i]=1+(x%6); x/=6; sumL+=Ls[i]; }
                if(nd&&sumL>9) continue;
                Poly base=aff;
                int okp=1;
                for(int i=0;i<nd;i++){
                    Poly f; memset(&f,0,sizeof f);
                    f.n=Ls[i]; f.c[0]=-pw(3,ds[i]*Ls[i]); f.c[Ls[i]]=1;
                    if(base.n+f.n>MAXORD){ okp=0; break; }
                    Poly r; pmul(&r,&base,&f); base=r;
                }
                if(!okp) continue;
                for(int La=0;La<=6;La++){                  /* additive period */
                    Poly p=base;
                    if(La>=2){
                        Poly f; memset(&f,0,sizeof f);
                        /* (x^La - 1)/(x-1) = 1+x+...+x^{La-1} */
                        for(int i=0;i<La;i++) f.c[i]=1; f.n=La-1;
                        if(p.n+f.n>MAXORD) continue;
                        Poly r; pmul(&r,&p,&f); p=r;
                    }
                    if(NPOL<16384){ POL[NPOL++]=p; }
                }
            }
        }
    }
    /* sort by order */
    for(int i=0;i<NPOL;i++)for(int j=i+1;j<NPOL;j++)
        if(POL[j].n<POL[i].n){ Poly t=POL[i];POL[i]=POL[j];POL[j]=t; }
}
/* check: does poly annihilate v[t0..t0+n] for all shifts in [t0, R-n-1]? */
static int annihilates(const Poly*p,const long long*v,int R,int t0){
    int n=p->n;
    if(t0+n>=R) return 0;
    for(int t=t0;t+n<R;t++){
        __int128 s=0;
        for(int i=0;i<=n;i++) s+=( __int128)p->c[i]*(__int128)v[t+i];
        if(s!=0) return 0;
    }
    return 1;
}
/* minimal order annihilator; strict: full window (t0=0) only;
   loose: any suffix (for eventual pre-periods).  mineq: minimum
   number of equations (R-t0-n) a pass must carry -- high-order
   polys on short windows are 1-2 equation coincidences (measured:
   the period-7 adversarial passes at order 12 with 2 equations).
   *ppi: poly index. */
static int rec_test3(const long long*v,int R,int strict,int mineq,int*ppi){
    for(int pi=0;pi<NPOL;pi++){
        int n=POL[pi].n;
        if(n>R-mineq) break;            /* fewer than mineq equations
                                           possible even at t0=0 */
        int t0hi = strict?0:(R-n-1);
        if(t0hi<0) t0hi=0;
        for(int t0=0;t0<=t0hi;t0++)
            if(R-t0-n>=mineq && annihilates(&POL[pi],v,R,t0)){
                if(ppi)*ppi=pi;
                return n;
            }
    }
    return -1;
}
static int rec_test2(const long long*v,int R,int strict,int*ppi){
    return rec_test3(v,R,strict,1,ppi);
}
/* labeled evaluator (from ledger3) */
static char  sb_s[NBUF][SBCAP];
static int   sb_l[NBUF][SBCAP];
static int evalL(int e,int s,const char*w,int wl,const int*rlab){
    Node*n=&N[e]; if(s>=MAXD) return -2;
    char*o=sb_s[s]; int*ol=sb_l[s];
    if(n->t==0){int l=strlen(CONSTS[n->a]);memcpy(o,CONSTS[n->a],l);
        for(int i=0;i<l;i++)ol[i]=-1; return l;}
    if(n->t==1){memcpy(o,w,wl);for(int i=0;i<wl;i++)ol[i]=rlab[i];return wl;}
    if(n->t==2){int l1=evalL(n->a,s+1,w,wl,rlab);
        int l2=evalL(n->b,s+2,w,wl,rlab);
        if(l1<0)return l1; if(l2<0)return l2; if(l1+l2>SBCAP)return -2;
        memcpy(o,sb_s[s+1],l1); memcpy(o+l1,sb_s[s+2],l2);
        memcpy(ol,sb_l[s+1],l1*sizeof(int));
        memcpy(ol+l1,sb_l[s+2],l2*sizeof(int));
        return l1+l2;}
    int lf=evalL(n->c,s+1,w,wl,rlab), lp=evalL(n->b,s+2,w,wl,rlab),
        lr=evalL(n->a,s+3,w,wl,rlab);
    if(lf<0)return lf; if(lp<0)return lp; if(lr<0)return lr;
    if(lp==0)return -1;
    const char*T=sb_s[s+1],*P=sb_s[s+2],*A=sb_s[s+3];
    const int*TL=sb_l[s+1],*AL=sb_l[s+3];
    int tl=lf,pl=lp,al=lr,m=pl,i=0,oln=0;
    while(i<tl){
        if(i+m<=tl&&memcmp(T+i,P,m)==0){
            if(oln+al>SBCAP)return -2;
            memcpy(o+oln,A,al); memcpy(ol+oln,AL,al*sizeof(int));
            oln+=al; i+=m;
        } else { if(oln+1>SBCAP)return -2;
            o[oln]=T[i]; ol[oln]=TL[i]; oln++; i++; }
    }
    return oln;
}
/* run walk on labeled text: per run (value, minlab, maxlab, nlab) */
typedef struct { long long v; int mn, mx, nl; } RInfo;
static int runinfo(const char*s,const int*lab,int l,RInfo*out,int maxr){
    int n=0,a=0;
    while(a<l){
        int b=a; while(b<l&&s[b]=='a')b++;
        if(b>a){
            int mn=999,mx=-999; unsigned char seen[256]; memset(seen,0,256);
            int nl=0;
            for(int i=a;i<b;i++) if(lab[i]>=0){
                if(lab[i]<mn)mn=lab[i]; if(lab[i]>mx)mx=lab[i];
                if(!seen[lab[i]]){seen[lab[i]]=1;nl++;} }
            if(n<maxr){ out[n].v=b-a; out[n].mn=mn; out[n].mx=mx; out[n].nl=nl; }
            n++;
        }
        a=b+1;
    }
    return n;
}
/* slot sequences across ks: unlabeled values at wide cap (left/right
   alignment), labeled runs (signature alignment).  strict first, then
   loose (any suffix -- EPT licenses a V-fixed eventual pre-period);
   counts reported separately. */
typedef struct { long long v[16]; int np; } Seq;
static int collect_slots(int E,int k0,int k1,int verbose,const char*tag,
                        int*maxord_out,int mineq,int*lrleads_out){
    static char w[CAP];
    static int rlab[CAP];
    static long long V_[16][8192];
    static RInfo ri_[16][8192];
    int nru[16], ks_u[16], nku=0;
    int nr[16], ks[16], nk_=0;
    /* unlabeled pass (wide cap via eval on buf) */
    for(int k=k0;k<=k1;k++){
        int wl; mkwk(w,&wl,k,3);
        int l=eval(E,0,w,wl);
        if(l<0) continue;
        nru[nku]=runs_of(buf[0],l,V_[nku],8192);
        if(nru[nku]>8192) nru[nku]=8192;   /* partial coverage */
        ks_u[nku]=k; nku++;
        if(nku>=16) break;
    }
    /* labeled pass (input and output must fit SBCAP) */
    for(int k=k0;k<=k1;k++){
        int wl; mkwk(w,&wl,k,3);
        if(wl>SBCAP) break;
        int pos=0;
        for(int t=0;t<=k;t++){ long long len=t?pw(3,t):1;
            for(long long q=0;q<len;q++) rlab[pos++]=t;
            if(t<k) rlab[pos++]=-1; }
        int l=evalL(E,0,w,wl,rlab);
        if(l<0) continue;
        nr[nk_]=runinfo(sb_s[0],sb_l[0],l,ri_[nk_],8192);
        if(nr[nk_]>8192) nr[nk_]=8192;      /* partial coverage */
        ks[nk_]=k; nk_++;
        if(nk_>=16) break;
    }
    if(nku<3&&nk_<3) return -1;
    int nslots=0, nfail=0, nloose=0, maxord=0;   /* LR + SIG combined */
    int nfailLR=0, nfailSIG=0, nlooseLR=0, nlooseSIG=0;
    /* left/right on unlabeled */
    if(nku>=3){
        int minc=1<<30;
        for(int i=0;i<nku;i++) if(nru[i]<minc)minc=nru[i];
        for(int i=0;i<minc;i++){
            long long v[16];
            for(int t=0;t<nku;t++) v[t]=V_[t][i];
            int o=rec_test3(v,nku,1,mineq,NULL);
            nslots++;
            if(o<0){
                o=rec_test3(v,nku,0,mineq,NULL);
                if(o<0){ nfail++; nfailLR++;
                    if(verbose&&nfailLR<=3){
                        printf("    %s slot L%d: NO RECURRENCE, vals:",tag,i);
                        for(int t=0;t<nku;t++)printf(" %lld",v[t]);
                        printf("\n"); }
                } else { nloose++; nlooseLR++; }
            } else if(o>maxord) maxord=o;
        }
        for(int i=0;i<minc;i++){
            long long v[16];
            for(int t=0;t<nku;t++) v[t]=V_[t][nru[t]-1-i];
            int o=rec_test3(v,nku,1,mineq,NULL);
            nslots++;
            if(o<0){
                o=rec_test3(v,nku,0,mineq,NULL);
                if(o<0){ nfail++; nfailLR++; }
                else { nloose++; nlooseLR++; }
            } else if(o>maxord) maxord=o;
        }
    }
    /* signature groupings on labeled runs: four anchor modes */
    if(nk_>=3){
        for(int mode=0;mode<4;mode++){
            static long long key[16][8192];
            for(int t=0;t<nk_;t++)
                for(int i=0;i<nr[t];i++){
                    long long a,b;
                    long long mn=ri_[t][i].mn, mx=ri_[t][i].mx;
                    if(mx<0){ mn=999; mx=-999; }
                    switch(mode){
                    case 0: a=mn; b=mx; break;
                    case 1: a=ks[t]-mx; b=ks[t]-mn; break;
                    case 2: a=mn; b=ks[t]-mx; break;
                    default: a=ks[t]-mn; b=mx; break;
                    }
                    key[t][i]=a*1000000000LL+b;
                }
            for(int t0=0;t0<nk_;t0++){
                for(int i=0;i<nr[t0];i++){
                    long long K0=key[t0][i];
                    int mult=1<<30;
                    for(int t=0;t<nk_;t++){
                        int m2=0;
                        for(int q=0;q<nr[t];q++) if(key[t][q]==K0) m2++;
                        if(m2<mult) mult=m2;
                    }
                    if(mult<1) continue;
                    for(int w2=0;w2<mult;w2++){
                        long long v[16]; int have=0;
                        for(int t=0;t<nk_;t++){
                            int seen=0;
                            for(int q=0;q<nr[t];q++) if(key[t][q]==K0){
                                if(seen==w2){ v[have++]=ri_[t][q].v; break; }
                                seen++;
                            }
                        }
                        if(have<nk_) continue;
                        int o=rec_test3(v,nk_,1,mineq,NULL);
                        nslots++;
                        if(o<0){
                            o=rec_test3(v,nk_,0,mineq,NULL);
                            if(o<0){ nfail++; nfailSIG++;
                                if(verbose&&nfailSIG<=3){
                                    printf("    %s SIG slot (key %lld, "
                                           "idx %d): NO RECURRENCE, vals:",
                                           tag,K0,w2);
                                    for(int t=0;t<nk_;t++)
                                        printf(" %lld",v[t]);
                                    printf("\n"); }
                            } else { nloose++; nlooseSIG++;
                                if(verbose&&nlooseSIG<=2){
                                    printf("    %s SIG slot (key %lld, "
                                           "idx %d): LOOSE-ONLY, vals:",
                                           tag,K0,w2);
                                    for(int t=0;t<nk_;t++)
                                        printf(" %lld",v[t]);
                                    printf("\n"); } }
                        } else if(o>maxord) maxord=o;
                    }
                    int m0=0;
                    for(int q=0;q<nr[t0];q++) if(key[t0][q]==K0) m0++;
                    i+=m0-1;
                }
            }
        }
    }
    if(verbose)
        printf("  %s: %d slots (unlab %d ks, lab %d ks), leads: %d sig + "
               "%d LR; loose-only: %d sig + %d LR; max order %d\n",
               tag,nslots,nku,nk_,nfailSIG,nfailLR,nlooseSIG,nlooseLR,maxord);
    if(maxord_out)*maxord_out=maxord;
    if(lrleads_out)*lrleads_out=nfailLR;
    return nfailSIG;
}
static void mode_rec(uint64_t seed,int trials){
    printf("=== [rec] cross-k recurrence battery on D(k;3) ===\n");
    build_family();
    printf("  family: %d char polys, max order %d\n",NPOL,POL[NPOL-1].n);
    rs=seed;
    static char w[CAP];
    Ent Es[32]; int n=build_battery(Es);
    int totsig=0, totlr=0;
    for(int i=0;i<n;i++){
        /* find kmax by cap.  The three huge-pattern expressions
           (pattern ~ S/2 vs scrutinee ~ 2S: the matcher is
           O(tl*pl) ~ S^2) are capped at k=8 to keep the run under
           the 1-minute discipline; their slots need only order 3. */
        int kcap = 13;
        if(!strcmp(Es[i].name,"Ecbox")||!strcmp(Es[i].name,"Esmm")
           ||!strcmp(Es[i].name,"Eh2")) kcap = 8;
        int kmax=3;
        for(int k=3;k<=kcap;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[i].e,0,w,wl);
            if(l<0) break;
            kmax=k;
        }
        int lr=0;
        clock_t c0=clock();
        int f=collect_slots(Es[i].e,3,kmax,1,Es[i].name,NULL,1,&lr);
        if(getenv("PR_TIMING"))
            fprintf(stderr,"[timing] %-10s kmax=%d %.2fs\n",
                    Es[i].name,kmax,(double)(clock()-c0)/CLOCKS_PER_SEC);
        ck(Es[i].name,0,f,"sig-slot recurrence");
        if(f>0) totsig+=f;
        if(lr>0) totlr+=lr;
    }
    printf("  battery: %d sig-slot leads (theory: 0), %d LR-index leads "
           "(alignment artifacts, dispositioned in report)\n",totsig,totlr);
    /* adversarial + positive-control synthetic sequences, k=3..16.
       NOTE (theory): the family is CLOSED UNDER PERIODIC MODULATION
       (x^L-3^{dL} annihilates ANY period-L multiplicative modulation
       of a degree-d component, regardless of the modulating values),
       so modulation sequences are CONTROLS, not adversarial.  The
       teeth are against: non-3-power bases, polynomial junk beyond
       affine, out-of-family periods, random walks.  mineq=3: a pass
       needs >= 3 equations (order-12 two-equation coincidences were
       MEASURED at mineq=1 and are not evidence). */
    {
        int npass=0, cpass=0,ctot=0, k2pass=0;
        long long v[20]; int R=14;
        long long fib[20]; fib[0]=1;fib[1]=1;
        for(int i=2;i<20;i++)fib[i]=fib[i-1]+fib[i-2];
        struct { const char*name; int kind; int which; } A[]={
            {"2^k",0,0},{"5^k",0,1},{"6^k",0,2},{"3^k+k^2",0,3},
            {"3^k+k^3",0,4},{"fib",0,5},{"walk",0,6},
            {"3^k+999*(k mod 7)",0,7},          /* La=7 out of family */
            {"3^k",1,0},{"3^k+k",1,1},{"(3^k-1)/2",1,2},
            {"3^k+3^(2k)",1,3},
            {"3^k*((k mod 4)+1)",1,5},
            {"3^k+700*(k mod 5)",1,6},
            {"3^k*2^{k mod 3}",1,7},            /* period-3 mod: x^3-27 */
            {"k^2+7 (boundary)",2,4},            /* junk must be affine */
        };
        for(int a=0;a<(int)(sizeof A/sizeof A[0]);a++){
            for(int t=0;t<R;t++){
                int k=3+t;
                long long val;
                switch(A[a].kind*100+A[a].which){
                case 0: val=pw(2,k); break;
                case 1: val=pw(5,k); break;
                case 2: val=pw(6,k); break;
                case 3: val=pw(3,k)+(long long)k*k; break;
                case 4: val=pw(3,k)+(long long)k*k*k; break;
                case 5: val=fib[k]; break;
                case 6: val=(long long)(rnd()%1000)*k; break;
                case 7: val=pw(3,k)+999*(k%7); break;
                case 100: val=pw(3,k); break;
                case 101: val=pw(3,k)+k; break;
                case 102: val=(pw(3,k)-1)/2; break;
                case 103: val=pw(3,k)+pw(9,k); break;
                case 105: val=pw(3,k)*((k%4)+1); break;
                case 106: val=pw(3,k)+700*(k%5); break;
                case 107: val=pw(3,k)*pw(2,k%3); break;
                case 204: val=(long long)k*k+7; break;
                default: val=0;
                }
                v[t]=val;
            }
            int pi=-1;
            int o=rec_test3(v,R,1,3,&pi);
            if(A[a].kind==1){ ctot++; if(o>=0) cpass++;
                printf("  ctrl %-28s order %s%d",A[a].name,
                       o<0?"FAIL":"",o);
                if(o>=0&&pi>=0){ printf(" [");
                    for(int i=0;i<=POL[pi].n;i++)
                        printf(" %lld",POL[pi].c[i]);
                    printf(" ]"); }
                printf("\n");
            } else if(A[a].kind==2){ if(o>=0) k2pass++;
                printf("  bnd  %-28s order %s%d (expected: none -- "
                       "closure junk is affine)\n",A[a].name,
                       o<0?"":"",o);
            } else { if(o>=0) npass++;
                printf("  adv  %-28s order %s%d",A[a].name,o<0?"none":"",o);
                if(o>=0&&pi>=0){ printf(" [");
                    for(int i=0;i<=POL[pi].n;i++)
                        printf(" %lld",POL[pi].c[i]);
                    printf(" ]"); }
                printf("\n");
            }
        }
        ck("controls-all-pass",ctot,cpass,"positive controls");
        ck_le("adversarial-pass",npass,0,"teeth (strict, mineq=3)");
        ck("affine-junk-boundary",0,k2pass,"k^2 outside family");
        printf("  adversarial strict (mineq=3): %d/8 spurious; controls: "
               "%d/%d; k^2-junk admitted: %d\n",npass,cpass,ctot,k2pass);
        {
            int lp=0;
            for(int a=0;a<(int)(sizeof A/sizeof A[0]);a++){
                if(A[a].kind!=0) continue;
                for(int t=0;t<R;t++){
                    int k=3+t; long long val;
                    switch(A[a].which){
                    case 0: val=pw(2,k); break;
                    case 1: val=pw(5,k); break;
                    case 2: val=pw(6,k); break;
                    case 3: val=pw(3,k)+(long long)k*k; break;
                    case 4: val=pw(3,k)+(long long)k*k*k; break;
                    case 5: val=fib[k]; break;
                    case 6: val=(long long)(rnd()%1000)*k; break;
                    case 7: val=pw(3,k)+999*(k%7); break;
                    default: val=0;
                    }
                    v[t]=val;
                }
                if(rec_test3(v,R,0,3,NULL)>=0) lp++;
            }
            printf("  adversarial loose (any suffix, mineq=3): %d/8 spurious\n",
                   lp);
        }
        /* teeth at the COMPS' regime: R=6 (k=3..8), mineq=2,
           strict + loose -- the exact test the random comps face */
        {
            int sp=0, lp=0;
            long long u[8];
            for(int a=0;a<(int)(sizeof A/sizeof A[0]);a++){
                if(A[a].kind!=0) continue;
                for(int t=0;t<6;t++){
                    int k=3+t; long long val;
                    switch(A[a].which){
                    case 0: val=pw(2,k); break;
                    case 1: val=pw(5,k); break;
                    case 2: val=pw(6,k); break;
                    case 3: val=pw(3,k)+(long long)k*k; break;
                    case 4: val=pw(3,k)+(long long)k*k*k; break;
                    case 5: val=fib[k]; break;
                    case 6: val=(long long)(rnd()%1000)*k; break;
                    case 7: val=pw(3,k)+999*(k%7); break;
                    default: val=0;
                    }
                    u[t]=val;
                }
                if(rec_test3(u,6,1,2,NULL)>=0) sp++;
                if(rec_test3(u,6,0,2,NULL)>=0) lp++;
            }
            printf("  teeth at comps' regime (R=6, mineq=2): strict %d/8, "
                   "loose %d/8 spurious\n",sp,lp);
        }
    }
    /* random compositions: calm ones only (selection bias disclosed).
       mineq=2: the TL form needs (x-3)(x-1)^2 = order 3 on 5-6 point
       windows (2 equations); mineq=3 was measured to reject legitimate
       closure slots (false negatives) at this R.  Teeth at this exact
       regime are measured separately above. */
    {
        int tried=0, badsig=0, badlr=0;
        for(int t=0;t<trials;t++){
            nn=0;
            int E=gen_expr(2+ri(3));
            /* require materializable at k=3..8 */
            int ok=1;
            static char w2[CAP];
            for(int k=3;k<=8&&ok;k++){
                int wl; mkwk(w2,&wl,k,3);
                if(eval(E,0,w2,wl)<0) ok=0;
            }
            if(!ok) continue;
            tried++;
            int lr=0, mo=0;
            int f=collect_slots(E,3,8,0,"rand",&mo,2,&lr);
            if(f<0&&lr==0) continue;
            if(f>0){ badsig++;
                if(badsig<=4){ printf("  random comp SIG-LEAD:\n");
                    collect_slots(E,3,8,1,"rand-lead",&mo,2,&lr); } }
            if(lr>0) badlr++;
        }
        printf("  random calm comps: %d evaluated, %d with sig-slot leads, "
               "%d with LR-index leads\n",tried,badsig,badlr);
        ck_le("random-sig-leads",badsig,tried/20,"<=5% sig leads");
    }
}

/* ---------- [dbg] labeled run dump ---------- */
static void mode_dbg(const char*which,int kk){
    static char w[SBCAP]; static int rlab[SBCAP];
    Ent Es[32]; int n=build_battery(Es);
    int found=-1;
    for(int i=0;i<n;i++) if(!strcmp(Es[i].name,which)) found=i;
    if(found<0){ printf("no such expr\n"); return; }
    if(kk>10) kk=10;
    for(int k=(kk>0?kk:3); k<=(kk>0?kk:6); k++){
        int wl; mkwk(w,&wl,k,3);
        int pos=0;
        for(int t=0;t<=k;t++){ long long len=t?pw(3,t):1;
            for(long long q=0;q<len;q++) rlab[pos++]=t;
            if(t<k) rlab[pos++]=-1; }
        int l=evalL(Es[found].e,0,w,wl,rlab);
        if(l<0){ printf("k=%d: evalL failed (%d)\n",k,l); continue; }
        RInfo ri[8192];
        int nr=runinfo(sb_s[0],sb_l[0],l,ri,8192);
        printf("k=%d: %d runs:",k,nr);
        for(int i=0;i<nr&&i<14;i++)
            printf(" [%lld {%d..%d} n%d]",ri[i].v,ri[i].mn,ri[i].mx,ri[i].nl);
        if(nr>14) printf(" ...");
        printf("\n");
    }
}

/* ---------- main ---------- */
int main(int argc,char**argv){
    clock_t t0=clock();
    const char*mode = argc>1?argv[1]:"all";
    uint64_t seed = argc>2?(uint64_t)strtoull(argv[2],NULL,10):271828;
    int trials = argc>3?atoi(argv[3]):500;
    printf("INVOCATION:");
    for(int i=0;i<argc;i++) printf(" %s",argv[i]);
    printf("   [mode=%s seed=%llu trials=%d]\n",mode,
           (unsigned long long)seed,trials);
    if(!strcmp(mode,"po1")||!strcmp(mode,"all")) mode_po1(seed,trials);
    if(!strcmp(mode,"rec")||!strcmp(mode,"all")) mode_rec(seed,trials/2);
    if(!strcmp(mode,"dbg")){ const char*w=argc>2?argv[2]:"Eprod";
        int kk=argc>3?atoi(argv[3]):0; mode_dbg(w,kk); }
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}

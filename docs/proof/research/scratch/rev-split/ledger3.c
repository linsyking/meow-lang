/* rev-split ROUND 5 -- THE TERM-LEDGER WRITE-OUT ON B >= 3
 * (charter CHARTER_ledger.md).  Family D(k;B) = a^{B^0} b a^{B^1} ... b
 * a^{B^k}, strongly super-increasing for B >= 3 (B = 2 the telescoping
 * boundary, recorded as such per Lane D round 3).
 *
 * Modes:
 *  [forms]  exact hand-derived closed forms of the battery on D(k;3)
 *           AND D(k;2) (incl. Lane D's six B=2 degeneracy constructions
 *           and their B=3 pinned counterparts -- E_last on B=3 is
 *           (S+k+1)/2: the k-affine junk witness).
 *  [ledger] the term ledger at the VALUE level: every run of the
 *           battery + random compositions classifies as
 *               v = sum_{i<=M} (a_i/b) * B^{e_i} + (A k + B + beta)
 *           checked as: exists modulus b (small) and junk c (|c|<=512,
 *           covers A*k+B for k<=8) with balanced-ternary weight of
 *           (b*v - c) at most 12.
 *  [spec]   classifier specificity: adversarial non-closure values must
 *           FAIL; positive controls (the hand forms) must PASS.
 *  [ba3]    Boundary Alignment on B=3: first/last runs of battery +
 *           random compositions are bounded / alpha*S+beta / top- or
 *           bottom-pinned (rational slope, a/b small).
 *  [atoms]  the atoms-vs-terms demonstration (dropab: support-atoms=k+1
 *           but value = S-k: 1 term + k-affine; E_prod: support-atoms=1
 *           but the measure has 2) -- documents why the ledger lives
 *           at the value/measure level, not the support-atom level.
 *  [msb3]   the round-4 two-stratum budget identities re-run on D(k;3)
 *           (per-node Phi' identity + tree total + E_poll witness).
 *
 * Every log's first line is the full invocation (discipline).
 * Machine checks CONFIRM hand derivations; they do not replace them.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP      (1 << 20)
#define SBCAP    (1 << 17)
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
static long long Stot(int k,int B){ return (pw(B,k+1)-1)/(B-1); }
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
/* value-level ledger classifier (with a direct-mapped memo): v =
 * sum_{i<=M} (a_i/b)*3^{e_i} + (A k + B + beta), M<=4, |a_i|<=16,
 * b<=12, junk |A k + B + beta| <= 160 (k<=8).  dec() searches a
 * decomposition of w=b*v into <=m signed power terms + scaled junk. */
static int dec_terms(long long w,int m,int b){
    if(w<0) w=-w;
    if(w<=160LL*b) return 1;            /* junk (covers A*k+B+beta) */
    if(m<=0) return 0;
    int e=0; while(pw(3,e+1)<=w) e++;
    for(int ee=e-1;ee<=e+1;ee++){
        if(ee<0) continue;
        long long p3=pw(3,ee);
        long long a0=w/p3;
        for(long long a=a0-1;a<=a0+1;a++){
            if(!a||a<-16||a>16) continue;
            long long r=w-a*p3;
            if(!r) return 1;
            if(dec_terms(r,m-1,b)) return 1;
        }
    }
    return 0;
}
static long long cmoV[1<<14]; static int cmoW[1<<14]; static int cmoU[1<<14];
static void cmo_init(void){ memset(cmoU,0,sizeof cmoU); }
static int classify_ledger(long long v){
    if(v<0) v=-v;
    int h=(int)(((uint64_t)v*2654435761u)>>20)&((1<<14)-1);
    if(cmoU[h]&&cmoV[h]==v) return cmoW[h];
    int res=-1;
    if(v<=4096) res=0;
    else for(int m=1;m<=4;m++)
        for(int b=1;b<=12;b++)
            if(dec_terms((long long)b*v,m,b)){ res=m; goto found; }
found:
    cmoU[h]=1; cmoV[h]=v; cmoW[h]=res;
    return res;
}
/* Boundary-Alignment simple check on D(k;B): the value is bounded, or
 * <=2 terms (a/b)*B^e with SMALL |a/b| (<=8, b<=16) at ANCHORED
 * exponents e (top k-c / k+1-c, products 2k-c / 2k+1-c / 3k-c (depth),
 * bottom c), plus junk |Ak+B+beta|<=160b.  (E_prod's last run
 * 1+floor(B^k/2)*S forces the count*xS product class with top-anchored
 * exponents -- no middle-depth reference: BA's true content.) */
static int ba_class(long long v,int k,int B){
    if(v<0) v=-v;
    if(v<=4096) return 1;
    long long T[64]; int nt=0;
    for(int c=0;c<=4;c++){
        if(k+1-c>=0) T[nt++]=pw(B,k+1-c);
        if(k-c>=0)   T[nt++]=pw(B,k-c);
        if(2*k+1-c>=0) T[nt++]=pw(B,2*k+1-c);
        if(2*k-c>=0) T[nt++]=pw(B,2*k-c);
    }
    for(int c=0;c<=2;c++){
        if(3*k+1-c>=0) T[nt++]=pw(B,3*k+1-c);
        if(3*k-c>=0)   T[nt++]=pw(B,3*k-c);
    }
    for(int c=0;c<=6;c++) T[nt++]=pw(B,c);
    for(int b=1;b<=16;b++){
        long long w=b*v, J=160LL*b;
        for(int i=0;i<nt;i++){
            long long T1=T[i]; if(!T1) continue;
            long long a1=(w+T1/2)/T1;
            if(!a1||a1<-8||a1>8) continue;
            long long r1=w-a1*T1;
            if(llabs(r1)<=J) return 2;
            for(int j2=0;j2<nt;j2++){
                long long T2=T[j2]; if(!T2) continue;
                long long a2 = r1<0 ? -(((-r1)+T2/2)/T2) : ((r1+T2/2)/T2);
                if(!a2||a2<-8||a2>8) continue;
                if(llabs(r1-a2*T2)<=J) return 5;
            }
        }
    }
    return 0;
}

/* ---------- battery construction ---------- */
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
static long long halv_tot(int k,int B){
    long long t=0; for(int j=0;j<=k;j++){ long long u=pw(B,j); t+=(u+(u&1))/2; }
    return t;
}
static int expected_runs(const char*name,int k,int B,long long*rr,long maxr){
    int n=0; long long S=Stot(k,B);
    if(!strcmp(name,"mrg")){ rr[n++]=S; }
    else if(!strcmp(name,"half")){
        for(int j=0;j<=k;j++){ long long u=pw(B,j); rr[n++]=(u+(u&1))/2; } }
    else if(!strcmp(name,"third")){
        for(int j=0;j<=k;j++){ long long u=pw(B,j); rr[n++]=u/3+(u%3); } }
    else if(!strcmp(name,"dbl")){
        for(int j=0;j<=k;j++) rr[n++]=2*pw(B,j); }
    else if(!strcmp(name,"shave")){
        for(int j=0;j<k;j++) rr[n++]=pw(B,j)-1;
        rr[n++]=pw(B,k); }
    else if(!strcmp(name,"dropab")){ rr[n++]=S-k; }
    else if(!strcmp(name,"Eleak")){
        for(int j=0;j<k;j++) rr[n++]=pw(B,j)+S;
        rr[n++]=pw(B,k); }
    else if(!strcmp(name,"Eprod")){
        rr[n++]=1;
        for(int j=1;j<=k;j++) rr[n++]=(pw(B,j)&1)+(pw(B,j)/2)*S; }
    else if(!strcmp(name,"dlast")){
        for(int j=0;j<=k-2;j++) rr[n++]=pw(B,j);
        rr[n++]=pw(B,k-1)+pw(B,k); }
    else if(!strcmp(name,"dfirst")){
        rr[n++]=pw(B,0)+pw(B,1);
        for(int j=2;j<=k;j++) rr[n++]=pw(B,j); }
    else if(!strcmp(name,"Elast")){ rr[n++]=halv_tot(k,B); }
    else if(!strcmp(name,"Ecbox")){ rr[n++]=S-halv_tot(k,B); rr[n++]=S; }
    else if(!strcmp(name,"Esmm")){ rr[n++]=S-halv_tot(k,B); }
    else if(!strcmp(name,"Eh2")){
        long long u=S-halv_tot(k,B); rr[n++]=(u+(u&1))/2; }
    else if(!strcmp(name,"dblmerge")){ rr[n++]=2*S; }
    else return -1;
    (void)maxr; return n;
}
static int decb_expected(int k,int B,long long*rr,long maxr){
    static char t[CAP]; long tl=0;
    for(int j=0;j<=k;j++){
        long long len = j?pw(B,j):1;
        for(long long q=0;q<len;q++) t[tl++]='a';
        if(j<k){
            for(int m=0;m<=k;m++){
                long long l2 = m?pw(B,m):1;
                for(long long q=0;q<l2;q++) t[tl++]='a';
                if(m<k) t[tl++]='b';
            }
        }
    }
    return runs_of(t,(int)tl,rr,maxr);
}

/* ---------- [forms] ---------- */
static void mode_forms(void){
    printf("=== [forms] exact closed forms on D(k;B), B=2 and B=3 ===\n");
    Ent Es[32];
    for(int B=2;B<=3;B++){
        int n=build_battery(Es);
        for(int i=0;i<n;i++){
            int kmax = 8;
            if(!strcmp(Es[i].name,"Eprod")) kmax = (B==2)?9:6;
            for(int k=1;k<=kmax;k++){
                static char w[CAP]; int wl; mkwk(w,&wl,k,B);
                int l=eval(Es[i].e,0,w,wl);
                char det[64]; snprintf(det,sizeof det,"%s B=%d k=%d",Es[i].name,B,k);
                if(l<0){ ck(det,1,0,"eval-overflow"); continue; }
                static long long rr[4096], er[4096];
                int rn=runs_of(buf[0],l,rr,4096);
                int en = strcmp(Es[i].name,"decb") ?
                         expected_runs(Es[i].name,k,B,er,4096) :
                         decb_expected(k,B,er,4096);
                ck("run-count",en,rn,det);
                if(en==rn&&en>=0) for(int j=0;j<en;j++)
                    if(rr[j]!=er[j]){ ck("run-value",er[j],rr[j],det); break; }
            }
            printf("  %s: exact forms checked on B=2,3\n",Es[i].name);
        }
    }
}

/* ---------- [ledger] ---------- */
static int gen_expr(int d){
    if(d<=0){ return ri(2)? nv() : nk(ri(7)); }
    int t=ri(12);
    if(t<2) return nv();
    if(t<4) return nk(ri(7));
    if(t<8) return nc(gen_expr(d-1),gen_expr(d-1));
    return ns(gen_expr(d-1),gen_expr(d-1),gen_expr(d-1));
}
static int count_S(int e){ Node*n=&N[e];
    if(n->t==3) return 1+count_S(n->a)+count_S(n->b)+count_S(n->c);
    if(n->t==2) return count_S(n->a)+count_S(n->b);
    return 0; }
static void mode_ledger(uint64_t seed,int trials){
    printf("=== [ledger] term ledger at the value level on D(k;3) ===\n");
    rs=seed; cmo_init();
    static char w[8192];
    Ent Es[32]; int n=build_battery(Es);
    int maxwt=0;
    for(int i=0;i<n;i++){
        int kmax = !strcmp(Es[i].name,"Eprod")?6:8;
        int bad=0, wmax=0;
        for(int k=3;k<=kmax;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[i].e,0,w,wl); if(l<0) continue;
            static long long rr[CAP+2];
            int rn=runs_of(buf[0],l,rr,CAP+2);
            for(int j=0;j<rn;j++){
                int m=classify_ledger(rr[j]);
                if(m>wmax) wmax=m;
                if(m<0){ bad++;
                    if(bad<=3) printf("  UNCLASSIFIED %s k=%d run %d/%d "
                        "L=%lld\n",Es[i].name,k,j,rn,rr[j]); }
            }
        }
        ck(Es[i].name,0,bad,"battery");
        if(wmax>maxwt) maxwt=wmax;
    }
    printf("  battery: max ledger terms observed %d (bound M=4)\n",maxwt);
    long long tot=0, cls=0, nrun=0;
    static long long rr[CAP+2];
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(2+ri(3));
        int k=4+ri(4);
        int wl; mkwk(w,&wl,k,3);
        int l=eval(E,0,w,wl); if(l<0) continue;
        int rn=runs_of(buf[0],l,rr,CAP+2);
        nrun+=rn;
        int allc=1, wmax=0;
        for(int j=0;j<rn;j++){
            int m=classify_ledger(rr[j]);
            if(m>wmax) wmax=m;
            if(m<0) allc=0;
        }
        tot++; if(allc) cls++;
        else if(tot-cls<=10)
            printf("  UNCLASSIFIED random: k=%d runs=%d #S=%d maxterms=%d\n",
                   k,rn,count_S(E),wmax);
        if(wmax>maxwt) maxwt=wmax;
    }
    printf("  random compositions: %lld/%lld fully classified, %lld runs "
           "(global max terms %d)\n",cls,tot,nrun,maxwt);
    ck_le("battery-unclassified",0,0,"value ledger");
}

/* ---------- [spec] ---------- */
static void mode_spec(uint64_t seed){
    printf("=== [spec] classifier specificity on D(k;3)-scale values ===\n");
    rs=seed; cmo_init();
    static long long pos[1024]; int np=0;
    for(int k=4;k<=8;k++){
        long long S=Stot(k,3);
        pos[np++]=S; pos[np++]=S-k; pos[np++]=(S+k+1)/2;
        for(int j=0;j<=k;j++){ pos[np++]=pw(3,j);
            pos[np++]=(pw(3,j)+1)/2; pos[np++]=pw(3,j)+S;
            if(j>=1) pos[np++]=1+(pw(3,j)/2)*S; }
    }
    int pok=0;
    for(int i=0;i<np;i++) if(classify_ledger(pos[i])>=0) pok++;
    ck("positive-controls",np,pok,"all hand forms must pass");
    printf("  positive controls: %d/%d pass\n",pok,np);
    int aok=0, an=0, bok=0;
    for(int k=4;k<=8;k++){
        long long S=Stot(k,3), T=pw(3,k);
        long long adv[10];
        adv[0]=T+104729; adv[1]=T/2+7919*k; adv[2]=5*T+k*(long long)k;
        adv[3]=7*T+99991; adv[4]=(S/3)+31337; adv[5]=T+2*S/5;
        adv[6]=S+1234567; adv[7]=T/2+S/7; adv[8]=11*T/7; adv[9]=S-77777;
        for(int i=0;i<10;i++){ an++; if(classify_ledger(adv[i])>=0) aok++;
                                if(ba_class(adv[i],k,3)) bok++; }
    }
    int rok=0, rn_=0, rbok=0;
    for(int i=0;i<400;i++){ long long v=1+rnd()%(uint64_t)(pw(3,9)); rn_++;
        if(classify_ledger(v)>=0) rok++;
        if(ba_class(v,4+ri(5),3)) rbok++; }
    printf("  LEDGER adversarial structured: %d/%d, random: %d/%d pass --\n"
           "    at k<=8 the closure lattice covers the value range:\n"
           "    the ledger check is a NECESSARY condition only (specificity\n"
           "    needs k >> C_V, beyond the string cap); load-bearing\n"
           "    verification is the exact [forms] battery + the proof.\n",
           aok,an,rok,rn_);
    printf("  BA adversarial structured: %d/%d, random: %d/%d simple\n"
           "    (want ~0: THIS check has teeth at k<=8)\n",bok,an,rbok,rn_);
    /* adversarial rates are REPORT-ONLY: at k<=8 the closure/BA
     * lattices cover the value range (measured), so value-level checks
     * have no specificity there; failures on REAL compositions are
     * the leads that matter. */
}

/* ---------- [ba3] ---------- */
static void mode_ba3(uint64_t seed,int trials){
    printf("=== [ba3] boundary alignment on D(k;3) ===\n");
    rs=seed;
    static char w[8192];
    Ent Es[32]; int n=build_battery(Es);
    for(int i=0;i<n;i++){
        int kmax = !strcmp(Es[i].name,"Eprod")?6:8;
        int bad=0;
        for(int k=3;k<=kmax;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[i].e,0,w,wl); if(l<0) continue;
            static long long rr[CAP+2];
            int rn=runs_of(buf[0],l,rr,CAP+2);
            char det[64]; snprintf(det,sizeof det,"%s k=%d",Es[i].name,k);
            if(!ba_class(rr[0],k,3)) { bad++; ck("BA-first",1,0,det); }
            if(rn>1 && !ba_class(rr[rn-1],k,3)) { bad++; ck("BA-last",1,0,det); }
        }
        ck(Es[i].name,0,bad,"boundary");
    }
    printf("  battery: all first/last runs simple\n");
    long long tot=0, ok=0;
    static long long rr[CAP+2];
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(2+ri(3));
        int k=4+ri(4);
        int wl; mkwk(w,&wl,k,3);
        int l=eval(E,0,w,wl); if(l<0) continue;
        int rn=runs_of(buf[0],l,rr,CAP+2);
        if(rn<1) continue;
        tot++;
        int c1=ba_class(rr[0],k,3), c2=ba_class(rr[rn-1],k,3);
        if(c1&&c2) ok++;
        else if(tot-ok<=10)
            printf("  BA violation random: k=%d first=%lld(class %d) "
                   "last=%lld(class %d)\n",k,rr[0],c1,rr[rn-1],c2);
    }
    ck_le("BA-random-violations",tot-ok,tot/20,"allow 5% battery slack");
    printf("  random: %lld/%lld boundary pairs simple\n",ok,tot);
}

/* ---------- [atoms] ---------- */
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
static int support_atoms(const int*lab,int a,int b){
    unsigned char seen[256]; memset(seen,0,sizeof seen);
    for(int i=a;i<b;i++) if(lab[i]>=0&&lab[i]<256) seen[lab[i]]=1;
    int atoms=0, prev=-10;
    for(int t=0;t<256;t++) if(seen[t]){ if(t!=prev+1) atoms++; prev=t; }
    return atoms;
}
static void mode_atoms(void){
    printf("=== [atoms] atoms are NOT the ledger (B=3, k=5) ===\n");
    static char w[SBCAP]; int k=5, B=3;
    int wl; mkwk(w,&wl,k,B);
    static int rlab[SBCAP]; int pos=0;
    for(int t=0;t<=k;t++){ long long len=t?pw(B,t):1;
        for(long long q=0;q<len;q++) rlab[pos++]=t;
        if(t<k) rlab[pos++]=-1; }
    Ent Es[32]; int n=build_battery(Es);
    for(int i=0;i<n;i++){
        if(strcmp(Es[i].name,"dropab")&&strcmp(Es[i].name,"Eprod")
           &&strcmp(Es[i].name,"decb")) continue;
        int l=evalL(Es[i].e,0,w,wl,rlab);
        if(l<0){ printf("  %s: eval overflow\n",Es[i].name); continue; }
        int a=0, shown=0;
        while(a<l){
            int b=a; while(b<l&&sb_s[0][b]=='a')b++;
            if(b>a){
                int atoms=support_atoms(sb_l[0],a,b);
                long long val=b-a;
                if(shown<8) printf("  %-7s run: value=%lld support-atoms=%d\n",
                       Es[i].name,val,atoms), shown++;
            }
            a=b+1;
        }
    }
    printf("  hand: dropab support-atoms=1 (one interval, collapses) and\n"
           "  value S-k = 1 site term + k-affine: consistent; Eprod run j\n"
           "  has support-atoms=1 but value 1+floor(3^j/2)*S: the site-j\n"
           "  reference rides the PINNED COUNT, not the support -- the\n"
           "  ledger lives at the value/measure level, not the atom level.\n");
}

/* ---------- [msb3] ---------- */
static int phi_mj(const char*s,const int*lab,int l,int k,
                  unsigned char*pairset,int*mj){
    for(int i=0;i<64;i++) pairset[i]=0;
    if(mj) *mj=0;
    int pairs=0, m=0;
    for(int p=0;p<l;p++){
        if(s[p]!='b') continue;
        int a=p-1,b=p+1;
        if(a<0||s[a]!='a') continue;
        if(b>=l||s[b]!='a') continue;
        while(a>=0&&s[a]=='a')a--;
        while(b<l&&s[b]=='a')b++;
        int multi=0;
        { int seen=-2;
          for(int u=p-1;u>a;u--) if(lab[u]>=0){
              if(seen>=0&&seen!=lab[u]) multi=1; seen=lab[u]; } }
        if(!multi){ int seen=-2;
          for(int v=p+1;v<b;v++) if(lab[v]>=0){
              if(seen>=0&&seen!=lab[v]) multi=1; seen=lab[v]; } }
        for(int u=p-1;u>a;u--){ if(lab[u]<0) continue;
            for(int v=p+1;v<b;v++){ if(lab[v]<0) continue;
                if(lab[v]==lab[u]-1){ if(!pairset[lab[v]]){pairset[lab[v]]=1;
                    pairs++;} if(multi) m++; } } }
    }
    if(mj) *mj=m;
    return pairs;
}
static void count_nodes(int e,int*ns_,int*nc_){
    Node*n=&N[e];
    if(n->t==3){(*ns_)++;count_nodes(n->a,ns_,nc_);
        count_nodes(n->b,ns_,nc_);count_nodes(n->c,ns_,nc_);}
    else if(n->t==2){(*nc_)++;count_nodes(n->a,ns_,nc_);
        count_nodes(n->b,ns_,nc_);}
}
static void mode_msb3(uint64_t seed,int trials){
    printf("=== [msb3] two-stratum budget identities on D(k;3) ===\n");
    rs=seed;
    unsigned char ps[64], psF[64], psR[64];
    static char w[SBCAP];
    static int rlab[SBCAP];
    long long idok=0, idtot=0, treetot=0, treeok=0;
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(2+ri(3));
        int k=2+ri(4);
        int wl; mkwk(w,&wl,k,3);
        int pos=0;
        for(int i2=0;i2<=k;i2++){ long long len=i2?pw(3,i2):1;
            for(long long q=0;q<len;q++) rlab[pos++]=i2;
            if(i2<k) rlab[pos++]=-1; }
        long long sumMJ=0;
        int stack[256],sp=0; stack[sp++]=E;
        int abort=0;
        while(sp>0){
            int e=stack[--sp];
            Node*n=&N[e];
            if(n->t==2){stack[sp++]=n->a;stack[sp++]=n->b;continue;}
            if(n->t!=3) continue;
            stack[sp++]=n->a;stack[sp++]=n->b;stack[sp++]=n->c;
            int lo=evalL(e,0,w,wl,rlab); if(lo<0){abort=1;break;}
            int Po=phi_mj(sb_s[0],sb_l[0],lo,k,ps,NULL);
            int lf=evalL(n->c,0,w,wl,rlab); if(lf<0){abort=1;break;}
            int PF=phi_mj(sb_s[0],sb_l[0],lf,k,psF,NULL);
            int lr=evalL(n->a,0,w,wl,rlab); if(lr<0){abort=1;break;}
            int PR=phi_mj(sb_s[0],sb_l[0],lr,k,psR,NULL);
            int mj; phi_mj(sb_s[0],sb_l[0],lo,k,ps,&mj);
            idtot++;
            if(Po <= PF + PR + 4 + mj) idok++;
            else ck("MSB-identity",(long long)(PF+PR+4+mj),(long long)Po,
                   "per-node B=3");
            sumMJ += mj;
        }
        if(abort) continue;
        int lo=evalL(E,0,w,wl,rlab); if(lo<0) continue;
        int PE=phi_mj(sb_s[0],sb_l[0],lo,k,ps,NULL);
        int nS=0,nC=0; count_nodes(E,&nS,&nC);
        treetot++;
        if(PE <= 4*nS + 2*nC + sumMJ) treeok++;
        else ck("MSB-tree",(long long)(4*nS+2*nC+sumMJ),(long long)PE,
               "tree total B=3");
    }
    printf("  per-node identity: %lld/%lld hold; tree total: %lld/%lld\n",
           idok,idtot,treeok,treetot);
    for(int k=3;k<=5;k++){
        nn=0; int X=nv();
        int MG1=ns(nk(0),nk(2),X), MG2=ns(nk(0),nk(2),X);
        int E=ns(nc(MG1,nk(2)), nk(3), MG2);
        int wl; mkwk(w,&wl,k,3);
        int pos=0;
        for(int i2=0;i2<=k;i2++){ long long len=i2?pw(3,i2):1;
            for(long long q=0;q<len;q++) rlab[pos++]=i2;
            if(i2<k) rlab[pos++]=-1; }
        int lo=evalL(E,0,w,wl,rlab);
        if(lo<0){ printf("  E_poll k=%d overflow\n",k); continue; }
        int mj; int P=phi_mj(sb_s[0],sb_l[0],lo,k,ps,&mj);
        ck("E_poll-Phi'=k",k,P,"B=3");
        printf("  E_poll k=%d: Phi'=%d MJ=%d (identity: %d <= 0+0+4+%d)\n",
               k,P,mj,P,mj);
    }
}

/* ---------- main ---------- */
int main(int argc,char**argv){
    clock_t t0=clock();
    const char*mode = argc>1?argv[1]:"all";
    uint64_t seed = argc>2?(uint64_t)strtoull(argv[2],NULL,10):271828;
    int trials = argc>3?atoi(argv[3]):1000;
    printf("INVOCATION:");
    for(int i=0;i<argc;i++) printf(" %s",argv[i]);
    printf("   [mode=%s seed=%llu trials=%d]\n",mode,
           (unsigned long long)seed,trials);
    if(!strcmp(mode,"forms")||!strcmp(mode,"all")) mode_forms();
    if(!strcmp(mode,"ledger")||!strcmp(mode,"all")) mode_ledger(seed,trials);
    if(!strcmp(mode,"spec")||!strcmp(mode,"all")) mode_spec(seed);
    if(!strcmp(mode,"ba3")||!strcmp(mode,"all")) mode_ba3(seed,trials);
    if(!strcmp(mode,"atoms")||!strcmp(mode,"all")) mode_atoms();
    if(!strcmp(mode,"msb3")||!strcmp(mode,"all")) mode_msb3(seed,trials/3+1);
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}

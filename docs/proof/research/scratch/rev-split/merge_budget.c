/* rev-split ROUND 4 -- THE MERGE-SENSITIVE BUDGET + L1 SHARP FORM
 * (charter CHARTER_merge.md).  Modes:
 *
 *  [leak]  L1 REFUTATION, exact: E_leak = [(mrg.b)/'b']X has runs
 *          S+2^j per site (padded extractions; middle sites neither
 *          tweak nor affine); E_prod = [mrg/'aa']X has runs
 *          S*2^{j-1} (site x global products).  Verified exactly on
 *          w^(k), plus the non-classification of middle runs under
 *          the ORIGINAL L1 (distance to any power > 8; no small
 *          (alpha,beta) affine fit).
 *  [class] repaired-schema battery: known expressions + random
 *          compositions on w^(k), every run classified as
 *          alpha*(S+1) + [signed powers of two, weight <= 4] +
 *          bounded junk (|c| <= 64), alpha from the small-rational
 *          family {p/2^d} or the power family {+-2^t, +-2^t/2}
 *          (products).  Unclassified runs are reported.
 *  [msb]   two-stratum budget: per S-node identity
 *          Phi'(out) <= Phi'(F) + Phi'(R) + 4 + MJ(out), MJ = # of
 *          separations with a reversed pair AND a multi-label
 *          flanking run (mergey); tree total
 *          Phi'(E) <= 4#S + 2#C + Sum_v MJ(v).
 *  [sb2]   SB tight-constant hunt (carry): random merge-free
 *          derivations; does Phi' <= 2#S + 2#C ever fail; max slack.
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
#define MAXD     12
#define NBUF     (3 * MAXD + 4)
#define NCONST   12

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};

static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci) { N[nn].t=0; N[nn].a=ci; return nn++; }
static int nv(void)   { N[nn].t=1; return nn++; }
static int nc(int a,int b) { N[nn].t=2; N[nn].a=a; N[nn].b=b; return nn++; }
static int ns(int r,int p,int f) { N[nn].t=3; N[nn].a=r; N[nn].b=p; N[nn].c=f; return nn++; }

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

static int runs_of(const char*s,int l,long long*out,int maxr){
    int n=0; long long cur=0;
    for(int i=0;i<=l;i++){
        if(i<l&&s[i]=='a') cur++;
        else { if(n<maxr) out[n]=cur; n++; cur=0; }
    }
    return n;
}
static void mkwk(char*w,int*wl,int k){   /* w^(k) = a^1 b a^2 b ... b a^{2^k} */
    *wl=0;
    for(int t=0;t<=k;t++){
        int len = (t==0)?1:(1<<t);
        for(int q=0;q<len;q++) w[(*wl)++]='a';
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

/* signed-digit (NAF-style) weight: # of +/- power terms */
static int naf_weight(long long x){
    if(x<0) x=-x; int w=0;
    while(x){ if(x&1){ w++; if((x&3)==3){ x++; } } x>>=1; }
    return w;
}
/* repaired-class check for one run length L on w^(k):
 * L = alpha*(S+1) + [<=4 signed powers] + junk(|c|<=64), alpha from
 * {p/2^d: |p|<=4, d<=2} or {+-2^t, +-2^t/2: 0<=t<=k+1}. */
static int try_alpha(long long an,long long ad,long long L,long long Sp1){
    if(an==0) return 0;
    long long prod = an*Sp1;
    if(prod % ad) return 0;
    long long r = L - prod/ad;
    long long c = r & 63;                 /* 0..63: legal junk */
    if(naf_weight(r-c)<=4) return 1;
    if(naf_weight(r-c-64)<=4) return 1;   /* negative junk reach */
    return 0;
}
static int classify(long long L,int k){
    long long Sp1 = 1LL<<(k+1);           /* S+1 */
    for(int p=-4;p<=4;p++) for(int d=0;d<=2;d++)
        if(try_alpha(p, 1LL<<d, L, Sp1)) return 1;
    for(int t=0;t<=k+1;t++){
        if(try_alpha( 1LL<<t, 1, L, Sp1)) return 1;
        if(try_alpha(-(1LL<<t), 1, L, Sp1)) return 1;
        if(try_alpha( 1, 2, L, Sp1)) return 1;
    }
    if(try_alpha(1,2,L,Sp1)) return 1;
    return 0;
}

/* ---------- [leak] ---------- */
static void mode_leak(void){
    printf("=== [leak] L1 refutation: exact forms on w^(k) ===\n");
    static char w[CAP];
    for(int k=2;k<=13;k++){
        nn=0; int X=nv();
        int mrg = ns(nk(0), nk(2), X);
        int R   = nc(mrg, nk(2));
        int E   = ns(R, nk(2), X);
        int wl; mkwk(w,&wl,k);
        int l=eval(E,0,w,wl); if(l<0){ printf("  k=%d overflow\n",k); break; }
        long long S=(1LL<<(k+1))-1;
        long long rr[80]; int rn=runs_of(buf[0],l,rr,80);
        char det[64]; snprintf(det,sizeof det,"k=%d",k);
        int okform = (rn==k+1);
        for(int j=0;j<rn && okform;j++){
            long long want = (j<k)? (S + (1LL<<j)) : (1LL<<k);
            if(rr[j]!=want) okform=0;
        }
        ck("E_leak-runs",1,okform?1:0,det);
        int jmid = k/2;
        if(jmid>=4 && jmid<k){
            long long L = S + (1LL<<jmid);
            long long best=1LL<<60;
            for(int m=0;m<=2*k+2;m++){ long long d=L-(1LL<<m);
                if(d<0)d=-d; if(d<best)best=d; }
            ck("E_leak-notweak",1,best>8?1:0,det);
            /* original-L1 affine fit: alpha*S+beta, alpha=p/2^d,
             * |beta|<=16 < 2^jmid (needs jmid>=5 so 2^jmid>16) */
            int aff=0;
            if(jmid>=5){
            for(int p=-16;p<=16 && !aff;p++) for(int d=0;d<=6 && !aff;d++){
                for(int b=-16;b<=16 && !aff;b++){
                    long long num=p*S;
                    if(num & ((1LL<<d)-1)) continue;
                    if((num>>d)+b==L) aff=1;
                }
            }
            ck("E_leak-notaffine",0,aff,det);
            }
        }
        if(k<=6||k==13)
            printf("  E_leak k=%d: %d runs = (S+2^j, 2^k) verified\n",k,rn);
    }
    for(int k=2;k<=9;k++){
        nn=0; int X=nv();
        int mrg = ns(nk(0), nk(2), X);
        int E   = ns(mrg, nk(3), X);
        int wl; mkwk(w,&wl,k);
        int l=eval(E,0,w,wl); if(l<0){ printf("  k=%d overflow\n",k); break; }
        long long S=(1LL<<(k+1))-1;
        long long rr[80]; int rn=runs_of(buf[0],l,rr,80);
        char det[64]; snprintf(det,sizeof det,"k=%d",k);
        int okform = (rn==k+1);
        for(int j=0;j<rn && okform;j++){
            long long want = (j==0)?1:( S*(1LL<<(j-1)) );
            if(rr[j]!=want) okform=0;
        }
        ck("E_prod-runs",1,okform?1:0,det);
        int jmid=k/2;
        if(jmid>=4 && jmid<k){
            /* L = 2^{k+jmid-1} - 2^{jmid-1}: nearest power at distance
             * exactly 2^{jmid-1} = 8 > tolerance 4 at k>=8 */
            long long L=S*(1LL<<(jmid-1));
            long long best=1LL<<60;
            for(int m=0;m<=2*k+jmid;m++){ long long d=L-(1LL<<m);
                if(d<0)d=-d; if(d<best)best=d; }
            ck("E_prod-notweak",1,best>4?1:0,det);
        }
        if(k<=6||k==9)
            printf("  E_prod k=%d: %d runs = (1, S*2^{j-1}) verified\n",k,rn);
    }
}

/* ---------- [class] ---------- */
static int gen_expr(int d){
    if(d<=0){ return ri(2)? nv() : nk(ri(7)); }
    int t=ri(12);
    if(t<2) return nv();
    if(t<4) return nk(ri(7));
    if(t<8) return nc(gen_expr(d-1),gen_expr(d-1));
    return ns(gen_expr(d-1),gen_expr(d-1),gen_expr(d-1));
}
static void mode_class(uint64_t seed,int trials){
    printf("=== [class] repaired-schema battery on w^(k) ===\n");
    rs=seed;
    static char w[CAP];
    for(int k=3;k<=9;k++){
        int wl; mkwk(w,&wl,k);
        char det[64]; snprintf(det,sizeof det,"k=%d",k);
        const char*names[9]={"mrg","half","dbl","dlast","dfirst",
                             "shave","Eleak","Eprod","C(E,E)"};
        nn=0; int X=nv();
        int mrg = ns(nk(0), nk(2), X);
        int HALF= ns(nk(1), nk(3), X);
        int DBL = ns(nk(3), nk(1), X);
        int patL= nc(nk(2), nc(mrg, nk(1)));
        int Dlast= ns(nk(0), patL, nc(nc(X,mrg),nk(1)));
        int patF= nc(nc(nk(1), mrg), nk(2));
        int Dfirst=ns(nk(0), patF, nc(nc(nk(1),mrg),X));
        int SHV = ns(nk(2), nk(4), X);
        int Rl  = nc(mrg, nk(2));
        int Eleak = ns(Rl, nk(2), X);
        int Eprod = ns(mrg, nk(3), X);
        int CE  = nc(Eleak, Eleak);
        int B[9]={mrg,HALF,DBL,Dlast,Dfirst,SHV,Eleak,Eprod,CE};
        for(int b=0;b<9;b++){
            int l=eval(B[b],0,w,wl); if(l<0){ck("battery-eval",1,0,det);continue;}
            long long rr[96]; int rn=runs_of(buf[0],l,rr,96);
            int bad=0;
            for(int j=0;j<rn;j++){
                if(!classify(rr[j],k)){ bad++;
                    if(bad<=3) printf("  UNCLASSIFIED %s k=%d run %d/%d "
                        "L=%lld\n",names[b],k,j,rn,rr[j]);
                }
            }
            ck(names[b],0,bad,det);
        }
    }
    printf("  exact battery done (all runs must classify)\n");
    long long tot=0, cls=0;
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(2+ri(3));
        int k=4+ri(5);
        int wl; mkwk(w,&wl,k);
        int l=eval(E,0,w,wl); if(l<0) continue;
        /* rr must hold EVERY run (rn can reach l+1): fixed-size stack
         * array was overrun past 512 -> garbage "unclassified" values
         * (round-4 slip, caught on delivery re-read). */
        static long long rr[CAP+2]; int rn=runs_of(buf[0],l,rr,CAP+2);
        int allc=1; long long firstbad=-1;
        for(int j=0;j<rn;j++) if(!classify(rr[j],k)){ allc=0; firstbad=rr[j];
            break; }
        tot++; if(allc) cls++;
        else if(fails<20)
            printf("  UNCLASSIFIED random: k=%d runs=%d firstbad=%lld\n",
                   k,rn,firstbad);
    }
    printf("  random compositions: %lld/%lld fully classified\n",cls,tot);
}

/* ---------- labeled evaluator (small cap) for msb/sb2 ---------- */
#define SBCAP (1<<16)
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
static int run_mf(const char*s,const int*lab,int l){
    int i=0, seen=-2;
    while(i<=l){
        if(i<l&&s[i]=='a'){
            if(lab[i]>=0){ if(seen>=0&&seen!=lab[i]) return 0; seen=lab[i]; }
            i++;
        } else { seen=-2; i++; }
    }
    return 1;
}
/* Phi' = # distinct reversed adjacent-label pairs at separations;
   MJ  = # separations with a reversed pair AND a multi-label flank */
static int phi_mj(const char*s,const int*lab,int l,int k,
                  unsigned char*pairset,int*mj){
    for(int i=0;i<k+2;i++) pairset[i]=0;
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
        int hadpair=0;
        for(int u=p-1;u>a;u--){ if(lab[u]<0) continue;
            for(int v=p+1;v<b;v++){ if(lab[v]<0) continue;
                if(lab[v]==lab[u]-1){ if(!pairset[lab[v]]){pairset[lab[v]]=1;
                    pairs++;} hadpair=1;
                    if(multi) m++; } } }
        (void)hadpair;
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
/* ---------- [msb] two-stratum budget ---------- */
static void mode_msb(uint64_t seed,int trials){
    printf("=== [msb] two-stratum budget on w^(k) ===\n");
    rs=seed;
    unsigned char ps[64], psF[64], psR[64];
    long long idok=0, idtot=0, treetot=0, treeok=0;
    static char w[256];
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(2+ri(3));
        int k=2+ri(5);
        int wl; mkwk(w,&wl,k);
        int rlab[256];
        { int pos=0;
          for(int i=0;i<=k;i++){ int len=(i==0)?1:(1<<i);
              for(int q=0;q<len;q++) rlab[pos++]=i;
              if(i<k) rlab[pos++]=-1; } }
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
                   "per-node");
            sumMJ += mj;
        }
        if(abort) continue;
        int lo=evalL(E,0,w,wl,rlab); if(lo<0) continue;
        int PE=phi_mj(sb_s[0],sb_l[0],lo,k,ps,NULL);
        int nS=0,nC=0; count_nodes(E,&nS,&nC);
        treetot++;
        if(PE <= 4*nS + 2*nC + sumMJ) treeok++;
        else ck("MSB-tree",(long long)(4*nS+2*nC+sumMJ),(long long)PE,
               "tree total");
    }
    printf("  per-node identity: %lld/%lld hold; tree total: %lld/%lld\n",
           idok,idtot,treeok,treetot);
    /* E_poll witness (round 3): one pass creates ALL k reversed pairs
     * from all-label merged flanks: MJ must absorb k-4 of them. */
    for(int k=5;k<=7;k++){
        nn=0; int X=nv();
        int MG1 = ns(nk(0), nk(2), X);
        int MG2 = ns(nk(0), nk(2), X);
        int Rp  = nc(MG1, nk(2));
        int Ep  = ns(Rp, nk(3), MG2);
        int wl; mkwk(w,&wl,k);
        int rlab[256];
        { int pos=0;
          for(int i=0;i<=k;i++){ int len=(i==0)?1:(1<<i);
              for(int q=0;q<len;q++) rlab[pos++]=i;
              if(i<k) rlab[pos++]=-1; } }
        int lo=evalL(Ep,0,w,wl,rlab); if(lo<0) continue;
        int mj; int Po=phi_mj(sb_s[0],sb_l[0],lo,k,ps,&mj);
        int lf=evalL(MG2,0,w,wl,rlab);
        int PF=lf<0?-1:phi_mj(sb_s[0],sb_l[0],lf,k,psF,NULL);
        int lr=evalL(Rp,0,w,wl,rlab);
        int PR=lr<0?-1:phi_mj(sb_s[0],sb_l[0],lr,k,psR,NULL);
        printf("  E_poll k=%d: Phi'(out)=%d MJ=%d (identity: %d <= %d+"
               "%d+4+%d)\n",k,Po,mj,Po,PF,PR,mj);
        ck("MSB-poll-phi",k,Po,"Phi'(E_poll)=k");
        ck("MSB-poll-mj",1,(Po <= PF+PR+4+mj)?1:0,"identity holds");
        ck("MSB-poll-mjbig",1,(mj>=Po-4)?1:0,"MJ absorbs k-4");
    }
}

/* ---------- [sb2] SB tight-constant hunt ---------- */
static void mode_sb2(uint64_t seed,int trials){
    printf("=== [sb2] SB tight-constant hunt (general inputs) ===\n");
    rs=seed;
    unsigned char ps[64];
    long long nmf=0, viol22=0, worst=-999999;
    static char w[256];
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(3+ri(2));
        int k=1+ri(5);
        int r[8]; int rlab[256];
        for(int i=0;i<=k;i++) r[i]=1+ri(3);
        for(int i=0;i<=k;i++) for(int j=0;j<i;j++)
            if(r[i]==r[j]) r[i]+=1+ri(2);
        int wl=0;
        for(int t2=0;t2<=k;t2++){
            for(int q=0;q<r[t2];q++){w[wl++]='a';}
            if(t2<k) w[wl++]='b';
        }
        { int pos=0;
          for(int i=0;i<=k;i++){ for(int q=0;q<r[i];q++) rlab[pos++]=i;
              if(i<k) rlab[pos++]=-1; } }
        int l=evalL(E,0,w,wl,rlab); if(l<0) continue;
        int mfok=1;
        int stack[256],sp=0; stack[sp++]=E;
        while(sp>0 && mfok){
            int e=stack[--sp]; Node*n=&N[e];
            if(n->t==2){stack[sp++]=n->a;stack[sp++]=n->b;}
            else if(n->t==3){stack[sp++]=n->a;stack[sp++]=n->b;
                stack[sp++]=n->c;}
            else continue;
            int ll=evalL(e,0,w,wl,rlab);
            if(ll<0) continue;
            if(!run_mf(sb_s[0],sb_l[0],ll)) mfok=0;
        }
        l=evalL(E,0,w,wl,rlab); if(l<0) continue;
        int phi=phi_mj(sb_s[0],sb_l[0],l,k,ps,NULL);
        int nS=0,nC=0; count_nodes(E,&nS,&nC);
        if(mfok){ nmf++;
            long long slack = 2*nS+2*nC-phi;
            if(slack>worst) worst=slack;
            if(phi>2*nS+2*nC){ viol22++;
                ck("SB-2/2",(long long)(2*nS+2*nC),(long long)phi,"tight");
            }
        }
    }
    printf("  merge-free: %lld; 2#S+2#C violations: %lld; "
           "max Phi'-excess under 2/2: %lld\n",nmf,viol22,-worst);
}

int main(int argc,char**argv){
    clock_t t0=clock();
    const char*m = argc>1?argv[1]:"all";
    uint64_t seed = argc>2?strtoull(argv[2],0,10):314159ULL;
    int tr = argc>3?atoi(argv[3]):400;
    printf("INVOCATION: %s", argv[0]);
    for(int i=1;i<argc;i++) printf(" %s", argv[i]);
    printf("   [mode=%s seed=%llu trials=%d]\n", m,
           (unsigned long long)seed, tr);
    if(!strcmp(m,"leak")) mode_leak();
    else if(!strcmp(m,"class")) mode_class(seed,tr);
    else if(!strcmp(m,"msb")) mode_msb(seed,tr);
    else if(!strcmp(m,"sb2")) mode_sb2(seed,tr);
    else {
        mode_leak();
        mode_class(seed,tr);
        mode_msb(seed,tr);
        mode_sb2(seed,tr);
    }
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}

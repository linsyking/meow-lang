/* rev-split ROUND 1b -- Lemma S stress on its HOME family W2 =
 * {a^i b a^j b a^k}.  Signature (corrected lemma): on the constant-S
 * plane slice, the a-content takes at most C(E) distinct values,
 * INDEPENDENT of S; a split-like value (a^j) takes ~S.
 *
 *   - random ensemble (S-depth <= 4), S in {12,15,18}, all points
 *   - W2 adversarials incl. Lane A's quadratic [merge/'bb'].[b/a]X
 *   - W2 split-hit check (a^i/a^j/a^k/b a^j b) on the 3x3x3 grid,
 *     ALL-points semantics
 *   - positive controls (merge, junction shave)
 * Falsify only.  Caps: 1<<16, capped evals skipped+counted.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define CAP      (1 << 16)
#define MAXD     24
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
static uint32_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (uint32_t)(rs>>32);}
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

static void mkw2(char *w, int *wl, int i, int j, int k){
    *wl=0;
    for(int t=0;t<i;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<j;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<k;t++)w[(*wl)++]='a';
}

static int gval(int e, int i, int j, int k){
    char w[192]; int wl; mkw2(w,&wl,i,j,k);
    int l = eval(e,0,w,wl);
    if (l < 0) return -1;
    int c=0; for(int t=0;t<l;t++) c += (buf[0][t]=='a');
    return c;
}

static int suppS(int e, int S, int *ndef){
    int vals[512], nv=0; *ndef=0;
    for(int i=1;i<S-1;i++) for(int j=1;j<S-i;j++){
        int k=S-i-j; if(k<1) break;
        int g=gval(e,i,j,k);
        if(g<0) continue;
        (*ndef)++;
        int d=0; for(int t=0;t<nv;t++) if(vals[t]==g){d=1;break;}
        if(!d && nv<512) vals[nv++]=g;
    }
    return nv;
}

static int split_hits_w2(int e){
    int m=7;
    for(int i=1;i<=3;i++)for(int j=1;j<=3;j++)for(int k=1;k<=3;k++){
        char w[64]; int wl; mkw2(w,&wl,i,j,k);
        int l=eval(e,0,w,wl); if(l<0) return 0;
        char*o=buf[0];
        int ok=(l==j); for(int t=0;ok&&t<l;t++) ok=(o[t]=='a');
        if(!ok) m&=~1;
        ok=(l==i); for(int t=0;ok&&t<l;t++) ok=(o[t]=='a');
        if(!ok) m&=~2;
        ok=(l==k); for(int t=0;ok&&t<l;t++) ok=(o[t]=='a');
        if(!ok) m&=~4;
        ok=(l==j+2)&&o[0]=='b'&&o[l-1]=='b';
        for(int t=1;ok&&t<l-1;t++) ok=(o[t]=='a');
        if(!(ok&&l==j+2)) m&=~8;
        ok=(l==j+2)&&o[l-1]=='b';
        for(int t=0;ok&&t<l-1;t++) ok=(o[t]=='a');
        if(!(ok&&l==j+2)) m&=~16;
    }
    return m&31;
}

static int gen(int depth){
    if(depth<=0) return ri(2)?nk(ri(NCONST)):nv();
    int r=ri(100);
    if(r<15) return nk(ri(NCONST));
    if(r<25) return nv();
    if(r<55){int a=gen(depth-1);int b=gen(depth-1);return nc(a,b);}
    int rr=gen(depth-1),pp=gen(depth-1),ff=gen(depth-1);
    return ns(rr,pp,ff);
}

int main(int argc, char**argv){
    rs = (argc>1)?strtoull(argv[1],0,10):975312468ULL; if(!rs) rs=975312468ULL;
    int NR = (argc>2)?atoi(argv[2]):8000;
    /* controls */
    nn=0; int X=nv();
    int MRG = ns(nk(0),nk(2),X);
    int SHV = ns(nk(0),nk(4),X);           /* [e/ab]X */
    printf("[w2-ctl] merge a-content on slices / junction shave\n");
    for(int S=10;S<=14;S+=2){
        int nd, s1=suppS(MRG,S,&nd), s2=suppS(SHV,S,&nd);
        int ok1=1;
        for(int i=1;ok1&&i<S-1;i++)for(int j=1;ok1&&j<S-i;j++){
            int k=S-i-j; if(k<1)break;
            if(gval(MRG,i,j,k)!=S) ok1=0;
        }
        printf("  S=%d: merge support %d (S-consistent:%s) | [e/ab] support %d\n",
               S,s1,ok1?"yes":"NO",s2);
    }
    /* random ensemble */
    static const int SS[3]={12,15,18};
    int computed=0, skipped=0, maxs=0, hits=0, bigs=0;
    for(int t=0;t<NR;t++){
        nn=0; X=nv(); int e=gen(4);
        int mx=0, ndtot=0;
        for(int q=0;q<3;q++){int nd;int s=suppS(e,SS[q],&nd);ndtot+=nd;if(s>mx)mx=s;}
        if(ndtot==0){ int nd,mx2=0,any=0;
            for(int q=0;q<3;q++){int s=suppS(e,SS[q],&nd); if(nd)any=1; if(s>mx2)mx2=s;}
            /* try tiny too */
            int s0=suppS(e,9,&nd); if(nd)any=1; if(s0>mx2)mx2=s0;
            if(!any){skipped++;continue;} mx=mx2;
        }
        computed++;
        if(mx>maxs)maxs=mx;
        if(mx>12){bigs++; if(bigs<=10) printf("  BIG idx=%d max=%d\n",t,mx);}
        int h=split_hits_w2(e);
        if(h){hits++; printf("  SPLIT HIT idx=%d mask=%d\n",t,h);}
    }
    printf("[w2-supp] random %d: computed %d, skipped %d, max support %d, big %d, hits %d\n",
           NR,computed,skipped,maxs,bigs,hits);
    /* adversarials */
    nn=0; X=nv();
    int MRG2=ns(nk(0),nk(2),X);
    int EXPL=ns(nk(2),nk(1),X);                        /* [b/a]X = b^{S+2} */
    int LA=ns(MRG2,nk(6),EXPL);                        /* [merge/'bb']expl */
    int LA3=ns(MRG2,nk(11),EXPL);                      /* [merge/'aaa']expl */
    int DBL=ns(nk(3),nk(1),X);
    int HALF=ns(nk(1),nk(3),X);
    int HMRG=ns(nk(1),nk(3),MRG2);                     /* [a/aa]merge */
    int PW=ns(X,MRG2,X);                                /* [X/merge]X */
    int PH=ns(X,HMRG,X);                                /* [X/halfmerge]X */
    int BIG2=nc(nc(MRG2,nk(2)),MRG2);
    int SW2=ns(nk(2),X,BIG2);                           /* swap-style */
    int CEX=nc(EXPL,X);
    int REX=ns(X,nk(6),EXPL);                          /* [X/'bb']expl */
    int adv[]={LA,LA3,EXPL,MRG2,DBL,HALF,HMRG,PW,PH,BIG2,SW2,CEX,REX};
    const char*an[]={"[mrg/bb]expl QUADRATIC","[mrg/aaa]expl","[b/a]w2","merge",
        "dbl","half","halfmerge","[X/merge]w2","[X/halfmrg]w2","big2","swap2",
        "C(expl,w2)","[X/bb]expl"};
    printf("[w2-supp] adversarial\n");
    for(unsigned k=0;k<sizeof adv/sizeof adv[0];k++){
        int mx=0,ndtot=0;
        for(int q=0;q<3;q++){int nd;int s=suppS(adv[k],SS[q],&nd);ndtot+=nd;if(s>mx)mx=s;}
        if(ndtot==0){int nd,mx2=0,any=0;
            for(int q=0;q<3;q++){int s=suppS(adv[k],SS[q],&nd);if(nd)any=1;if(s>mx2)mx2=s;}
            int s0=suppS(adv[k],9,&nd);if(nd)any=1;if(s0>mx2)mx2=s0;
            mx=any?mx2:-1;ndtot=any?1:0;}
        int h=split_hits_w2(adv[k]);
        if(h)printf("  SPLIT HIT '%s' mask=%d\n",an[k],h);
        printf("  %-24s max support %s%d\n",an[k],ndtot?"":"ALL-UNDEF ",mx);
    }
    return 0;
}

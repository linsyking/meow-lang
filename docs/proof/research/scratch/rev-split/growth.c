/* rev-split ROUND 1c -- FINAL growth signature test for Lemma S.
 * For each random expression (S-depth <= 4) on W2 and on F:
 *   supports of the a-content AND the b-count on constant-S slices
 *   at S = 9, 15, 21, 27 (W2) resp. S = 12, 18, 24, 30 (F).
 * FLAG only GROWTH: supp(last) > supp(second) + 4, or supp > 40.
 * A split-like value takes ~S values; Lemma S predicts a fixed C(E).
 * Positive controls: merge (support 1), half (2), Lane A quadratic (1).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define CAP (1<<16)
#define MAXD 24
#define NBUF (3*MAXD+4)
#define NCONST 12
static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};
static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci){N[nn].t=0;N[nn].a=ci;return nn++;}
static int nv(void){N[nn].t=1;return nn++;}
static int nc(int a,int b){N[nn].t=2;N[nn].a=a;N[nn].b=b;return nn++;}
static int ns(int r,int p,int f){N[nn].t=3;N[nn].a=r;N[nn].b=p;N[nn].c=f;return nn++;}
static uint64_t rs;
static uint32_t rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return (uint32_t)(rs>>32);}
static int ri(int n){return (int)(rnd()%(uint64_t)n);}
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
static int gen(int depth){
    if(depth<=0) return ri(2)?nk(ri(NCONST)):nv();
    int r=ri(100);
    if(r<15) return nk(ri(NCONST));
    if(r<25) return nv();
    if(r<55){int a=gen(depth-1);int b=gen(depth-1);return nc(a,b);}
    int rr=gen(depth-1),pp=gen(depth-1),ff=gen(depth-1);
    return ns(rr,pp,ff);
}
/* mode 0: W2 slice (i,j,k>=1, i+j+k=S); mode 1: F slice (i,j>=1, i+j=S) */
static int counts(int e,int p1,int p2,int p3,int mode,int *na,int *nb,int *nd){
    int va[1024],vb[1024],ka=0,kb=0; *nd=0; *na=*nb=0;
    if(mode==0){
        int S=p1+p2+p3; (void)S;
        for(int i=1;i<p1+p2+p3-2;i++)for(int j=1;j<p1+p2+p3-i-1;j++){
            int k=p1+p2+p3-i-j; if(k<1)break;
            char w[192]; int wl=0;
            for(int t=0;t<i;t++)w[wl++]='a'; w[wl++]='b';
            for(int t=0;t<j;t++)w[wl++]='a'; w[wl++]='b';
            for(int t=0;t<k;t++)w[wl++]='a';
            int l=eval(e,0,w,wl); if(l<0)continue;
            int a=0,b=0; for(int t=0;t<l;t++){a+=(buf[0][t]=='a');b+=(buf[0][t]=='b');}
            (*nd)++;
            int d=0; for(int t=0;t<ka;t++) if(va[t]==a){d=1;break;}
            if(!d&&ka<1024) va[ka++]=a;
            d=0; for(int t=0;t<kb;t++) if(vb[t]==b){d=1;break;}
            if(!d&&kb<1024) vb[kb++]=b;
        }
    } else {
        for(int i=1;i<p1+p2-1;i++){
            int j=p1+p2-i;
            char w[128]; int wl=0;
            for(int t=0;t<i;t++)w[wl++]='a'; w[wl++]='b';
            for(int t=0;t<j;t++)w[wl++]='a';
            int l=eval(e,0,w,wl); if(l<0)continue;
            int a=0,b=0; for(int t=0;t<l;t++){a+=(buf[0][t]=='a');b+=(buf[0][t]=='b');}
            (*nd)++;
            int d=0; for(int t=0;t<ka;t++) if(va[t]==a){d=1;break;}
            if(!d&&ka<1024) va[ka++]=a;
            d=0; for(int t=0;t<kb;t++) if(vb[t]==b){d=1;break;}
            if(!d&&kb<1024) vb[kb++]=b;
        }
    }
    *na=ka; *nb=kb; return 0;
}
int main(int argc,char**argv){
    rs=(argc>1)?strtoull(argv[1],0,10):13572468ULL; if(!rs) rs=13572468ULL;
    int NR=(argc>2)?atoi(argv[2]):8000;
    printf("[growth] W2 ensemble: %d exprs, slices S=9,15,21,27 (a- and b-counts)\n",NR);
    int SW[4]={9,15,21,27};
    int flag=0, comp=0, skip=0, maxa=0, maxb=0;
    for(int t=0;t<NR;t++){
        nn=0; int X=nv(); int e=gen(4);
        int na[4],nb[4],nd[4];
        for(int q=0;q<4;q++) counts(e,SW[q],0,0,0,&na[q],&nb[q],&nd[q]);
        if(nd[0]+nd[1]+nd[2]+nd[3]==0){
            int a2,b2,d2; counts(e,6,0,0,0,&a2,&b2,&d2);
            if(d2==0){skip++;continue;}
            for(int q=0;q<4;q++){na[q]=a2;nb[q]=b2;}
        }
        comp++;
        int ma=0,mb=0;
        for(int q=0;q<4;q++){ if(na[q]>ma)ma=na[q]; if(nb[q]>mb)mb=nb[q]; }
        if(ma>maxa)maxa=ma; if(mb>maxb)maxb=mb;
        if((na[3]>na[2]+4)||(nb[3]>nb[2]+4)||ma>40||mb>40){
            flag++;
            if(flag<=10) printf("  GROWTH idx=%d a:%d,%d,%d,%d b:%d,%d,%d,%d\n",
                t,na[0],na[1],na[2],na[3],nb[0],nb[1],nb[2],nb[3]);
        }
    }
    printf("  computed %d, skipped %d, flags %d, max a-support %d, max b-support %d\n",
           comp,skip,flag,maxa,maxb);
    printf("[growth] F ensemble: %d exprs, slices S=12,18,24,30\n",NR);
    int SF[4]={12,18,24,30};
    flag=0;comp=0;skip=0;maxa=0;maxb=0;
    for(int t=0;t<NR;t++){
        nn=0; int X=nv(); int e=gen(4);
        int na[4],nb[4],nd[4];
        for(int q=0;q<4;q++) counts(e,SF[q],0,0,1,&na[q],&nb[q],&nd[q]);
        if(nd[0]+nd[1]+nd[2]+nd[3]==0){
            int a2,b2,d2; counts(e,8,0,0,1,&a2,&b2,&d2);
            if(d2==0){skip++;continue;}
            for(int q=0;q<4;q++){na[q]=a2;nb[q]=b2;}
        }
        comp++;
        int ma=0,mb=0;
        for(int q=0;q<4;q++){ if(na[q]>ma)ma=na[q]; if(nb[q]>mb)mb=nb[q]; }
        if(ma>maxa)maxa=ma; if(mb>maxb)maxb=mb;
        if((na[3]>na[2]+4)||(nb[3]>nb[2]+4)||ma>40||mb>40){
            flag++;
            if(flag<=10) printf("  GROWTH idx=%d a:%d,%d,%d,%d b:%d,%d,%d,%d\n",
                t,na[0],na[1],na[2],na[3],nb[0],nb[1],nb[2],nb[3]);
        }
    }
    printf("  computed %d, skipped %d, flags %d, max a-support %d, max b-support %d\n",
           comp,skip,flag,maxa,maxb);
    /* controls */
    nn=0; int X=nv();
    int MRG=ns(nk(0),nk(2),X), HALF=ns(nk(1),nk(3),X), DBL=ns(nk(3),nk(1),X);
    int EXPL=ns(nk(2),nk(1),X), LA=ns(MRG,nk(6),EXPL);
    int c[6][2]={{0}};
    int adv2[]={MRG,HALF,DBL,LA}; const char*nm[]={"merge","half","dbl","LA-quadratic"};
    printf("[growth-ctl]\n");
    for(unsigned k=0;k<4;k++){
        int ma=0,mb=0;
        for(int q=0;q<4;q++){int a,b,d; counts(adv2[k],SW[q],0,0,0,&a,&b,&d);
            if(a>ma)ma=a; if(b>mb)mb=b;}
        printf("  %-13s W2 max a/b supports: %d/%d\n",nm[k],ma,mb);
    }
    return 0;
}

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
static void mkw2(char*w,int*wl,int i,int j,int k){
    *wl=0;
    for(int t=0;t<i;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<j;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<k;t++)w[(*wl)++]='a';
}
static int gval(int e,int i,int j,int k){
    char w[192]; int wl; mkw2(w,&wl,i,j,k);
    int l=eval(e,0,w,wl); if(l<0) return -1;
    int c=0; for(int t=0;t<l;t++)c+=(buf[0][t]=='a'); return c;
}
static int suppS(int e,int S,int*ndef){
    int vals[1024],nv=0; *ndef=0;
    for(int i=1;i<S-1;i++)for(int j=1;j<S-i;j++){
        int k=S-i-j; if(k<1)break;
        int g=gval(e,i,j,k); if(g<0)continue;
        (*ndef)++;
        int d=0; for(int t=0;t<nv;t++) if(vals[t]==g){d=1;break;}
        if(!d&&nv<1024) vals[nv++]=g;
    }
    return nv;
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
static void ppn(int e){
    Node*n=&N[e];
    if(n->t==0){printf("\"%s\"",CONSTS[n->a]);return;}
    if(n->t==1){printf("X");return;}
    if(n->t==2){printf("C(");ppn(n->a);printf(",");ppn(n->b);printf(")");return;}
    printf("S(");ppn(n->a);printf(",");ppn(n->b);printf(",");ppn(n->c);printf(")");
}
int main(){
    int targets[]={1521,4790,4893,5065,6663,7197,7375,7556};
    rs=975312468ULL;
    for(int t=0;t<=7556;t++){
        nn=0; int X=nv(); int e=gen(4);
        int hit=0;
        for(unsigned q=0;q<sizeof targets/sizeof targets[0];q++) if(t==targets[q]) hit=1;
        if(!hit) continue;
        printf("=== idx %d: ", t); ppn(e); printf("\n");
        for(int S=9;S<=24;S+=3){
            int nd, s=suppS(e,S,&nd);
            printf("   S=%2d: support %3d  (nd=%d)\n",S,s,nd);
        }
    }
    return 0;
}

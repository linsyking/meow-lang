#include <stdio.h>
#include <string.h>
#define CAP (1<<16)
#define MAXD 24
#define NBUF (3*MAXD+4)
static char buf[NBUF][CAP];
typedef struct { int t,a,b,c; } Node;
static Node N[400]; static int nn;
static int nk(int ci){N[nn].t=0;N[nn].a=ci;return nn++;}
static int nv(void){N[nn].t=1;return nn++;}
static int nc(int a,int b){N[nn].t=2;N[nn].a=a;N[nn].b=b;return nn++;}
static int ns(int r,int p,int f){N[nn].t=3;N[nn].a=r;N[nn].b=p;N[nn].c=f;return nn++;}
static const char*CS[]={ "","a","b","aa","ab","ba","bb","aab","abb","bab","abba" };
static int eval(int e,int s,const char*w,int wl){
    Node*n=&N[e]; if(s>=MAXD) return -2; char*o=buf[s];
    if(n->t==0){int l=strlen(CS[n->a]);memcpy(o,CS[n->a],l);return l;}
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
int main(){
    nn=0; int X=nv();
    int MERGE=ns(nk(0),nk(2),X);
    int DBL=ns(nk(3),nk(1),X);
    int DBL2=ns(nk(3),nk(1),DBL);
    int E=ns(nk(0),MERGE,DBL2);
    for(int i=2;i<=6;i++)for(int j=1;j<=2;j++){
        char w[32]; int wl=0;
        for(int t=0;t<i;t++)w[wl++]='a'; w[wl++]='b';
        for(int t=0;t<j;t++)w[wl++]='a';
        int l=eval(E,0,w,wl);
        printf("(i=%d,j=%d) len=%d out='%.*s'\n",i,j,l,l<0?0:l,buf[0]);
    }
    return 0;
}

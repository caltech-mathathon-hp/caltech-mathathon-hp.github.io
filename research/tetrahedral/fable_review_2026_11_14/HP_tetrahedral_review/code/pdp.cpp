// weaker relaxation (P): layer at interior breakpoint x with adjacent intervals l,r holds <= min(x, C-x, l*r).
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
  int mmax=atoi(argv[1]);
  for(int m=1;m<=mmax;m++){
    int C=2*m*m;
    vector<vector<long long>> dp(C+1, vector<long long>(C+1,-1)); vector<vector<double>> cnt(C+1, vector<double>(C+1,0));
    for(int b=1;b<=C;b++){dp[b][b]=0;cnt[b][b]=1;}
    for(int x=1;x<C;x++) for(int l=1;l<=x;l++){ long long v=dp[x][l]; if(v<0) continue; double c=cnt[x][l];
      for(int r=1;x+r<=C;r++){ long long g=min((long long)min(x,C-x),(long long)l*r); long long nv=v+g;
        if(nv>dp[x+r][r]){dp[x+r][r]=nv;cnt[x+r][r]=c;} else if(nv==dp[x+r][r]) cnt[x+r][r]+=c; } }
    long long best=-1; double bc=0; for(int l=1;l<=C;l++){ if(dp[C][l]>best){best=dp[C][l];bc=cnt[C][l];} else if(dp[C][l]==best) bc+=cnt[C][l]; }
    printf("m=%d C=%d  max(P)=%lld  N_m=%d  #optimal partitions=%.0f\n",m,C,best,m*(4*m*m-1)/3,bc);
  }
}

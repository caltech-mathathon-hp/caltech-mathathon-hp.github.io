// Relaxed 1-D problem (R): intervals beta_1..beta_n (positive ints, sum C), layers at interior breakpoints,
// s_k <= beta_{k-1}*beta_k, |s_k - s_{k+1}| <= beta_k, s_0 = s_n = 0 (outside). Maximise sum s_k. Count optimal (beta,s) solutions.
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
  int Cmax=atoi(argv[1]);
  for(int C=2;C<=Cmax;C+=2){
    int SM=C/2+1;
    // dp[x][bp][s] : best total with a layer of size s at breakpoint x, previous interval bp. x from 1..C-1
    vector<vector<vector<int>>> dp(C+1, vector<vector<int>>(C+1, vector<int>(SM+1,-1)));
    vector<vector<vector<double>>> cnt(C+1, vector<vector<double>>(C+1, vector<double>(SM+1,0)));
    // first interval beta=b, layer at x=b with s<=b (Lipschitz from 0) ; cap needs next interval, applied at transition
    for(int b=1;b<C;b++) for(int s=1;s<=min(b,SM);s++){ dp[b][b][s]=s; cnt[b][b][s]=1; }
    int best=-1; double bc=0;
    for(int x=1;x<C;x++) for(int bp=1;bp<=x;bp++) for(int s=1;s<=SM;s++){
      int v=dp[x][bp][s]; if(v<0) continue; double c=cnt[x][bp][s];
      for(int r=1;x+r<=C;r++){
        if(s>(long long)bp*r) continue;       // cap at x
        if(x+r==C){ if(s<=r){ if(v>best){best=v;bc=c;} else if(v==best) bc+=c; } continue; }
        for(int s2=max(1,s-r); s2<=min(SM,s+r); s2++){
          if(s2>C-(x+r)) break;
          int nv=v+s2;
          if(nv>dp[x+r][r][s2]){dp[x+r][r][s2]=nv;cnt[x+r][r][s2]=c;}
          else if(nv==dp[x+r][r][s2]) cnt[x+r][r][s2]+=c;
        }
      }
    }
    // is C = 2 m^2 ?
    int m=(int)llround(sqrt(C/2.0)); bool sq=(2*m*m==C);
    printf("C=%d  boundary=%d  maxN=%d  #opt=%.0f %s\n",C,2*C,best,bc, sq? ("<- m="+to_string(m)+" N_m="+to_string(m*(4*m*m-1)/3)).c_str():"");
  }
}

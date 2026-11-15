# Equality cases of (*), checked against the statements used in the proof of Claim U:
#   (T')  tight  =>  r >= s            (a = s^2 + r)
#   (T)   tight  =>  l <= s
#   exact: for s>=2, tight  <=>  t = s+1, r >= s, min(2s+1-r, s) <= l <= s
import math, sys
isq=math.isqrt
A=int(sys.argv[1])
pre=[0]*(3*A+10)
for y in range(3*A+8): pre[y+1]=pre[y]+isq(y)
W=lambda u,v: pre[v]-pre[u]
bad=[0,0,0]; n=0
for a in range(1,A):
    s=isq(a); r=a-s*s
    for t in range(s+1,a+1):
        for l in range(1,2*a+2):
            lhs=(a-t)+min(a,l*t); rhs=W(a-t,a)+W(a,a+l)
            assert lhs<=rhs
            tight=(lhs==rhs)
            pred=(t==s+1 and r>=s and min(2*s+1-r,s)<=l<=s)
            if tight:
                n+=1
                if r<s: bad[0]+=1
                if l>s: bad[1]+=1
            if s>=2 and tight!=pred: bad[2]+=1
print("a < %d: (*) holds everywhere; tight cases %d; violations of (T') %d, of (T) %d, of the exact description (s>=2) %d"%(A,n,bad[0],bad[1],bad[2]))

# Route for a hand proof of (*):  (a-t) + min(a, l*t) <= W(a-t,a) + W(a,a+l)   for t >= floor(sqrt(a))+1,  W(u,v)=sum_{u<=y<v} floor(sqrt(y)).
# Reduction: W(a,a+l) >= s*l + e(l), e(l)=max(0, r+l-2s-1) (a=s^2+r).  Put L(t)=W(a-t,a), l0=floor(a/t),
#   Req(t) = max( a-t+l0*t - s*l0 - e(l0),  2a-t - s*(l0+1) - e(l0+1) ).
# Then (*) for all l  <=>  L(t) >= Req(t)   [worst l is l0 or l0+1].   Induction on t:
#   base  : L(s+1) >= Req(s+1)
#   step  : Req(t+1)-Req(t) <= floor(sqrt(a-t-1)) = L(t+1)-L(t)
import sys, math
A=int(sys.argv[1])
isq=math.isqrt
bad_base=bad_step=bad_red=bad_star=0; tight=0
for a in range(1,A):
    s=isq(a); r=a-s*s
    pre=[0]*(a+2)
    for y in range(a+1): pre[y+1]=pre[y]+isq(y)
    def e(l): return max(0,r+l-2*s-1)
    def Req(t):
        l0=a//t
        return max(a-t+l0*t-s*l0-e(l0), 2*a-t-s*(l0+1)-e(l0+1))
    prevReq=None
    for t in range(s+1,a+1):
        L=pre[a]-pre[a-t]; R=Req(t)
        if t==s+1:
            if L<R: bad_base+=1
        else:
            if R-prevReq>isq(a-t): bad_step+=1          # floor(sqrt(a-(t-1)-1)) = isq(a-t)
        if L==R: tight+=1
        prevReq=R
    # spot check of (*) itself and of the reduction for a few l (full check for small a)
    if a<400:
        for t in range(s+1,a+1):
            L=pre[a]-pre[a-t]
            for l in range(1,a+3):
                W2=sum(isq(y) for y in range(a,a+l))
                if (a-t)+min(a,l*t)>L+W2: bad_star+=1
                if W2<s*l+e(l): bad_red+=1
print("a < %d: base case violations %d, step violations %d ; (for a<400: violations of (*) %d, of the bound W(a,a+l)>=s*l+e(l) %d) ; tight cases L=Req: %d"%(A,bad_base,bad_step,bad_star,bad_red,tight))

# one-sided problem: A[x][l] = max sum of gains at breakpoints strictly inside (0,x) for partitions of [0,x] whose last interval has length l
# gain at breakpoint y between intervals (l,r) = min(y, l*r)
import math
X=130
NEG=-10**9
A=[[NEG]*(X+2) for _ in range(X+2)]
for l in range(1,X+1): A[l][l]=0
for x in range(1,X+1):
    for l in range(1,x+1):
        a=A[x][l]
        if a<0: continue
        for r in range(1,X-x+1):
            v=a+min(x,l*r)
            if v>A[x+r][r]: A[x+r][r]=v
F=[max(A[x][1:x+1]) if x>0 else 0 for x in range(X+1)]
print("x : F(x)=max_l A(x,l) : argmax l's : [A(x,l)-F(x) for l near sqrt]")
for x in range(1,70):
    arg=[l for l in range(1,x+1) if A[x][l]==F[x]]
    q=int(math.isqrt(x))
    print(x, F[x], arg, {l:A[x][l]-F[x] for l in range(max(1,q-2),q+4) if l<=x})

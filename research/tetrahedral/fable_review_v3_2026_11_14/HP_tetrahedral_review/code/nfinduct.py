"""Machine check of the two inductive steps behind the Near-field Lemma (notes 10.7):
   every D-ball picture of the skin-1 near field of instance B occurs, translated, in instance A, where
   (step m)  A = (m, K), B = (m+2, K): translations = the ten region transfers of 5.6 (concentric octahedra);
   (step K)  A = (m, K), B = (m, K+1): translations along the frame edges and the track by the slot / separator periods.
   Picture = which sites are H, which are near-field P's (with kind), which H's are bulk run ends."""
import sys, itertools
D=5
def build(m,K):
    sys.argv=['build3.py',str(m),'4','['+','.join(['[2,2]']*K)+']','20','nochain','0','natural','nfind']
    src=open('build3.py').read().split("# ---------- far field")[0].replace("import os\nif os.environ.get('NEARONLY'):","if False:")
    ns={}
    exec(src,ns)
    lab={}
    norm=lambda l: 'cap' if 'cap' in l else ('zone' if l=='zone' else l)
    for q,l in ns['reserved'].items():
        if 'tether' in l or ns['skin'](q)!=1: continue
        lab[q]=norm(l)
    ends=set(ns['bulkends'])
    return dict(S=ns['S'],lab=lab,ends=ends,m=m)
def pic(I,w):
    if w in I['S']: return 'E' if w in I['ends'] else 'H'
    return I['lab'].get(w)
R=range(-D,D+1); BALL=[(a,b,c) for a in R for b in R for c in R if (a-b)%2==0 and (b-c)%2==0]
def check(A,B,shiftB,TS,name):
    bad=0; n=0; used={}
    for q in B['lab']:
        n+=1; ok=False
        for T in TS:
            good=True
            for d in BALL:
                wB=(q[0]+d[0],q[1]+d[1],q[2]+d[2])
                wA=(wB[0]-shiftB[0]-T[0],wB[1]-shiftB[1]-T[1],wB[2]-shiftB[2]-T[2])
                if pic(B,wB)!=pic(A,wA): good=False; break
            if good: ok=True; used[T]=used.get(T,0)+1; break
        if not ok:
            bad+=1
            if bad<=3: print("   no match for",q,B['lab'][q])
    print("%s: %d near-field sites of B ; without a matching %d-ball in A: %d ; translations used: %d"%(name,n,D,bad,len(used)))
mode=sys.argv[1]; m=int(sys.argv[2]); K=int(sys.argv[3])
if mode=='m':
    A=build(m,K); B=build(m+2,K)
    TS=[(4,0,0),(-4,0,0),(0,4,0),(0,-4,0),(0,0,4),(0,0,-4),(0,2,2),(0,2,-2),(0,-2,2),(0,-2,-2)]
    check(A,B,(0,4,0),TS,"step m=%d -> %d (K=%d)"%(m,m+2,K))
else:
    A=build(m,K); B=build(m,K+1)
    base=[(0,0,0),(0,6,6),(10,-10,0),(-10,10,0),(12,0,12),(-12,0,-12),(0,-6,-6)]
    TS=[]
    for a in base:
        for b in base:
            t=(a[0]+b[0],a[1]+b[1],a[2]+b[2])
            if t not in TS: TS.append(t)
    check(A,B,(0,0,0),TS,"step K=%d -> %d (m=%d)"%(K,K+1,m))

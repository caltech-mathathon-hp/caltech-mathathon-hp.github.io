"""Bulk Lemma, Claim 1, for given m: the cover is valid (degrees, free bonds at ends, paths) and every path has >= 3 sites."""
import sys
from canon import *
from canon_patches import PATCH
for m in map(int,sys.argv[1:]):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    msg,paths=validate(X,adj,legit)
    print("m=%d: %s ; %d paths ; shortest %d sites ; all sites covered: %s"%(m,msg,len(paths),min(len(p) for p in paths),sum(len(p) for p in paths)==len(X)),flush=True)

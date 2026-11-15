"""Periodicity of the near field along the frame edges and the track (used in the Near-field Lemma, notes 10.7):
   the skin-1 picture (frame links, P^3 links, caps, bulk run ends, borrowed columns) around slot k, relative to the slot,
   is the same for all slots away from the vertices; likewise around track positions of the same kind."""
import sys
sys.argv=['build3.py','80','4','[[2,2],[2,2],[2,2],[2,2],[2,2],[2,2]]','20','nochain','0','natural','slotsig']
src=open('build3.py').read().split("# ---------- far field")[0].replace("import os\nif os.environ.get('NEARONLY'):","if False:")
exec(src)
RADIUS=9
norm=lambda l: 'tether' if 'tether' in l else l
def sig(ref):
    out=set()
    for q,l in reserved.items():
        if l=="zone" or skin(q)!=1: continue
        d=tuple(q[i]-ref[i] for i in range(3))
        if max(abs(x) for x in d)<=RADIUS: out.add((d,norm(l)))
    for v in bulkends:
        d=tuple(v[i]-ref[i] for i in range(3))
        if max(abs(x) for x in d)<=RADIUS: out.add((d,'bulk end'))
    for c in linkercaps:
        d=tuple(c[i]-ref[i] for i in range(3))
        if max(abs(x) for x in d)<=RADIUS: out.add((d,'col2',tuple(COL[c][1][i]-ref[i] for i in range(3))))
    return frozenset(out)
print("2-slots on e1 (index 6k):")
s1=[sig(e1[2*s]) for s in SL1]
print("   classes:",[s1.index(x)+1 for x in s1],"(slot k has the same picture as slot ...)")
print("6-slots on e2 (index 10k+6 from V_c):")
s2=[sig(e2c[2*s]) for s in SL2]
print("   classes:",[s2.index(x) for x in s2])
print("separators on the track:")
s3=[sig(z[2*j]) for j in JS]
print("   classes:",[s3.index(x)+1 for x in s3])
print("ring / track generic positions: P^3 links are unique paths (no choice), nothing to compare")

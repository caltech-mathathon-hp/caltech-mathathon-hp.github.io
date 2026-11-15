"""Section 42 of the note: a geometric count of long chains, for the search for a counterexample to Conjecture R.

Fix an axis direction.  The slice of the body S at level l splits into pieces (components under the four in-plane
steps).  For a piece p, D(p) is the set of the lower neighbours of its sites (four per site).  Write p -> p' if
p' = D(p) and p' is a whole piece of the next slice: p' grows out of p exactly as the slices of the upper half of a
regular octahedron do.  A geometric chain is a maximal sequence p_1 -> p_2 -> ... -> p_k; it is long if k - 1 > J.
L(S, J) = number of long geometric chains over the six directions.  For O_n and J < n - 1 this is 6.
(This is a stand-in for the chains of Section 12, which need a decoration: an exact dilation step is what a regular
growing piece with one parent looks like.  A body with 3 L(S, J) > U*(S) for J large would contradict Conjecture R.
Chains whose first piece is not a local top are the ones Theorem 36 does not pay for.)"""
from gmin import *

def chains(S, J):
    """list of (axis, sign, top level, steps, top) of the long geometric chains; top says whether the first piece is a
    local top (no site of it has an occupied neighbour in the slice above)"""
    out = []
    for ax in range(3):
        o = [i for i in range(3) if i != ax]
        for sg in (1, -1):
            sl = {}
            for h in S: sl.setdefault(sg * h[ax], set()).add((h[o[0]], h[o[1]]))
            comp = {}                                              # level -> list of pieces (frozensets)
            for l, sq in sl.items():
                seen = set(); ps = []
                for s in sq:
                    if s in seen: continue
                    c = {s}; st = [s]; seen.add(s)
                    while st:
                        u, v = st.pop()
                        for du, dv in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                            t = (u + du, v + dv)
                            if t in sq and t not in seen: seen.add(t); c.add(t); st.append(t)
                    ps.append(frozenset(c))
                comp[l] = ps
            nxt = {}; has_pred = set()
            for l, ps in comp.items():
                below = set(comp.get(l - 1, []))
                for p in ps:
                    d = frozenset(t for u, v in p for t in ((u + 1, v), (u - 1, v), (u, v + 1), (u, v - 1)))
                    if d in below: nxt[(l, p)] = (l - 1, d); has_pred.add((l - 1, d))
            for l, ps in comp.items():
                for p in ps:
                    if (l, p) in has_pred or (l, p) not in nxt: continue
                    k = 0; cur = (l, p)
                    while cur in nxt: cur = nxt[cur]; k += 1
                    if k > J:
                        up = sl.get(l + 1, ())
                        top = not any(t in up for u, v in p for t in ((u + 1, v), (u - 1, v), (u, v + 1), (u, v - 1)))
                        out.append((ax, sg, l, k, top))
    return out

def L(S, J): return len(chains(S, J))

if __name__ == '__main__':
    import time
    for n in (5, 6, 7, 8):
        S = octa(n); t = time.time(); c = chains(S, 3)
        print(f"O_{n}: U* = {cost(S)['U']}, long geometric chains (J = 3): {len(c)}, steps {sorted(x[3] for x in c)}  [{time.time() - t:.3f} s]")
    for n, v in ((7, (13, 1, 0)), (7, (12, 2, 0)), (7, (8, 3, 3)), (7, (5, 4, 3)), (7, (2, 2, 2)), (7, (1, 1, 0)), (7, (3, 3, 0)), (7, (6, 0, 0)), (7, (12, 0, 0)),
                 (9, (2, 2, 2)), (9, (17, 1, 0))):
        S = octa(n) | octa(n, v); c = chains(S, 3); u = cost(S)['U']
        print(f"O_{n} + translate by {v}: U* = {u}, long geometric chains (J = 3): {len(c)}, of which not from a local top {sum(1 for x in c if not x[4])}, U* - 3 L = {u - 3 * len(c)}, steps {sorted(x[3] for x in c)}")
    for k in (6, 9):
        S = tetra(k); print(f"tetrahedron of side {k}: U* = {cost(S)['U']}, long geometric chains (J = 3): {L(S, 3)}")

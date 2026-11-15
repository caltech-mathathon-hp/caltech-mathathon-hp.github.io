"""Lemma 51 of the note: the three interior paths.
O_N = {|x|+|y|+|z| <= N-1} (same parity class as O_n, N = n-2) is swept along the z-axis.  The slice z = c is a square
of k x k cells, k = N - |c|; the cell (i, j), 0 <= i, j <= K = k-1, is the site with x+y = 2i-K, x-y = 2j-K.
Corners: (K,K) on the +x axis, (K,0) on +y, (0,0) on -x, (0,K) on -y.

Path: (1,0,N-2), the top vertex, the other three sites of the slice z = N-2, then the slices z = N-3, ..., -(N-3), each
from a corner to a corner, the next slice entered at the corner on the same half-axis; then three sites of the slice
z = -(N-2), the bottom vertex, and (1,0,-(N-2)).  A slice that contains a cut is traversed by slicepath.candidates;
of the two candidates the first whose cut pair passes the test ok(p, p') is taken.  The last slice (3 x 3) leaves at a
corner on the y-axis.
Check (main): for every N in the range, every first cut (more than a quarter, less than half of the sites) and two second
cuts, the three parts are paths that cover O_N, the outer ends are the two fixed sites, and both cut pairs are pairs of
adjacent boundary sites that pass the test of surface.run_ends (run ends exist in one piece, of kind 'a' or 'b').
Cut pairs that touch the equatorial slice z = 0 are counted separately: they do not occur in the reduction."""
import sys, random
import slicepath as sp
from surface import Surface, adj, norm1

ADJ3 = [(0, 0), (0, 1), (0, 2), (1, 2), (2, 2), (2, 1), (1, 1), (1, 0), (2, 0)]      # 3 x 3 from (0,0) to the corner (2,0)

def cell_site(K, i, j, z):
    u, v = 2 * i - K, 2 * j - K
    return ((u + v) // 2, (u - v) // 2, z)

def build(N, cuts, ok=lambda p, q: True):
    """sites of O_N in path order; cuts = numbers of sites before each cut.  Returns (sites, info) or (None, reason)"""
    sites = [(1, 0, N - 2), (0, 0, N - 1), (0, 1, N - 2), (-1, 0, N - 2), (0, -1, N - 2)]
    entry = (0, 1); info = []                              # corner flags (i > 0, j > 0): (0,K) is on the -y axis
    for z in range(N - 3, -(N - 3) - 1, -1):
        k = N - abs(z); K = k - 1; done = len(sites); o = 0
        for c in cuts:
            if done < c < done + k * k: o = c - done
            if c == done: info.append(('between', z))
        if o:
            cands = sp.candidates(k, o)
        elif z == -(N - 3):
            cands = [sp.plain(3)] if entry[0] != entry[1] else [ADJ3]
        else:
            cands = [sp.plain(k)]
        chosen = None
        for path in cands:
            cells = [((K - r) if entry[0] else r, (K - c) if entry[1] else c) for r, c in path]
            pts = [cell_site(K, i, j, z) for i, j in cells]
            if o and not ok(pts[o - 1], pts[o]): continue
            chosen = (cells, pts); break
        if chosen is None: return None, ('no candidate passes', z, o, k)
        cells, pts = chosen
        if o: info.append(('inside', z, o, k))
        sites += pts; i, j = cells[-1]
        if i not in (0, K) or j not in (0, K): return None, ('exit not at a corner', z)
        entry = (i > 0, j > 0)
    if entry[0] == entry[1]: return None, ('last slice leaves on the x-axis',)
    s = 1 if entry[0] else -1                              # (K,0): +y axis, (0,K): -y axis
    zb = -(N - 2)
    sites += [(0, s, zb), (-1, 0, zb), (0, -s, zb), (0, 0, -(N - 1)), (1, 0, zb)]
    return sites, info

def check(N, cuts, sf=None):
    ok = (lambda p, q: sf.run_ends(p, q) is not None) if sf else (lambda p, q: True)
    sites, info = build(N, cuts, ok)
    if sites is None: return False, info
    size = N * (2 * N * N + 1) // 3; S = set(sites)
    if len(sites) != size or len(S) != size or any(norm1(h) > N - 1 for h in S): return False, 'cover'
    parts = [0] + list(cuts) + [size]
    for a, b in zip(parts, parts[1:]):
        if any(not adj(sites[u], sites[u + 1]) for u in range(a, b - 1)): return False, 'not a path'
    if sites[0] != (1, 0, N - 2) or sites[-1] != (1, 0, -(N - 2)): return False, 'outer ends'
    for c in cuts:
        p, q = sites[c - 1], sites[c]
        if not adj(p, q) or norm1(p) != N - 1 or norm1(q) != N - 1: return False, 'cut pair'
        if not ok(p, q): return False, ('run ends', p, q)
    return True, info

def slice_of(N, c):
    """(z, o): the cut after c sites lies in the slice z after o of its sites (o = 0: between the slices z+1 and z)"""
    done = 5
    for z in range(N - 3, -(N - 3) - 1, -1):
        k = N - abs(z)
        if done <= c < done + k * k: return z, c - done
        done += k * k

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(1)
    for N in range(lo, hi + 1, 2):
        sf = Surface(N + 2); size = N * (2 * N * N + 1) // 3
        lo1, hi1 = size // 4 + 1, (size - 1) // 2          # first part: more than a quarter, less than half
        away = [0, 0]; near = [0, 0]; kinds = {}
        for c1 in range(lo1, hi1 + 1):
            for cuts in ([c1, size - c1], [c1, size - rng.randint(lo1, hi1)]):   # second cut: mirror position, and a random one
                good, info = check(N, cuts, sf)
                dist = min(min(abs(z), abs(z + 1)) if o == 0 else abs(z) for z, o in (slice_of(N, c) for c in cuts))
                st = away if dist >= 1 else near; st[0] += 1; st[1] += not good
                if good:
                    for x in info: kinds[x[0]] = kinds.get(x[0], 0) + 1
                elif dist >= 1: print('   FAIL', N, cuts, info)
        print(f"N = {N} (n = {N+2}): pairs of cuts with no cut pair in the slice z = 0: {away[0]}, failing {away[1]} "
              f"(cuts inside a slice {kinds.get('inside', 0)}, between two slices {kinds.get('between', 0)}, counted over all good cases); "
              f"with a cut pair in the slice z = 0: {near[0]}, failing {near[1]} (not needed)", flush=True)

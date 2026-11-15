"""One octahedron of the intended fold (Proposition 52 of the note): for three run lengths s_1 + s_2 + s_3 = |O_{n-2}|
it returns the three item runs (surface end, interior path, surface end), the adjacent pairs of singly decorated sites
and the doubly decorated sites, each with the coat sites (slots) of its chain P's.

Run ends: the two tips (2,1,n-4) and (2,1,-(n-4)) of the piece x, y > 0 for the outer ends; at a cut, the two sites
given by surface.run_ends (in the regime of the note: the path ends shifted by (sign x, sign y, 0) of their side).
Check (main): for every admissible pair of cuts tried, the six run ends are different singly decorated sites next to
the six path ends, every other singly decorated site is in exactly one adjacent pair, and with these chain neighbours
the octahedron has exactly 18 defect units.  Mode 'regime': n = 3*B*t + 2 and all triples a_1 + a_2 + a_3 = B with
B/4 < a_i < B/2, as in the reduction; it also reports how far the cut slices are from the equator and which kinds
of run ends occur."""
import sys, random
from surface import Surface, adj, norm1, units, pairing
import interior3

def octahedron(sf, lengths):
    n = sf.n; N = n - 2; c1, c2 = lengths[0], lengths[0] + lengths[1]
    ok = lambda p, q: sf.run_ends(p, q) is not None
    sites, info = interior3.build(N, [c1, c2], ok)
    if sites is None: return None, info
    e0, e3 = (2, 1, n - 4), (2, 1, -(n - 4))
    r1, r2 = sf.run_ends(sites[c1 - 1], sites[c1]), sf.run_ends(sites[c2 - 1], sites[c2])
    if r1 is None or r2 is None: return None, 'no run ends'
    ends = [e0, r1[0], r1[1], r2[0], r2[1], e3]
    if len(set(ends)) != 6 or any(e not in sf.single for e in ends): return None, 'run ends not distinct'
    runs = [[e0] + sites[:c1] + [r1[0]], [r1[1]] + sites[c1:c2] + [r2[0]], [r2[1]] + sites[c2:] + [e3]]
    if any(not adj(a, b) for run in runs for a, b in zip(run, run[1:])): return None, 'run not a path'
    pairs = []
    for key in sf.pieces:
        m = pairing(sf.rows(key), {e for e in ends if sf.piece_of(e) == key})
        if m is None: return None, ('no pairing', key)
        pairs += m
    php = sorted(sf.double)
    return dict(runs=runs, pairs=pairs, php=php, kinds=(r1[2], r2[2]), info=info, ends=ends), None

def verify(sf, oc):
    """independent of the construction: counts and the 18 units"""
    n = sf.n; S = sf.S
    used = [h for run in oc['runs'] for h in run] + [h for p in oc['pairs'] for h in p] + list(oc['php'])
    if len(used) != len(S) or set(used) != S: return False
    if len(oc['pairs']) != 2 * n * n - 12 * n + 9 or len(oc['php']) != 16 * n - 18: return False
    if any(not adj(a, b) or a not in sf.single or b not in sf.single for a, b in oc['pairs']): return False
    if any(run[0] not in sf.single or run[-1] not in sf.single or any(norm1(h) > n - 3 for h in run[1:-1]) for run in oc['runs']): return False
    u = units(S, sf.slots)                                   # the chain P's of every surface site are its slots
    return len(u) == 6 and all(sum(v) == 3 for v in u.values())

slice_of = interior3.slice_of

if __name__ == '__main__':
    if sys.argv[1] == 'regime':
        B, t = int(sys.argv[2]), int(sys.argv[3]); N = 3 * B * t; n = N + 2
        sf = Surface(n); size = N * (2 * N * N + 1) // 3; M = size // B; assert size % B == 0
        tried = bad = 0; kinds = {}; zmin = 10 ** 9; zmax = 0
        for a1 in range(B // 4 + 1, (B + 1) // 2):
            for a2 in range(B // 4 + 1, (B + 1) // 2):
                a3 = B - a1 - a2
                if not (B / 4 < a3 < B / 2): continue
                tried += 1; oc, err = octahedron(sf, [a1 * M, a2 * M, a3 * M])
                if oc is None or not verify(sf, oc): bad += 1; print('   FAIL', (a1, a2, a3), err); continue
                for kd in oc['kinds']: kinds[kd] = kinds.get(kd, 0) + 1
                for c in (a1 * M, (a1 + a2) * M):
                    z, o = slice_of(N, c); zz = min(abs(z), abs(z + 1)) if o == 0 else abs(z)
                    zmin = min(zmin, zz); zmax = max(zmax, abs(z))
        print(f"B = {B}, t = {t}, n = {n}: triples {tried}, failing {bad}; run ends of kind a/b: {kinds.get('a', 0)}/{kinds.get('b', 0)}; "
              f"cut slices at |z| between {zmin} and {zmax} (N = {N})", flush=True)
    else:
        lo, hi, cnt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(6); ZMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        for n in range(lo, hi + 1, 2):
            N = n - 2; sf = Surface(n); size = N * (2 * N * N + 1) // 3; lo1, hi1 = size // 4 + 1, (size - 1) // 2
            tried = bad = skipped = 0; kinds = {}
            c1s = range(lo1, hi1 + 1) if cnt == 0 else rng.sample(range(lo1, hi1 + 1), min(cnt, hi1 - lo1 + 1))
            for c1 in c1s:
                s3 = c1 if cnt == 0 else rng.randint(lo1, hi1)   # cnt = 0: every first cut, with the mirror position as second cut
                c2 = size - s3
                zs = []
                for c in (c1, c2):
                    z, o = slice_of(N, c); zs.append(min(abs(z), abs(z + 1)) if o == 0 else abs(z))
                if min(zs) < ZMIN or not (size / 4 < c2 - c1 < size / 2): skipped += 1; continue
                tried += 1; oc, err = octahedron(sf, [c1, c2 - c1, s3])
                if oc is None or not verify(sf, oc): bad += 1; print('   FAIL', n, (c1, c2), err); continue
                for kd in oc['kinds']: kinds[kd] = kinds.get(kd, 0) + 1
            print(f"n = {n}: pairs of cuts tried {tried} (cut slices at |z| >= {ZMIN}), failing {bad}; run ends of kind a/b: {kinds.get('a', 0)}/{kinds.get('b', 0)}", flush=True)


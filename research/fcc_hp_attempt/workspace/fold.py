"""The intended fold of the reduction, built in full (Lemma 53 and Theorem 54 of the note).

Input: n, the items a_1..a_3m, B, and a partition into m triples.  M = |O_{n-2}| / B.
The m octahedra are placed at (0, 0, j*D).  Blocks of the word, in order: the 3m item runs, then the m(16n-18) single
H's (octahedron by octahedron), then the m(2n^2-12n+9) pairs HH.  Every block has an in-slot and an out-slot (coat
sites); the P-run between two consecutive blocks goes from the out-slot of one to the in-slot of the next.

Routing of a P-run (all coordinates relative to the axis x = y = 0):
  ray    from a slot p = (x, y, z): direction d = (sx, sy, 0), sx = sign x, sy = sign y (zero counts as +),
         until |x| + |y| = rho_p;
  arc    at height z along |x| + |y| = rho_p to the point (rho_p, 0, z);
  column in the plane y = 0, the sites (rho_p + (i mod 2), 0, z + i), up to the height Z_r of the run;
  bridge in the plane z = Z_r: from the top of one column out along y = 1, 2 to x = X, through (X, 0), back along
         y = -1, -2 to the top of the other column; up to three kinks (one extra site at height Z_r + 1 each).
The radii rho_p are different for all slots, spaced by 3, and ordered so that among slots of one height the one whose
arc is shorter has the smaller radius.  The heights Z_r are different for all runs, spaced by 2, above all octahedra.
X and the number of kinks are chosen so that the run has exactly lam sites.  The first and the last P-run of the
chain have a free end and run out along y = 1, 2 at their height.  lam = 92 m n^2 + 188 m n + 14 n + 46 for every run.

Output: the coordinates of all residues (numpy array) and the word.  check.py verifies the result independently."""
import sys, time
import numpy as np
from surface import Surface, sg, add
from octa import octahedron, verify

def route(p, rho, Z):
    """sites from the slot p along ray, arc and column up to height Z, as an array; the last site is the column top"""
    x, y, z = p; sx, sy = (sg(x) or 1), (sg(y) or 1)
    T = (rho - abs(x) - abs(y)) // 2; t = np.arange(T + 1)
    parts = [np.stack([x + sx * t, y + sy * t, np.full(T + 1, z)], 1)]
    cx, cy = x + sx * T, y + sy * T                     # on |x| + |y| = rho
    if sx < 0:                                           # first to the corner on the y-axis: step (1, sy)
        s = np.arange(1, -cx + 1); parts.append(np.stack([cx + s, cy + sy * s, np.full(len(s), z)], 1)); cx, cy = 0, cy + sy * (-cx)
    s = np.arange(1, abs(cy) + 1); parts.append(np.stack([cx + s, cy - sg(cy) * s, np.full(len(s), z)], 1))
    i = np.arange(1, Z - z + 1); parts.append(np.stack([rho + i % 2, np.zeros(len(i), int), z + i], 1))
    return np.concatenate(parts)

def zig(x0, n, Z, sign, kinks=0):
    """n sites (x0 + i, sign*(1 or 2), Z), i = 1..n (x decreasing if sign < 0 is handled by the caller); kinks after i = 1, 3, 5"""
    out = []
    for i in range(1, n + 1):
        out.append((x0 + i, 1 if i % 2 else 2, Z))
        if i % 2 and (i + 1) // 2 <= kinks and i < n: out.append((x0 + i + 1, 1, Z + 1))
    return out

def build(n, items, B, triples, verbose=False):
    m = len(triples); N = n - 2; size = N * (2 * N * N + 1) // 3; assert size % B == 0 and n % 2 == 0
    M = size // B; D = 2 * n + 6; sf = Surface(n)
    shift = lambda h, j: (h[0], h[1], h[2] + j * D)
    slot1 = lambda h: sf.slots[h][0]
    item_block = {}; php_blocks = []; pair_blocks = []
    for j, tr in enumerate(triples):
        assert sum(items[i] for i in tr) == B
        oc, err = octahedron(sf, [items[i] * M for i in tr])
        if oc is None: raise ValueError(f'octahedron {j}: {err}')
        assert verify(sf, oc)
        for i, run in zip(tr, oc['runs']):
            item_block[i] = ([shift(h, j) for h in run], shift(slot1(run[0]), j), shift(slot1(run[-1]), j))
        php_blocks += [([shift(h, j)], shift(sf.slots[h][0], j), shift(sf.slots[h][1], j)) for h in oc['php']]
        pair_blocks += [([shift(a, j), shift(b, j)], shift(slot1(a), j), shift(slot1(b), j)) for a, b in oc['pairs']]
    blocks = [item_block[i] for i in range(3 * m)] + php_blocks + pair_blocks
    # radii
    ports = [b[1] for b in blocks] + [b[2] for b in blocks]; assert len(set(ports)) == len(ports)
    def key(p):
        x, y = p[0], p[1]; sx, sy = (sg(x) or 1), (sg(y) or 1)
        return (0 if sx > 0 else 1, -(x - y) if sx * sy > 0 else -(x + y))
    R0 = 2 * n + 4; rho = {}
    for idx, p in enumerate(sorted(ports, key=lambda p: key(p) + p)):
        r = R0 + 3 * idx; rho[p] = r + (abs(p[0]) + abs(p[1]) - r) % 2
    Rmax = max(rho.values()) + 2; Z0 = (m - 1) * D + n + 4
    nruns = len(blocks) + 1; height = lambda r: Z0 + 2 * r
    # common length
    def geom(r):
        a, b = blocks[r - 1][2], blocks[r][1]; Z = height(r)
        la = (rho[a] - abs(a[0]) - abs(a[1])) // 2 + 1 + arclen(a, rho[a]) + (Z - a[2])
        lb = (rho[b] - abs(b[0]) - abs(b[1])) // 2 + 1 + arclen(b, rho[b]) + (Z - b[2])
        A = rho[a] + (Z - a[2]) % 2; Bx = rho[b] + (Z - b[2]) % 2
        return la, lb, A, Bx
    def arclen(p, r):
        x, y = p[0], p[1]; sx, sy = (sg(x) or 1), (sg(y) or 1); T = (r - abs(x) - abs(y)) // 2
        cx, cy = x + sx * T, y + sy * T
        return (-cx + r) if sx < 0 else abs(cy)
    Xmin = Rmax + 12
    need = max(la + lb - A - Bx - 1 for la, lb, A, Bx in (geom(r) for r in range(1, nruns - 1))) + 2 * Xmin + 4
    lam = common_length(n, m); assert lam >= need and lam % 2 == 0
    if verbose: print(f"  slots {len(ports)}, largest radius {Rmax}, P-runs {nruns}, lambda = {lam} (the routes need at least {need})", flush=True)
    chunks = []; word = []
    def free_run(p, r, first):
        Z = height(r); rt = route(p, rho[p], Z); rem = lam - len(rt); assert rem >= 1
        ext = np.array(zig(int(rt[-1][0]), rem, Z, 1), int).reshape(-1, 3)
        run = np.concatenate([rt, ext]); return run[::-1] if first else run
    chunks.append(free_run(blocks[0][1], 0, True)); word.append('P' * lam)
    for r, blk in enumerate(blocks):
        chunks.append(np.array(blk[0], int)); word.append('H' * len(blk[0]))
        if r == len(blocks) - 1:
            chunks.append(free_run(blk[2], nruns - 1, False))
        else:
            a, b = blk[2], blocks[r + 1][1]; Z = height(r + 1)
            ra, rb = route(a, rho[a], Z), route(b, rho[b], Z); A, Bx = int(ra[-1][0]), int(rb[-1][0])
            twoX = lam - len(ra) - len(rb) + A + Bx + 1
            kinks = (twoX - 2 * A) % 4; X = (twoX - kinks) // 2; assert X >= Xmin and (X - A) % 2 == 0 and (X - Bx) % 2 == 0
            out = zig(A, X - A - 1, Z, 1, kinks) + [(X, 0, Z)]
            back = [(X - i, -1 if i % 2 else -2, Z) for i in range(1, X - Bx)]
            chunks.append(np.concatenate([ra, np.array(out + back, int), rb[::-1]]))
        word.append('P' * lam)
        assert len(chunks[-1]) == lam, (len(chunks[-1]), lam)
    return np.concatenate(chunks).astype(np.int32), ''.join(word), dict(lam=lam, M=M, m=m, n=n)

def common_length(n, m):
    """the length lambda of the P-runs in the reduction; it depends on n and m only"""
    return 92 * m * n * n + 188 * m * n + 14 * n + 46

def expected_word(n, items, B, lam):
    """the word of Section 6 of the note"""
    m = len(items) // 3; N = n - 2; M = N * (2 * N * N + 1) // 3 // B
    return 'P' * lam + ''.join('H' * (a * M + 2) + 'P' * lam for a in items) + ('H' + 'P' * lam) * (m * (16 * n - 18)) + ('HH' + 'P' * lam) * (m * (2 * n * n - 12 * n + 9))

if __name__ == '__main__':
    import check
    INST = {'n8': (8, [24, 24, 25, 23, 25, 25], 73, [(0, 1, 2), (3, 4, 5)]),
            'n8x': (8, [24, 23, 25, 25, 24, 25], 73, [(0, 2, 4), (1, 3, 5)]),
            'n10': (10, [14, 14, 15, 13, 15, 15], 43, [(0, 1, 2), (3, 4, 5)]),
            'n10x': (10, [14, 13, 15, 15, 14, 15], 43, [(0, 2, 4), (1, 3, 5)]),
            'n12': (12, [3, 3, 4, 3, 3, 4], 10, [(0, 1, 2), (3, 4, 5)]),
            'n8m3': (8, [24, 25, 23, 24, 26, 25, 24, 24, 24], 73, [(0, 1, 3), (2, 4, 6), (5, 7, 8)]),
            'n14': (14, [5, 6, 6, 5, 5, 7], 17, [(0, 1, 2), (3, 4, 5)])}
    for name in sys.argv[1:]:
        n, items, B, triples = INST[name]; t0 = time.time()
        print(f"instance {name}: n = {n}, items {items}, B = {B}, triples {triples}", flush=True)
        xyz, word, par = build(n, items, B, triples, verbose=True)
        print(f"  chain of {len(word)} residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: {word == expected_word(n, items, B, common_length(n, len(triples)))}", flush=True)
        print("  " + check.report(xyz, word, par['m']), flush=True)

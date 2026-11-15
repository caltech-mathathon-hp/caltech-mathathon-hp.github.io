# FCC HP folding: verification code, sixteenth pass (14 Nov 2026)

Scripts for Part III of the note (`claude/fcc-hp-hardness-attempt-part3.md`, Sections 26 to 32): the completeness of the reduction. They are self-contained: none of them imports a script of an earlier pass. `surface.py` recomputes the decoration of Lemma 47 and counts its defect units from the definitions of Theorem 5. Python 3 with numpy (only `fold.py` and `check.py` need numpy).

| Script | Statement | Run |
|---|---|---|
| `slicepath.py` | Lemma 49 (cut slice) | `python3 slicepath.py 3 44` |
| `surface.py` | decoration, pieces, rows, strips; the pairing search of Lemma 50 | `python3 surface.py 8 30` |
| `pairtest.py`, `strips.py` | Lemma 50 over all defects | `python3 pairtest.py 12 24 4 9`, `python3 pairtest.py 12 20 3 7`, `python3 pairtest.py 12 14 1 6`, `python3 strips.py` |
| `interior3.py`, `canon.py` | Lemma 51 (interior paths, run ends) | `python3 interior3.py 8 22`, `python3 canon.py 12 24` |
| `octa.py` | Proposition 52 (one octahedron) | `python3 octa.py 18 24 0 3`, `python3 octa.py regime B t` |
| `fold.py`, `check.py`, `controls.py` | Lemma 53 (routing), Theorem 54 (whole fold), independent checker | `python3 fold.py n8 n8x n8m3 n10 n10x n12 n14`, `python3 controls.py` |

## `slicepath.py`

```python
"""Lemma 49 of the note: the cut slice.
A slice of O_N by a plane z = const is a k x k square of cells (r, c) with grid adjacency.  For 1 <= o <= k*k - 1 we
need a Hamiltonian path of the square from the corner (0,0) to a corner such that the o-th and the (o+1)-th cell are
adjacent and lie on one side of the square (the cut pair).

Constructions (rows 0..k-1, q, s = divmod(o, k)):
  plain    : the row snake; used when s = 0 or q = 0.
  forward  : 1 <= q <= k-2, s >= 1.  Row q-1 runs towards side A.
             first part : rows 0..q-2; row q-1; and s cells of row q in vertical pairs with row q-1:
                          s odd : the last s columns before A, ends at (q, A);     the second part starts at (q+1, A)
                          s even: the s columns before the column at A, ends at (q-1, A); the second part starts at (q, A)
             second part: the rest of row q is a ledge of l cells at the far side (l = k-s, resp. k-1-s) over rows q+1..
                          l even: row q+1 up to the ledge, the ledge in vertical pairs with row q+1, then the row snake;
                          l odd (then k is even), l >= 3, at least two rows below row q: rows q+1, q+2 in vertical pairs
                          up to the ledge, the 3 x l block under the ledge as a spiral, then the row snake.
  reversed : the forward construction for k*k - o, run backwards and reflected so that it starts at (0,0).
  special  : k even, o = 2k-2 and o = 2k-1 (and their reversals), where forward and reversed both fail.
Each construction also has a transposed version (r and c exchanged); it has the mirrored cut pair.
Check (main): for every k in the range and every o, some construction gives a valid path, and for a cut pair that
contains a corner the transposed version puts the other cell on the other side at that corner."""
import sys

def snake_rows(rows, k, c0, d):
    """rows: iterable of row indices; start column c0, direction d (+1/-1); returns cells and the next (c0, d)"""
    out = []
    for r in rows:
        out += [(r, c0 + d * t) for t in range(k)]
        c0, d = c0 + d * (k - 1), -d
    return out, c0, d

def plain(k):
    return snake_rows(range(k), k, 0, 1)[0]

def forward(k, o):
    q, s = divmod(o, k)
    if s == 0 or q == 0: return plain(k)
    if q == k - 1: return None
    out, c0, d = snake_rows(range(q - 1), k, 0, 1)
    col = lambda t: c0 + d * t                       # col(k-1) is the side A where row q-1 ends
    if s % 2 == 1:
        out += [(q - 1, col(t)) for t in range(k - s)]
        for u in range(s):
            c = col(k - s + u); out += [(q - 1, c), (q, c)] if u % 2 == 0 else [(q, c), (q - 1, c)]
        l = k - s
    else:
        out += [(q - 1, col(t)) for t in range(k - s - 1)]
        for u in range(s):
            c = col(k - s - 1 + u); out += [(q - 1, c), (q, c)] if u % 2 == 0 else [(q, c), (q - 1, c)]
        out += [(q - 1, col(k - 1))]
        l = k - 1 - s
    assert len(out) == o
    if s % 2 == 0: out.append((q, col(k - 1)))
    h = k - 1 - q                                    # rows below row q
    if l % 2 == 0:
        out += [(q + 1, col(t)) for t in range(k - 1, l - 1, -1)]
        for u, t in enumerate(range(l - 1, -1, -1)):
            c = col(t); out += [(q + 1, c), (q, c)] if u % 2 == 0 else [(q, c), (q + 1, c)]
        nxt = q + 2
    else:
        if l < 3 or h < 2 or (k - l) % 2 == 0: return None
        for u, t in enumerate(range(k - 1, l - 1, -1)):
            c = col(t); out += [(q + 1, c), (q + 2, c)] if u % 2 == 0 else [(q + 2, c), (q + 1, c)]
        out += [(q + 2, col(l - 1)), (q + 1, col(l - 1))]
        out += [(q, col(t)) for t in range(l - 1, -1, -1)]
        out += [(q + 1, col(t)) for t in range(0, l - 1)]
        out += [(q + 2, col(t)) for t in range(l - 2, -1, -1)]
        nxt = q + 3
    rest, _, _ = snake_rows(range(nxt, k), k, col(0), d)
    return out + rest

def special(k, o):
    if k % 2 or k < 4: return None
    if o == 2 * k - 2:
        out = [(0, c) for c in range(k - 1)] + [(1, c) for c in range(k - 2, -1, -1)]
        for c in range(k):
            out += [(r, c) for r in (range(2, k) if c % 2 == 0 else range(k - 1, 1, -1))]
        return out + [(1, k - 1), (0, k - 1)]
    if o == 2 * k - 1:
        out = [(0, c) for c in range(k)] + [(r, k - 1) for r in range(1, k)]
        out += [(r, k - 2) for r in range(k - 1, 0, -1)] + [(1, c) for c in range(k - 3, -1, -1)]
        for r in range(2, k):
            out += [(r, c) for c in (range(k - 2) if r % 2 == 0 else range(k - 3, -1, -1))]
        return out
    return None

def backwards(path, k):
    """reverse a path that ends at a corner and reflect it so that it starts at (0,0)"""
    if path is None: return None
    p = path[::-1]; fr, fc = p[0][0] != 0, p[0][1] != 0
    return [((k - 1 - r) if fr else r, (k - 1 - c) if fc else c) for r, c in p]

def side_of(k, a, b):
    """the common side of two cells: 'r0', 'rK', 'c0', 'cK' or None"""
    for name, f in (('r0', lambda x: x[0] == 0), ('rK', lambda x: x[0] == k - 1), ('c0', lambda x: x[1] == 0), ('cK', lambda x: x[1] == k - 1)):
        if f(a) and f(b): return name
    return None

def valid(k, o, path):
    if path is None or len(path) != k * k or len(set(path)) != k * k or path[0] != (0, 0): return False
    if any(not (0 <= r < k and 0 <= c < k) for r, c in path): return False
    if any(abs(a[0] - b[0]) + abs(a[1] - b[1]) != 1 for a, b in zip(path, path[1:])): return False
    if path[-1][0] not in (0, k - 1) or path[-1][1] not in (0, k - 1): return False
    return 1 <= o <= k * k - 1 and side_of(k, path[o - 1], path[o]) is not None

def base(k, o):
    """one valid path for (k, o), or None"""
    for p in (forward(k, o), backwards(forward(k, k * k - o), k), special(k, o), backwards(special(k, k * k - o), k)):
        if valid(k, o, p): return p
    return None

def candidates(k, o):
    """the base path and its transpose"""
    p = base(k, o)
    return [] if p is None else [p, [(c, r) for r, c in p]]

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for k in range(lo, hi + 1):
        bad = corner_pairs = same_side = 0; which = dict(forward=0, reversed=0, special=0)
        for o in range(1, k * k):
            p = base(k, o)
            if p is None: bad += 1; continue
            if valid(k, o, forward(k, o)): which['forward'] += 1
            elif valid(k, o, backwards(forward(k, k * k - o), k)): which['reversed'] += 1
            else: which['special'] += 1
            t = [(c, r) for r, c in p]
            if not valid(k, o, t): bad += 1; continue
            pair = (p[o - 1], p[o]); corner = [x for x in pair if x[0] in (0, k - 1) and x[1] in (0, k - 1)]
            if corner:
                corner_pairs += 1
                if side_of(k, *pair) == side_of(k, t[o - 1], t[o]): same_side += 1
        print(f"k = {k}: offsets without a valid path: {bad} of {k*k-1}; by construction {which}; cut pairs with a corner: {corner_pairs}, transposed pair on the same side: {same_side}", flush=True)
```

## `surface.py`

```python
"""Surface of O_n in the intended fold: the decoration of Lemma 47 (no switches), its defect units (Theorem 5),
the four pieces of singly decorated sites with their rows, the run ends at a cut, and the pairing of Lemma 50.

O_n = {|x|+|y|+|z| <= n-1, x+y+z = n-1 mod 2}; the poles are on the z-axis.
A piece is the set of singly decorated sites with given signs of x and y.  In a piece the row z = r is ordered by
xi, where (xi, eta) = (|x|, |y|) if x*y > 0 and (|y|, |x|) otherwise; xi runs from 2 (left end) to the site with
eta = 1 (right end, next to the half-plane through the z-axis that the piece owns).

Pairing (Lemma 50).  Rows from the top tip to the bottom tip.  Two consecutive rows form a strip; listing its sites
alternately from the two rows gives an order in which sites at distance 1 or 2 are adjacent, so the sites that are
left after removing a set R form a path in this order as long as no two consecutive positions are both removed.
A Hamiltonian path of the piece less R is built as a sequence of bands (single rows, or strips), each traversed from
one end to the other; hamilton() searches this family by a small dynamic program.  Pairing = consecutive pairs."""
import sys, itertools
ROOTS = [(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]
RS = set(ROOTS)
add = lambda a, b: (a[0] + b[0], a[1] + b[1], a[2] + b[2])
sub = lambda a, b: (a[0] - b[0], a[1] - b[1], a[2] - b[2])
adj = lambda a, b: sub(a, b) in RS
sg = lambda v: (v > 0) - (v < 0)
norm1 = lambda h: abs(h[0]) + abs(h[1]) + abs(h[2])

def body(n):
    m = n - 1
    return {(x, y, z) for x in range(-m, m + 1) for y in range(-m + abs(x), m - abs(x) + 1) for z in range(-m, m + 1)
            if abs(x) + abs(y) + abs(z) <= m and (x + y + z - m) % 2 == 0}

def decoration(n):
    """Lemma 47 without switches: owner[p] = the surface site whose chain P sits on the coat site p"""
    S = body(n); coat = {add(h, r) for h in S for r in ROOTS} - S; owner = {}
    for p in coat:
        X, Y, Z = map(abs, p); s = tuple(map(sg, p)); sx, sy, sz = s; zeros = (X == 0) + (Y == 0) + (Z == 0)
        if zeros == 0:
            t = sx * sy
            if X == n - 1: o = (n - 2, 1, 0) if sy * sz > 0 else (n - 2, 0, 1)
            elif Y == n - 1: o = (0, n - 2, 1) if sx * sz > 0 else (1, n - 2, 0)
            elif Z == n - 1: o = (1, 0, n - 2) if t > 0 else (0, 1, n - 2)
            elif Y == 1 and X <= n - 3 and t > 0: o = (X, 0, Z - 1)
            elif X == 1 and Y <= n - 3 and t < 0: o = (0, Y, Z - 1)
            elif Y == 1: o = (X - 1, 1, Z - 1)
            elif X == 1: o = (1, Y - 1, Z - 1)
            else: o = (X - 1, Y - 1, Z)
        elif zeros == 1:
            if max(X, Y, Z) == n:
                small = [i for i in range(3) if (X, Y, Z)[i] == 1][0]
                if s[small] < 0: continue
                o = tuple((n - 1) * (c == n) for c in (X, Y, Z))
            else: o = tuple(c - 1 if c else 0 for c in (X, Y, Z))
        else: continue
        owner[p] = tuple(o[i] * (s[i] or 1) for i in range(3))
    return S, coat, owner

def units(S, slots):
    """defect units alpha, beta, gamma of Theorem 5 for a set S of H sites; slots[h] = the chain P's of h (sites)"""
    res = {}
    for h in S:
        M = [add(h, r) for r in ROOTS if add(h, r) not in S]
        if not M: continue
        P = slots.get(h, []); L = [x for x in M if x not in P]
        K = {a: [x for x in (add(h, r) for r in ROOTS) if adj(x, a)] for a in P}
        A = {x for a in P for x in K[a] if x not in S and x not in P}
        Bset = {x for r in ROOTS if add(h, r) in S for x in slots.get(add(h, r), []) if adj(x, h)}
        tau = len(A) + sum(sum(1 for x in K[a] if x in S) for a in P)
        al = sum(1 for x in L if x not in A); be = sum(1 for x in L if x not in Bset)
        ga = tau - 4 if len(P) == 1 else (tau - 5 if len(P) == 2 else 0)
        if al or be or ga: res[h] = (al, be, ga)
    return res

class Surface:
    def __init__(self, n):
        self.n = n; self.S, self.coat, self.owner = decoration(n)
        self.slots = {}
        for p, h in self.owner.items(): self.slots.setdefault(h, []).append(p)
        self.surface = {h for h in self.S if any(add(h, r) not in self.S for r in ROOTS)}
        self.single = {h for h, v in self.slots.items() if len(v) == 1}
        self.double = {h for h, v in self.slots.items() if len(v) == 2}
        self.pieces = {}
        for h in self.single: self.pieces.setdefault((sg(h[0]), sg(h[1])), {}).setdefault(h[2], []).append(h)
        for pc in self.pieces.values():
            for z in pc: pc[z].sort(key=self.xi)
    def xi(self, h): return abs(h[0]) if h[0] * h[1] > 0 else abs(h[1])
    def eta(self, h): return abs(h[1]) if h[0] * h[1] > 0 else abs(h[0])
    def piece_of(self, h): return (sg(h[0]), sg(h[1]))
    def rows(self, key): return [self.pieces[key][z] for z in sorted(self.pieces[key], reverse=True)]
    def valid(self):
        n = self.n
        ok = len(self.coat) - len(self.owner) == 12 and all(h in self.S and adj(p, h) for p, h in self.owner.items())
        ok = ok and set(self.slots) == self.surface and max(len(v) for v in self.slots.values()) <= 2
        u = units(self.S, self.slots); verts = {h for h in self.S if norm1(h) == n - 1 and sorted(map(abs, h))[1] == 0}
        ok = ok and set(u) == verts and all(sum(v) == 3 for v in u.values()) and len(self.double) == 16 * n - 18
        ok = ok and all(not (set(self.slots[h]) and len(self.slots[h]) == 2 and not adj(*self.slots[h])) for h in self.double)
        return ok
    def candidates(self, p):
        """singly decorated surface neighbours of an interior site p"""
        return [add(p, r) for r in ROOTS if add(p, r) in self.single]
    def run_ends(self, p, q):
        """run ends for the two path ends p, q at a cut: e next to p, f next to q, e != f, in one piece, and either
        in one row and adjacent (kind 'a'; the row z = z(p) is preferred), or the right ends of two consecutive rows (kind 'b')"""
        best = None
        for e in self.candidates(p):
            for f in self.candidates(q):
                if e == f or self.piece_of(e) != self.piece_of(f) or not adj(e, f): continue
                if e[2] == f[2]: rank = 0 if e[2] == p[2] else 1; kind = 'a'
                elif self.eta(e) == 1 and self.eta(f) == 1 and abs(e[2] - f[2]) == 1: rank = 2; kind = 'b'
                else: continue
                if best is None or rank < best[0]: best = (rank, e, f, kind)
        return None if best is None else best[1:]

def strip_order(top, bot):
    """sites of two consecutive rows listed alternately from the left, so that positions at distance <= 2 are adjacent"""
    for a, b in ((top, bot), (bot, top)):
        if len(a) < len(b): continue
        out = []
        for i in range(len(a)):
            out.append(a[i])
            if i < len(b): out.append(b[i])
        if all(adj(out[i], out[i + 1]) for i in range(len(out) - 1)) and all(adj(out[i], out[i + 2]) for i in range(len(out) - 2)): return out
    raise ValueError('rows do not form a strip')

def is_path(seq):
    return all(adj(x, y) for x, y in zip(seq, seq[1:]))

def band_traversals(rows, i, width, R):
    """the ways to traverse a band (row i alone, or rows i and i+1) less R, as lists of sites"""
    if width == 1:
        seq = [h for h in rows[i] if h not in R]
        cands = [seq, seq[::-1]]
        if len(seq) + sum(1 for h in rows[i] if h in R) != len(rows[i]): cands = []
    else:
        seq = [h for h in strip_order(rows[i], rows[i + 1]) if h not in R]
        cands = []
        for s in (seq, seq[::-1]):
            for a in (0, 1):
                for b in (0, 1):
                    t = list(s)
                    if a and len(t) >= 2: t[0], t[1] = t[1], t[0]
                    if b and len(t) >= 4: t[-1], t[-2] = t[-2], t[-1]
                    cands.append(t)
    return [t for t in cands if t and is_path(t)]

def hamilton(rows, R):
    """a Hamiltonian path of the piece less R through bands in order (rows from the top), or None; prefers few strips"""
    T = len(rows)
    best = [dict() for _ in range(T + 1)]; best[0][None] = (0, None)     # best[i][last site] = (strips used, back pointer)
    for i in range(T):
        for last, (cost, _) in list(best[i].items()):
            if all(h in R for h in rows[i]):                              # a row that is removed entirely (a tip)
                if last not in best[i + 1] or best[i + 1][last][0] > cost: best[i + 1][last] = (cost, (i, last, []))
                continue
            for width in (1, 2):
                if i + width > T: continue
                for t in band_traversals(rows, i, width, R):
                    if last is not None and not adj(last, t[0]): continue
                    c = cost + (width == 2)
                    if t[-1] not in best[i + width] or best[i + width][t[-1]][0] > c:
                        best[i + width][t[-1]] = (c, (i, last, t))
    if not best[T]: return None
    last = min(best[T], key=lambda l: best[T][l][0]); out = []; i = T
    while i > 0:
        c, (j, prev, t) = best[i][last]; out = t + out; i, last = j, prev
    return out

def pairing(rows, R):
    """perfect matching of the piece less R along a Hamiltonian path, or None"""
    p = hamilton(rows, R)
    if p is None or len(p) % 2: return None
    return [(p[i], p[i + 1]) for i in range(0, len(p), 2)]

def row_structure(sf):
    """the adjacencies inside each piece are exactly: neighbours in a row; and the site xi of row z (z >= 1) with the
    sites xi and xi+1 of row z-1, mirrored for z <= -1.  Returns True if this holds for the four pieces."""
    for key, pc in sf.pieces.items():
        pos = {h: (z, i) for z, r in pc.items() for i, h in enumerate(r)}
        for h, (z, i) in pos.items():
            want = {(z, i - 1), (z, i + 1)}
            for zz in (z - 1, z + 1):                      # zz nearer to the equator: this site sees i, i+1 there; farther: i-1, i
                want |= {(zz, i), (zz, i + 1)} if abs(zz) < abs(z) else {(zz, i - 1), (zz, i)}
            want = {w for w in want if w[0] in pc and 0 <= w[1] < len(pc[w[0]])}
            have = {pos[g] for g in (add(h, r) for r in ROOTS) if g in pos}
            if want != have: return False
        if any(sf.xi(r[0]) != 2 or [sf.xi(h) for h in r] != list(range(2, 2 + len(r))) for r in pc.values()): return False
    return True

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for n in range(lo, hi + 1, 2):
        sf = Surface(n); ok = sf.valid()
        sizes = sorted(sum(len(r) for r in pc.values()) for pc in sf.pieces.values())
        lens = [len(r) for r in sf.rows((1, 1))]
        want = list(range(1, n - 4)) + [n - 5, n - 4, n - 5] + list(range(n - 5, 0, -1))
        strips = all(len(strip_order(a, b)) == len(a) + len(b) for key in sf.pieces for a, b in zip(sf.rows(key), sf.rows(key)[1:]))
        print(f"n = {n}: decoration valid (18 units, {16*n-18} doubly decorated sites): {ok}; four pieces of {n*n-6*n+6} sites: {sizes == [n*n-6*n+6]*4}; "
              f"row lengths as stated: {lens == want}; adjacencies inside the pieces as stated: {row_structure(sf)}; consecutive rows form strips: {strips}", flush=True)
```

## `pairtest.py`

```python
"""Lemma 50, test of the pairing over all defects.  For a piece (the piece x, y > 0 without its two tips, and the piece
x < 0 < y), every defect of kind 'a' (two neighbouring sites of a row) and of kind 'b' (the right ends of two
consecutive rows) in the rows zmin <= z <= n - ztop is combined with nothing, and with every (or 6000 random) mirror
defects in the lower half; surface.pairing must return a perfect matching of the rest into adjacent pairs."""
import sys, random
from surface import *
def defects(sf, key, half, zmin, ztop):
    rows = sf.pieces[key]; out = []
    for z in [z for z in rows if zmin <= half * z <= sf.n - ztop]:
        r = rows[z]
        for i in range(len(r) - 1): out.append(('a', abs(z), (r[i], r[i + 1])))
        z2 = z + half
        if z2 in rows and half * z2 <= sf.n - ztop and sf.eta(r[-1]) == 1 and sf.eta(rows[z2][-1]) == 1 and adj(r[-1], rows[z2][-1]): out.append(('b', abs(z), (r[-1], rows[z2][-1])))
    return out
if __name__ == '__main__':
    rng = random.Random(4); zmin, ztop = int(sys.argv[3]), int(sys.argv[4])
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
        sf = Surface(n); res = {}
        for key in [(1, 1), (-1, 1)]:
            rows = sf.rows(key); tips = {rows[0][0], rows[-1][0]} if key == (1, 1) else set()
            up = defects(sf, key, 1, zmin, ztop); dn = defects(sf, key, -1, zmin, ztop)
            combos = [(u, None) for u in up] + [(None, d) for d in dn] + [(None, None)]
            allpairs = [(u, d) for u in up for d in dn]
            combos += allpairs if len(allpairs) <= 6000 else rng.sample(allpairs, 6000)
            fails = 0
            for u, d in combos:
                R = set(tips)
                for x in (u, d):
                    if x: R |= set(x[2])
                m = pairing(rows, R)
                if m is None: fails += 1
                else: assert len(m) * 2 == sum(len(r) for r in rows) - len(R) and all(adj(a, b) for a, b in m) and len({h for p in m for h in p}) == 2 * len(m)
            res[key] = (len(up), len(combos), fails)
        print(f"n = {n}, defects in rows {zmin} <= |z| <= {n - ztop}: " + "; ".join(f"piece {k}: {v[0]} defects in each half, {v[1]} combinations, no pairing in {v[2]}" for k, v in res.items()), flush=True)
```

## `strips.py`

```python
import sys
import surface as sv
from surface import *
from pairtest import defects
def hamilton_cost(rows, R):
    T = len(rows); best = [dict() for _ in range(T + 1)]; best[0][None] = 0
    for i in range(T):
        for last, cost in list(best[i].items()):
            if all(h in R for h in rows[i]):
                best[i+1][last] = min(best[i+1].get(last, 99), cost); continue
            for width in (1, 2):
                if i + width > T: continue
                for t in band_traversals(rows, i, width, R):
                    if last is not None and not adj(last, t[0]): continue
                    best[i+width][t[-1]] = min(best[i+width].get(t[-1], 99), cost + (width == 2))
    return min(best[T].values()) if best[T] else None
for n in (14, 16, 18):
    sf = Surface(n)
    for key in [(1,1), (-1,1)]:
        rows = sf.rows(key); tips = {rows[0][0], rows[-1][0]} if key == (1,1) else set()
        up = defects(sf, key, 1, 4, 9); dn = defects(sf, key, -1, 4, 9); hist = {}
        for u in up + [None]:
            for d in dn + [None]:
                R = set(tips)
                for x in (u, d):
                    if x: R |= set(x[2])
                c = hamilton_cost(rows, R); hist[c] = hist.get(c, 0) + 1
        print(n, key, 'defects per half', len(up), 'strips used -> cases', dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0]))))
```

## `interior3.py`

```python
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
```

## `canon.py`

```python
"""Check of the remark after Lemma 51: the run ends chosen by surface.run_ends are the path ends shifted by (sign x, sign y, 0) of their piece, whenever the cut pair is in slices |z| >= 2."""
import sys
from surface import *
import interior3
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
    N = n - 2; sf = Surface(n); size = N * (2 * N * N + 1) // 3; cnt = bad = 0
    for c1 in range(size // 4 + 1, (size - 1) // 2 + 1):
        cuts = [c1, size - c1]
        if min(min(abs(z), abs(z + 1)) if o == 0 else abs(z) for z, o in (interior3.slice_of(N, c) for c in cuts)) < 2: continue
        sites, info = interior3.build(N, cuts, lambda p, q: sf.run_ends(p, q) is not None)
        for c in cuts:
            p, q = sites[c - 1], sites[c]; e, f, kind = sf.run_ends(p, q); s = sf.piece_of(e); cnt += 1
            if e != (p[0] + s[0], p[1] + s[1], p[2]) or f != (q[0] + s[0], q[1] + s[1], q[2]): bad += 1
            if kind == 'a' and e[2] != p[2]: bad += 1
    print(f"n = {n}: cut pairs {cnt}, run ends not of the form path end + (sign x, sign y, 0): {bad}")
```

## `octa.py`

```python
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
```

## `fold.py`

```python
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
```

## `check.py`

```python
"""Independent checker for a fold: it uses only the coordinates and the word, and the definitions of Section 1 of the
note.  It knows nothing about octahedra, slots or routes.
  1. consecutive residues are adjacent in FCC (difference a permutation of (+-1, +-1, 0));
  2. no two residues on one site;
  3. Loss = number of pairs (H residue h, neighbouring site that carries no H and is not a chain neighbour of h);
     contacts = number of pairs of H residues on adjacent sites that are not consecutive; Lemma 1 is checked;
  4. n_1, n_2 = numbers of H with one / two chain neighbours P;  gap = Loss - (2 n_1 + 2.5 n_2);  HPH does not occur.
The fold is a witness for the reduction if gap <= 9 m."""
import numpy as np
ROOTS = [(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]

def report(xyz, word, m):
    L = len(word); assert xyz.shape == (L, 3)
    d = np.abs(np.diff(xyz, axis=0)); d.sort(axis=1)
    adjacent = bool(np.all(d == np.array([0, 1, 1])))
    lo = xyz.min(axis=0).astype(np.int64); span = xyz.max(axis=0).astype(np.int64) - lo + 1
    keys = ((xyz[:, 0].astype(np.int64) - lo[0]) * span[1] + (xyz[:, 1] - lo[1])) * span[2] + (xyz[:, 2] - lo[2])
    injective = len(np.unique(keys)) == L
    w = np.frombuffer(word.encode(), dtype='S1') == b'H'
    hidx = np.nonzero(w)[0]; pos = {tuple(int(v) for v in xyz[i]): int(i) for i in hidx}
    assert len(pos) == len(hidx)
    loss = contacts2 = 0
    for h, i in pos.items():
        chain = set()
        if i > 0: chain.add(tuple(int(v) for v in xyz[i - 1]))
        if i < L - 1: chain.add(tuple(int(v) for v in xyz[i + 1]))
        for r in ROOTS:
            g = (h[0] + r[0], h[1] + r[1], h[2] + r[2])
            if g in pos:
                if abs(pos[g] - i) != 1: contacts2 += 1
            elif g not in chain: loss += 1
    nH = len(hidx); eH = int(w[0]) + int(w[-1]); contacts = contacts2 // 2
    lemma1 = 2 * contacts + loss == 10 * nH + eH
    left = np.concatenate([[False], ~w[:-1]]); right = np.concatenate([~w[1:], [False]])
    pn = left[hidx].astype(int) + right[hidx].astype(int)
    n1, n2 = int(np.sum(pn == 1)), int(np.sum(pn == 2)); hph = 'HPH' in word
    gap = loss - (2 * n1 + 2.5 * n2)
    return (f"checker: adjacent {adjacent}; self-avoiding {injective}; H's {nH}, contacts {contacts}, Loss {loss}; Lemma 1 holds {lemma1}; "
            f"n_1 = {n1}, n_2 = {n2}; HPH occurs {hph}; gap = {gap} against 9m = {9*m}: {'WITNESS' if adjacent and injective and not hph and gap <= 9*m else 'NOT a witness'}")
```

## `controls.py`

```python
"""Controls for check.py.  The fold of the instance n8 is given to the checker unchanged, and then in three altered
forms that it must reject: (a) one residue moved by (2, 0, 0); (b) the same coordinates read with the word shifted by
one residue; (c) the last P before the first H-run declared an H."""
import numpy as np, fold, check
n, items, B, triples = 8, [24, 24, 25, 23, 25, 25], 73, [(0, 1, 2), (3, 4, 5)]
xyz, word, par = fold.build(n, items, B, triples)
print("unchanged:        ", check.report(xyz, word, 2)[-60:])
bad = xyz.copy(); bad[123456] += (2, 0, 0)
print("one residue moved:", check.report(bad, word, 2)[:60])
print("word shifted:     ", check.report(xyz, word[1:] + 'P', 2)[-60:])
i = word.index('H'); w2 = word[:i - 1] + 'H' + word[i:]
print("one P turned to H:", check.report(xyz, w2, 2)[-60:])
```

## Output of `python3 slicepath.py 3 44`

```
k = 3: offsets without a valid path: 0 of 8; by construction {'forward': 6, 'reversed': 2, 'special': 0}; cut pairs with a corner: 8, transposed pair on the same side: 0
k = 4: offsets without a valid path: 0 of 15; by construction {'forward': 7, 'reversed': 4, 'special': 4}; cut pairs with a corner: 8, transposed pair on the same side: 0
k = 5: offsets without a valid path: 0 of 24; by construction {'forward': 20, 'reversed': 4, 'special': 0}; cut pairs with a corner: 10, transposed pair on the same side: 0
k = 6: offsets without a valid path: 0 of 35; by construction {'forward': 19, 'reversed': 12, 'special': 4}; cut pairs with a corner: 10, transposed pair on the same side: 0
k = 7: offsets without a valid path: 0 of 48; by construction {'forward': 42, 'reversed': 6, 'special': 0}; cut pairs with a corner: 12, transposed pair on the same side: 0
k = 8: offsets without a valid path: 0 of 63; by construction {'forward': 39, 'reversed': 20, 'special': 4}; cut pairs with a corner: 12, transposed pair on the same side: 0
k = 9: offsets without a valid path: 0 of 80; by construction {'forward': 72, 'reversed': 8, 'special': 0}; cut pairs with a corner: 14, transposed pair on the same side: 0
k = 10: offsets without a valid path: 0 of 99; by construction {'forward': 67, 'reversed': 28, 'special': 4}; cut pairs with a corner: 14, transposed pair on the same side: 0
k = 11: offsets without a valid path: 0 of 120; by construction {'forward': 110, 'reversed': 10, 'special': 0}; cut pairs with a corner: 16, transposed pair on the same side: 0
k = 12: offsets without a valid path: 0 of 143; by construction {'forward': 103, 'reversed': 36, 'special': 4}; cut pairs with a corner: 16, transposed pair on the same side: 0
k = 13: offsets without a valid path: 0 of 168; by construction {'forward': 156, 'reversed': 12, 'special': 0}; cut pairs with a corner: 18, transposed pair on the same side: 0
k = 14: offsets without a valid path: 0 of 195; by construction {'forward': 147, 'reversed': 44, 'special': 4}; cut pairs with a corner: 18, transposed pair on the same side: 0
k = 15: offsets without a valid path: 0 of 224; by construction {'forward': 210, 'reversed': 14, 'special': 0}; cut pairs with a corner: 20, transposed pair on the same side: 0
k = 16: offsets without a valid path: 0 of 255; by construction {'forward': 199, 'reversed': 52, 'special': 4}; cut pairs with a corner: 20, transposed pair on the same side: 0
k = 17: offsets without a valid path: 0 of 288; by construction {'forward': 272, 'reversed': 16, 'special': 0}; cut pairs with a corner: 22, transposed pair on the same side: 0
k = 18: offsets without a valid path: 0 of 323; by construction {'forward': 259, 'reversed': 60, 'special': 4}; cut pairs with a corner: 22, transposed pair on the same side: 0
k = 19: offsets without a valid path: 0 of 360; by construction {'forward': 342, 'reversed': 18, 'special': 0}; cut pairs with a corner: 24, transposed pair on the same side: 0
k = 20: offsets without a valid path: 0 of 399; by construction {'forward': 327, 'reversed': 68, 'special': 4}; cut pairs with a corner: 24, transposed pair on the same side: 0
k = 21: offsets without a valid path: 0 of 440; by construction {'forward': 420, 'reversed': 20, 'special': 0}; cut pairs with a corner: 26, transposed pair on the same side: 0
k = 22: offsets without a valid path: 0 of 483; by construction {'forward': 403, 'reversed': 76, 'special': 4}; cut pairs with a corner: 26, transposed pair on the same side: 0
k = 23: offsets without a valid path: 0 of 528; by construction {'forward': 506, 'reversed': 22, 'special': 0}; cut pairs with a corner: 28, transposed pair on the same side: 0
k = 24: offsets without a valid path: 0 of 575; by construction {'forward': 487, 'reversed': 84, 'special': 4}; cut pairs with a corner: 28, transposed pair on the same side: 0
k = 25: offsets without a valid path: 0 of 624; by construction {'forward': 600, 'reversed': 24, 'special': 0}; cut pairs with a corner: 30, transposed pair on the same side: 0
k = 26: offsets without a valid path: 0 of 675; by construction {'forward': 579, 'reversed': 92, 'special': 4}; cut pairs with a corner: 30, transposed pair on the same side: 0
k = 27: offsets without a valid path: 0 of 728; by construction {'forward': 702, 'reversed': 26, 'special': 0}; cut pairs with a corner: 32, transposed pair on the same side: 0
k = 28: offsets without a valid path: 0 of 783; by construction {'forward': 679, 'reversed': 100, 'special': 4}; cut pairs with a corner: 32, transposed pair on the same side: 0
k = 29: offsets without a valid path: 0 of 840; by construction {'forward': 812, 'reversed': 28, 'special': 0}; cut pairs with a corner: 34, transposed pair on the same side: 0
k = 30: offsets without a valid path: 0 of 899; by construction {'forward': 787, 'reversed': 108, 'special': 4}; cut pairs with a corner: 34, transposed pair on the same side: 0
k = 31: offsets without a valid path: 0 of 960; by construction {'forward': 930, 'reversed': 30, 'special': 0}; cut pairs with a corner: 36, transposed pair on the same side: 0
k = 32: offsets without a valid path: 0 of 1023; by construction {'forward': 903, 'reversed': 116, 'special': 4}; cut pairs with a corner: 36, transposed pair on the same side: 0
k = 33: offsets without a valid path: 0 of 1088; by construction {'forward': 1056, 'reversed': 32, 'special': 0}; cut pairs with a corner: 38, transposed pair on the same side: 0
k = 34: offsets without a valid path: 0 of 1155; by construction {'forward': 1027, 'reversed': 124, 'special': 4}; cut pairs with a corner: 38, transposed pair on the same side: 0
k = 35: offsets without a valid path: 0 of 1224; by construction {'forward': 1190, 'reversed': 34, 'special': 0}; cut pairs with a corner: 40, transposed pair on the same side: 0
k = 36: offsets without a valid path: 0 of 1295; by construction {'forward': 1159, 'reversed': 132, 'special': 4}; cut pairs with a corner: 40, transposed pair on the same side: 0
k = 37: offsets without a valid path: 0 of 1368; by construction {'forward': 1332, 'reversed': 36, 'special': 0}; cut pairs with a corner: 42, transposed pair on the same side: 0
k = 38: offsets without a valid path: 0 of 1443; by construction {'forward': 1299, 'reversed': 140, 'special': 4}; cut pairs with a corner: 42, transposed pair on the same side: 0
k = 39: offsets without a valid path: 0 of 1520; by construction {'forward': 1482, 'reversed': 38, 'special': 0}; cut pairs with a corner: 44, transposed pair on the same side: 0
k = 40: offsets without a valid path: 0 of 1599; by construction {'forward': 1447, 'reversed': 148, 'special': 4}; cut pairs with a corner: 44, transposed pair on the same side: 0
k = 41: offsets without a valid path: 0 of 1680; by construction {'forward': 1640, 'reversed': 40, 'special': 0}; cut pairs with a corner: 46, transposed pair on the same side: 0
k = 42: offsets without a valid path: 0 of 1763; by construction {'forward': 1603, 'reversed': 156, 'special': 4}; cut pairs with a corner: 46, transposed pair on the same side: 0
k = 43: offsets without a valid path: 0 of 1848; by construction {'forward': 1806, 'reversed': 42, 'special': 0}; cut pairs with a corner: 48, transposed pair on the same side: 0
k = 44: offsets without a valid path: 0 of 1935; by construction {'forward': 1767, 'reversed': 164, 'special': 4}; cut pairs with a corner: 48, transposed pair on the same side: 0
```

## Output of `python3 surface.py 8 30`

```
n = 8: decoration valid (18 units, 110 doubly decorated sites): True; four pieces of 22 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 10: decoration valid (18 units, 142 doubly decorated sites): True; four pieces of 46 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 12: decoration valid (18 units, 174 doubly decorated sites): True; four pieces of 78 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 14: decoration valid (18 units, 206 doubly decorated sites): True; four pieces of 118 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 16: decoration valid (18 units, 238 doubly decorated sites): True; four pieces of 166 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 18: decoration valid (18 units, 270 doubly decorated sites): True; four pieces of 222 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 20: decoration valid (18 units, 302 doubly decorated sites): True; four pieces of 286 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 22: decoration valid (18 units, 334 doubly decorated sites): True; four pieces of 358 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 24: decoration valid (18 units, 366 doubly decorated sites): True; four pieces of 438 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 26: decoration valid (18 units, 398 doubly decorated sites): True; four pieces of 526 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 28: decoration valid (18 units, 430 doubly decorated sites): True; four pieces of 622 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
n = 30: decoration valid (18 units, 462 doubly decorated sites): True; four pieces of 726 sites: True; row lengths as stated: True; adjacencies inside the pieces as stated: True; consecutive rows form strips: True
```

## Output of `python3 pairtest.py 12 24 4 9` (the range of Lemma 50)

```
n = 12, defects in rows 4 <= |z| <= 3: piece (1, 1): 0 defects in each half, 1 combinations, no pairing in 0; piece (-1, 1): 0 defects in each half, 1 combinations, no pairing in 0
n = 14, defects in rows 4 <= |z| <= 5: piece (1, 1): 12 defects in each half, 169 combinations, no pairing in 0; piece (-1, 1): 12 defects in each half, 169 combinations, no pairing in 0
n = 16, defects in rows 4 <= |z| <= 7: piece (1, 1): 29 defects in each half, 900 combinations, no pairing in 0; piece (-1, 1): 29 defects in each half, 900 combinations, no pairing in 0
n = 18, defects in rows 4 <= |z| <= 9: piece (1, 1): 50 defects in each half, 2601 combinations, no pairing in 0; piece (-1, 1): 50 defects in each half, 2601 combinations, no pairing in 0
n = 20, defects in rows 4 <= |z| <= 11: piece (1, 1): 75 defects in each half, 5776 combinations, no pairing in 0; piece (-1, 1): 75 defects in each half, 5776 combinations, no pairing in 0
n = 22, defects in rows 4 <= |z| <= 13: piece (1, 1): 104 defects in each half, 6209 combinations, no pairing in 0; piece (-1, 1): 104 defects in each half, 6209 combinations, no pairing in 0
n = 24, defects in rows 4 <= |z| <= 15: piece (1, 1): 137 defects in each half, 6275 combinations, no pairing in 0; piece (-1, 1): 137 defects in each half, 6275 combinations, no pairing in 0
```

## Output of `python3 pairtest.py 12 20 3 7` (a wider range)

```
n = 12, defects in rows 3 <= |z| <= 5: piece (1, 1): 14 defects in each half, 225 combinations, no pairing in 0; piece (-1, 1): 14 defects in each half, 225 combinations, no pairing in 0
n = 14, defects in rows 3 <= |z| <= 7: piece (1, 1): 29 defects in each half, 900 combinations, no pairing in 0; piece (-1, 1): 29 defects in each half, 900 combinations, no pairing in 0
n = 16, defects in rows 3 <= |z| <= 9: piece (1, 1): 48 defects in each half, 2401 combinations, no pairing in 0; piece (-1, 1): 48 defects in each half, 2401 combinations, no pairing in 0
n = 18, defects in rows 3 <= |z| <= 11: piece (1, 1): 71 defects in each half, 5184 combinations, no pairing in 0; piece (-1, 1): 71 defects in each half, 5184 combinations, no pairing in 0
n = 20, defects in rows 3 <= |z| <= 13: piece (1, 1): 98 defects in each half, 6197 combinations, no pairing in 0; piece (-1, 1): 98 defects in each half, 6197 combinations, no pairing in 0
```

## Output of `python3 pairtest.py 12 14 1 6` (outside the range of the lemma: failures are expected)

```
n = 12, defects in rows 1 <= |z| <= 6: piece (1, 1): 30 defects in each half, 961 combinations, no pairing in 2; piece (-1, 1): 30 defects in each half, 961 combinations, no pairing in 2
n = 14, defects in rows 1 <= |z| <= 8: piece (1, 1): 49 defects in each half, 2500 combinations, no pairing in 2; piece (-1, 1): 49 defects in each half, 2500 combinations, no pairing in 2
```

## Output of `python3 strips.py`

```
14 (1, 1) defects per half 12 strips used -> cases {0: 3, 1: 41, 2: 117, 3: 8}
14 (-1, 1) defects per half 12 strips used -> cases {0: 3, 1: 41, 2: 117, 3: 8}
16 (1, 1) defects per half 29 strips used -> cases {0: 11, 1: 189, 2: 668, 3: 32}
16 (-1, 1) defects per half 29 strips used -> cases {0: 11, 1: 189, 2: 668, 3: 32}
18 (1, 1) defects per half 50 strips used -> cases {0: 23, 1: 493, 2: 2013, 3: 72}
18 (-1, 1) defects per half 50 strips used -> cases {0: 23, 1: 493, 2: 2013, 3: 72}
```

## Output of `python3 interior3.py 8 22`

```
N = 8 (n = 10): pairs of cuts with no cut pair in the slice z = 0: 84, failing 0 (cuts inside a slice 234, between two slices 4, counted over all good cases); with a cut pair in the slice z = 0: 86, failing 46 (not needed)
N = 10 (n = 12): pairs of cuts with no cut pair in the slice z = 0: 194, failing 0 (cuts inside a slice 521, between two slices 3, counted over all good cases); with a cut pair in the slice z = 0: 140, failing 65 (not needed)
N = 12 (n = 14): pairs of cuts with no cut pair in the slice z = 0: 388, failing 0 (cuts inside a slice 959, between two slices 4, counted over all good cases); with a cut pair in the slice z = 0: 188, failing 86 (not needed)
N = 14 (n = 16): pairs of cuts with no cut pair in the slice z = 0: 639, failing 0 (cuts inside a slice 1576, between two slices 8, counted over all good cases); with a cut pair in the slice z = 0: 277, failing 115 (not needed)
N = 16 (n = 18): pairs of cuts with no cut pair in the slice z = 0: 1014, failing 0 (cuts inside a slice 2403, between two slices 7, counted over all good cases); with a cut pair in the slice z = 0: 352, failing 148 (not needed)
N = 18 (n = 20): pairs of cuts with no cut pair in the slice z = 0: 1485, failing 0 (cuts inside a slice 3489, between two slices 12, counted over all good cases); with a cut pair in the slice z = 0: 461, failing 183 (not needed)
N = 20 (n = 22): pairs of cuts with no cut pair in the slice z = 0: 2104, failing 0 (cuts inside a slice 4854, between two slices 11, counted over all good cases); with a cut pair in the slice z = 0: 564, failing 222 (not needed)
N = 22 (n = 24): pairs of cuts with no cut pair in the slice z = 0: 2849, failing 0 (cuts inside a slice 6538, between two slices 17, counted over all good cases); with a cut pair in the slice z = 0: 703, failing 259 (not needed)
```

## Output of `python3 canon.py 12 24`

```
n = 12: cut pairs 72, run ends not of the form path end + (sign x, sign y, 0): 0
n = 14: cut pairs 190, run ends not of the form path end + (sign x, sign y, 0): 0
n = 16: cut pairs 382, run ends not of the form path end + (sign x, sign y, 0): 0
n = 18: cut pairs 660, run ends not of the form path end + (sign x, sign y, 0): 0
n = 20: cut pairs 1044, run ends not of the form path end + (sign x, sign y, 0): 0
n = 22: cut pairs 1546, run ends not of the form path end + (sign x, sign y, 0): 0
n = 24: cut pairs 2186, run ends not of the form path end + (sign x, sign y, 0): 0
```

## Output of `python3 octa.py 18 24 0 3`

```
n = 18: pairs of cuts tried 134 (cut slices at |z| >= 3), failing 0; run ends of kind a/b: 268/0
n = 20: pairs of cuts tried 266 (cut slices at |z| >= 3), failing 0; run ends of kind a/b: 530/2
n = 22: pairs of cuts tried 449 (cut slices at |z| >= 3), failing 0; run ends of kind a/b: 896/2
n = 24: pairs of cuts tried 693 (cut slices at |z| >= 3), failing 0; run ends of kind a/b: 1382/4
```

## Output of `python3 octa.py regime B t` for (B, t) = (7, 4), (10, 2), (11, 2), (13, 2), (17, 2)

```
B = 7, t = 4, n = 86: triples 3, failing 0; run ends of kind a/b: 6/0; cut slices at |z| between 4 and 14 (N = 84)
B = 10, t = 2, n = 62: triples 3, failing 0; run ends of kind a/b: 6/0; cut slices at |z| between 4 and 9 (N = 60)
B = 11, t = 2, n = 68: triples 6, failing 0; run ends of kind a/b: 12/0; cut slices at |z| between 2 and 12 (N = 66)
B = 13, t = 2, n = 80: triples 3, failing 0; run ends of kind a/b: 6/0; cut slices at |z| between 7 and 12 (N = 78)
B = 17, t = 2, n = 104: triples 6, failing 0; run ends of kind a/b: 12/0; cut slices at |z| between 6 and 17 (N = 102)
```

## Output of `python3 octa.py regime 3 4` and `python3 octa.py regime 10 4`

```
B = 3, t = 4, n = 38: triples 1, failing 0; run ends of kind a/b: 2/0; cut slices at |z| between 5 and 5 (N = 36)
B = 10, t = 4, n = 122: triples 3, failing 0; run ends of kind a/b: 6/0; cut slices at |z| between 9 and 19 (N = 120)
```

## Output of `python3 fold.py n8 n8x n8m3 n10 n10x n12 n14`

```
instance n8: n = 8, items [24, 24, 25, 23, 25, 25], B = 73, triples [(0, 1, 2), (3, 4, 5)]
  slots 616, largest radius 1868, P-runs 309, lambda = 14942 (the routes need at least 8143)
  chain of 4617766 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 688, contacts 2980, Loss 920; Lemma 1 holds True; n_1 = 176, n_2 = 220; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
instance n8x: n = 8, items [24, 23, 25, 25, 24, 25], B = 73, triples [(0, 2, 4), (1, 3, 5)]
  slots 616, largest radius 1868, P-runs 309, lambda = 14942 (the routes need at least 8143)
  chain of 4617766 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 688, contacts 2980, Loss 920; Lemma 1 holds True; n_1 = 176, n_2 = 220; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
instance n8m3: n = 8, items [24, 25, 23, 24, 26, 25, 24, 24, 24], B = 73, triples [(0, 1, 3), (2, 4, 6), (5, 7, 8)]
  slots 924, largest radius 2792, P-runs 463, lambda = 22334 (the routes need at least 12191)
  chain of 10341674 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 1032, contacts 4470, Loss 1380; Lemma 1 holds True; n_1 = 264, n_2 = 330; HPH occurs False; gap = 27.0 against 9m = 27: WITNESS
instance n10: n = 10, items [14, 14, 15, 13, 15, 15], B = 43, triples [(0, 1, 2), (3, 4, 5)]
  slots 936, largest radius 2832, P-runs 469, lambda = 22346 (the routes need at least 12678)
  chain of 10481614 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 1340, contacts 5968, Loss 1464; Lemma 1 holds True; n_1 = 368, n_2 = 284; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
instance n10x: n = 10, items [14, 13, 15, 15, 14, 15], B = 43, triples [(0, 2, 4), (1, 3, 5)]
  slots 936, largest radius 2832, P-runs 469, lambda = 22346 (the routes need at least 12678)
  chain of 10481614 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 1340, contacts 5968, Loss 1464; Lemma 1 holds True; n_1 = 368, n_2 = 284; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
instance n12: n = 12, items [3, 3, 4, 3, 3, 4], B = 10, triples [(0, 1, 2), (3, 4, 5)]
  slots 1320, largest radius 3988, P-runs 661, lambda = 31222 (the routes need at least 18003)
  chain of 20640054 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 2312, contacts 10492, Loss 2136; Lemma 1 holds True; n_1 = 624, n_2 = 348; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
instance n14: n = 14, items [5, 6, 6, 5, 5, 7], B = 17, triples [(0, 1, 2), (3, 4, 5)]
  slots 1768, largest radius 5336, P-runs 885, lambda = 41570 (the routes need at least 24358)
  chain of 36793118 residues; word equals the word of Section 6 with lambda = 92mn^2 + 188mn + 14n + 46: True
  checker: adjacent True; self-avoiding True; H's 3668, contacts 16872, Loss 2936; Lemma 1 holds True; n_1 = 944, n_2 = 412; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
```

## Output of `python3 controls.py`

```
unchanged:         = 220; HPH occurs False; gap = 18.0 against 9m = 18: WITNESS
one residue moved: checker: adjacent False; self-avoiding False; H's 688, conta
word shifted:      PH occurs False; gap = 2390.0 against 9m = 18: NOT a witness
one P turned to H:  HPH occurs False; gap = 24.0 against 9m = 18: NOT a witness
```

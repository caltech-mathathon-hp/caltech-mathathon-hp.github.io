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

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

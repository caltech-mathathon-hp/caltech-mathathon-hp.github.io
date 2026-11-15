"""Section 45: (L_n) and (M_n) on the remaining families of Sections 42 to 44.
For every body: the least Lam_n over n >= 3 (lin.py) and the largest n with M_n < 0 (chordM.py).
    python3 lintest.py special | roof N n | bridge2 r | near2 r"""
import sys, itertools
from gmin import *
from lin import minlam
from chordM import data, M
from psi import boundary_moves, toggle
def both(S):
    c, oo = data(S); top = (max(oo) if oo else 3) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    return minlam(c), (max(bad) if bad else 0), c
def scan(name, bodies, verbose=False):
    cnt = 0; neg = 0; low = None; hist = {}
    for tag, S in bodies:
        (m, n), b, c = both(S); cnt += 1; neg += m < 0; hist[b] = hist.get(b, 0) + 1
        if verbose: print(f"   {tag}: N = {len(S)}, U* = {c['U']}, least Lam_n = {m} at n = {n}; largest n with M_n < 0: {b}")
        if low is None or m < low[0]: low = (m, n, tag, c['U'])
    print(f"{name}: {cnt} bodies; with Lam_n < 0: {neg}; least Lam_n = {low[0]} at n = {low[1]} ({low[2]}, U* = {low[3]}); largest n with M_n < 0, by number of bodies: {dict(sorted(hist.items()))}", flush=True)
mode = sys.argv[1]
if mode == 'special':
    sp = [("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
          ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
          ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
          ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
          ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
          ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
          ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}),
          ("O_7 with twin tops (2,0,0)", octa(7) | octa(7, (2, 0, 0)))]
    scan("special bodies", sp, True)
if mode == 'roof':
    N, n = int(sys.argv[2]), int(sys.argv[3]); A = octa(N)
    def gen():
        for a in range(0, N + n + 1):
            for b in range(0, 3):
                for c in range(0, N + n + 1):
                    if (a + b + c - (N - n)) % 2: continue
                    B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); S = A | B1 | B2
                    if not connected(S): continue
                    if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue
                    yield (a, b, c), S
    scan(f"roof O_{N} over two legs O_{n}", gen())
if mode == 'bridge2':
    r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A
    def gen():
        for x in range(0, 2 * r + 5):
            for y in range(0, x + 1):
                for z in range(0, y + 1):
                    if (x + y + z) % 2: continue
                    B = octa(r, (x, y, z))
                    if A & B or coatA & B: continue
                    coatB = {add(h, s) for h in B for s in ROOTS} - B; one = coatA & coatB
                    for c1 in coatA - B:
                        for s in ROOTS:
                            c2 = add(c1, s)
                            if c2 in coatB - A and c1 not in one and c2 not in one: yield ((x, y, z), c1, c2), A | B | {c1, c2}
    scan(f"two O_{r} joined by two sites", gen())
if mode == 'near2':
    r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
    def gen():
        for h, g in itertools.combinations(mv, 2):
            T = toggle(toggle(S, h), g)
            if connected(T): yield (h, g), T
    scan(f"bodies at two sites from O_{r}", gen())

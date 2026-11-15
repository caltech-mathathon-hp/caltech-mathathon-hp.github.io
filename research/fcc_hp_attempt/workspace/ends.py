"""Section 46: open ends.  An open end of a chord has half-length l = |C| if the other end is blocked, |C|/2 if it is open.
    M'_n = (2n^2 - 3n) U* - 3n p + 3 sum over open ends of min(l - 1/4, n/2).
Tested here, for every body:
    (K')  number of open ends with l <= x  <=  (16/3) U* x          for every x in (1/2) Z
    (I_n) M'_(n+1) - M'_n = (4n - 1) U* - 3p + (3/4) (N(n/2 + 1) + N(n/2 + 1/2)) >= 0,   N(x) = number of open ends with l >= x
(K') is false (Section 46.7); (I_n) is the conjecture of Section 46.4.  The scans also report M'_3 and the least M'_n with n >= 4.
    python3 ends.py families | special | unions a b | near r | near2 r | islands r | bridge r | roof N n"""
import sys
from fractions import Fraction
from gmin import *
from chords import chords
from chordM3 import data3, M1
def ends(oo, ob):
    return sorted([Fraction(L, 2) for L in oo] * 2 + [Fraction(L) for L in ob])
def tests(S):
    c, oo, ob, bb = data3(S); U = c['U']; p = c['boundary'] - 3 * c['nu1']; E = ends(oo, ob)
    kmin = None
    for i, l in enumerate(E):
        if i + 1 == len(E) or E[i + 1] > l:
            v = Fraction(16, 3) * U * l - (i + 1)
            if kmin is None or v < kmin[0]: kmin = (v, l)
    top = int(2 * max(E)) + 3 if E else 4
    N = lambda x: sum(1 for l in E if l >= x)
    inc = [( (4 * n - 1) * U - 3 * p + Fraction(3, 4) * (N(Fraction(n, 2) + 1) + N(Fraction(n + 1, 2))), n) for n in range(3, top + 1)]
    for v, n in inc: assert M1(c, oo, ob, n + 1) - M1(c, oo, ob, n) == v
    return kmin, min(inc), M1(c, oo, ob, 3), c, min(M1(c, oo, ob, n) for n in range(4, top + 2))
def scan(name, bodies):
    cnt = 0; kn = 0; inn = 0; m3 = 0; m4n = 0; wk = None; wi = None; w4 = None
    for tag, S in bodies:
        if len(S) < 2: continue
        k, i, m, c, m4 = tests(S); cnt += 1; kn += k[0] < 0; inn += i[0] < 0; m3 += m < 0; m4n += m4 < 0
        if m4 > 0 and (w4 is None or m4 < w4[0]): w4 = (m4, tag, c['U'])
        if wk is None or k[0] < wk[0]: wk = (k[0], k[1], tag, c['U'])
        if wi is None or i[0] < wi[0]: wi = (i[0], i[1], tag, c['U'])
    print(f"{name}: {cnt} bodies; (K') fails: {kn}, least slack {float(wk[0]):.2f} at x = {wk[1]} ({wk[2]}, U* = {wk[3]}); (I_n) fails: {inn}, least increment {float(wi[0]):.2f} at n = {wi[1]} ({wi[2]}, U* = {wi[3]}); M'_3 < 0: {m3}; M'_n < 0 for some n >= 4: {m4n}; least positive value of min over n >= 4 of M'_n: {float(w4[0]) if w4 else None} ({w4[1] if w4 else None})", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    if mode == 'families':
        named = [("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        named += [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)})]
        for nm, S in named:
            k, i, m, c, m4 = tests(S); print(f"   {nm}: U* = {c['U']}, (K') least slack {float(k[0]):.2f} at x = {k[1]}; least increment {float(i[0]):.2f} at n = {i[1]}; M'_3 = {float(m):.1f}; least M'_n, n >= 4: {float(m4):.1f}")
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'islands':
        from islands import island, supported
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen())
    if mode == 'bridge':
        r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A
        def gen():
            for x in range(0, 2 * r + 5):
                for y in range(0, x + 1):
                    for z in range(0, y + 1):
                        if (x + y + z) % 2: continue
                        B = octa(r, (x, y, z))
                        if A & B or coatA & B: continue
                        coatB = {add(h, s) for h in B for s in ROOTS} - B
                        for g in coatA & coatB: yield ((x, y, z), g), A | B | {g}
        scan(f"two O_{r} joined by one site", gen())
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
    if mode == 'near2':
        import itertools
        r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
        def gen():
            for h, g in itertools.combinations(mv, 2):
                T = toggle(toggle(S, h), g)
                if connected(T): yield (h, g), T
        scan(f"bodies at two sites from O_{r}", gen())
    if mode == 'special':
        sp = [("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
              ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
              ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
              ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
              ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
              ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
              ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}), ("O_7 with twin tops (2,0,0)", octa(7) | octa(7, (2, 0, 0))),
              ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})]
        for nm, S in sp:
            k, i, m, c, m4 = tests(S); print(f"   {nm}: U* = {c['U']}, (K') least slack {float(k[0]):.2f} at x = {k[1]}; least increment {float(i[0]):.2f} at n = {i[1]}; M'_3 = {float(m):.1f}; least M'_n, n >= 4: {float(m4):.1f}", flush=True)

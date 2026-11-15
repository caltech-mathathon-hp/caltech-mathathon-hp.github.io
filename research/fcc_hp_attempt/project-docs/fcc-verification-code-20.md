# FCC HP folding: verification code, part 20 (twenty-third pass, 15 Nov 2026)

Scripts for Section 46 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): islands on a face of an octahedron, which refute "(M_n) from n = 6 on" of Section 45; the repaired decomposition with half-open chords (Proposition 65); the local potential (Lemma 66); the increments of M'_n and the conjecture (I_n) (Proposition 67); statements that turned out false. They import `gmin.py`, `psi.py` (part 16) and `lin.py`, `chords.py`, `chordM.py` (part 19). `blocked.py` is the enumeration behind Lemma 66(b) and `check67.py` checks the identities on bodies; nothing else here is a proof.

| Script | What it does | Run |
|---|---|---|
| `islands.py`, `islands2.py` | one-layer triangular islands on a face of O_r: U*, Lam_n, the n with M_n < 0, the slack of (K) | `python3 islands.py 9`, `python3 islands2.py 13` |
| `chordM3.py` | M'_n (half-open chords counted), the identity of Proposition 65, the n with M_n < 0 and with M'_n < 0 | `python3 chordM3.py island r k a b`, `families`, `unions a b`, `near r`, `islands r` |
| `ends.py` | open ends: (K'), the increments (I_n), M'_3, the least M'_n for n >= 4, by family | `python3 ends.py families`, `special`, `unions a b`, `near r`, `near2 r`, `islands r`, `bridge r`, `roof N n` |
| `stacks.py` | islands on all eight faces, stacked islands | `python3 stacks.py 9` |
| `blocked.py` | Lemma 66(b): tau and the bound for blocked ends over the 4,096 neighbourhoods | `python3 blocked.py` |
| `sharp.py` | the potential pi, Pi, and the runs-only inequality (false) | `python3 sharp.py` |
| `m0.py` | the runs-only form M0_n with the potential | `python3 m0.py named`, `island r k a b`, `islands r` |
| `check67.py` | Lemma 66(a), formula (3), both forms of the increment | `python3 check67.py` |
| `corner.py` | units at a corner site against the number of corners, over all neighbourhoods | `python3 corner.py` |
| `isearch.py` | annealing against (I_n) and (M'_n) | `python3 isearch.py seed steps T0 kind` |

## `islands.py`

```python
"""Section 46: one-layer triangular islands and pits on the face x + y + z = r - 1 of O_r.
For each island the least Lam_n (lin.py), the n at which M_n < 0 (chordM.py), U* and the slack of (K).
    python3 islands.py r"""
import sys
from gmin import *
from lin import minlam, lam
from chordM import data, M
def island(r, k, up, shift=(0, 0)):
    """sites of the layer x + y + z = r + 1 over the face, a triangle with k sites per side; up: orientation"""
    out = set()
    a0, b0 = shift
    for i in range(k):
        for j in range(k - i):
            if up: x, y = 1 + a0 + i, 1 + b0 + j
            else: x, y = 1 + a0 + k - 1 - i, 1 + b0 + k - 1 - j
            z = r + 1 - x - y
            out.add((x, y, z))
    return out
def supported(S, I):
    low = [(-1, -1, 0), (-1, 0, -1), (0, -1, -1)]
    return all(all(add(h, d) in S for d in low) for h in I)
def row(name, S):
    c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(3, top + 1) if M(c, oo, n) < 0]
    m, n = minlam(c); U = c['U']; H = len(oo)
    ks = min((4 * U * L - 3 * sum(1 for x in oo if x <= L)) / 3 for L in set(oo))
    print(f"{name}: N = {len(S)}, U* = {U}, n2* = {c['n2']}, least Lam_n = {m} at n = {n}; M_n < 0 for n in {bad}; least slack of (K) = {ks:.2f}", flush=True)
if __name__ == '__main__':
  r = int(sys.argv[1]); O = octa(r)
  for up in (True, False):
      for k in range(1, r):
          for shift in ((0, 0), (1, 1), (2, 1)):
              I = island(r, k, up, shift)
              if not supported(O, I): continue
              row(f"island k = {k}, {'same' if up else 'reversed'} orientation, shift {shift}", O | I)
```

## `islands2.py`

```python
"""Section 46: islands of the cheap orientation on a face of O_r, all sizes and positions (up to the symmetry of the face not used).
Reports the largest n with M_n < 0, the least slack of (K), the least Lam_n, by island size.
    python3 islands2.py r"""
import sys
from gmin import *
from lin import minlam
from chordM import data, M
from islands import island, supported
r = int(sys.argv[1]); O = octa(r)
for k in range(1, r):
    best = None; cnt = 0
    for a in range(0, r):
        for b in range(a, r):
            I = island(r, k, True, (a, b))
            if not supported(O, I): continue
            S = O | I; c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(3, top + 1) if M(c, oo, n) < 0]
            U = c['U']; ks = min((4 * U * L - 3 * sum(1 for x in oo if x <= L)) / 3 for L in set(oo)); m, n = minlam(c); cnt += 1
            rec = (max(bad) if bad else 0, ks, m, n, (a, b), U)
            if best is None: best = [rec, rec, rec]
            if rec[0] > best[0][0]: best[0] = rec
            if rec[1] < best[1][1]: best[1] = rec
            if rec[2] < best[2][2]: best[2] = rec
    if best:
        print(f"k = {k}: {cnt} positions; largest n with M_n < 0: {best[0][0]} (shift {best[0][4]}, U* = {best[0][5]}); least slack of (K): {best[1][1]:.2f} (shift {best[1][4]}, U* = {best[1][5]}); least Lam_n = {best[2][2]} at n = {best[2][3]} (shift {best[2][4]})", flush=True)
```

## `chordM3.py`

```python
"""Section 46: the count with half-open chords.  For a finite set S (chords.py; U*, p, d from gmin.cost):
    A_n = sum over chords with two open ends of (n + 1/2 - |C|)+  +  sum over chords with one open end of (n/2 + 1/4 - |C|)+,
    M'_n = (2n^2 - 3n) U* + 3n (H + H1/2 - p) - 3 A_n,      H, H1 = numbers of chords with two and with one open end.
Identity:  Lam_n = M'_n + 3 sum_OO (|C| - n - 1/2)+ + 3 sum_OB (|C| - n/2 - 1/4)+ + 3 sum_BB |C| + 3 sum_h beta(h),
beta(h) = deg - 3e + o/4 >= 0 (Lemma 63).  So Lam_n >= M'_n >= M_n.
    python3 chordM3.py island r k a b | families | unions a b | near r | islands r"""
import sys
from fractions import Fraction
from gmin import *
from chords import chords, NUS, RNU, dot
from lin import lam, minlam
Q = Fraction(1, 4)
def data3(S, c=None):
    if c is None: c = cost(S)
    ch = chords(S)
    return c, sorted(x[3] for x in ch if x[4] == 2), sorted(x[3] for x in ch if x[4] == 1), sum(x[3] for x in ch if x[4] == 0)
def M1(c, oo, ob, n):
    """M'_n"""
    U = c['U']; p = c['boundary'] - 3 * c['nu1']
    A = sum(n + 2 * Q - L for L in oo if L <= n) + sum(Fraction(n, 2) + Q - L for L in ob if L < Fraction(n, 2) + Q)
    return (2 * n * n - 3 * n) * U + 3 * n * (len(oo) + Fraction(len(ob), 2) - p) - 3 * A
def M0(c, oo, n):
    U = c['U']; p = c['boundary'] - 3 * c['nu1']
    return (2 * n * n - 3 * n) * U + 3 * n * (len(oo) - p) - 3 * sum(n + 2 * Q - L for L in oo if L <= n)
def beta_sum(S):
    tot = Fraction(0)
    for h in S:
        emp = [r for r in ROOTS if add(h, r) not in S]
        if not emp: continue
        es = set(emp); ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
        o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
        tot += len(emp) - 3 * len(ex) + Fraction(o, 4)
    return tot
def check(S, c, oo, ob, bb, n):
    rest = 3 * sum(L - n - 2 * Q for L in oo if L > n) + 3 * sum(L - Fraction(n, 2) - Q for L in ob if L > Fraction(n, 2) + Q) + 3 * bb + 3 * beta_sum(S)
    assert lam(c, n) == M1(c, oo, ob, n) + rest, (lam(c, n), M1(c, oo, ob, n), rest)
def bad_ranges(S, verify=False):
    c, oo, ob, bb = data3(S); top = max(oo + ob) + 3
    if verify:
        for n in (3, 6, 11): check(S, c, oo, ob, bb, n)
    b0 = [n for n in range(3, top + 1) if M0(c, oo, n) < 0]; b1 = [n for n in range(3, top + 1) if M1(c, oo, ob, n) < 0]
    return c, b0, b1
def scan(name, bodies):
    cnt = 0; h0 = {}; h1 = {}; w = None
    for tag, S in bodies:
        c, b0, b1 = bad_ranges(S, cnt % 50 == 0); cnt += 1
        k0 = max(b0) if b0 else 0; k1 = max(b1) if b1 else 0; h0[k0] = h0.get(k0, 0) + 1; h1[k1] = h1.get(k1, 0) + 1
        if w is None or k1 > w[0]: w = (k1, tag, c['U'])
    print(f"{name}: {cnt} bodies; largest n with M_n < 0: {dict(sorted(h0.items()))}; largest n with M'_n < 0: {dict(sorted(h1.items()))}; worst for M': {w}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    if mode == 'island':
        from islands import island, supported
        r, k, a, b = map(int, sys.argv[2:6]); O = octa(r); I = island(r, k, True, (a, b)); assert supported(O, I)
        S = O | I; c, b0, b1 = bad_ranges(S, True); m, n = minlam(c)
        print(f"O_{r} with island k = {k} at {(a, b)}: N = {len(S)}, U* = {c['U']}, least Lam_n = {m} at n = {n}; M_n < 0 for n in {b0}; M'_n < 0 for n in {b1}", flush=True)
    if mode == 'families':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        scan("named bodies", named)
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
```

## `ends.py`

```python
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
```

## `stacks.py`

```python
"""Section 46: octahedra with islands on all eight faces, and with islands stacked on one face.
For each: U*, least Lam_n, least increment of M'_n (n >= 3), least M'_n (n >= 4).     python3 stacks.py r"""
import sys, itertools
from gmin import *
from lin import minlam
from ends import tests
from islands import island
def all_faces(r, k, a, b):
    I = island(r, k, True, (a, b)); out = set()
    for s in itertools.product((1, -1), repeat=3):
        out |= {(s[0] * x, s[1] * y, s[2] * z) for x, y, z in I}
    return out
def stacked(r, ks, a, b):
    """islands with ks[0], ks[1], ... sites per side, each one layer above the one before, each shifted by (1, 1)"""
    out = set()
    for j, k in enumerate(ks):
        for i in range(k):
            for l in range(k - i):
                x, y = 1 + a + j + i, 1 + b + j + l; z = r + 1 + 2 * j - x - y
                out.add((x, y, z))
    return out
def row(name, S):
    k, i, m, c, m4 = tests(S); mm, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, least Lam_n = {mm} at n = {n}; least increment {float(i[0]):.1f} at n = {i[1]}; M'_3 = {float(m):.1f}; least M'_n, n >= 4: {float(m4):.1f}", flush=True)
r = int(sys.argv[1]); O = octa(r)
for k, a, b in ((3, 1, 1), (3, 0, 0), (4, 1, 1), (r - 3, 0, 0), (r - 4, 1, 1), (2, 1, 1), (1, 1, 1)):
    row(f"O_{r} with islands k = {k} at ({a},{b}) on all eight faces", O | all_faces(r, k, a, b))
for ks, a, b in (((5, 2), 0, 0), ((6, 3), 0, 0), ((6, 3), 1, 0), ((4, 1), 1, 1), ((7, 4, 1), 0, 0)):
    St = stacked(r, ks, a, b)
    if any(sum(abs(t) for t in h) > r + 1 + 2 * len(ks) for h in St): continue
    row(f"O_{r} with stacked islands {ks} at ({a},{b})", O | St)
```

## `blocked.py`

```python
"""Section 46: blocked ends, seen from the blocking site.  For a site g with set E of empty neighbours:
tau(g) = o/2 - deg + 3 (o = open ends at g);  bl+(g) = number of pairs (nu, d), d a root with d.nu = 0, such that g + d is
occupied, g is not nu-exposed, and the neighbour g + d + r of g is empty for the r in R_nu with r.d = -1
(necessary for g + d to be nu-exposed, so bl+ bounds the number of chord ends blocked by g).
Prints, by (deg, exposures), the least value of 3 tau - (3/2) bl+ over the 4096 sets, and the sets where it is negative."""
import itertools
from gmin import ROOTS, add
from chords import NUS, RNU, dot
neg = lambda a: (-a[0], -a[1], -a[2])
tab = {}; worst = []
for mask in range(1, 1 << 12):
    emp = [ROOTS[i] for i in range(12) if mask >> i & 1]; es = set(emp)
    ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
    o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
    tau2 = o - 2 * len(emp) + 6                      # 2 tau
    bl = 0
    for nu in NUS:
        if nu in ex: continue
        for d in ROOTS:
            if dot(d, nu) != 0 or d in es: continue
            rm = [r for r in RNU[nu] if dot(r, d) == -1]
            assert len(rm) == 1
            if add(d, rm[0]) in es: bl += 1
    v = 3 * tau2 - 3 * bl                              # 2 * (3 tau - (3/2) bl)
    key = (len(emp), len(ex)); t = tab.setdefault(key, [10**9, None, 0])
    t[2] += 1
    if v < t[0]: t[0], t[1] = v, (tau2 / 2, bl)
print("(deg, e): least 3 tau - (3/2) bl+, attained with (tau, bl+), number of sets")
for key in sorted(tab): print("  ", key, tab[key][0] / 2, tab[key][1], tab[key][2])
```

## `sharp.py`

```python
"""Section 46: the local potential.  For a surface site g: tau(g) = o/2 - deg + 3, bl(g) = number of chord ends blocked by g
(pairs (nu, d) with g + d nu-exposed and g in S not nu-exposed), pi(g) = 3 tau(g) - (3/2) bl(g), Pi = sum of pi.
(I0_n):  3 H_n + (3/2) h_(n+1) <= (4n - 1) U* + Pi - 9 def1     (silhouette runs only; stronger than (I_n))
    python3 sharp.py"""
import sys
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, dot, sub
from chordM3 import data3
def potential(S):
    F = {nu: {h for h in S if all(add(h, r) not in S for r in RNU[nu])} for nu in NUS}
    tot = Fraction(0); by = {}
    for g in S:
        emp = [r for r in ROOTS if add(g, r) not in S]
        if not emp: continue
        ex = [nu for nu in NUS if g in F[nu]]
        o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
        bl = sum(1 for nu in NUS if g not in F[nu] for d in ROOTS if dot(d, nu) == 0 and add(g, d) in F[nu])
        pi = 3 * (Fraction(o, 2) - len(emp) + 3) - Fraction(3 * bl, 2); tot += pi
        if pi != 0: by[(len(emp), len(ex), pi)] = by.get((len(emp), len(ex), pi), 0) + 1
    return tot, by
def i0(S):
    c, oo, ob, bb = data3(S); U = c['U']; d1 = c['surface'] - c['nu1']; Pi, by = potential(S)
    top = max(oo) + 2; out = []
    for n in range(3, top + 1):
        Hn = sum(1 for L in oo if L <= n); h1 = sum(1 for L in oo if L == n + 1)
        out.append(((4 * n - 1) * U + Pi - 9 * d1 - 3 * Hn - Fraction(3 * h1, 2), n))
    return min(out), Pi, by, c, d1
if __name__ == '__main__':
    from islands import island
    bodies = [(f"O_{r}", octa(r)) for r in (5, 7)] + [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}),
              ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))), ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))),
              ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)}),
              ("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 5 at (1,1)", octa(9) | island(9, 5, True, (1, 1))),
              ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
              ("tetrahedron 6", tetra(6)), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0)))]
    for name, S in bodies:
        (v, n), Pi, by, c, d1 = i0(S)
        print(f"{name}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; least slack of (I0_n) = {float(v):.1f} at n = {n}; sites with pi != 0 by (deg, e, pi): { {k: v for k, v in sorted(by.items())} }", flush=True)
```

## `m0.py`

```python
"""Section 46: the runs-only form.  With Pi the sum of the local potential (sharp.py) and D_n the sum of (n + 1/2 - |C|)+ over
the silhouette runs,   M0_n = (2n^2 - 3n) U* + n Pi - 9n def1 - 3 D_n,   and   M'_n = M0_n + 3 sum_OB min(|C| - 1/4, n/2) + 3n H2.
For each body: the n >= 3 with M0_n < 0.     python3 m0.py island r k a b | islands r | unions a b | near r | bridge r | named"""
import sys
from fractions import Fraction
from gmin import *
from chordM3 import data3, M1
from sharp import potential
H = Fraction(1, 2)
def m0(S, check=True):
    c, oo, ob, bb = data3(S); U = c['U']; d1 = c['surface'] - c['nu1']; Pi, by = potential(S)
    top = max(oo) + 3; out = {}
    for n in range(3, top + 1):
        out[n] = (2 * n * n - 3 * n) * U + n * Pi - 9 * n * d1 - 3 * sum(n + H - L for L in oo if L <= n)
    if check:
        from chords import chords
        nbb = sum(1 for x in chords(S) if x[4] == 0)
        for n in (3, min(7, top)):
            assert M1(c, oo, ob, n) == out[n] + 3 * sum(min(L - Fraction(1, 4), Fraction(n, 2)) for L in ob) + 3 * n * nbb
    return [n for n in out if out[n] < 0], c, Pi, d1
def scan(name, bodies):
    cnt = 0; hist = {}; w = None
    for tag, S in bodies:
        bad, c, Pi, d1 = m0(S, cnt % 40 == 0); cnt += 1; k = max(bad) if bad else 0; hist[k] = hist.get(k, 0) + 1
        if w is None or k > w[0]: w = (k, tag, c['U'], Pi)
    print(f"{name}: {cnt} bodies; largest n with M0_n < 0, by number of bodies: {dict(sorted(hist.items()))}; worst {w}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    if mode == 'island':
        r, k, a, b = map(int, sys.argv[2:6]); O = octa(r); I = island(r, k, True, (a, b)); assert supported(O, I)
        bad, c, Pi, d1 = m0(O | I); print(f"O_{r} with island k = {k} at {(a, b)}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; M0_n < 0 for n in {bad}", flush=True)
    if mode == 'islands':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen())
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
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
    if mode == 'named':
        named = [("pair", {(0, 0, 0), (1, 1, 0)}), ("single", {(0, 0, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        for nm, S in named:
            bad, c, Pi, d1 = m0(S); print(f"   {nm}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; M0_n < 0 for n in {bad}")
```

## `check67.py`

```python
"""Section 46: checks of Lemma 66 and of the two forms of the increment (Proposition 67) on bodies.
    E = H - H2 - Pi/3;   M'_n = (2n^2 - 3n) U + n Pi - 9n def1 - 3 D_n + 3 sum_OB min(|C| - 1/4, n/2) + 3n H2;
    M'_(n+1) - M'_n = (4n - 1) U - 3p + (3/4)(N(n/2 + 1) + N((n + 1)/2))
                    = (4n - 1) U + Pi - 9 def1 - 3 H_n - (3/2) h_(n+1) + (3/2) #{OB: |C| > (n+1)/2} + (3/4) #{OB: |C| = (n+1)/2} + 3 H2
    python3 check67.py"""
from fractions import Fraction
from gmin import *
from chords import chords
from chordM3 import M1
from sharp import potential
from islands import island
Q = Fraction(1, 4)
bodies = [("O_6", octa(6)), ("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
          ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("O_9 with island 4 at (1,1)", octa(9) | island(9, 4, True, (1, 1))), ("tetrahedron 6", tetra(6)),
          ("rod of 10", {(i, -i, 0) for i in range(10)}), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("O_9 with a cavity O_3", octa(9) - octa(3)), ("single site", {(0, 0, 0)})]
for name, S in bodies:
    c = cost(S); ch = chords(S); oo = sorted(x[3] for x in ch if x[4] == 2); ob = sorted(x[3] for x in ch if x[4] == 1); bbn = sum(1 for x in ch if x[4] == 0)
    U = c['U']; d = c['boundary']; E = d - 3 * c['surface']; d1 = c['surface'] - c['nu1']; p = d - 3 * c['nu1']; Pi, by = potential(S)
    assert 3 * E == 3 * len(oo) - 3 * bbn - Pi                                     # Lemma 66 (a)
    ends = [Fraction(L, 2) for L in oo] * 2 + [Fraction(L) for L in ob]; N = lambda x: sum(1 for l in ends if l >= x)
    for n in range(1, max(oo + ob + [3]) + 4):
        Dn = sum(n + 2 * Q - L for L in oo if L <= n)
        assert M1(c, oo, ob, n) == (2 * n * n - 3 * n) * U + n * Pi - 9 * n * d1 - 3 * Dn + 3 * sum(min(L - Q, Fraction(n, 2)) for L in ob) + 3 * n * bbn
        inc = M1(c, oo, ob, n + 1) - M1(c, oo, ob, n)
        assert inc == (4 * n - 1) * U - 3 * p + 3 * Q * (N(Fraction(n, 2) + 1) + N(Fraction(n + 1, 2)))
        Hn = sum(1 for L in oo if L <= n); h1 = sum(1 for L in oo if L == n + 1)
        assert inc == (4 * n - 1) * U + Pi - 9 * d1 - 3 * Hn - Fraction(3, 2) * h1 + Fraction(3, 2) * sum(1 for L in ob if 2 * L > n + 1) + 3 * Q * sum(1 for L in ob if 2 * L == n + 1) + 3 * bbn
    print(f"{name}: E = {E}, H = {len(oo)}, H1 = {len(ob)}, H2 = {bbn}, Pi = {Pi}, def1 = {d1}: Lemma 66 and both forms of the increment hold for n = 1..{max(oo + ob + [3]) + 3}", flush=True)
```

## `corner.py`

```python
"""Section 46: units at a site against the corners of faces at that site.
For a site h with set E of non-H neighbours and chain P's P (a subset of E with at most two elements), Theorem 5 gives
    alpha = number of x in E \\ P not adjacent to any element of P,
    beta >= beta- = number of x in E \\ P all of whose four common neighbours with h are in E (such an x cannot be a
                    chain P of an H-neighbour of h),
    gamma = 0 for |P| <= 1, and |K_a u K_b minus {a, b}| - 5 + (number of H's in K_a n K_b) for P = {a, b}.
u-(E) = min over P of alpha + beta- + gamma is a lower bound for the units located at h that depends on E only.
c1(E) = number of pairs (nu, line d) with h exposed for nu and both neighbours of h on the line empty: the silhouette runs
of one site at h.  Question: is 4 u-(E) >= 3 c1(E) for all E?"""
import itertools
from gmin import ROOTS
from chords import NUS, RNU, dot
K = {r: [q for q in ROOTS if dot(q, r) == 1] for r in ROOTS}
neg = lambda a: (-a[0], -a[1], -a[2])
def uminus(es):
    best = None
    E = sorted(es)
    for k in range(0, 3):
        for P in itertools.combinations(E, k):
            rest = [x for x in E if x not in P]
            alpha = sum(1 for x in rest if not any(dot(x, a) == 1 for a in P))
            beta = sum(1 for x in rest if all(q in es for q in K[x]))
            gamma = 0
            if k == 2:
                a, b = P; Ua = (set(K[a]) | set(K[b])) - {a, b}
                gamma = len(Ua) - 5 + sum(1 for q in set(K[a]) & set(K[b]) if q not in es)
            v = alpha + beta + gamma
            if best is None or v < best[0]: best = (v, P, alpha, beta, gamma)
    return best
def c1(es):
    n = 0
    for nu in NUS:
        if not all(r in es for r in RNU[nu]): continue
        for d in ROOTS:
            if d > (0, 0, 0) and dot(d, nu) == 0 and d in es and neg(d) in es: n += 1
    return n
bad = {}; tab = {}; tight = {}
for mask in range(1, 1 << 12):
    es = {ROOTS[i] for i in range(12) if mask >> i & 1}
    c = c1(es)
    if c == 0: continue
    u = uminus(es)[0]; key = (len(es), c)
    t = tab.setdefault(key, [10**9, 0]); t[0] = min(t[0], u); t[1] += 1
    if 4 * u < 3 * c: bad[key] = bad.get(key, 0) + 1
    if 4 * u == 3 * c: tight[key] = tight.get(key, 0) + 1
print("(number of empty neighbours, corners c1): least u-, number of sets")
for key in sorted(tab): print("  ", key, tab[key][0], tab[key][1], "  4u- < 3c1 in", bad.get(key, 0), "sets; equality in", tight.get(key, 0))
print("sets with 4 u- < 3 c1:", sum(bad.values()), "of", sum(t[1] for t in tab.values()), "sets with a corner")
```

## `isearch.py`

```python
"""Section 46: search for a finite set with a negative increment M'_(n+1) - M'_n (n >= 3), or with M'_n < 0 for some n >= 4.
Score: min(least increment over n >= 3, least M'_n over n >= 4) / boundary.  Annealing by single sites, then nothing else.
    python3 isearch.py seed steps T0 kind      kind: octa | near | islands | unions | bridge | blobs"""
import sys, random, math
from fractions import Fraction
from gmin import *
from chordM3 import data3, M1
from ends import ends
from psi import boundary_moves, toggle, unions
from islands import island
def score(S):
    c, oo, ob, bb = data3(S); U = c['U']; p = c['boundary'] - 3 * c['nu1']; E = ends(oo, ob)
    top = int(2 * max(E)) + 3 if E else 4
    Ms = [M1(c, oo, ob, n) for n in range(3, top + 2)]
    inc = min(Ms[i + 1] - Ms[i] for i in range(len(Ms) - 1)); mm = min(Ms[1:])
    return float(min(inc, mm)) / c['boundary'], float(inc), float(mm), U
seed = int(sys.argv[1]); steps = int(sys.argv[2]); T0 = float(sys.argv[3]); kind = sys.argv[4]; rng = random.Random(seed)
if kind == 'octa': starts = [(f"O_{r}", octa(r)) for r in (5, 6, 7)]
if kind == 'near': starts = [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 without two vertices", octa(7) - {(6, 0, 0), (0, 6, 0)})]
if kind == 'islands': starts = [("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 4 at (1,1)", octa(9) | island(9, 4, True, (1, 1))), ("O_7 with island 3 at (0,1)", octa(7) | island(7, 3, True, (0, 1)))]
if kind == 'unions':
    U = list(unions(6, 6)); rng.shuffle(U); starts = [(f"O_6 u O_6+{v}", S) for v, ov, S in U[:8]]
if kind == 'bridge': starts = [("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_5 and a site (10,2,0)", octa(5) | octa(5, (10, 2, 0)) | {(5, 1, 0)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2)))]
if kind == 'blobs':
    starts = []
    for t in range(5):
        S = {(0, 0, 0)}
        while len(S) < rng.choice((40, 80, 120)):
            h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
        starts.append((f"blob {t}", S))
for name, S in starts:
    cur = score(S); s0 = cur; best = (cur, set(S)); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.003
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = score(S2)
        if u[0] <= cur[0] or rng.random() < math.exp((cur[0] - u[0]) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur[0] < best[0][0]: best = (cur, set(S))
    b = best[0]
    print(f"{name}: score {s0[0]:.4f} -> {b[0]:.4f}; at the end N = {len(best[1])}, U* = {b[3]}, least increment {b[1]:.1f}, least M'_n (n >= 4) {b[2]:.1f}", flush=True)
    if b[0] < 0: print("   NEGATIVE", sorted(best[1]), flush=True)
```

## Output of `python3 islands.py 9`

```
island k = 1, same orientation, shift (0, 0): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in []; least slack of (K) = 5.00
island k = 1, same orientation, shift (1, 1): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 2.00
island k = 1, same orientation, shift (2, 1): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 2.00
island k = 2, same orientation, shift (0, 0): N = 492, U* = 24, n2* = 126, least Lam_n = 579 at n = 7; M_n < 0 for n in []; least slack of (K) = 8.00
island k = 2, same orientation, shift (1, 1): N = 492, U* = 24, n2* = 126, least Lam_n = 579 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 5.00
island k = 2, same orientation, shift (2, 1): N = 492, U* = 24, n2* = 126, least Lam_n = 579 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 5.00
island k = 3, same orientation, shift (0, 0): N = 495, U* = 21, n2* = 127, least Lam_n = 330 at n = 8; M_n < 0 for n in [3, 4, 5]; least slack of (K) = 4.00
island k = 3, same orientation, shift (1, 1): N = 495, U* = 21, n2* = 127, least Lam_n = 330 at n = 8; M_n < 0 for n in [3, 4, 5, 6]; least slack of (K) = 1.00
island k = 3, same orientation, shift (2, 1): N = 495, U* = 21, n2* = 127, least Lam_n = 330 at n = 8; M_n < 0 for n in [3, 4, 5, 6]; least slack of (K) = 0.00
island k = 4, same orientation, shift (0, 0): N = 499, U* = 21, n2* = 127, least Lam_n = 348 at n = 8; M_n < 0 for n in [3, 4]; least slack of (K) = 4.00
island k = 4, same orientation, shift (1, 1): N = 499, U* = 21, n2* = 127, least Lam_n = 348 at n = 8; M_n < 0 for n in [3, 4, 5, 6]; least slack of (K) = 1.00
island k = 4, same orientation, shift (2, 1): N = 499, U* = 21, n2* = 127, least Lam_n = 348 at n = 8; M_n < 0 for n in [3, 4, 5, 6]; least slack of (K) = 1.00
island k = 5, same orientation, shift (0, 0): N = 504, U* = 21, n2* = 127, least Lam_n = 366 at n = 8; M_n < 0 for n in [3]; least slack of (K) = 4.00
island k = 5, same orientation, shift (1, 1): N = 504, U* = 21, n2* = 127, least Lam_n = 366 at n = 8; M_n < 0 for n in [3, 4, 5]; least slack of (K) = 1.00
island k = 5, same orientation, shift (2, 1): N = 504, U* = 21, n2* = 127, least Lam_n = 366 at n = 8; M_n < 0 for n in [3, 4]; least slack of (K) = 1.00
island k = 6, same orientation, shift (0, 0): N = 510, U* = 21, n2* = 127, least Lam_n = 384 at n = 8; M_n < 0 for n in [3]; least slack of (K) = 4.00
island k = 6, same orientation, shift (1, 1): N = 510, U* = 21, n2* = 127, least Lam_n = 384 at n = 8; M_n < 0 for n in [3]; least slack of (K) = 1.00
island k = 7, same orientation, shift (0, 0): N = 517, U* = 21, n2* = 127, least Lam_n = 402 at n = 8; M_n < 0 for n in []; least slack of (K) = 4.00
island k = 8, same orientation, shift (0, 0): N = 525, U* = 21, n2* = 127, least Lam_n = 420 at n = 8; M_n < 0 for n in []; least slack of (K) = 10.00
island k = 1, reversed orientation, shift (0, 0): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in []; least slack of (K) = 5.00
island k = 1, reversed orientation, shift (1, 1): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 2.00
island k = 1, reversed orientation, shift (2, 1): N = 490, U* = 24, n2* = 126, least Lam_n = 561 at n = 7; M_n < 0 for n in [3]; least slack of (K) = 2.00
island k = 2, reversed orientation, shift (0, 0): N = 492, U* = 27, n2* = 127, least Lam_n = 738 at n = 6; M_n < 0 for n in [3]; least slack of (K) = 6.00
island k = 2, reversed orientation, shift (1, 1): N = 492, U* = 27, n2* = 127, least Lam_n = 738 at n = 6; M_n < 0 for n in [3]; least slack of (K) = 6.00
island k = 2, reversed orientation, shift (2, 1): N = 492, U* = 27, n2* = 127, least Lam_n = 738 at n = 6; M_n < 0 for n in [3]; least slack of (K) = 6.00
island k = 3, reversed orientation, shift (0, 0): N = 495, U* = 33, n2* = 127, least Lam_n = 1020 at n = 5; M_n < 0 for n in [3]; least slack of (K) = 14.00
island k = 3, reversed orientation, shift (1, 1): N = 495, U* = 33, n2* = 127, least Lam_n = 1020 at n = 5; M_n < 0 for n in [3]; least slack of (K) = 14.00
island k = 3, reversed orientation, shift (2, 1): N = 495, U* = 33, n2* = 127, least Lam_n = 1020 at n = 5; M_n < 0 for n in [3]; least slack of (K) = 14.00
island k = 4, reversed orientation, shift (0, 0): N = 499, U* = 39, n2* = 127, least Lam_n = 1203 at n = 5; M_n < 0 for n in []; least slack of (K) = 22.00
```

## Output of `python3 islands2.py 9` and `python3 islands2.py 13`

```
k = 1: 20 positions; largest n with M_n < 0: 3 (shift (0, 1), U* = 24); least slack of (K): 2.00 (shift (0, 1), U* = 24); least Lam_n = 561 at n = 7 (shift (0, 0))
k = 2: 16 positions; largest n with M_n < 0: 3 (shift (0, 1), U* = 24); least slack of (K): 5.00 (shift (0, 1), U* = 24); least Lam_n = 579 at n = 7 (shift (0, 0))
k = 3: 12 positions; largest n with M_n < 0: 6 (shift (1, 1), U* = 21); least slack of (K): 0.00 (shift (1, 2), U* = 21); least Lam_n = 330 at n = 8 (shift (0, 0))
k = 4: 9 positions; largest n with M_n < 0: 6 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 348 at n = 8 (shift (0, 0))
k = 5: 6 positions; largest n with M_n < 0: 5 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 366 at n = 8 (shift (0, 0))
k = 6: 4 positions; largest n with M_n < 0: 3 (shift (0, 0), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 384 at n = 8 (shift (0, 0))
k = 7: 2 positions; largest n with M_n < 0: 0 (shift (0, 0), U* = 21); least slack of (K): 4.00 (shift (0, 0), U* = 21); least Lam_n = 402 at n = 8 (shift (0, 0))
k = 8: 1 positions; largest n with M_n < 0: 0 (shift (0, 0), U* = 21); least slack of (K): 10.00 (shift (0, 0), U* = 21); least Lam_n = 420 at n = 8 (shift (0, 0))
k = 1: 42 positions; largest n with M_n < 0: 3 (shift (0, 1), U* = 24); least slack of (K): 2.00 (shift (0, 1), U* = 24); least Lam_n = 1272 at n = 10 (shift (0, 0))
k = 2: 36 positions; largest n with M_n < 0: 3 (shift (0, 1), U* = 24); least slack of (K): 5.00 (shift (0, 1), U* = 24); least Lam_n = 1290 at n = 10 (shift (0, 0))
k = 3: 30 positions; largest n with M_n < 0: 7 (shift (1, 3), U* = 21); least slack of (K): 0.00 (shift (0, 3), U* = 21); least Lam_n = 726 at n = 11 (shift (0, 0))
k = 4: 25 positions; largest n with M_n < 0: 7 (shift (0, 4), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 744 at n = 11 (shift (0, 0))
k = 5: 20 positions; largest n with M_n < 0: 7 (shift (0, 3), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 762 at n = 11 (shift (0, 0))
k = 6: 16 positions; largest n with M_n < 0: 7 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 780 at n = 11 (shift (0, 0))
k = 7: 12 positions; largest n with M_n < 0: 6 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 798 at n = 11 (shift (0, 0))
k = 8: 9 positions; largest n with M_n < 0: 6 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 816 at n = 11 (shift (0, 0))
k = 9: 6 positions; largest n with M_n < 0: 5 (shift (1, 1), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 834 at n = 11 (shift (0, 0))
k = 10: 4 positions; largest n with M_n < 0: 3 (shift (0, 0), U* = 21); least slack of (K): 1.00 (shift (0, 1), U* = 21); least Lam_n = 852 at n = 11 (shift (0, 0))
k = 11: 2 positions; largest n with M_n < 0: 0 (shift (0, 0), U* = 21); least slack of (K): 4.00 (shift (0, 0), U* = 21); least Lam_n = 870 at n = 11 (shift (0, 0))
k = 12: 1 positions; largest n with M_n < 0: 0 (shift (0, 0), U* = 21); least slack of (K): 10.00 (shift (0, 0), U* = 21); least Lam_n = 888 at n = 11 (shift (0, 0))
```

## Output of `python3 chordM3.py island` for (r, k, a, b) = (9, 3, 1, 1), (13, 4, 0, 4), (17, 6, 1, 4), (21, 9, 1, 5)

```
O_9 with island k = 3 at (1, 1): N = 495, U* = 21, least Lam_n = 330 at n = 8; M_n < 0 for n in [3, 4, 5, 6]; M'_n < 0 for n in []
O_13 with island k = 4 at (0, 4): N = 1479, U* = 21, least Lam_n = 744 at n = 11; M_n < 0 for n in [3, 4, 5, 6, 7]; M'_n < 0 for n in []
O_17 with island k = 6 at (1, 4): N = 3302, U* = 21, least Lam_n = 1332 at n = 15; M_n < 0 for n in [3, 4, 5, 6, 7, 8]; M'_n < 0 for n in []
O_21 with island k = 9 at (1, 5): N = 6226, U* = 21, least Lam_n = 2106 at n = 18; M_n < 0 for n in [3, 4, 5, 6, 7, 8, 9]; M'_n < 0 for n in []
```

## Output of `python3 chordM3.py`: `families`, `unions 7 7`, `unions 5 8`, `near 5`, `near 6`; `unions 9 9`, `unions 6 9`; `islands 9`, `near 7`; `islands 13`

```
named bodies: 15 bodies; largest n with M_n < 0: {0: 15}; largest n with M'_n < 0: {0: 15}; worst for M': (0, 'single site', 15)
unions O_7, O_7+v: 79 bodies; largest n with M_n < 0: {0: 70, 3: 8, 5: 1}; largest n with M'_n < 0: {0: 79}; worst for M': (0, (1, 1, 0), 20)
unions O_5, O_8+v: 61 bodies; largest n with M_n < 0: {0: 51, 3: 10}; largest n with M'_n < 0: {0: 61}; worst for M': (0, (2, 2, 1), 21)
bodies at one site from O_5: 206 bodies; largest n with M_n < 0: {0: 150, 3: 56}; largest n with M'_n < 0: {0: 206}; worst for M': (0, (-5, -1, 0), 29)
bodies at one site from O_6: 294 bodies; largest n with M_n < 0: {0: 198, 3: 96}; largest n with M'_n < 0: {0: 294}; worst for M': (0, (-6, -1, 0), 29)
unions O_9, O_9+v: 146 bodies; largest n with M_n < 0: {0: 137, 3: 8, 5: 1}; largest n with M'_n < 0: {0: 146}; worst for M': (0, (1, 1, 0), 20)
unions O_6, O_9+v: 88 bodies; largest n with M_n < 0: {0: 79, 3: 9}; largest n with M'_n < 0: {0: 88}; worst for M': (0, (2, 2, 1), 21)
islands on a face of O_9: 110 bodies; largest n with M_n < 0: {0: 11, 3: 74, 4: 5, 5: 14, 6: 6}; largest n with M'_n < 0: {0: 110}; worst for M': (0, (True, 1, 0, 0), 24)
bodies at one site from O_7: 398 bodies; largest n with M_n < 0: {0: 254, 3: 144}; largest n with M'_n < 0: {0: 398}; worst for M': (0, (-7, -1, 0), 29)
islands on a face of O_13: 315 bodies; largest n with M_n < 0: {0: 29, 3: 170, 4: 13, 5: 17, 6: 43, 7: 43}; largest n with M'_n < 0: {0: 315}; worst for M': (0, (True, 1, 0, 0), 24)
```

## Output of `python3 ends.py`: `families`, `special`, then the scans `unions`, `near`, `near2 5`, `islands`, `bridge`, `roof`

```
   pair: U* = 26, (K') least slack 13.33 at x = 1/2; least increment 238.00 at n = 3; M'_3 = 150.0; least M'_n, n >= 4: 388.0
   O_2: U* = 42, (K') least slack 64.00 at x = 1/2; least increment 372.00 at n = 3; M'_3 = 252.0; least M'_n, n >= 4: 624.0
   O_3: U* = 54, (K') least slack 96.00 at x = 1/2; least increment 432.00 at n = 3; M'_3 = 324.0; least M'_n, n >= 4: 756.0
   O_4: U* = 42, (K') least slack 64.00 at x = 1/2; least increment 264.00 at n = 3; M'_3 = 216.0; least M'_n, n >= 4: 480.0
   O_5: U* = 18, (K') least slack 0.00 at x = 1/2; least increment 0.00 at n = 3; M'_3 = 0.0; least M'_n, n >= 4: 0.0
   O_6: U* = 18, (K') least slack 0.00 at x = 1/2; least increment 0.00 at n = 3; M'_3 = 0.0; least M'_n, n >= 4: 0.0
   O_7: U* = 18, (K') least slack 0.00 at x = 1/2; least increment 0.00 at n = 3; M'_3 = 0.0; least M'_n, n >= 4: 0.0
   O_8: U* = 18, (K') least slack 0.00 at x = 1/2; least increment 0.00 at n = 3; M'_3 = 0.0; least M'_n, n >= 4: 0.0
   O_9: U* = 18, (K') least slack 0.00 at x = 1/2; least increment 0.00 at n = 3; M'_3 = 0.0; least M'_n, n >= 4: 0.0
   tetra 4: U* = 60, (K') least slack 112.00 at x = 1/2; least increment 498.00 at n = 3; M'_3 = 288.0; least M'_n, n >= 4: 786.0
   tetra 6: U* = 60, (K') least slack 112.00 at x = 1/2; least increment 462.00 at n = 3; M'_3 = 180.0; least M'_n, n >= 4: 642.0
   tetra 9: U* = 78, (K') least slack 160.00 at x = 1/2; least increment 606.00 at n = 3; M'_3 = 180.0; least M'_n, n >= 4: 786.0
   rod: U* = 114, (K') least slack 120.00 at x = 1/2; least increment 1050.00 at n = 3; M'_3 = 552.0; least M'_n, n >= 4: 1602.0
   layer: U* = 195, (K') least slack 424.00 at x = 1/2; least increment 1803.00 at n = 3; M'_3 = 882.0; least M'_n, n >= 4: 2685.0
   O_6 without a vertex: U* = 19, (K') least slack 5.33 at x = 5/2; least increment 6.00 at n = 4; M'_3 = 12.0; least M'_n, n >= 4: 26.0
   O_7 u O_7+(2,2,2): U* = 24, (K') least slack -124.00 at x = 1; least increment 12.00 at n = 3; M'_3 = 225.0; least M'_n, n >= 4: 237.0
   two O_5 and a site: U* = 43, (K') least slack 14.67 at x = 1/2; least increment 47.00 at n = 3; M'_3 = -15.0; least M'_n, n >= 4: 32.0
   O_9 with a cavity O_3: U* = 126, (K') least slack 288.00 at x = 1/2; least increment 1026.00 at n = 3; M'_3 = 486.0; least M'_n, n >= 4: 1512.0
   O_7 with a one-site cavity: U* = 36, (K') least slack 48.00 at x = 1/2; least increment 171.00 at n = 3; M'_3 = 81.0; least M'_n, n >= 4: 252.0
   ring of four O_5: U* = 141, (K') least slack 248.00 at x = 1/2; least increment 1011.00 at n = 3; M'_3 = 933.0; least M'_n, n >= 4: 1944.0
   three O_6 in a row, vertex to vertex: U* = 70, (K') least slack 58.67 at x = 1/2; least increment 152.00 at n = 3; M'_3 = 60.0; least M'_n, n >= 4: 212.0
   three O_6 at a right angle: U* = 70, (K') least slack 58.67 at x = 1/2; least increment 152.00 at n = 3; M'_3 = 60.0; least M'_n, n >= 4: 212.0
   two O_7 tip to tip: U* = 51, (K') least slack 56.00 at x = 1/2; least increment 168.00 at n = 3; M'_3 = 132.0; least M'_n, n >= 4: 300.0
   two O_7 along an axis, offset 6: U* = 54, (K') least slack 64.00 at x = 1/2; least increment 348.00 at n = 3; M'_3 = 396.0; least M'_n, n >= 4: 744.0
   O_8 and O_4 on a vertex: U* = 54, (K') least slack 64.00 at x = 1/2; least increment 264.00 at n = 3; M'_3 = 252.0; least M'_n, n >= 4: 516.0
   O_8 and O_4 on a face: U* = 60, (K') least slack 82.00 at x = 1/2; least increment 322.50 at n = 3; M'_3 = 202.5; least M'_n, n >= 4: 525.0
   two O_6 joined by a zigzag: U* = 54, (K') least slack 24.00 at x = 1/2; least increment 144.00 at n = 3; M'_3 = 36.0; least M'_n, n >= 4: 180.0
   O_7 with twin tops (2,0,0): U* = 42, (K') least slack 0.00 at x = 1; least increment 216.00 at n = 3; M'_3 = 312.0; least M'_n, n >= 4: 528.0
   two O_6 vertex to vertex: U* = 44, (K') least slack 29.33 at x = 1/2; least increment 76.00 at n = 3; M'_3 = 30.0; least M'_n, n >= 4: 106.0
   two O_6 and a site: U* = 43, (K') least slack 14.67 at x = 1/2; least increment 47.00 at n = 3; M'_3 = -15.0; least M'_n, n >= 4: 32.0
unions O_7, O_7+v: 79 bodies; (K') fails: 3, least slack -124.00 at x = 1 ((2, 2, 2), U* = 24); (I_n) fails: 0, least increment 12.00 at n = 3 ((2, 2, 2), U* = 24); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 58.0 ((1, 1, 0))
unions O_9, O_9+v: 146 bodies; (K') fails: 5, least slack -172.00 at x = 1 ((2, 2, 2), U* = 24); (I_n) fails: 0, least increment 12.00 at n = 3 ((2, 2, 2), U* = 24); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 58.0 ((1, 1, 0))
unions O_5, O_8+v: 61 bodies; (K') fails: 2, least slack -32.00 at x = 1 ((2, 2, 1), U* = 21); (I_n) fails: 0, least increment 18.00 at n = 3 ((2, 2, 1), U* = 21); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 99.0 ((2, 2, 1))
unions O_6, O_9+v: 88 bodies; (K') fails: 3, least slack -40.00 at x = 1 ((2, 2, 1), U* = 21); (I_n) fails: 0, least increment 18.00 at n = 3 ((2, 2, 1), U* = 21); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 106.0 ((14, 1, 0))
bodies at one site from O_5: 206 bodies; (K') fails: 0, least slack 2.00 at x = 1 ((-2, -2, -2), U* = 24); (I_n) fails: 0, least increment 2.00 at n = 3 ((-4, 0, 0), U* = 19); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 14.0 ((-4, 0, 0))
bodies at one site from O_6: 294 bodies; (K') fails: 0, least slack 4.00 at x = 1/2 ((-4, -2, -1), U* = 24); (I_n) fails: 0, least increment 6.00 at n = 4 ((-5, 0, 0), U* = 19); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 26.0 ((-5, 0, 0))
bodies at one site from O_7: 398 bodies; (K') fails: 0, least slack 4.00 at x = 1/2 ((-5, -2, -1), U* = 24); (I_n) fails: 0, least increment 10.00 at n = 5 ((-6, 0, 0), U* = 19); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 26.0 ((-6, 0, 0))
bodies at one site from O_8: 518 bodies; (K') fails: 0, least slack 4.00 at x = 1/2 ((-6, -2, -1), U* = 24); (I_n) fails: 0, least increment 14.00 at n = 3 ((-7, 0, 0), U* = 19); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 26.0 ((-7, 0, 0))
bodies at two sites from O_5: 21055 bodies; (K') fails: 0, least slack 4.00 at x = 1 (((-2, -2, -2), (-2, -2, 2)), U* = 30); (I_n) fails: 0, least increment 4.00 at n = 3 (((-4, 0, 0), (0, -4, 0)), U* = 20); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 25.0 (((-4, 0, 0), (0, -4, 0)))
islands on a face of O_9: 110 bodies; (K') fails: 30, least slack -62.00 at x = 1 ((True, 5, 1, 1), U* = 21); (I_n) fails: 0, least increment 3.00 at n = 3 ((True, 3, 1, 2), U* = 21); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 46.5 ((True, 3, 0, 0))
islands on a face of O_13: 315 bodies; (K') fails: 127, least slack -110.00 at x = 1 ((True, 9, 1, 1), U* = 21); (I_n) fails: 0, least increment 0.00 at n = 4 ((True, 6, 2, 2), U* = 21); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 46.5 ((True, 3, 0, 0))
two O_5 joined by one site: 146 bodies; (K') fails: 0, least slack 10.67 at x = 1/2 (((10, 2, 0), (5, 1, 0)), U* = 43); (I_n) fails: 0, least increment 44.00 at n = 3 (((10, 2, 0), (5, 1, 0)), U* = 43); M'_3 < 0: 3; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 14.0 (((10, 2, 0), (5, 1, 0)))
two O_6 joined by one site: 233 bodies; (K') fails: 0, least slack 10.67 at x = 1/2 (((12, 2, 0), (6, 1, 0)), U* = 43); (I_n) fails: 0, least increment 44.00 at n = 3 (((12, 2, 0), (6, 1, 0)), U* = 43); M'_3 < 0: 3; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 14.0 (((12, 2, 0), (6, 1, 0)))
roof O_6 over two legs O_5: 92 bodies; (K') fails: 0, least slack 17.33 at x = 1 ((2, 2, 1), U* = 40); (I_n) fails: 0, least increment 152.00 at n = 3 ((10, 0, 1), U* = 70); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 212.0 ((10, 0, 1))
roof O_6 over two legs O_6: 116 bodies; (K') fails: 3, least slack -62.67 at x = 1 ((2, 2, 2), U* = 40); (I_n) fails: 0, least increment 117.00 at n = 3 ((1, 1, 2), U* = 30); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 212.0 ((11, 0, 1))
roof O_7 over two legs O_5: 104 bodies; (K') fails: 0, least slack 6.67 at x = 1 ((4, 2, 2), U* = 56); (I_n) fails: 0, least increment 152.00 at n = 3 ((11, 0, 1), U* = 70); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 212.0 ((11, 0, 1))
roof O_7 over two legs O_6: 130 bodies; (K') fails: 0, least slack 1.33 at x = 1 ((2, 2, 1), U* = 40); (I_n) fails: 0, least increment 152.00 at n = 3 ((12, 0, 1), U* = 70); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 212.0 ((12, 0, 1))
roof O_8 over two legs O_4: 96 bodies; (K') fails: 0, least slack 5.33 at x = 1 ((0, 2, 4), U* = 46); (I_n) fails: 0, least increment 98.00 at n = 3 ((5, 0, 1), U* = 34); M'_3 < 0: 0; M'_n < 0 for some n >= 4: 0; least positive value of min over n >= 4 of M'_n: 275.0 ((5, 0, 1))
```

## Output of `python3 stacks.py 9`

```
O_9 with islands k = 3 at (1,1) on all eight faces: N = 537, U* = 42, least Lam_n = 1488 at n = 5; least increment 36.0 at n = 3; M'_3 = 552.0; least M'_n, n >= 4: 588.0
O_9 with islands k = 3 at (0,0) on all eight faces: N = 537, U* = 42, least Lam_n = 1488 at n = 5; least increment 84.0 at n = 3; M'_3 = 360.0; least M'_n, n >= 4: 444.0
O_9 with islands k = 4 at (1,1) on all eight faces: N = 569, U* = 42, least Lam_n = 1632 at n = 5; least increment 24.0 at n = 3; M'_3 = 840.0; least M'_n, n >= 4: 864.0
O_9 with islands k = 6 at (0,0) on all eight faces: N = 657, U* = 42, least Lam_n = 1920 at n = 5; least increment 180.0 at n = 3; M'_3 = 960.0; least M'_n, n >= 4: 1140.0
O_9 with islands k = 5 at (1,1) on all eight faces: N = 609, U* = 42, least Lam_n = 1776 at n = 5; least increment 48.0 at n = 3; M'_3 = 900.0; least M'_n, n >= 4: 948.0
O_9 with islands k = 2 at (1,1) on all eight faces: N = 513, U* = 66, least Lam_n = 1800 at n = 3; least increment 348.0 at n = 3; M'_3 = 480.0; least M'_n, n >= 4: 828.0
O_9 with islands k = 1 at (1,1) on all eight faces: N = 497, U* = 66, least Lam_n = 1656 at n = 3; least increment 396.0 at n = 3; M'_3 = 264.0; least M'_n, n >= 4: 660.0
O_9 with stacked islands (5, 2) at (0,0): N = 507, U* = 27, least Lam_n = 828 at n = 6; least increment 88.5 at n = 3; M'_3 = 103.5; least M'_n, n >= 4: 192.0
O_9 with stacked islands (6, 3) at (0,0): N = 516, U* = 24, least Lam_n = 642 at n = 7; least increment 54.0 at n = 3; M'_3 = 114.0; least M'_n, n >= 4: 168.0
O_9 with stacked islands (6, 3) at (1,0): N = 516, U* = 24, least Lam_n = 642 at n = 7; least increment 39.0 at n = 3; M'_3 = 135.0; least M'_n, n >= 4: 174.0
O_9 with stacked islands (4, 1) at (1,1): N = 500, U* = 27, least Lam_n = 792 at n = 6; least increment 63.0 at n = 3; M'_3 = 133.5; least M'_n, n >= 4: 196.5
O_9 with stacked islands (7, 4, 1) at (0,0): N = 528, U* = 30, least Lam_n = 1026 at n = 6; least increment 111.0 at n = 3; M'_3 = 147.0; least M'_n, n >= 4: 258.0
```

## Output of `python3 blocked.py`

```
(deg, e): least 3 tau - (3/2) bl+, attained with (tau, bl+), number of sets
   (1, 0) 0.0 (2.0, 4) 12
   (2, 0) -9.0 (1.0, 8) 66
   (3, 0) -18.0 (0.0, 12) 212
   (3, 1) 0.0 (0.0, 0) 8
   (4, 0) -27.0 (-1.0, 16) 423
   (4, 1) -9.0 (-1.0, 4) 72
   (5, 0) -30.0 (-2.0, 16) 516
   (5, 1) -15.0 (-1.5, 7) 264
   (5, 2) 0.0 (0.0, 0) 12
   (6, 0) -33.0 (-3.0, 16) 352
   (6, 1) -21.0 (-2.0, 10) 472
   (6, 2) -9.0 (-1.0, 4) 100
   (7, 0) -36.0 (-4.0, 16) 108
   (7, 1) -24.0 (-2.5, 11) 384
   (7, 2) -12.0 (-1.0, 6) 276
   (7, 3) 3.0 (1.0, 0) 24
   (8, 0) -39.0 (-5.0, 16) 9
   (8, 1) -27.0 (-3.5, 11) 96
   (8, 2) -15.0 (-1.5, 7) 264
   (8, 3) -3.0 (0.5, 3) 120
   (8, 4) 9.0 (3.0, 0) 6
   (9, 2) -18.0 (-2.0, 8) 44
   (9, 3) -6.0 (0.5, 5) 120
   (9, 4) 6.0 (3.0, 2) 56
   (10, 4) 3.0 (3.0, 4) 42
   (10, 5) 15.0 (5.0, 0) 24
   (11, 6) 24.0 (8.0, 0) 12
   (12, 8) 45.0 (15.0, 0) 1
```

## Output of `python3 sharp.py`

```
O_5: U* = 18, Pi = 54, def1 = 0; least slack of (I0_n) = 0.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(8, 4, 9): 6}
O_7: U* = 18, Pi = 54, def1 = 0; least slack of (I0_n) = 0.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(8, 4, 9): 6}
O_6 without a vertex: U* = 19, Pi = 45, def1 = 0; least slack of (I0_n) = 6.0 at n = 4; sites with pi != 0 by (deg, e, pi): {(8, 4, 9): 5}
O_6 with a site on a face: U* = 24, Pi = 45, def1 = 0; least slack of (I0_n) = 46.5 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -6): 3, (8, 4, 9): 6, (9, 4, 9): 1}
O_7 u O_7+(2,0,0): U* = 42, Pi = 54, def1 = 0; least slack of (I0_n) = 216.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -9): 4, (8, 4, 9): 10}
O_7 u O_7+(4,0,0): U* = 54, Pi = 54, def1 = 0; least slack of (I0_n) = 300.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -9): 4, (8, 4, 9): 10}
O_7 u O_7+(1,1,0): U* = 20, Pi = 48, def1 = 0; least slack of (I0_n) = 28.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(7, 3, 3): 4, (8, 4, 9): 4}
O_7 u O_7+(2,2,2): U* = 24, Pi = 36, def1 = 0; least slack of (I0_n) = 12.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -6): 6, (7, 3, 3): 6, (8, 4, 9): 6}
two O_6 vertex to vertex: U* = 44, Pi = 66, def1 = 0; least slack of (I0_n) = 58.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(7, 2, -12): 2, (8, 4, 9): 10}
two O_6 and a site: U* = 43, Pi = 69, def1 = 0; least slack of (I0_n) = 32.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(7, 2, -12): 2, (8, 4, 9): 10, (10, 4, 3): 1}
O_9 with island 3 at (1,2): U* = 21, Pi = 45, def1 = 0; least slack of (I0_n) = -9.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -6): 3, (7, 3, 3): 3, (8, 4, 9): 6}
O_9 with island 5 at (1,1): U* = 21, Pi = 45, def1 = 0; least slack of (I0_n) = 6.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -6): 3, (7, 3, 3): 3, (8, 4, 9): 6}
O_13 with island 6 at (2,2): U* = 21, Pi = 45, def1 = 0; least slack of (I0_n) = -7.5 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -6): 3, (7, 3, 3): 3, (8, 4, 9): 6}
O_9 with reversed island 3: U* = 33, Pi = 27, def1 = 0; least slack of (I0_n) = 102.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -3): 6, (5, 1, -3): 3, (8, 4, 9): 6}
tetrahedron 6: U* = 60, Pi = -36, def1 = 0; least slack of (I0_n) = 462.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(6, 2, -3): 24, (9, 4, 9): 4}
two O_7 tip to tip: U* = 51, Pi = 63, def1 = 0; least slack of (I0_n) = 144.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(4, 0, -27): 1, (8, 4, 9): 10}
O_8 and O_4 on a vertex: U* = 54, Pi = 54, def1 = 0; least slack of (I0_n) = 228.0 at n = 3; sites with pi != 0 by (deg, e, pi): {(2, 0, -9): 4, (8, 4, 9): 10}
```

## Output of `python3 m0.py named`, `island` for five islands, `islands 9`

```
   pair: U* = 26, Pi = 48, def1 = 0; M0_n < 0 for n in []
   single: U* = 15, Pi = 45, def1 = 0; M0_n < 0 for n in []
   O_2: U* = 42, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_3: U* = 54, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_4: U* = 42, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_5: U* = 18, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_6: U* = 18, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_7: U* = 18, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_8: U* = 18, Pi = 54, def1 = 0; M0_n < 0 for n in []
   O_9: U* = 18, Pi = 54, def1 = 0; M0_n < 0 for n in []
   tetra 4: U* = 60, Pi = 0, def1 = 0; M0_n < 0 for n in []
   tetra 6: U* = 60, Pi = -36, def1 = 0; M0_n < 0 for n in []
   tetra 9: U* = 78, Pi = -90, def1 = 0; M0_n < 0 for n in []
   rod: U* = 114, Pi = 72, def1 = 0; M0_n < 0 for n in []
   layer: U* = 195, Pi = -171, def1 = 0; M0_n < 0 for n in []
O_9 with island k = 3 at (1, 2): U* = 21, Pi = 45, def1 = 0; M0_n < 0 for n in [3, 4, 5, 6]
O_13 with island k = 6 at (2, 2): U* = 21, Pi = 45, def1 = 0; M0_n < 0 for n in [3, 4, 5, 6, 7]
O_13 with island k = 4 at (0, 4): U* = 21, Pi = 45, def1 = 0; M0_n < 0 for n in [3, 4, 5, 6, 7]
O_17 with island k = 6 at (1, 4): U* = 21, Pi = 45, def1 = 0; M0_n < 0 for n in [3, 4, 5, 6, 7, 8]
O_21 with island k = 9 at (1, 5): U* = 21, Pi = 45, def1 = 0; M0_n < 0 for n in [3, 4, 5, 6, 7, 8, 9]
islands on a face of O_9: 110 bodies; largest n with M0_n < 0, by number of bodies: {0: 11, 3: 74, 4: 5, 5: 14, 6: 6}; worst (6, (True, 3, 1, 1), 21, Fraction(45, 1))
```

## Output of `python3 check67.py`

```
O_6: E = 126, H = 144, H1 = 0, H2 = 0, Pi = 54, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..9
O_6 without a vertex: E = 125, H = 140, H1 = 0, H2 = 0, Pi = 45, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..9
O_6 with a site on a face: E = 129, H = 144, H1 = 18, H2 = 0, Pi = 45, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..9
O_7 u O_7+(2,2,2): E = 180, H = 192, H1 = 132, H2 = 0, Pi = 36, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..10
two O_5 and a site: E = 209, H = 232, H1 = 14, H2 = 0, Pi = 69, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..9
O_9 with island 4 at (1,1): E = 201, H = 216, H1 = 54, H2 = 0, Pi = 45, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..12
tetrahedron 6: E = 96, H = 84, H1 = 0, H2 = 0, Pi = -36, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..9
rod of 10: E = 72, H = 96, H1 = 0, H2 = 0, Pi = 72, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..13
two O_7 tip to tip: E = 291, H = 312, H1 = 16, H2 = 0, Pi = 63, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..10
O_9 with a cavity O_3: E = 126, H = 216, H1 = 0, H2 = 48, Pi = 126, def1 = 42: Lemma 66 and both forms of the increment hold for n = 1..12
single site: E = 9, H = 24, H1 = 0, H2 = 0, Pi = 45, def1 = 0: Lemma 66 and both forms of the increment hold for n = 1..6
```

## Output of `python3 corner.py`

```
(number of empty neighbours, corners c1): least u-, number of sets
   (5, 1) 0 24   4u- < 3c1 in 24 sets; equality in 0
   (6, 1) 0 168   4u- < 3c1 in 48 sets; equality in 0
   (7, 1) 0 336   4u- < 3c1 in 24 sets; equality in 0
   (7, 2) 1 84   4u- < 3c1 in 84 sets; equality in 0
   (8, 1) 2 96   4u- < 3c1 in 0 sets; equality in 0
   (8, 2) 1 216   4u- < 3c1 in 48 sets; equality in 0
   (8, 3) 1 96   4u- < 3c1 in 96 sets; equality in 0
   (8, 4) 3 6   4u- < 3c1 in 0 sets; equality in 6
   (9, 2) 3 24   4u- < 3c1 in 0 sets; equality in 0
   (9, 3) 2 24   4u- < 3c1 in 24 sets; equality in 0
   (9, 4) 2 132   4u- < 3c1 in 48 sets; equality in 84
   (9, 6) 3 32   4u- < 3c1 in 32 sets; equality in 0
   (10, 6) 4 24   4u- < 3c1 in 24 sets; equality in 0
   (10, 8) 3 18   4u- < 3c1 in 18 sets; equality in 0
   (10, 9) 6 24   4u- < 3c1 in 24 sets; equality in 0
   (11, 14) 9 12   4u- < 3c1 in 12 sets; equality in 0
   (12, 24) 15 1   4u- < 3c1 in 1 sets; equality in 0
sets with 4 u- < 3 c1: 507 of 1317 sets with a corner
```

## Output of `python3 isearch.py`: `1 1500 0.05 octa`, `2 1500 0.05 near`, `3 1200 0.05 islands`, `4 1200 0.1 unions`, `5 1500 0.05 bridge`, `6 2500 0.3 blobs`, `7 1500 0.2 near`, `8 1200 0.15 islands` (stopped; lines written until then, run 6 had written none)

```
O_5: score 0.0000 -> 0.0000; at the end N = 85, U* = 18, least increment 0.0, least M'_n (n >= 4) 0.0
O_6: score 0.0000 -> 0.0000; at the end N = 146, U* = 18, least increment 0.0, least M'_n (n >= 4) 0.0
O_7: score 0.0000 -> 0.0000; at the end N = 231, U* = 18, least increment 0.0, least M'_n (n >= 4) 0.0
O_6 without a vertex: score 0.0140 -> 0.0140; at the end N = 145, U* = 19, least increment 6.0, least M'_n (n >= 4) 26.0
O_6 with a site on a face: score 0.1130 -> 0.1130; at the end N = 147, U* = 24, least increment 49.5, least M'_n (n >= 4) 82.5
O_7 without two vertices: score 0.0345 -> 0.0345; at the end N = 229, U* = 20, least increment 20.0, least M'_n (n >= 4) 52.0
O_9 with island 3 at (1,2): score 0.0030 -> 0.0030; at the end N = 495, U* = 21, least increment 3.0, least M'_n (n >= 4) 88.5
O_9 with island 4 at (1,1): score 0.0030 -> 0.0030; at the end N = 499, U* = 21, least increment 3.0, least M'_n (n >= 4) 108.0
O_7 with island 3 at (0,1): score 0.0223 -> 0.0223; at the end N = 237, U* = 21, least increment 13.5, least M'_n (n >= 4) 63.0
O_6 u O_6+(7, 3, 2): score 0.2775 -> 0.2775; at the end N = 292, U* = 52, least increment 227.0, least M'_n (n >= 4) 437.0
O_6 u O_6+(7, 2, 1): score 0.2556 -> 0.2556; at the end N = 286, U* = 48, least increment 204.0, least M'_n (n >= 4) 420.0
two O_5 and a site: score 0.0526 -> 0.0526; at the end N = 171, U* = 43, least increment 47.0, least M'_n (n >= 4) 32.0
two O_5 and a site (10,2,0): score 0.0230 -> 0.0230; at the end N = 171, U* = 43, least increment 44.0, least M'_n (n >= 4) 14.0
O_7 u O_7+(2,2,2): score 0.0147 -> 0.0147; at the end N = 358, U* = 24, least increment 12.0, least M'_n (n >= 4) 237.0
O_6 without a vertex: score 0.0140 -> 0.0140; at the end N = 145, U* = 19, least increment 6.0, least M'_n (n >= 4) 26.0
O_9 with island 3 at (1,2): score 0.0030 -> 0.0030; at the end N = 495, U* = 21, least increment 3.0, least M'_n (n >= 4) 88.5
```

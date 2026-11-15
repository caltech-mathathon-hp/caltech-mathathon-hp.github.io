"""Section 43 of the note: tops, splits and merges of the slice pieces in the three axes.
For an axis, the pieces of all slices form a graph (piece - child).  T_a = pieces without parent + pieces without child,
sigma_a = sum over pieces of (children - 1)_+ + (parents - 1)_+, b1_a = cycle rank.  For a connected body
T_a = 2 - 2 b1_a + sigma_a.          Conjecture G': U* >= 3 T + 3 sigma   (T, sigma summed over the three axes)."""
from gmin import *
from tops import slices, pieces
LOW = ((1, 0), (-1, 0), (0, 1), (0, -1))
def axis_data(S, ax):
    sl = slices(S, ax, 1); pcs = {l: pieces(sq) for l, sq in sl.items()}
    idx = {}
    for l, ps in pcs.items():
        for i, p in enumerate(ps):
            for s in p: idx[(l, s)] = (l, i)
    kids = {}; pars = {}; V = 0; E = 0
    for l, ps in pcs.items():
        for i, p in enumerate(ps):
            V += 1
            ch = {idx[(l - 1, (u + a, v + b))] for u, v in p for a, b in LOW if (l - 1, (u + a, v + b)) in idx}
            kids[(l, i)] = ch; E += len(ch)
            for c in ch: pars.setdefault(c, set()).add((l, i))
    T = sum(1 for k in kids if not kids[k]) + sum(1 for k in kids if k not in pars)
    sig = sum(max(0, len(kids[k]) - 1) for k in kids) + sum(max(0, len(v) - 1) for v in pars.values())
    return T, sig, E - V + 1
def morse(S):
    T = sig = b1 = 0
    for ax in range(3):
        t, s, b = axis_data(S, ax); T += t; sig += s; b1 += b
    return T, sig, b1
def gslack(S):
    T, sig, b1 = morse(S); return cost(S)['U'] - 3 * T - 3 * sig
if __name__ == '__main__':
    from tops import tops
    def show(name, S):
        T, sig, b1 = morse(S); u = cost(S)['U']; assert T == tops(S)[0]; assert not connected(S) or T == 6 - 2 * b1 + sig
        print(f"{name}: N={len(S)} U*={u} T={T} sigma={sig} b1={b1}  U*-3T-3sigma={u - 3*T - 3*sig}")
    n = 6
    show('O_6', octa(n)); show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0)))
    show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    ring = octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0)); show('ring of four (connected: %s)' % connected(ring), ring)
    S = octa(9); T = {h for h in S if not (abs(h[0]) + abs(h[1]) <= 2)}; show('O_9 with a tunnel along z', T)
    show('O_9 with cavity O_3', octa(9) - octa(3))
    S = octa(9) - {h for h in octa(9) if h[2] >= 5 and abs(h[0]) + abs(h[1]) <= 1}; show('O_9 with a pit from above', S)
    show('lambda: bar with two O_5', octa(5) | octa(5, (12, 0, 0)) | {(i, 0, 4) for i in range(0, 13, 2)} | {(i, 1, 4) for i in range(1, 12, 2)})
    for v in ((4,0,0),(2,2,2),(4,4,4),(8,3,3),(3,3,0),(5,4,3)): show(f'O_7+{v}', octa(7) | octa(7, v))

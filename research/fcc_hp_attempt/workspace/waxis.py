"""Section 44 of the note: W split by axis: W_a = sum over surface sites of (empty in-plane neighbours in the a-slice - 1) + sum over coat sites of (occupied in-plane neighbours - 1).
Also per level: corners, e, f."""
from gmin import *
from morse import axis_data
from wdef import parts
def w_axes(S):
    S = set(S); out = []
    surf = [h for h in S if any(add(h, r) not in S for r in ROOTS)]
    coat = {add(h, r) for h in S for r in ROOTS} - S
    for ax in range(3):
        inpl = [r for r in ROOTS if r[ax] == 0]
        w = sum(sum(1 for r in inpl if add(h, r) not in S) - 1 for h in surf) + sum(sum(1 for r in inpl if add(p, r) in S) - 1 for p in coat)
        out.append(w)
    return out
if __name__ == '__main__':
    def show(name, S):
        w = w_axes(S); p = parts(S); T = [axis_data(S, a)[0] for a in range(3)]
        assert sum(w) == p['W']
        print(f"{name}: U*={p['U']} W={p['W']} = {w}  def2={p['d2']} def1={p['d1']}  T by axis {T}   6(T_a-1) = {[6*(t-1) for t in T]}")
    n = 6
    show('O_6', octa(n)); show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('tips coincide', octa(n) | octa(n, (2*n-2, 0, 0)))
    show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0))); show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    show('twin tops', octa(n) | octa(n, (2, 0, 0))); show('O_6 + cell', octa(n) | {(n,1,0)}); show('O_6 + site over an edge', octa(n) | {(4, 3, 0)})
    show('O_6+(1,1,0)', octa(n) | octa(n,(1,1,0))); show('O_6+(2,2,2)', octa(n) | octa(n,(2,2,2))); show('O_6 minus vertex', octa(n) - {(5,0,0)})
    show('pair', {(0,0,0),(1,1,0)}); show('rod 6', {(i,i,0) for i in range(6)}); show('tetra 6', tetra(6))
    show('O_6+(4,0,0)', octa(n) | octa(n,(4,0,0))); show('O_6+(4,4,4)', octa(n) | octa(n,(4,4,4)))

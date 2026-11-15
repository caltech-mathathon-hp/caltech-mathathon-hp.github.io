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

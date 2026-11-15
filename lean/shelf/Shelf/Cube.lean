import Mathlib
import ProteinFolding.Cubic.Proofs.PackingGeometryBlockRails
import ProteinFolding.Cubic.Proofs.PackingGeometryOutward
import ProteinFolding.Cubic.Proofs.PackingGeometryWallsCrossing
import ProteinFolding.Cubic.Proofs.PackingAnchors

/-!
# The cube and its skeleton

The vocabulary of Section 2.2 of the paper (`proof/paper/paper.tex`). Throughout,
`n` is the side of the cube, `N = n - 1`, and the cube is `Q = {0, …, N}³`.

The team's library already has this vocabulary, for a cube `cube a n` with any
corner `a`, and we use it as it is, with `a = 0`. The dictionary, with `n = d + 2`
(so `d = n - 2` is the number of nodes of an edge):

| Paper | Lean (namespace `ProteinFolding.CubicPackingGeometry`) |
|---|---|
| a coordinate of `p` lies in `{0, N}` | `BoundaryCoordinate 0 p n k` |
| `p` is a point of the skeleton | `EdgeSkeleton 0 n p`, as a finite set `skeletonFinset 0 n` |
| `p` is a corner | `p ∈ cornerFinset 0 d` |
| an edge of `Q` | `e : CubeEdge` (twelve of them) |
| the node number `r + 1` of the edge `e` | `openEdgePoint 0 d e r`, `r : Fin d` |
| the set of nodes of `e` | `openEdgeFinset 0 d e` |
| an end node of `e` | `openEdgePoint 0 d e r` with `IsEnd r` (below) |
| `e` and `e'` do not touch | `NoCommonCorner e e'` |
| a simple path in the graph `G` | a list `ps` with `ps.Nodup`, `ps.IsChain cubicLattice.Adj` and `∀ p ∈ ps, EdgeSkeleton 0 n p` |
| the edges that a path runs through | `visitedEdges 0 d ps` |

What is new in this file is the cube in standard position and the clamp map `κ`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding

/-- The cube `Q = {0, …, n-1}³`. -/
abbrev Q (n : ℕ) : Set Site := cube 0 n

theorem mem_Q {n : ℕ} {p : Site} : p ∈ Q n ↔ ∀ k : Fin 3, 0 ≤ p k ∧ p k < n := by
  simp [cube]

/-- The clamp map `κ` of Lemma 5: every negative coordinate becomes `0` and every
coordinate larger than `N` becomes `N`. -/
def clamp (n : ℕ) (w : Site) : Site := fun k => max 0 (min (w k) ((n : ℤ) - 1))

/-- The node number `r` (counting from 0) of an edge with `d` nodes is an end
node: it is next to one of the two corners of the edge. -/
def IsEnd {d : ℕ} (r : Fin d) : Prop := r.val = 0 ∨ r.val + 1 = d

end ProteinFolding.Shelf

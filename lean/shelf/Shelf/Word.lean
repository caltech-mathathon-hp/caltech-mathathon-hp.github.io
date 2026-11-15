import ProteinFolding.Cubic.Encodings
import Shelf.Source

/-!
# The string of the reduction

Section 3 of the paper (`proof/paper/paper.tex`). For a normalised instance `(a₁, …, a_k; m, B)` put

  `n = m (B + 1) + 3`,  `N₀ = n³ - 12 n + 16`,  `λ = 4 n + 2 k`.

The string is

  `H^N₀  PP  D(9n-10)  P^λ  D(n-2)  P^n  H (P^(B+6) H)^m  P^n  D(n-2)  ∏ᵢ (P^λ D(aᵢ))  P`

where `D(r) = H (PPH)^(r-1)` is the dense run with `r` letters `H`. In the order
above the pieces are: the core, the long run `A`, a linker, the filler `F₁`, a
tether, the `m + 1` separators joined by inner tethers, a tether, the filler
`F₂`, and one linker and one dense run for each item.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue List

/-- The dense run `D(r) = H (PPH)^(r-1)`: `r` letters `H`, any two consecutive ones
separated by `PP`. `D(0)` is the empty word. -/
def denseRun : ℕ → Sequence
  | 0 => []
  | r + 1 => H :: (replicate r [P, P, H]).flatten

/-- The side of the cube, `n = m (B + 1) + 3`. One edge then has `n - 2 = (m + 1) + m B`
inner nodes: room for `m + 1` separators and `m` bins of size `B`. -/
def side (J : Packing.Instance) : ℕ :=
  J.bins * (J.capacity + 1) + 3

/-- `N₀ = n³ - 12 n + 16`, the number of points of the cube that are not on an edge.
Written with the subtraction last so that it is right for every `n ≥ 2`. -/
def coreLength (n : ℕ) : ℕ :=
  n ^ 3 + 16 - 12 * n

/-- `λ = 4 n + 2 k`, the length of every linker. -/
def linkerLength (J : Packing.Instance) : ℕ :=
  4 * side J + 2 * J.sizes.length

/-- The separators `σ₁, …, σ_{m+1}`: single `H`'s, consecutive ones joined by an
inner tether `P^(B+6)`. -/
def separators (J : Packing.Instance) : Sequence :=
  H :: (replicate J.bins (replicate (J.capacity + 6) P ++ [H])).flatten

/-- The items in input order, each one a dense run preceded by its linker. -/
def itemsWord (J : Packing.Instance) : Sequence :=
  (J.sizes.map fun a => replicate (linkerLength J) P ++ denseRun a).flatten

/-- The pieces of the string, in order (the displayed formula of Section 3). -/
def shelfPieces (J : Packing.Instance) : List Sequence :=
  [ replicate (coreLength (side J)) H,   -- core
    [P, P],
    denseRun (9 * side J - 10),          -- A
    replicate (linkerLength J) P,        -- linker
    denseRun (side J - 2),               -- F₁
    replicate (side J) P,                -- tether
    separators J,
    replicate (side J) P,                -- tether
    denseRun (side J - 2),               -- F₂
    itemsWord J,
    [P] ]

/-- The string `S` of the reduction. -/
def shelfWord (J : Packing.Instance) : Sequence :=
  (shelfPieces J).flatten

/-- Where the reduction sends an input that fails the check: the empty string with
`n = 1`. It has no `H`, so it is a no-instance. (The paper counts `∑ aᵢ = m · B` as
part of the definition of an instance, so it needs no such string.) -/
def noInstance : PerfectInput :=
  ([], 1)

/-- The reduction on raw inputs: check the instance, normalise it, write the
string and the side of the cube. -/
def shelfReduction (I : Packing.Instance) : PerfectInput :=
  if Guard I then (shelfWord (normalise I), side (normalise I)) else noInstance

end ProteinFolding.Shelf

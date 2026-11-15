import Shelf

/-!
# The website's examples, computed from the Lean definitions

The website's page about the one-edge proof folds the string of this project for
a few small instances (section "Folding a small instance") and says how large
each cube is. Here Lean computes the same numbers from `Shelf.shelfReduction`,
the map that `Shelf.reductionCorrect` is about.

`#guard` evaluates a condition and stops with an error if it is false. So
`lake env lean checks/SmallInstances.lean` prints nothing when every number
agrees. These are computations and not proofs, and no file of `Shelf/` uses them.
-/

namespace ProteinFolding.Shelf.SmallInstances

open ProteinFolding ProteinFolding.Shelf

/-- The string and the side of the cube for items of the given sizes and `m` bins
of capacity `B`. -/
def reduce (sizes : List ℕ) (m B : ℕ) : PerfectInput :=
  shelfReduction { sizes := sizes, capacity := B, bins := m }

/-- The side `n` of the cube. -/
def cubeSide (sizes : List ℕ) (m B : ℕ) : ℕ := (reduce sizes m B).2

/-- The number of letters `H` in the string. -/
def countH (sizes : List ℕ) (m B : ℕ) : ℕ := (reduce sizes m B).1.count Residue.H

/-- The number of letters of the string. -/
def letters (sizes : List ℕ) (m B : ℕ) : ℕ := (reduce sizes m B).1.length

/-! "Two bins of size 2 become three bins of size 12, so `n = 42`, with 74,088
`H`'s and about 76,000 letters." -/

#guard cubeSide [1, 1, 2] 2 2 = 42
#guard countH [1, 1, 2] 2 2 = 74088
#guard letters [1, 1, 2] 2 2 = 76063

/-! "One bin of size 2 already gives `n = 16`." -/

#guard cubeSide [1, 1] 1 2 = 16
#guard countH [1, 1] 1 2 = 16 ^ 3

/-! The other instances that the 3D view offers, with the `n` it shows. In each
one the string has `n³` letters `H`. The fourth has no packing, and the
reduction still writes its string: that string has no perfect fold. -/

#guard cubeSide [1, 1] 2 1 = 24
#guard countH [1, 1] 2 1 = 24 ^ 3
#guard cubeSide [1, 2, 1, 2] 3 2 = 42
#guard countH [1, 2, 1, 2] 3 2 = 42 ^ 3
#guard cubeSide [2, 1, 1, 2] 2 3 = 60
#guard countH [2, 1, 1, 2] 2 3 = 60 ^ 3
#guard cubeSide [2, 2, 2] 2 3 = 60
#guard countH [2, 2, 2] 2 3 = 60 ^ 3
#guard cubeSide [1, 2, 1, 2, 3] 3 3 = 60
#guard countH [1, 2, 1, 2, 3] 3 3 = 60 ^ 3

/-! When `m` is even the reduction adds one item of size `B`, after it has
multiplied every size by 6. Lean puts the new item first in the list (it uses the
team's `Packing.pad`), and the website's 3D view puts it last. So for the three
examples with `m = 2` and items of different sizes, the two strings have the same
pieces, and the dense runs of the items come in a different order. Theorems 12
and 16 hold for the items in any order, so they hold for both strings. -/

#guard (normalise { sizes := [1, 1, 2], capacity := 2, bins := 2 }).sizes = [12, 6, 6, 12]
#guard (normalise { sizes := [2, 1, 1, 2], capacity := 3, bins := 2 }).sizes = [18, 12, 6, 6, 12]
#guard (normalise { sizes := [2, 2, 2], capacity := 3, bins := 2 }).sizes = [18, 12, 12, 12]

/-! An input whose sizes do not add up to `m · B` is not an instance. The
reduction sends it to the empty string with `n = 1`, which has no perfect fold
(`noInstance_rejected`). -/

#guard reduce [1, 1] 2 3 = ([], 1)

end ProteinFolding.Shelf.SmallInstances

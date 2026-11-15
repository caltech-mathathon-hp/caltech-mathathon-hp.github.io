import ProteinFolding.Cubic.Statement

/-! Small kernel-checked examples that pin down the modelling conventions. -/

namespace ProteinFolding.Examples

open Residue

private def site (x y z : ℤ) : Site :=
  fun k => if k = 0 then x else if k = 1 then y else z

-- Axis steps are edges; diagonal steps are not.
example : cubicLattice.Adj (site 0 0 0) (site 0 0 1) := by decide
example : ¬ cubicLattice.Adj (site 0 0 0) (site 1 1 0) := by decide

private def twoHFold : Fold cubicLattice [H, H].length where
  pos i := site (i.val : ℤ) 0 0
  injective_pos := by decide
  consecutive := by decide

-- A consecutive H-H pair contributes one bond, not zero or two.
example : bondCount [H, H] twoHFold = 1 := by decide
example : energy [H, H] twoHFold = -1 := by decide
example : HPStringFold (G := cubicLattice) [H, H] 1 :=
  ⟨twoHFold, by decide⟩

private def squareFold : Fold cubicLattice [H, H, H, H].length where
  pos i := if i.val = 0 then site 0 0 0 else
    if i.val = 1 then site 1 0 0 else
    if i.val = 2 then site 1 1 0 else site 0 1 0
  injective_pos := by decide
  consecutive := by decide

-- Three backbone bonds plus one contact between the two endpoints.
example : bondCount [H, H, H, H] squareFold = 4 := by decide
-- On the same geometric walk, only the H-H endpoint contact counts.
example : bondCount [H, P, P, H] squareFold = 1 := by decide
example : bondCount [P, P, P, P] squareFold = 0 := by decide

example : hydrophobicCount [H, P, H] = 2 := by decide
example : site 1 1 1 ∈ cube (site 0 0 0) 2 := by decide
example : site 2 1 1 ∉ cube (site 0 0 0) 2 := by decide
example : cubeBondThreshold 2 = 12 := by decide

end ProteinFolding.Examples

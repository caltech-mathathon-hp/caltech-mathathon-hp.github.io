import Mathlib.Data.Int.Basic

/-! # HP words and folds (test fixture) -/

namespace ProteinFolding

/-- Hydrophobic (H) and hydrophilic (P) residues. -/
inductive Residue where
  | H
  | P
  deriving DecidableEq

/-- A word over {H, P}. -/
abbrev Sequence := List Residue

/-- A walk on the square grid that never visits a site twice. -/
structure Fold (N : ℕ) where
  pos : Fin N → ℤ × ℤ
  injective_pos : Function.Injective pos

def bondCount (S : Sequence) (f : Fold S.length) : ℕ := 0

instance : Inhabited Residue := ⟨Residue.H⟩

-- An old attempt, kept as a comment: theorem bad : False := by sorry
/- theorem worse : False := by
  sorry -/

end ProteinFolding

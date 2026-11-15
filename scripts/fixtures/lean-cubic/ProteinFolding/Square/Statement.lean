import ProteinFolding.Common.Statement

namespace ProteinFolding.Square

/-- A fold on the square grid, a second `Fold`. -/
structure Fold (N : ℕ) where
  pos : Fin N → ℤ × ℤ

/-- Only the square problem has a grid. -/
def Grid : Type := ℤ × ℤ

def Instance.Accepts (n : ℕ) : Prop := n = 0

def message : String := "no sorry here"

end ProteinFolding.Square

namespace ProteinFolding.Cubic

def Instance.Accepts (n : ℕ) : Prop := n = 1

end ProteinFolding.Cubic

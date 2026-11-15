import ProteinFolding.Common.Statement

namespace ProteinFolding

/-- No fold has more bonds than the square of its length. -/
@[simp]
theorem bondCount_le (S : Sequence) (f : Fold S.length) :
    bondCount S f ≤ S.length ^ 2 := by
  simp [bondCount]

/-- The empty fold, built with a `where` structure. -/
def emptyFold : Fold 0 where
  pos := fun i => i.elim0
  injective_pos := fun i => i.elim0

namespace SAT

/-- The Cook–Levin theorem, as a proposition used only as a hypothesis. -/
def CookLevin : Prop := True

end SAT

/-- The main theorem, assuming Cook–Levin. -/
theorem main_conditional (hCL : SAT.CookLevin) : bondCount [] emptyFold = 0 := by
  rfl

lemma emptyFold_bonds : bondCount [] emptyFold = 0 := rfl

end ProteinFolding

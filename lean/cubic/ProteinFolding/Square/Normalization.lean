import ProteinFolding.Square.LossRepresentation

/-! Translation invariance removes arbitrary integer coordinates from certificates. -/

namespace ProteinFolding.Square

def shift (a p : Site) : Site := fun k => p k - a k

theorem shift_inj (a : Site) : Function.Injective (shift a) := by
  intro p q h
  funext k
  have hk := congrFun h k
  simp only [shift] at hk
  omega

theorem shift_eq_iff (a p q : Site) : shift a p = shift a q ↔ p = q :=
  ⟨fun h => shift_inj a h, congrArg (shift a)⟩

theorem step_shift (a p : Site) (d : Fin 4) : step (shift a p) d = shift a (step p d) := by
  apply site_ext <;> simp only [step, shift]
  all_goals split_ifs <;> omega

theorem latticeDistance_shift (a p q : Site) : latticeDistance (shift a p) (shift a q) =
    latticeDistance p q := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [shift]
  omega

def shiftFold {S : Sequence} (f : Fold squareLattice S.length) (a : Site) :
    Fold squareLattice S.length where
  pos := shift a ∘ f.pos
  injective_pos := (shift_inj a).comp f.injective_pos
  consecutive := by
    intro i j h
    change latticeDistance (shift a (f.pos i)) (shift a (f.pos j)) = 1
    rw [latticeDistance_shift]
    exact f.consecutive i j h

theorem lossEdges_shift {S : Sequence} (f : Fold squareLattice S.length) (a : Site) :
    lossEdges S (shiftFold f a) = lossEdges S f := by
  ext id
  simp only [mem_lossEdges, shiftFold, Function.comp_apply, step_shift, ne_eq, shift_eq_iff]

theorem lossCount_shift {S : Sequence} (f : Fold squareLattice S.length) (a : Site) :
    lossCount S (shiftFold f a) = lossCount S f := by
  unfold lossCount
  rw [lossEdges_shift]

theorem fold_ext {n : ℕ} {f g : Fold squareLattice n} (h : f.pos = g.pos) : f = g := by
  cases f
  cases g
  cases h
  rfl

end ProteinFolding.Square

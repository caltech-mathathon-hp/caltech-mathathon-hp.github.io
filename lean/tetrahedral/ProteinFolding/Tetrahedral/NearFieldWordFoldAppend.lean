import ProteinFolding.Tetrahedral.FoldAssembly

/-! Position-wise properties and endpoint formulas for literal-word concatenation. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem appendWord_property {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) hdisjoint hseam (P : Site → Prop)
    (hf : ∀ i, P (f.pos i)) (hg : ∀ j, P (g.pos j)) (i : Fin (S ++ T).length) :
    P ((Fold.appendWord f g hdisjoint hseam).pos i) := by
  have hmem := (mem_foldSites (Fold.appendWord f g hdisjoint hseam) _).mpr ⟨i, rfl⟩
  rw [foldSites_appendWord] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hf j
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hg j

theorem appendWord_first {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) hdisjoint hseam (hS : 0 < S.length)
    (p : Site) (hp : ∀ i, i.val = 0 → f.pos i = p)
    (i : Fin (S ++ T).length) (hi : i.val = 0) :
    (Fold.appendWord f g hdisjoint hseam).pos i = p := by
  let j : Fin S.length := ⟨0, hS⟩
  have hij : i = Fold.leftWordIndex S T j := Fin.ext hi
  rw [hij, Fold.appendWord_pos_left]
  exact hp j rfl

theorem appendWord_last {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) hdisjoint hseam (hT : 0 < T.length)
    (p : Site) (hp : ∀ j, j.val + 1 = T.length → g.pos j = p)
    (i : Fin (S ++ T).length) (hi : i.val + 1 = (S ++ T).length) :
    (Fold.appendWord f g hdisjoint hseam).pos i = p := by
  have hil := i.isLt
  simp only [List.length_append] at hi hil
  let j : Fin T.length := ⟨i.val - S.length, by omega⟩
  have hij : i = Fold.rightWordIndex S T j := by
    apply Fin.ext
    dsimp [Fold.rightWordIndex, j]
    omega
  rw [hij, Fold.appendWord_pos_right]
  apply hp j
  dsimp [j]
  omega

end ProteinFolding.Tetrahedral.NearField

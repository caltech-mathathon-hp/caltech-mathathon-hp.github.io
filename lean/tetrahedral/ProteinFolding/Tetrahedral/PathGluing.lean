import ProteinFolding.Tetrahedral.FarFieldPathTools

/-! Exact support and inherited predicates for the explicit shared-endpoint
gluing constructor. No endpoint is counted twice. -/

namespace ProteinFolding.Tetrahedral

theorem glue_exists_pos {n m : ℕ} (f : Fold tetrahedralLattice n)
    (g : Fold tetrahedralLattice m) (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0) (p : Site) :
    (∃ i, (FarField.glue f g hn hm hjoin hinter).pos i = p) ↔
      (∃ i, f.pos i = p) ∨ ∃ j, g.pos j = p := by
  constructor
  · rintro ⟨i, hi⟩
    dsimp only [FarField.glue] at hi
    split_ifs at hi with h
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · refine ⟨⟨i.val, by have h := i.isLt; omega⟩, ?_⟩
      simpa only [FarField.glue, dif_pos i.isLt] using hi
    · by_cases hjzero : j.val = 0
      · refine ⟨⟨n - 1, by omega⟩, ?_⟩
        have hj' : j = ⟨0, hm⟩ := Fin.ext hjzero
        simpa only [FarField.glue, dif_pos (show n - 1 < n by omega)] using hjoin.trans (hj' ▸ hj)
      · refine ⟨⟨n + j.val - 1, by have h := j.isLt; omega⟩, ?_⟩
        change (if h : n + j.val - 1 < n then f.pos _ else g.pos _) = p
        rw [dif_neg (show ¬ n + j.val - 1 < n by omega)]
        have heq : (⟨n + j.val - 1 - n + 1, by have h := j.isLt; omega⟩ : Fin m) = j :=
          Fin.ext (by change n + j.val - 1 - n + 1 = j.val; omega)
        simpa only [heq] using hj

theorem glue_property {n m : ℕ} (f : Fold tetrahedralLattice n)
    (g : Fold tetrahedralLattice m) (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (P : Site → Prop) (hf : ∀ i, P (f.pos i)) (hg : ∀ j, P (g.pos j)) :
    ∀ i, P ((FarField.glue f g hn hm hjoin hinter).pos i) := by
  intro i
  have h := (glue_exists_pos f g hn hm hjoin hinter _).mp ⟨i, rfl⟩
  rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hj ▸ hf j
  · exact hj ▸ hg j

end ProteinFolding.Tetrahedral

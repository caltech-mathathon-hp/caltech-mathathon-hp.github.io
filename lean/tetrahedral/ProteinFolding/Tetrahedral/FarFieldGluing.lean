import ProteinFolding.Tetrahedral.FarFieldPathTools
import ProteinFolding.Common.FoldConcatenation

namespace ProteinFolding.Tetrahedral.FarField

theorem glue_pos_cases {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (i : Fin (n + m - 1)) :
    (∃ a, f.pos a = (glue f g hn hm hjoin hinter).pos i) ∨
      (∃ b, g.pos b = (glue f g hn hm hjoin hinter).pos i) := by
  dsimp only [glue]
  split_ifs with h
  · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
  · exact Or.inr ⟨⟨i.val - n + 1, by have hi := i.isLt; omega⟩, rfl⟩

theorem glue_profile {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (P : Site → Prop) (hf : ∀ i, P (f.pos i)) (hg : ∀ j, P (g.pos j))
    (i : Fin (n + m - 1)) : P ((glue f g hn hm hjoin hinter).pos i) := by
  rcases glue_pos_cases f g hn hm hjoin hinter i with ⟨a, ha⟩ | ⟨b, hb⟩
  · rw [← ha]; exact hf a
  · rw [← hb]; exact hg b

theorem glue_disjoint {n m k : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    (h : Fold tetrahedralLattice k) (hn : 0 < n) (hm : 0 < m)
    (hjoin : f.pos ⟨n - 1, by omega⟩ = g.pos ⟨0, hm⟩)
    (hinter : ∀ i j, f.pos i = g.pos j → i.val + 1 = n ∧ j.val = 0)
    (hf : Disjoint (Set.range f.pos) (Set.range h.pos))
    (hg : Disjoint (Set.range g.pos) (Set.range h.pos)) :
    Disjoint (Set.range (glue f g hn hm hjoin hinter).pos) (Set.range h.pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, rfl⟩ ⟨j, hj⟩
  rcases glue_pos_cases f g hn hm hjoin hinter i with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Set.disjoint_left.mp hf ⟨a, ha⟩ ⟨j, hj⟩
  · exact Set.disjoint_left.mp hg ⟨b, hb⟩ ⟨j, hj⟩

theorem reverse_pos_mem {n : ℕ} (f : Fold tetrahedralLattice n) (i : Fin n) :
    ∃ j, f.pos j = f.reverse.pos i := ⟨i.rev, rfl⟩

theorem reverse_first {n : ℕ} (f : Fold tetrahedralLattice n) (hn : 0 < n)
    (i : Fin n) (hi : i.val = 0) : f.reverse.pos i = f.pos ⟨n - 1, by omega⟩ := by
  change f.pos i.rev = _
  apply congrArg f.pos
  apply Fin.ext
  simp [Fin.val_rev, hi]

theorem reverse_last {n : ℕ} (f : Fold tetrahedralLattice n) (hn : 0 < n)
    (i : Fin n) (hi : i.val + 1 = n) : f.reverse.pos i = f.pos ⟨0, hn⟩ := by
  change f.pos i.rev = _
  apply congrArg f.pos
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

end ProteinFolding.Tetrahedral.FarField

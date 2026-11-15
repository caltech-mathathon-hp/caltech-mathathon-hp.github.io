import ProteinFolding.Tetrahedral.FaceRowsAvoidance
import ProteinFolding.Common.FoldConcatenation

/-! Finite initial segments of the actual dangling columns, including their
exact upper endpoints and skin bounds. -/

namespace ProteinFolding.Tetrahedral.NearField

def columnPrefix {m : ℕ} (C : DanglingColumn m) (n : ℕ) : Fold tetrahedralLattice n where
  pos i := C.point i.val
  injective_pos := by intro i j h; exact Fin.ext (C.point_injective h)
  consecutive i j hij := by rw [← hij]; exact C.point_adj i.val

theorem columnPrefix_on_column {m : ℕ} (C : DanglingColumn m) (n : ℕ) (i : Fin n) :
    OnDanglingColumn m ((columnPrefix C n).pos i) := ⟨C, i.val, rfl⟩

theorem columnPrefix_outside {m : ℕ} (C : DanglingColumn m) (n : ℕ) (i : Fin n) :
    (columnPrefix C n).pos i ∉ octahedron m := C.point_outside i.val

theorem columnPrefix_mem_solid {m : ℕ} (C : DanglingColumn m) (j : ℕ) (hj : 1 ≤ j)
    (i : Fin (2 * j - 1)) : (columnPrefix C (2 * j - 1)).pos i ∈ skinSolid m j := by
  have hrank : i.val / 2 + 1 ≤ j := by have h := i.isLt; omega
  exact skinSolid_mono m hrank (C.point_mem_own_solid i.val)

theorem columnPrefix_first {m : ℕ} (C : DanglingColumn m) (n : ℕ)
    (i : Fin n) (hi : i.val = 0) : (columnPrefix C n).pos i = C.seed := by
  change C.point i.val = C.seed
  rw [hi]
  rfl

theorem columnPrefix_last (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (j : ℕ) (hj : 1 ≤ j) (i : Fin (2 * j - 1)) (hi : i.val + 1 = 2 * j - 1) :
    (columnPrefix (faceDanglingColumn m a b c hs) (2 * j - 1)).pos i =
      faceSubSite m j (a + j) (b + j) (c + 1) (by omega) := by
  change (faceDanglingColumn m a b c hs).point i.val = _
  rw [show i.val = 2 * j - 2 by omega]
  exact faceDanglingColumn_sub_in_skin m a b c hs j hj

theorem columnPrefix_disjoint {m : ℕ} (C D : DanglingColumn m) (hne : C.seed ≠ D.seed)
    (n r : ℕ) (i : Fin n) (j : Fin r) : (columnPrefix C n).pos i ≠ (columnPrefix D r).pos j :=
  DanglingColumn.points_ne_of_seed_ne hne i.val j.val

theorem append_property {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    hdisjoint hseam (P : Site → Prop) (hf : ∀ i, P (f.pos i)) (hg : ∀ j, P (g.pos j))
    (i : Fin (n + m)) : P ((Fold.append f g hdisjoint hseam).pos i) := by
  rcases (Fold.append_exists_pos f g hdisjoint hseam _).mp ⟨i, rfl⟩ with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hj ▸ hf j
  · exact hj ▸ hg j

theorem append_first {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    hdisjoint hseam (hn : 0 < n) (i : Fin (n + m)) (hi : i.val = 0) :
    (Fold.append f g hdisjoint hseam).pos i = f.pos ⟨0, hn⟩ := by
  have heq : i = Fin.castAdd m ⟨0, hn⟩ := Fin.ext hi
  rw [heq, Fold.append_pos_left]

theorem append_last {n m : ℕ} (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice m)
    hdisjoint hseam (hm : 0 < m) (i : Fin (n + m)) (hi : i.val + 1 = n + m) :
    (Fold.append f g hdisjoint hseam).pos i = g.pos ⟨m - 1, Nat.sub_lt hm (by decide)⟩ := by
  have heq : i = Fin.natAdd n ⟨m - 1, Nat.sub_lt hm (by decide)⟩ := Fin.ext (by dsimp; omega)
  rw [heq, Fold.append_pos_right]

end ProteinFolding.Tetrahedral.NearField

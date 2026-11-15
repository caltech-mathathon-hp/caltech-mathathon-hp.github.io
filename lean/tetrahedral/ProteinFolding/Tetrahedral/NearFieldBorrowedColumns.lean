import ProteinFolding.Tetrahedral.FaceRowsColumns

/-! The entry tether's borrowed column: retain the original cap, then use
the column over (a-1,b,c+1) from its second site onward. All sites and bonds
are explicit, and an X-coordinate separation proves self-avoidance. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem faceColumn_seed_x (m a b c : ℕ) (hs : a + b + c + 2 = m) :
    (faceDanglingColumn m a b c hs).seed.val 0 = 2 * (c : ℤ) + 2 := by
  have h := faceDanglingColumn_point_coordinates m a b c hs 0 0
  simpa only [ite_true, Nat.zero_mod, Nat.cast_zero, sub_zero] using h

theorem borrowed_cap_step (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) :
    step (faceDanglingColumn m a b c hs).seed 0 =
      (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point 1 := by
  have hA : InASublattice (faceDanglingColumn m a b c hs).seed.val :=
    step_in_A (faceSurfaceCoordinates_inB m 0 a b c hs) 3
  apply Subtype.ext
  rw [step_val_of_A _ hA]
  funext k
  rw [faceDanglingColumn_point_coordinates, faceDanglingColumn_seed]
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [faceSubSite, faceSubCoordinates, bondComponent] <;> omega

theorem borrowed_cap_not_in_column (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) :
    (faceDanglingColumn m a b c hs).seed ∉
      (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).sites := by
  rintro ⟨n, hn⟩
  have hx := congrArg (fun p : Site => p.val 0) hn
  dsimp only at hx
  rw [faceDanglingColumn_point_coordinates, faceColumn_seed_x] at hx
  omega

def borrowedPoint (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) : ℕ → Site
  | 0 => (faceDanglingColumn m a b c hs).seed
  | n + 1 => (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point (n + 1)

theorem borrowedPoint_adj (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) (n : ℕ) :
    tetrahedralLattice.Adj (borrowedPoint m a b c hs ha n)
      (borrowedPoint m a b c hs ha (n + 1)) := by
  cases n with
  | zero =>
    change tetrahedralLattice.Adj (faceDanglingColumn m a b c hs).seed
      ((faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point 1)
    rw [← borrowed_cap_step m a b c hs ha]
    exact step_adj _ _
  | succ n =>
    exact (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point_adj (n + 1)

theorem borrowedPoint_injective (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) :
    Function.Injective (borrowedPoint m a b c hs ha) := by
  intro n k h
  cases n with
  | zero =>
    cases k with
    | zero => rfl
    | succ k =>
      exact False.elim (borrowed_cap_not_in_column m a b c hs ha ⟨k + 1, h.symm⟩)
  | succ n =>
    cases k with
    | zero =>
      exact False.elim (borrowed_cap_not_in_column m a b c hs ha ⟨n + 1, h⟩)
    | succ k =>
      exact (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point_injective h

def borrowedPrefixFold (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a)
    (n : ℕ) : Fold tetrahedralLattice n where
  pos i := borrowedPoint m a b c hs ha i.val
  injective_pos := by
    intro i k h
    exact Fin.ext (borrowedPoint_injective m a b c hs ha h)
  consecutive i k hik := by
    rw [← hik]
    exact borrowedPoint_adj m a b c hs ha i.val

theorem borrowedPoint_outside (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (n : ℕ) : borrowedPoint m a b c hs ha n ∉ octahedron m := by
  cases n with
  | zero => exact (faceDanglingColumn m a b c hs).seed_outside
  | succ n => exact (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point_outside (n + 1)

end ProteinFolding.Tetrahedral.NearField

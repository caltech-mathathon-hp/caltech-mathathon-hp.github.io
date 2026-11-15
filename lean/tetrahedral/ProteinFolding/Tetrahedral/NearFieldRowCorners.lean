import ProteinFolding.Tetrahedral.FaceRowsSegments
import ProteinFolding.Tetrahedral.PathGluing

/-! Actual two-row corners used by the entry and exit tethers in N4.
Their intersection is proved to be exactly the shared corner, so the glued
paths remain injective. Triangle bounds ensure they stay in the stated skin. -/

namespace ProteinFolding.Tetrahedral.NearField

def rowFold (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (length : ℕ) :
    Fold tetrahedralLattice (2 * length + 1) where
  pos i := faceRowPoint kind m j a b c hs i.val
  injective_pos := by
    intro i k h
    exact Fin.ext (faceRowPoint_injective kind m j a b c hs h)
  consecutive i k hik := by
    rw [← hik]
    exact faceRowPoint_adj kind m j a b c hs i.val

theorem rowCB_intersection (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b)
    (i : Fin (2 * l₁ + 1)) (k : Fin (2 * l₂ + 1))
    (hpos : (rowFold 2 m j a b c hs l₁).pos i =
      (rowFold 1 m j (a + l₁) (b - l₁) c (by omega) l₂).pos k) :
    i.val + 1 = 2 * l₁ + 1 ∧ k.val = 0 := by
  have hx := congrArg (fun p : Site => p.val 0) hpos
  have hy := congrArg (fun p : Site => p.val 1) hpos
  dsimp [rowFold, faceRowPoint, faceRowCoordinates] at hx hy
  omega

theorem rowCB_join (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b) :
    (rowFold 2 m j a b c hs l₁).pos ⟨2 * l₁ + 1 - 1, by omega⟩ =
      (rowFold 1 m j (a + l₁) (b - l₁) c (by omega) l₂).pos ⟨0, by omega⟩ := by
  change faceRowPoint 2 m j a b c hs (2 * l₁ + 1 - 1) = _
  rw [show 2 * l₁ + 1 - 1 = 2 * l₁ by omega, faceRowC_even m j a b c hs l₁ h₁]
  exact (faceRowPoint_zero 1 m j (a + l₁) (b - l₁) c _).symm

def rowCBFold (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b) :
    Fold tetrahedralLattice ((2 * l₁ + 1) + (2 * l₂ + 1) - 1) :=
  FarField.glue (rowFold 2 m j a b c hs l₁)
    (rowFold 1 m j (a + l₁) (b - l₁) c (by omega) l₂)
    (by omega) (by omega) (rowCB_join m j a b c l₁ l₂ hs h₁)
    (rowCB_intersection m j a b c l₁ l₂ hs h₁)

theorem rowCBFold_mem_skin (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b)
    (h₂ : l₂ ≤ a + l₁) (hj : 1 ≤ j) (hc : 1 ≤ c) (hb : 1 ≤ b - l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    (rowCBFold m j a b c l₁ l₂ hs h₁).pos i ∈ skin m j := by
  apply glue_property _ _ _ _ _ _ (fun p => p ∈ skin m j) ?_ ?_ i
  · intro k
    exact faceRowC_mem_skin m j a b c hs hj hc k.val (by have h := k.isLt; omega)
  · intro k
    exact faceRowB_mem_skin m j (a + l₁) (b - l₁) c (by omega) hj hb k.val (by have h := k.isLt; omega)

theorem rowBA_intersection (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a)
    (i : Fin (2 * l₁ + 1)) (k : Fin (2 * l₂ + 1))
    (hpos : (rowFold 1 m j a b c hs l₁).pos i =
      (rowFold 0 m j (a - l₁) b (c + l₁) (by omega) l₂).pos k) :
    i.val + 1 = 2 * l₁ + 1 ∧ k.val = 0 := by
  have hx := congrArg (fun p : Site => p.val 0) hpos
  have hz := congrArg (fun p : Site => p.val 2) hpos
  have hi := i.isLt
  dsimp [rowFold, faceRowPoint, faceRowCoordinates] at hx hz
  omega

theorem rowBA_join (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a) :
    (rowFold 1 m j a b c hs l₁).pos ⟨2 * l₁ + 1 - 1, by omega⟩ =
      (rowFold 0 m j (a - l₁) b (c + l₁) (by omega) l₂).pos ⟨0, by omega⟩ := by
  change faceRowPoint 1 m j a b c hs (2 * l₁ + 1 - 1) = _
  rw [show 2 * l₁ + 1 - 1 = 2 * l₁ by omega, faceRowB_even m j a b c hs l₁ h₁]
  exact (faceRowPoint_zero 0 m j (a - l₁) b (c + l₁) _).symm

def rowBAFold (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a) :
    Fold tetrahedralLattice ((2 * l₁ + 1) + (2 * l₂ + 1) - 1) :=
  FarField.glue (rowFold 1 m j a b c hs l₁)
    (rowFold 0 m j (a - l₁) b (c + l₁) (by omega) l₂)
    (by omega) (by omega) (rowBA_join m j a b c l₁ l₂ hs h₁)
    (rowBA_intersection m j a b c l₁ l₂ hs h₁)

theorem rowBAFold_mem_skin (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a)
    (h₂ : l₂ ≤ c + l₁) (hj : 1 ≤ j) (hb : 1 ≤ b) (ha : 1 ≤ a - l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    (rowBAFold m j a b c l₁ l₂ hs h₁).pos i ∈ skin m j := by
  apply glue_property _ _ _ _ _ _ (fun p => p ∈ skin m j) ?_ ?_ i
  · intro k
    exact faceRowB_mem_skin m j a b c hs hj hb k.val (by have h := k.isLt; omega)
  · intro k
    exact faceRowA_mem_skin m j (a - l₁) b (c + l₁) (by omega) hj ha k.val (by have h := k.isLt; omega)

end ProteinFolding.Tetrahedral.NearField

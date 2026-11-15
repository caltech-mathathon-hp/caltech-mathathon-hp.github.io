import ProteinFolding.Tetrahedral.NearFieldTetherSupport
import ProteinFolding.Tetrahedral.NearFieldFrameCapBounds
import ProteinFolding.Tetrahedral.NearFieldFrameVertexCaps

/-! The actual N4 tethers stay in X>0 and Y>0. This separates them
uniformly from the N1 borrowed linker prefixes and the two free end columns. -/

namespace ProteinFolding.Tetrahedral.NearField

def FacePositive (m : ℕ) (s : Site) : Prop := 1 ≤ s.val 0 ∧ 1 ≤ bulkY m s

theorem faceColumn_positive (m a b c : ℕ) (hs : a + b + c + 2 = m) (n : ℕ) :
    FacePositive m ((faceDanglingColumn m a b c hs).point n) := by
  have hx := faceDanglingColumn_point_coordinates m a b c hs n 0
  have hy := faceDanglingColumn_point_coordinates m a b c hs n 1
  constructor
  · omega
  · change 1 ≤ ((faceDanglingColumn m a b c hs).point n).val 1 - octRadius m
    omega

theorem borrowedPoint_positive (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a) (n : ℕ) :
    FacePositive m (borrowedPoint m a b c hs ha n) := by
  cases n with
  | zero => exact faceColumn_positive m a b c hs 0
  | succ n => exact faceColumn_positive m (a - 1) b (c + 1) (by omega) (n + 1)

theorem rowCBFold_positive (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b) (hc : 1 ≤ c) (hb : 1 ≤ b - l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    FacePositive m ((rowCBFold m j a b c l₁ l₂ hs h₁).pos i) := by
  unfold rowCBFold
  apply glue_property _ _ _ _ _ _ (FacePositive m) ?_ ?_ i
  · intro r
    have hr := r.isLt
    constructor
    · change 1 ≤ 2 * (c : ℤ) + 1 - (r.val % 2 : ℕ)
      omega
    · change 1 ≤ (octRadius m + 2 * (b : ℤ) + 1 - r.val) - octRadius m
      omega
  · intro r
    constructor
    · change 1 ≤ 2 * (c : ℤ) + 1 + r.val
      omega
    · change 1 ≤ (octRadius m + 2 * ((b - l₁ : ℕ) : ℤ) + 1 - (r.val % 2 : ℕ)) - octRadius m
      omega

theorem rowBAFold_positive (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a) (hb : 1 ≤ b) (h₂ : l₂ ≤ c + l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    FacePositive m ((rowBAFold m j a b c l₁ l₂ hs h₁).pos i) := by
  unfold rowBAFold
  apply glue_property _ _ _ _ _ _ (FacePositive m) ?_ ?_ i
  · intro r
    constructor
    · change 1 ≤ 2 * (c : ℤ) + 1 + r.val
      omega
    · change 1 ≤ (octRadius m + 2 * (b : ℤ) + 1 - (r.val % 2 : ℕ)) - octRadius m
      omega
  · intro r
    have hr := r.isLt
    constructor
    · change 1 ≤ 2 * ((c + l₁ : ℕ) : ℤ) + 1 - r.val
      omega
    · change 1 ≤ (octRadius m + 2 * (b : ℤ) + 1 + r.val) - octRadius m
      omega

theorem entryTetherFold_positive (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) : FacePositive p.side ((entryTetherFold p k hk).pos i) := by
  apply entryTetherFold_property p k hk (FacePositive p.side) _ _ _ i
  · intro r
    exact borrowedPoint_positive p.side (entryAnchorA p k) (3 * (k + 1)) 0
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val
  · intro r
    unfold entryRowFold
    exact rowCBFold_positive _ _ _ _ _ _ _ _ _ (by omega)
      (by have h := p.tether_skin_bounds k hk; omega) r
  · intro r
    exact faceColumn_positive p.side (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
      (by have h := p.separator_room k hk; omega) r.rev.val

theorem exitTetherFold_positive (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) : FacePositive p.side ((exitTetherFold p k hk).pos i) := by
  apply exitTetherFold_property p k hk (FacePositive p.side) _ _ _ i
  · intro r
    exact faceColumn_positive p.side (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
      (by have h := p.separator_room k hk; omega) r.val
  · intro r
    unfold exitRowFold
    exact rowBAFold_positive _ _ _ _ _ _ _ _ _
      (by have h := p.tether_skin_bounds k hk; omega)
      (by have h := p.exit_column_triangle_room k; have hr := p.separator_room k hk; omega) r
  · intro r
    exact faceColumn_positive p.side 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
      (by have h := p.exit_column_triangle_room k; omega) r.rev.val

theorem FacePositive.ne_frameBorrowPoint {m : ℕ} {s : Site} (hs : FacePositive m s)
    (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i)
    (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) :
    s ≠ frameBorrowPoint hm i hi hilo hihi mode n := by
  intro heq
  have hx := frameBorrowPoint_negativeX hm i hi hilo hihi mode n
  rw [← heq] at hx
  have h := hs.1
  omega

theorem FacePositive.ne_frameEndpointColumn {m : ℕ} {s : Site} (hs : FacePositive m s)
    (hm : 1 ≤ m) (atStart : Bool) (n : ℕ) : s ≠ (frameEndpointColumn hm atStart).point n := by
  intro heq
  have hy := frameEndpointColumn_negativeY hm atStart n
  rw [← heq] at hy
  have h := hs.2
  omega

end ProteinFolding.Tetrahedral.NearField

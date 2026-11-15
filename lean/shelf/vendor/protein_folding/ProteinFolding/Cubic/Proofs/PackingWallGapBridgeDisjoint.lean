import ProteinFolding.Cubic.Proofs.PackingGapFold
import ProteinFolding.Cubic.Proofs.PackingPrefixWallsDisjoint

/-! The depth-two unit bridges avoid the two depth-two endpoints of every
gap bridge. The remaining gap bridge sites have depth three. -/

namespace ProteinFolding.CubicPackingWalls

open CubicPacking CubicPackingRouting

theorem period_mul_ne_add (period m n : ℕ) (r : ℤ)
    (hr : 0 < r ∧ r < period) :
    (m : ℤ) * period ≠ (n : ℤ) * period + r := by
  by_cases hmn : m ≤ n
  · have hm : (m : ℤ) * period ≤ (n : ℤ) * period := by
      exact_mod_cast Nat.mul_le_mul_right period hmn
    omega
  · have hm : ((n : ℤ) + 1) * period ≤ (m : ℤ) * period := by
      exact_mod_cast Nat.mul_le_mul_right period (show n + 1 ≤ m by omega)
    rw [add_mul, one_mul] at hm
    omega

theorem unitPBridge_avoids_gap_endpoint_rows (d A m n : ℕ)
    (i : Fin (List.replicate (2 * A) Residue.P).length) :
    (unitPBridge d A ((m : ℤ) * (2 * A + 2))).pos i 1 ≠
        (n : ℤ) * (2 * A + 2) - A ∧
      (unitPBridge d A ((m : ℤ) * (2 * A + 2))).pos i 1 ≠
        (n : ℤ) * (2 * A + 2) - A - 1 := by
  have hi := i.isLt
  simp only [List.length_replicate] at hi
  constructor
  · intro he
    change (m : ℤ) * (2 * A + 2) - A - 2 - (i.val : ℤ) =
      (n : ℤ) * (2 * A + 2) - A at he
    apply period_mul_ne_add (2 * A + 2) m n ((i.val : ℤ) + 2) (by omega)
    push_cast
    omega
  · intro he
    change (m : ℤ) * (2 * A + 2) - A - 2 - (i.val : ℤ) =
      (n : ℤ) * (2 * A + 2) - A - 1 at he
    apply period_mul_ne_add (2 * A + 2) m n ((i.val : ℤ) + 1) (by omega)
    push_cast
    omega

/-- All unit bridges are disjoint from all canonical gap bridges. No
ordering or internal-gap bound on the two indices is needed. -/
theorem unitPBridge_gapPBridge_disjoint (q Q : ℕ) (k j : Fin q) :
    ∀ i l, (unitPBridge (depth q Q) (alpha Q) (wallTop q Q k)).pos i ≠
      (gapPBridge (depth q Q) (alpha Q)
        (gapLast (alpha Q) ((alpha Q : ℤ) + 1) j.val)).pos l := by
  intro i l he
  have hk : k.val ≤ q := by omega
  have ht : wallTop q Q k = ((q - k.val : ℕ) : ℤ) * (2 * alpha Q + 2) := by
    have hb : beta Q = 2 * alpha Q + 2 := by dsimp [beta, alpha]; omega
    simp only [wallTop, depth, Nat.cast_mul, Nat.cast_sub hk, hb]
    push_cast
    ring
  have hrows₁ := unitPBridge_avoids_gap_endpoint_rows (depth q Q) (alpha Q)
    (q - k.val) (j.val + 1) i
  have hrows₂ := unitPBridge_avoids_gap_endpoint_rows (depth q Q) (alpha Q)
    (q - k.val) (j.val + 2) i
  rw [←ht] at hrows₁ hrows₂
  have hy := congrFun he 1
  have hz := congrFun he 2
  have hu : (unitPBridge (depth q Q) (alpha Q) (wallTop q Q k)).pos i 2 = -2 := rfl
  dsimp only [gapPBridge, Fold.onLength, bentBridgeFold] at hy hz
  unfold bentBridgePos at hy hz
  split_ifs at hy hz
  · apply hrows₁.1
    dsimp only [point, gapLast] at hy
    push_cast at hy ⊢
    rw [add_mul]
    omega
  · dsimp only [point] at hz
    omega
  · apply hrows₂.2
    dsimp only [point, gapLast] at hy
    push_cast at hy ⊢
    rw [add_mul]
    ring_nf at hy ⊢
    omega

end ProteinFolding.CubicPackingWalls

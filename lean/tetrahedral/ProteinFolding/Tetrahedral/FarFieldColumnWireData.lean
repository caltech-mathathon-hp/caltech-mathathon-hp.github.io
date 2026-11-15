import ProteinFolding.Tetrahedral.FarFieldColumnBridge
import ProteinFolding.Tetrahedral.FarFieldExactLengths

namespace ProteinFolding.Tetrahedral.FarField

theorem column_identities_injective {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) :
    Function.Injective (fun i => armIdentity (octRadius m) (Column.quadrant (C i)) (Column.base (C i))) := by
  intro i j he
  obtain ⟨t, z, ht, hz, heq⟩ := (arm_identity_iff_rays_meet (octRadius m) Column.radius_even
    (Column.quadrant (C i)) (Column.quadrant (C j)) (Column.base (C i)) (Column.base (C j))
    (Column.base_positive (C i)) (Column.base_positive (C j))).1 he
  have hp : (C i).point (1 + t.toNat) = (C j).point (1 + z.toNat) := by
    rw [← Column.arm_eq_point_int (C i) t ht, ← Column.arm_eq_point_int (C j) z hz]
    exact heq
  exact hseed (DanglingColumn.seeds_eq_of_point_eq (C i) (C j) hp)

/-- Concrete far-field input from finitely many distinct canonical dangling
columns. Starting at the second column site handles seeds lying on a bend. -/
def columnsWireData {m w : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) : WireData w where
  R := octRadius m
  R_even := Column.radius_even
  H := 20 * m + 21
  H_odd := by omega
  quadrants := fun i => Column.quadrant (C i)
  bases := fun i => Column.base (C i)
  positive := fun i => Column.base_positive (C i)
  below := by intro i; have h := Column.base_rho_bound (C i); omega
  high := by intro i; have h := Column.base_alpha_bound (C i); omega
  x_below := by
    intro i
    have h := Column.base_x_bounds (C i)
    change quadrantArmBaseX (Column.quadrant (C i)) (Column.base (C i)) + 1 < 20 * (m : ℤ) + 21
    omega
  identities := column_identities_injective C hseed

namespace columnsWireData

variable {m w : ℕ} (C : Fin w → DanglingColumn m) (hseed : Function.Injective (fun i => (C i).seed))

theorem x_lower (i : Fin w) :
    -(columnsWireData C hseed).H ≤ wireBaseXs (columnsWireData C hseed).quadrants (columnsWireData C hseed).bases i := by
  have h := Column.base_x_bounds (C i)
  change -(20 * (m : ℤ) + 21) ≤ quadrantArmBaseX (Column.quadrant (C i)) (Column.base (C i))
  omega

theorem armCap_eq (i : Fin w) : (columnsWireData C hseed).armCaps i = (C i).point 1 := by
  simp only [WireData.armCaps, columnsWireData, Column.base, quadrantMap_unmap]

theorem column_pos_eq (i : Fin w)
    (a : Fin (columnHeight (columnsWireData C hseed).R (columnsWireData C hseed).H
      (columnsWireData C hseed).quadrants (columnsWireData C hseed).bases i + 1)) :
    ((columnsWireData C hseed).columns i).pos a = (C i).point (1 + a.val) := by
  change quadrantArm (octRadius m) Column.radius_even (Column.quadrant (C i)) (Column.base (C i)) (0 + a.val) = _
  simp only [zero_add]
  exact Column.arm_eq_point (C i) a.val

end columnsWireData

end ProteinFolding.Tetrahedral.FarField

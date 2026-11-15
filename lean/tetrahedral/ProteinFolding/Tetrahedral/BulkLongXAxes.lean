import ProteinFolding.Tetrahedral.BulkFarXAlpha
import ProteinFolding.Tetrahedral.BulkLineCoordinates

/-! Far X-edge joint boxes stay away from both bend axes. An adjacent site
therefore remains in the same transverse quadrant. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192

set_option maxHeartbeats 4000000 in
theorem bulkFarXEdgeAnchor_axes_lower (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (hm : 1 ≤ m) (hX : BulkXEdgeFrame F) (ht : 10 ≤ t) (htm : t + 11 ≤ m) :
    20 ≤ |bulkY m (bulkEdgeAnchor m F t)| ∧ 19 ≤ |bulkZ (bulkEdgeAnchor m F t)| := by
  unfold bulkY bulkZ
  rw [bulkEdgeAnchor_closedCoordinates hm F t]
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  fin_cases k <;> fin_cases j <;> fin_cases a <;> fin_cases b
  all_goals simp_all [BulkXEdgeFrame, bulkEdgeClosedCoordinates, bulkEdgeFaceValue, octRadius]
  all_goals simp only [bulk_int_abs_ite]
  all_goals split_ifs <;> constructor <;> omega

theorem int_abs_lower_of_box (a b B D : ℤ) (ha : B ≤ |a|) (hab : |b - a| ≤ D) :
    B - D ≤ |b| := by
  have hd := abs_le.mp hab
  have hbpos := le_abs_self b
  have hbneg := neg_le_abs b
  have haUpper : |a| ≤ |b| + D := by
    rw [abs_le]
    constructor <;> omega
  omega

theorem bulkFarXEdgeBox_axes_lower (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (p : Site)
    (hm : 1 ≤ m) (hX : BulkXEdgeFrame F) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hp : InBulkEdgeBox m F t 3 p) : 17 ≤ |bulkY m p| ∧ 16 ≤ |bulkZ p| := by
  have hanchor := bulkFarXEdgeAnchor_axes_lower m F t hm hX ht htm
  have hyEq : bulkY m p - bulkY m (bulkEdgeAnchor m F t) =
      p.val 1 - (bulkEdgeAnchor m F t).val 1 := by dsimp only [bulkY]; omega
  have hzEq : bulkZ p - bulkZ (bulkEdgeAnchor m F t) =
      p.val 2 - (bulkEdgeAnchor m F t).val 2 := by dsimp only [bulkZ]; omega
  have hy : |bulkY m p - bulkY m (bulkEdgeAnchor m F t)| ≤ 3 := by
    rw [hyEq]
    exact hp 1
  have hz : |bulkZ p - bulkZ (bulkEdgeAnchor m F t)| ≤ 3 := by
    rw [hzEq]
    exact hp 2
  exact ⟨int_abs_lower_of_box _ _ 20 3 hanchor.1 hy,
    int_abs_lower_of_box _ _ 19 3 hanchor.2 hz⟩

theorem bulkFarXEdgeBox_axes_separated (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (p : Site)
    (hm : 1 ≤ m) (hX : BulkXEdgeFrame F) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hp : InBulkEdgeBox m F t 3 p) : 2 ≤ |bulkY m p| ∧ 2 ≤ |bulkZ p| := by
  have h := bulkFarXEdgeBox_axes_lower m F t p hm hX ht htm hp
  constructor <;> omega

theorem int_unit_sign_eq_of_far_step (a b : ℤ) (ha : 2 ≤ |a|)
    (hd : b = a + 1 ∨ b = a - 1) :
    (if 0 ≤ b then (1 : ℤ) else -1) = if 0 ≤ a then 1 else -1 := by
  by_cases ha0 : 0 ≤ a
  · have ha2 : 2 ≤ a := by simpa only [abs_of_nonneg ha0] using ha
    have hb0 : 0 ≤ b := by rcases hd with h | h <;> omega
    simp only [if_pos ha0, if_pos hb0]
  · have ha2 : a ≤ -2 := by
      have h := ha
      rw [abs_of_neg (by omega : a < 0)] at h
      omega
    have hb0 : ¬0 ≤ b := by rcases hd with h | h <;> omega
    simp only [if_neg ha0, if_neg hb0]

theorem bulk_axes_separated_adj_signs (m : ℕ) (p q : Site)
    (haxes : 2 ≤ |bulkY m p| ∧ 2 ≤ |bulkZ p|) (hadj : tetrahedralLattice.Adj p q) :
    bulkYSign m q = bulkYSign m p ∧ bulkZSign q = bulkZSign p := by
  have hd := bulk_adj_deltas m hadj
  have hy : bulkY m q = bulkY m p + 1 ∨ bulkY m q = bulkY m p - 1 := by omega
  have hz : bulkZ q = bulkZ p + 1 ∨ bulkZ q = bulkZ p - 1 := by omega
  exact ⟨int_unit_sign_eq_of_far_step _ _ haxes.1 hy,
    int_unit_sign_eq_of_far_step _ _ haxes.2 hz⟩

theorem bulkFarXEdgeBox_adj_signs (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (p q : Site)
    (hm : 1 ≤ m) (hX : BulkXEdgeFrame F) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hp : InBulkEdgeBox m F t 3 p) (hadj : tetrahedralLattice.Adj p q) :
    bulkYSign m q = bulkYSign m p ∧ bulkZSign q = bulkZSign p :=
  bulk_axes_separated_adj_signs m p q
    (bulkFarXEdgeBox_axes_separated m F t p hm hX ht htm hp) hadj

end ProteinFolding.Tetrahedral

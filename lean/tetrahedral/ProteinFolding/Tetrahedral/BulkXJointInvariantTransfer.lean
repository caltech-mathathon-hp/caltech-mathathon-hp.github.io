import ProteinFolding.Tetrahedral.BulkXJointInvariantReference

/-! The raw X-joint invariants are preserved by arbitrary far-edge
translation; neither alpha sign nor construction-size parity is assumed. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkUnitSign_eq_of_bulkSign_eq (x y : ℤ) (h : bulkSign x = bulkSign y) :
    (if 0 ≤ x then (1 : ℤ) else -1) = if 0 ≤ y then 1 else -1 := by
  unfold bulkSign at h
  split_ifs at * <;> omega

theorem bulkEdgeReanchor_unitSigns (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkYSign M (bulkEdgeReanchor m M t T F p) = bulkYSign m p ∧
      bulkZSign (bulkEdgeReanchor m M t T F p) = bulkZSign p := by
  have hs := bulkEdgeReanchor_signs m M t T F D p ht htm hT hTM hp
  exact ⟨bulkUnitSign_eq_of_bulkSign_eq _ _ hs.1, bulkUnitSign_eq_of_bulkSign_eq _ _ hs.2⟩

theorem bulkEdgeReanchor_charge (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) :
    siteCharge (bulkEdgeReanchor m M t T F p) = siteCharge p := by
  unfold siteCharge
  simp only [bulkEdgeReanchor_inA_iff]

theorem bulkXEdgeReanchor_x (m M t T : ℕ) (F : OctEdgeFrame) (p : Site)
    (hm : 1 ≤ m) (hM : 1 ≤ M) (hX : BulkXEdgeFrame F) :
    (bulkEdgeReanchor m M t T F p).val 0 = p.val 0 := by
  rw [bulkEdgeReanchor_coordinates, bulkEdgeAnchor_x_of_X hm F t hX,
    bulkEdgeAnchor_x_of_X hM F T hX]
  omega

theorem bulkXJoint_invariants_edge_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p q : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hX : BulkXEdgeFrame F) (hp : InBulkEdgeBox m F t D p) (hq : InBulkEdgeBox m F t D q) :
    (BulkXPositiveJointInvariant M (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) ↔
      BulkXPositiveJointInvariant m p q) ∧
    (BulkXNegativeJointInvariant M (bulkEdgeReanchor m M t T F p) ↔ BulkXNegativeJointInvariant m p) := by
  have hs := bulkEdgeReanchor_unitSigns m M t T F D p ht htm hT hTM hp
  have hx := bulkXEdgeReanchor_x m M t T F p (by omega) (by omega) hX
  have hc := bulkEdgeReanchor_charge m M t T F p
  have hpα := (bulkEdgeReanchor_relative_rho_alpha m M t T F D p ht htm hT hTM hp).2
  have hqα := (bulkEdgeReanchor_relative_rho_alpha m M t T F D q ht htm hT hTM hq).2
  have hdiff : bulkAlpha M (bulkEdgeReanchor m M t T F q) - bulkAlpha M (bulkEdgeReanchor m M t T F p) =
      bulkAlpha m q - bulkAlpha m p := by omega
  unfold BulkXPositiveJointInvariant BulkXNegativeJointInvariant bulkXPositiveBend bulkXNegativeBend
  rw [hx, hc, hs.1, hs.2, hdiff]
  exact ⟨Iff.rfl, Iff.rfl⟩

end ProteinFolding.Tetrahedral

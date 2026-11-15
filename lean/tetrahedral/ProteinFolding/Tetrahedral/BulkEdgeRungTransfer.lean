import ProteinFolding.Tetrahedral.BulkEdgeSigns

/-! Primitive foliation and rule data commute with far-edge translation. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeBox_mono (m : ℕ) (F : OctEdgeFrame) (t : ℕ) {D E : ℕ}
    (hDE : D ≤ E) {p : Site} (hp : InBulkEdgeBox m F t D p) : InBulkEdgeBox m F t E p := by
  intro k
  have h := hp k
  omega

theorem bulkEdgeReanchor_relative_rho_alpha (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkRho M (bulkEdgeReanchor m M t T F p) - bulkRho M (bulkEdgeAnchor M F T) =
      bulkRho m p - bulkRho m (bulkEdgeAnchor m F t) ∧
    bulkAlpha M (bulkEdgeReanchor m M t T F p) - bulkAlpha M (bulkEdgeAnchor M F T) =
      bulkAlpha m p - bulkAlpha m (bulkEdgeAnchor m F t) := by
  have h := bulkEdgeReanchor_axis_data m M t T F D p ht htm hT hTM hp
  unfold bulkRho bulkAlpha
  constructor <;> omega

theorem bulkEdgeReanchor_signs (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkSign (bulkY M (bulkEdgeReanchor m M t T F p)) = bulkSign (bulkY m p) ∧
      bulkSign (bulkZ (bulkEdgeReanchor m M t T F p)) = bulkSign (bulkZ p) := by
  have h := bulkEdgeReanchor_axis_data m M t T F D p ht htm hT hTM hp
  exact ⟨h.1.1, h.2.1⟩

theorem bulkEdgeReanchor_zeros (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkY M (bulkEdgeReanchor m M t T F p) = 0 ↔ bulkY m p = 0) ∧
      (bulkZ (bulkEdgeReanchor m M t T F p) = 0 ↔ bulkZ p = 0) := by
  have h := bulkEdgeReanchor_signs m M t T F D p ht htm hT hTM hp
  constructor
  · rw [← bulkSign_eq_zero_iff, h.1, bulkSign_eq_zero_iff]
  · rw [← bulkSign_eq_zero_iff, h.2, bulkSign_eq_zero_iff]

theorem bulkEdgeReanchor_yz_differences (m M t T : ℕ) (F : OctEdgeFrame) (p q : Site) :
    bulkY M (bulkEdgeReanchor m M t T F q) - bulkY M (bulkEdgeReanchor m M t T F p) =
      bulkY m q - bulkY m p ∧
    bulkZ (bulkEdgeReanchor m M t T F q) - bulkZ (bulkEdgeReanchor m M t T F p) = bulkZ q - bulkZ p := by
  have hp1 := bulkEdgeReanchor_coordinates m M t T F p 1
  have hq1 := bulkEdgeReanchor_coordinates m M t T F q 1
  have hp2 := bulkEdgeReanchor_coordinates m M t T F p 2
  have hq2 := bulkEdgeReanchor_coordinates m M t T F q 2
  unfold bulkY bulkZ
  constructor <;> omega

theorem bulkEdgeReanchor_rule_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p q : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkRuleNeighbour M (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) ↔
      bulkRuleNeighbour m p q := by
  have hsign := bulkEdgeReanchor_signs m M t T F D p ht htm hT hTM hp
  have hzero := bulkEdgeReanchor_zeros m M t T F D p ht htm hT hTM hp
  have hdiff := bulkEdgeReanchor_yz_differences m M t T F p q
  unfold bulkRuleNeighbour
  rw [bulkEdgeReanchor_adj_iff, hsign.1, hsign.2, hdiff.1, hdiff.2]
  simp only [ne_eq, hzero.1, hzero.2]

theorem bulkEdgeReanchor_rung_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p q : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (hq : InBulkEdgeBox m F t D q) :
    (bulkRungGraph M).Adj (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) ↔
      (bulkRungGraph m).Adj p q := by
  have hpρ := (bulkEdgeReanchor_relative_rho_alpha m M t T F D p ht htm hT hTM hp).1
  have hqρ := (bulkEdgeReanchor_relative_rho_alpha m M t T F D q ht htm hT hTM hq).1
  change (_ ∧ _ ≠ _) ↔ (_ ∧ _ ≠ _)
  rw [bulkEdgeReanchor_adj_iff]
  exact and_congr_right (fun _ => by omega)

end ProteinFolding.Tetrahedral

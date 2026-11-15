import ProteinFolding.Tetrahedral.BulkXPositiveEscape
import ProteinFolding.Tetrahedral.BulkJointBendChanges
import ProteinFolding.Tetrahedral.BulkLongXRow

/-! Negative-alpha X segments have equal endpoint charges; their
opposite transverse signs force a strictly increasing bend-X joint. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkXNegative_endpoint_charges (m : ℕ) (p q : BulkVertex m)
    (hline : (bulkSegmentGraph m).Reachable p q) (hα : bulkAlpha m p.val < 0)
    (hop : bulkYSign m q.val = -bulkYSign m p.val)
    (hp : BulkXNegativeJointInvariant m p.val) (hq : BulkXNegativeJointInvariant m q.val) :
    siteCharge q.val = siteCharge p.val ∧ |bulkXNegativeBend m p.val| ≤ 2 := by
  have hαq := bulkSegment_alpha m hline
  have hαqNeg : bulkAlpha m q.val < 0 := by omega
  have hZ : bulkZSign q.val = bulkZSign p.val := by
    obtain ⟨w⟩ := bulkSegment_reachable_rung m hline
    exact bulkZSign_eq_of_rungWalk_negative m w hα
  have hb : bulkXNegativeBend m q.val = bulkXNegativeBend m p.val := by
    rw [bulkXNegativeBend_eq_bend m q.val hαqNeg, bulkXNegativeBend_eq_bend m p.val hα]
    exact congrArg (fun b : Site => b.val 0)
      (bulkBendPoint_eq_of_rungReachable m (bulkSegment_reachable_rung m hline)).symm
  unfold BulkXNegativeJointInvariant at hp hq
  rcases hp with hp | hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq | hq
  all_goals rcases bulkYSign_unit m p.val with hy | hy
  all_goals rw [abs_le]
  all_goals constructor
  all_goals omega

theorem bulkNegative_joint_bend_step (m : ℕ) (p q : Site)
    (hmerge : bulkMerge m p q ∨ bulkMerge m q p)
    (hp : bulkAlpha m p < 0) (hq : bulkAlpha m q < 0)
    (hpz : bulkZ p ≠ 0) (hqz : bulkZ q ≠ 0)
    (hY : bulkYSign m q = bulkYSign m p) (hZ : bulkZSign q = bulkZSign p) :
    (bulkBendPoint m q).val 0 - (bulkBendPoint m p).val 0 =
      (4 * siteCharge p - 2) * (bulkYSign m p * bulkZSign p) := by
  rcases hmerge with hm | hm
  · have hx := bulkRuleNeighbour_bendX_negative m hm.2.1.2.1 hpz hp hq hY hZ
    rcases p.property with hpA | hpB
    · rw [if_pos hpA] at hx
      simpa only [siteCharge_A hpA, mul_zero, zero_sub] using hx
    · rw [if_neg ((inB_iff_not_inA p).mp hpB)] at hx
      simpa only [siteCharge_B hpB, mul_one, show (4 : ℤ) - 2 = 2 by decide] using hx
  · have hx := bulkRuleNeighbour_bendX_negative m hm.2.1.2.1 hqz hq hp hY.symm hZ.symm
    rw [hY, hZ] at hx
    rcases adj_sublattices (bulkMerge_adj m hm).symm with ⟨hpA, hqB⟩ | ⟨hpB, hqA⟩
    · rw [if_neg ((inB_iff_not_inA q).mp hqB)] at hx
      simp only [siteCharge_A hpA, mul_zero, zero_sub]
      omega
    · rw [if_pos hqA] at hx
      simp only [siteCharge_B hpB, mul_one, show (4 : ℤ) - 2 = 2 by decide]
      omega

theorem bulkXNegative_bend_up_at_one_end (m : ℕ) (p q r s : BulkVertex m)
    (hop : bulkYSign m q.val = -bulkYSign m p.val)
    (hZ : bulkZSign q.val = bulkZSign p.val) (hc : siteCharge q.val = siteCharge p.val)
    (hp : (bulkBendPoint m r.val).val 0 - (bulkBendPoint m p.val).val 0 =
      (4 * siteCharge p.val - 2) * (bulkYSign m p.val * bulkZSign p.val))
    (hq : (bulkBendPoint m s.val).val 0 - (bulkBendPoint m q.val).val 0 =
      (4 * siteCharge q.val - 2) * (bulkYSign m q.val * bulkZSign q.val)) :
    (bulkBendPoint m p.val).val 0 < (bulkBendPoint m r.val).val 0 ∨
      (bulkBendPoint m q.val).val 0 < (bulkBendPoint m s.val).val 0 := by
  have hdiff : (bulkBendPoint m s.val).val 0 - (bulkBendPoint m q.val).val 0 =
      -((bulkBendPoint m r.val).val 0 - (bulkBendPoint m p.val).val 0) := by
    rw [hp, hq, hc, hop, hZ]
    ring
  have hne : (bulkBendPoint m r.val).val 0 - (bulkBendPoint m p.val).val 0 ≠ 0 := by
    rw [hp]
    rcases p.val.property with hpA | hpB
    · rw [siteCharge_A hpA]
      rcases bulkYSign_unit m p.val with hy | hy <;> rcases bulkZSign_unit p.val with hz | hz
      all_goals rw [hy, hz]
      all_goals norm_num
    · rw [siteCharge_B hpB]
      rcases bulkYSign_unit m p.val with hy | hy <;> rcases bulkZSign_unit p.val with hz | hz
      all_goals rw [hy, hz]
      all_goals norm_num
  omega

theorem bulkSegmentPotential_negative_to_positive (m : ℕ) (p q : BulkVertex m)
    (hp : bulkAlpha m p.val < 0) (hq : 0 < bulkAlpha m q.val) :
    bulkSegmentPotential m p < bulkSegmentPotential m q := by
  classical
  have hnr : ¬BulkRowSegment m p := by
    intro hrow
    have h := bulkRowSegment_alpha_positive m p hrow
    omega
  have hnot : ¬0 < bulkAlpha m p.val := by omega
  unfold bulkSegmentPotential
  simp only [if_neg hnr, if_neg hnot]
  by_cases hrow : BulkRowSegment m q
  · simp only [if_pos hrow]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (0 : ℕ) < 2 by decide))
  · simp only [if_neg hrow, if_pos hq]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (0 : ℕ) < 1 by decide))

end ProteinFolding.Tetrahedral

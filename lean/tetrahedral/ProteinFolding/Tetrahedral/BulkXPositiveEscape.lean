import ProteinFolding.Tetrahedral.BulkXJointInvariants
import ProteinFolding.Tetrahedral.BulkLineInjectivity
import ProteinFolding.Tetrahedral.BulkPotentialComparisons

/-! Opposite arms of a positive-alpha X segment give opposite alpha
changes at their joints. One neighbour therefore has strictly larger potential. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkZSign_opposite_of_coordinates (p q : Site)
    (h : (bulkZ p < 0 ∧ 0 < bulkZ q) ∨ (0 < bulkZ p ∧ bulkZ q < 0)) :
    bulkZSign q = -bulkZSign p := by
  rcases h with h | h
  all_goals unfold bulkZSign
  all_goals split_ifs <;> omega

theorem bulkYSign_opposite_of_coordinates (m : ℕ) (p q : Site)
    (h : (bulkY m p < 0 ∧ 0 < bulkY m q) ∨ (0 < bulkY m p ∧ bulkY m q < 0)) :
    bulkYSign m q = -bulkYSign m p := by
  rcases h with h | h
  all_goals unfold bulkYSign
  all_goals split_ifs <;> omega

theorem bulkXPositive_alpha_up_at_one_end (m : ℕ) (p q r s : BulkVertex m)
    (hline : (bulkSegmentGraph m).Reachable p q) (hα : 0 < bulkAlpha m p.val)
    (hop : bulkZSign q.val = -bulkZSign p.val)
    (hp : BulkXPositiveJointInvariant m p.val r.val) (hq : BulkXPositiveJointInvariant m q.val s.val) :
    bulkAlpha m p.val < bulkAlpha m r.val ∨ bulkAlpha m q.val < bulkAlpha m s.val := by
  have hαq := bulkSegment_alpha m hline
  have hαqPos : 0 < bulkAlpha m q.val := by omega
  have hY : bulkYSign m q.val = bulkYSign m p.val := by
    obtain ⟨w⟩ := bulkSegment_reachable_rung m hline
    exact bulkYSign_eq_of_rungWalk_positive m w hα
  have hb : bulkXPositiveBend m q.val = bulkXPositiveBend m p.val := by
    rw [bulkXPositiveBend_eq_bend m q.val hαqPos, bulkXPositiveBend_eq_bend m p.val hα]
    exact congrArg (fun b : Site => b.val 0)
      (bulkBendPoint_eq_of_rungReachable m (bulkSegment_reachable_rung m hline)).symm
  have hdiff : bulkAlpha m s.val - bulkAlpha m q.val = -(bulkAlpha m r.val - bulkAlpha m p.val) := by
    rw [hp.2, hq.2, hb, hY, hop]
    ring
  have hne : bulkAlpha m r.val - bulkAlpha m p.val ≠ 0 := by
    rw [hp.2]
    rcases bulkYSign_unit m p.val with hy | hy <;> rcases bulkZSign_unit p.val with hz | hz
    all_goals rw [hy, hz]
    all_goals split_ifs <;> norm_num
  omega

theorem bulkXPositive_escape_at_one_end (m : ℕ) (p q r s : BulkVertex m)
    (hline : (bulkSegmentGraph m).Reachable p q) (hα : 0 < bulkAlpha m p.val)
    (hnr : ¬BulkRowSegment m p) (hop : bulkZSign q.val = -bulkZSign p.val)
    (hp : BulkXPositiveJointInvariant m p.val r.val) (hq : BulkXPositiveJointInvariant m q.val s.val)
    (hpr : (bulkFiniteGraph m).Adj p r) (hqs : (bulkFiniteGraph m).Adj q s) :
    ∃ v : BulkVertex m, (bulkFiniteGraph m).Reachable p v ∧
      bulkSegmentPotential m p < bulkSegmentPotential m v := by
  rcases bulkXPositive_alpha_up_at_one_end m p q r s hline hα hop hp hq with hup | hup
  · exact ⟨r, hpr.reachable, bulkSegmentPotential_lt_of_alpha_up m p r hnr hα hup⟩
  · have hαq := bulkSegment_alpha m hline
    have hreach : (bulkFiniteGraph m).Reachable p q := by
      obtain ⟨w⟩ := hline
      let f : bulkSegmentGraph m →g bulkFiniteGraph m := ⟨id, by intro a b h; exact h.1⟩
      exact ⟨w.map f⟩
    exact ⟨s, hreach.trans hqs.reachable,
      bulkSegmentPotential_lt_of_alpha_up m p s hnr hα (by omega)⟩

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkXNegativeComparison
import ProteinFolding.Tetrahedral.BulkNegativeComponent

/-! The negative X case also permits a neighbouring component to reach
a leaf. Otherwise exact bend values give a strict potential increase. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulk_adj_Z_ne_zero_of_separated (m : ℕ) (p q : Site) (h : tetrahedralLattice.Adj p q)
    (hp : 2 ≤ |bulkZ p|) : bulkZ q ≠ 0 := by
  intro hq
  have hd := bulk_adj_deltas m h
  have hsmall : |bulkZ p| ≤ 1 := by
    rw [abs_le]
    constructor <;> omega
  omega

theorem bulkXNegative_escape_at_one_end (m : ℕ) (p q r s : BulkVertex m)
    (hline : (bulkSegmentGraph m).Reachable p q) (hα : bulkAlpha m p.val < 0)
    (hop : bulkYSign m q.val = -bulkYSign m p.val)
    (hpInv : BulkXNegativeJointInvariant m p.val) (hqInv : BulkXNegativeJointInvariant m q.val)
    (hpZ : 2 ≤ |bulkZ p.val|) (hqZ : 2 ≤ |bulkZ q.val|)
    (hpr : (bulkFiniteGraph m).Adj p r) (hqs : (bulkFiniteGraph m).Adj q s)
    (hpMerge : bulkMerge m p.val r.val ∨ bulkMerge m r.val p.val)
    (hqMerge : bulkMerge m q.val s.val ∨ bulkMerge m s.val q.val)
    (hpSigns : bulkYSign m r.val = bulkYSign m p.val ∧ bulkZSign r.val = bulkZSign p.val)
    (hqSigns : bulkYSign m s.val = bulkYSign m q.val ∧ bulkZSign s.val = bulkZSign q.val)
    (hpHat : bulkSegmentXhat m p = 2 * (bulkBendPoint m p.val).val 0)
    (hr : 0 < bulkAlpha m r.val ∨
      (∃ v : BulkVertex m, (bulkFiniteGraph m).Reachable r v ∧ (bulkFiniteGraph m).degree v ≤ 1) ∨
      (bulkAlpha m r.val < 0 ∧ bulkSegmentXhat m r = 2 * (bulkBendPoint m r.val).val 0))
    (hs : 0 < bulkAlpha m s.val ∨
      (∃ v : BulkVertex m, (bulkFiniteGraph m).Reachable s v ∧ (bulkFiniteGraph m).degree v ≤ 1) ∨
      (bulkAlpha m s.val < 0 ∧ bulkSegmentXhat m s = 2 * (bulkBendPoint m s.val).val 0)) :
    ∃ v : BulkVertex m, (bulkFiniteGraph m).Reachable p v ∧
      ((bulkFiniteGraph m).degree v ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m v) := by
  have hreach : (bulkFiniteGraph m).Reachable p q := by
    obtain ⟨w⟩ := hline
    let f : bulkSegmentGraph m →g bulkFiniteGraph m := ⟨id, by intro a b h; exact h.1⟩
    exact ⟨w.map f⟩
  rcases hr with hrPos | ⟨v, hrv, hv⟩ | ⟨hrNeg, hrHat⟩
  · exact ⟨r, hpr.reachable, Or.inr (bulkSegmentPotential_negative_to_positive m p r hα hrPos)⟩
  · exact ⟨v, hpr.reachable.trans hrv, Or.inl hv⟩
  rcases hs with hsPos | ⟨v, hsv, hv⟩ | ⟨hsNeg, hsHat⟩
  · exact ⟨s, hreach.trans hqs.reachable, Or.inr (bulkSegmentPotential_negative_to_positive m p s hα hsPos)⟩
  · exact ⟨v, hreach.trans (hqs.reachable.trans hsv), Or.inl hv⟩
  have hαq := bulkSegment_alpha m hline
  have hqNeg : bulkAlpha m q.val < 0 := by omega
  have hpz : bulkZ p.val ≠ 0 := by intro hz; rw [hz, abs_zero] at hpZ; omega
  have hqz : bulkZ q.val ≠ 0 := by intro hz; rw [hz, abs_zero] at hqZ; omega
  have hrz := bulk_adj_Z_ne_zero_of_separated m p.val r.val (bulkCoverBond_adj m hpr) hpZ
  have hsz := bulk_adj_Z_ne_zero_of_separated m q.val s.val (bulkCoverBond_adj m hqs) hqZ
  have hpStep := bulkNegative_joint_bend_step m p.val r.val hpMerge hα hrNeg hpz hrz hpSigns.1 hpSigns.2
  have hqStep := bulkNegative_joint_bend_step m q.val s.val hqMerge hqNeg hsNeg hqz hsz hqSigns.1 hqSigns.2
  have hZ : bulkZSign q.val = bulkZSign p.val := by
    obtain ⟨w⟩ := bulkSegment_reachable_rung m hline
    exact bulkZSign_eq_of_rungWalk_negative m w hα
  have hc := (bulkXNegative_endpoint_charges m p q hline hα hop hpInv hqInv).1
  have hup := bulkXNegative_bend_up_at_one_end m p q r s hop hZ hc hpStep hqStep
  have hnr : ¬BulkRowSegment m p := by
    intro hrow
    have hpos := bulkRowSegment_alpha_positive m p hrow
    omega
  rcases hup with hup | hup
  · have hX : bulkSegmentXhat m p < bulkSegmentXhat m r := by rw [hpHat, hrHat]; omega
    exact ⟨r, hpr.reachable, Or.inr (bulkSegmentPotential_lt_of_negative_x_up m p r hnr hα hX)⟩
  · have hB : (bulkBendPoint m p.val).val 0 = (bulkBendPoint m q.val).val 0 := congrArg (fun b : Site => b.val 0)
      (bulkBendPoint_eq_of_rungReachable m (bulkSegment_reachable_rung m hline))
    have hX : bulkSegmentXhat m p < bulkSegmentXhat m s := by rw [hpHat, hsHat, hB]; omega
    exact ⟨s, hreach.trans hqs.reachable, Or.inr (bulkSegmentPotential_lt_of_negative_x_up m p s hnr hα hX)⟩

theorem bulkNegative_neighbour_shape (m : ℕ) (hm : 50 ≤ m) (p r : BulkVertex m)
    (hx : |p.val.val 0| ≤ 3) (hbound : |bulkAlpha m p.val| ≤ octRadius m - 37)
    (hpr : (bulkFiniteGraph m).Adj p r) :
    0 < bulkAlpha m r.val ∨
      (∃ v : BulkVertex m, (bulkFiniteGraph m).Reachable r v ∧ (bulkFiniteGraph m).degree v ≤ 1) ∨
      (bulkAlpha m r.val < 0 ∧ bulkSegmentXhat m r = 2 * (bulkBendPoint m r.val).val 0) := by
  rcases bulkAlpha_signed m r.val with hrNeg | hrPos
  · have hx' := abs_le.mp hx
    have hstep := adj_coordinate (bulkCoverBond_adj m hpr) 0
    change r.val.val 0 = p.val.val 0 + 1 ∨ r.val.val 0 = p.val.val 0 - 1 at hstep
    have hrX : |r.val.val 0| ≤ 4 := by rw [abs_le]; constructor <;> omega
    have hrBound := (bulk_adj_alpha_abs_bound m (bulkCoverBond_adj m hpr)).trans (show
      |bulkAlpha m p.val| + 2 ≤ octRadius m - 35 by omega)
    rcases bulkNegative_component_leaf_or_bend m hm r hrX hrNeg hrBound with hleaf | hhat
    · exact Or.inr (Or.inl hleaf)
    · exact Or.inr (Or.inr ⟨hrNeg, hhat⟩)
  · exact Or.inl hrPos

end ProteinFolding.Tetrahedral

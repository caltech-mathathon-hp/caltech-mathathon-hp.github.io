import ProteinFolding.Tetrahedral.BulkSegments

/-! A rung line has one bend and its X coordinates differ by at most two.
This gives the uniform slab bounds of far class-X segments. -/

namespace ProteinFolding.Tetrahedral

theorem bulkBendPoint_eq_of_rungReachable (m : ℕ) {p q : Site}
    (h : (bulkRungGraph m).Reachable p q) : bulkBendPoint m p = bulkBendPoint m q :=
  bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p) (bulkBendPoint_is_bend m q)
    ((bulkBendPoint_reachable m p).symm.trans (h.trans (bulkBendPoint_reachable m q)))

theorem bulkRung_x_difference_le_two (m : ℕ) {p q : Site}
    (h : (bulkRungGraph m).Reachable p q) : |q.val 0 - p.val 0| ≤ 2 := by
  have hp := abs_le.mp (bulkSite_x_near_bend m p)
  have hq := abs_le.mp (bulkSite_x_near_bend m q)
  rw [← bulkBendPoint_eq_of_rungReachable m h] at hq
  rw [abs_le]
  constructor <;> omega

theorem bulkSegment_x_bound_of_site (m : ℕ) {p q : BulkVertex m} (B : ℤ)
    (h : (bulkSegmentGraph m).Reachable p q) (hp : |p.val.val 0| ≤ B) :
    |q.val.val 0| ≤ B + 2 := by
  have hd := abs_le.mp (bulkRung_x_difference_le_two m (bulkSegment_reachable_rung m h))
  have hp' := abs_le.mp hp
  rw [abs_le]
  constructor <;> omega

theorem finset_min_add_max_abs_bound (S : Finset ℤ) (hne : S.Nonempty) (B : ℤ)
    (h : ∀ x ∈ S, |x| ≤ B) : |S.min' hne + S.max' hne| ≤ 2 * B := by
  have hmin := abs_le.mp (h _ (Finset.min'_mem S hne))
  have hmax := abs_le.mp (h _ (Finset.max'_mem S hne))
  rw [abs_le]
  constructor <;> omega

theorem bulkSegmentXhat_bound_of_site (m : ℕ) (p : BulkVertex m) (B : ℤ)
    (hp : |p.val.val 0| ≤ B) : |bulkSegmentXhat m p| ≤ 2 * (B + 2) := by
  classical
  apply finset_min_add_max_abs_bound
  intro x
  simp only [bulkSegmentXValues, Finset.mem_image, mem_bulkSegmentSites]
  rintro ⟨q, hq, rfl⟩
  exact bulkSegment_x_bound_of_site m B hq hp

end ProteinFolding.Tetrahedral

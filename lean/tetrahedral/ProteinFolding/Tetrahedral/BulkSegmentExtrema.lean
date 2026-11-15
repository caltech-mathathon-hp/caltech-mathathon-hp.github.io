import ProteinFolding.Tetrahedral.BulkSegmentLocalBounds

/-! A segment containing both extreme X values of its line has Xhat equal
to twice the bend coordinate. The hypotheses are local sites and bonds,
not an assumed segment-order comparison. -/

namespace ProteinFolding.Tetrahedral

theorem finset_min_add_max_eq_window (S : Finset ℤ) (hne : S.Nonempty) (x : ℤ)
    (hlower : ∀ y ∈ S, x - 1 ≤ y) (hupper : ∀ y ∈ S, y ≤ x + 1)
    (hleft : x - 1 ∈ S) (hright : x + 1 ∈ S) :
    S.min' hne + S.max' hne = 2 * x := by
  have hmin := (Finset.min'_eq_iff S hne (x - 1)).mpr ⟨hleft, hlower⟩
  have hmax := (Finset.max'_eq_iff S hne (x + 1)).mpr ⟨hright, hupper⟩
  rw [hmin, hmax]
  ring

theorem bulkSegmentXhat_eq_of_window (m : ℕ) (p : BulkVertex m) (x : ℤ)
    (hwindow : ∀ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q → |q.val.val 0 - x| ≤ 1)
    (hleft : ∃ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q ∧ q.val.val 0 = x - 1)
    (hright : ∃ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q ∧ q.val.val 0 = x + 1) :
    bulkSegmentXhat m p = 2 * x := by
  classical
  have hlower : ∀ y ∈ bulkSegmentXValues m p, x - 1 ≤ y := by
    intro y
    simp only [bulkSegmentXValues, Finset.mem_image, mem_bulkSegmentSites]
    rintro ⟨q, hq, rfl⟩
    have h := abs_le.mp (hwindow q hq)
    omega
  have hupper : ∀ y ∈ bulkSegmentXValues m p, y ≤ x + 1 := by
    intro y
    simp only [bulkSegmentXValues, Finset.mem_image, mem_bulkSegmentSites]
    rintro ⟨q, hq, rfl⟩
    have h := abs_le.mp (hwindow q hq)
    omega
  have hleftMem : x - 1 ∈ bulkSegmentXValues m p := by
    simp only [bulkSegmentXValues, Finset.mem_image, mem_bulkSegmentSites]
    obtain ⟨q, hq, hx⟩ := hleft
    exact ⟨q, hq, hx⟩
  have hrightMem : x + 1 ∈ bulkSegmentXValues m p := by
    simp only [bulkSegmentXValues, Finset.mem_image, mem_bulkSegmentSites]
    obtain ⟨q, hq, hx⟩ := hright
    exact ⟨q, hq, hx⟩
  exact finset_min_add_max_eq_window _ _ x hlower hupper hleftMem hrightMem

theorem bulkSegmentXhat_eq_twice_bend (m : ℕ) (p b : BulkVertex m)
    (hpb : (bulkSegmentGraph m).Reachable p b) (hb : bulkY m b.val = 0 ∨ bulkZ b.val = 0)
    (hleft : ∃ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q ∧ q.val.val 0 = b.val.val 0 - 1)
    (hright : ∃ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q ∧ q.val.val 0 = b.val.val 0 + 1) :
    bulkSegmentXhat m p = 2 * b.val.val 0 := by
  apply bulkSegmentXhat_eq_of_window m p (b.val.val 0) _ hleft hright
  intro q hq
  have hqb := bulkSegment_reachable_rung m (hq.symm.trans hpb)
  have hBend := bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m q.val) hb
    ((bulkBendPoint_reachable m q.val).symm.trans hqb)
  have hx := bulkSite_x_near_bend m q.val
  rwa [hBend] at hx

end ProteinFolding.Tetrahedral

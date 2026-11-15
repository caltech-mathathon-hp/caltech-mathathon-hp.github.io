import ProteinFolding.Tetrahedral.BulkLongXBendPairs

/-! A simple spanning segment path whose two ends point inward contains its
bend and both extreme X values. No global component-compression premise is used. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegment_inward_spanning_bend_xhat (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath)
    (hspan : ∀ r, (bulkSegmentGraph m).Reachable p r → r ∈ w.support)
    (hpin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj p r ∧
      bulkRho m r.val < bulkRho m p.val)
    (hqin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj q r ∧
      bulkRho m r.val < bulkRho m q.val) :
    ∃ b : BulkVertex m, (bulkSegmentGraph m).Reachable p b ∧
      (bulkY m b.val = 0 ∨ bulkZ b.val = 0) ∧ bulkSegmentXhat m p = 2 * b.val.val 0 := by
  classical
  have hnonempty : w.support.toFinset.Nonempty :=
    ⟨p, List.mem_toFinset.mpr w.start_mem_support⟩
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image w.support.toFinset
    (fun r : BulkVertex m => bulkRho m r.val) hnonempty
  have hbs : b ∈ w.support := List.mem_toFinset.mp hb
  have hbp : b ≠ p := by
    intro h
    obtain ⟨r, hpr, hrho⟩ := hpin
    have hlow := hmin r (List.mem_toFinset.mpr (hspan r hpr.reachable))
    rw [h] at hlow
    omega
  have hbq : b ≠ q := by
    intro h
    obtain ⟨r, hqr, hrho⟩ := hqin
    have hpr : (bulkSegmentGraph m).Reachable p r :=
      (show (bulkSegmentGraph m).Reachable p q from ⟨w⟩).trans hqr.reachable
    have hlow := hmin r (List.mem_toFinset.mpr (hspan r hpr))
    rw [h] at hlow
    omega
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hbs
  have hipos : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    rw [hi0, Walk.getVert_zero] at hi
    exact hbp hi.symm
  have hilt : i < w.length := by
    by_contra h
    have hiend : i = w.length := by omega
    rw [hiend, Walk.getVert_length] at hi
    exact hbq hi.symm
  have hleft : (bulkSegmentGraph m).Adj (w.getVert (i - 1)) b := by
    have h := w.adj_getVert_succ (show i - 1 < w.length by omega)
    rwa [show i - 1 + 1 = i by omega, hi] at h
  have hright : (bulkSegmentGraph m).Adj b (w.getVert (i + 1)) := by
    have h := w.adj_getVert_succ hilt
    rwa [hi] at h
  have hne : w.getVert (i - 1) ≠ w.getVert (i + 1) := by
    intro h
    have hn := hw.getVert_injOn (show i - 1 ≤ w.length by omega)
      (show i + 1 ≤ w.length by omega) h
    omega
  have hnes : (w.getVert (i - 1)).val ≠ (w.getVert (i + 1)).val := by
    intro h
    exact hne (Subtype.ext h)
  have hleftle := hmin (w.getVert (i - 1))
    (List.mem_toFinset.mpr (w.getVert_mem_support (i - 1)))
  have hrightle := hmin (w.getVert (i + 1))
    (List.mem_toFinset.mpr (w.getVert_mem_support (i + 1)))
  have hbend := bulk_two_upper_rungs_bend m b.val (w.getVert (i - 1)).val
    (w.getVert (i + 1)).val hleft.symm.2 hright.2 hnes hleftle hrightle
  have hpb : (bulkSegmentGraph m).Reachable p b := by
    rw [← hi]
    exact ⟨w.take i⟩
  refine ⟨b, hpb, hbend, ?_⟩
  apply bulkSegmentXhat_eq_twice_bend m p b hpb hbend
  · rcases bulk_bend_rung_x_pair m b.val (w.getVert (i - 1)).val
        (w.getVert (i + 1)).val hbend hleft.symm.2 hright.2 hnes with h | h
    · exact ⟨w.getVert (i - 1), ⟨w.take (i - 1)⟩, h.1⟩
    · exact ⟨w.getVert (i + 1), ⟨w.take (i + 1)⟩, h.2⟩
  · rcases bulk_bend_rung_x_pair m b.val (w.getVert (i - 1)).val
        (w.getVert (i + 1)).val hbend hleft.symm.2 hright.2 hnes with h | h
    · exact ⟨w.getVert (i + 1), ⟨w.take (i + 1)⟩, h.2⟩
    · exact ⟨w.getVert (i - 1), ⟨w.take (i - 1)⟩, h.1⟩

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkLongXInwardPath
import ProteinFolding.Tetrahedral.BulkLineInjectivity
import ProteinFolding.Tetrahedral.IntegerUnitPath

/-! The two ends of an inward spanning segment path lie on opposite arms. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegment_path_Z_affine (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath) (hα : 0 < bulkAlpha m p.val) :
    (∀ i ≤ w.length, bulkZ (w.getVert i).val = bulkZ p.val + (i : ℤ)) ∨
      (∀ i ≤ w.length, bulkZ (w.getVert i).val = bulkZ p.val - (i : ℤ)) := by
  have h := integer_unit_segment_affine w.length (fun i => bulkZ (w.getVert i).val)
  apply (by simpa only [Walk.getVert_zero] using h)
  · intro i hi
    have hd := (bulk_adj_deltas m (w.adj_getVert_succ hi).2.1).2
    omega
  · intro i hi j hj heq
    have hpi : (bulkSegmentGraph m).Reachable p (w.getVert i) := ⟨w.take i⟩
    have hpj : (bulkSegmentGraph m).Reachable p (w.getVert j) := ⟨w.take j⟩
    have hαj := bulkSegment_alpha m hpj
    have heqsite := bulkRung_positive_Z_injective m
      (bulkSegment_reachable_rung m (hpj.symm.trans hpi)) (by omega) heq
    exact hw.getVert_injOn hi hj (Subtype.ext heqsite)

theorem bulkSegment_path_Y_affine (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath) (hα : bulkAlpha m p.val < 0) :
    (∀ i ≤ w.length, bulkY m (w.getVert i).val = bulkY m p.val + (i : ℤ)) ∨
      (∀ i ≤ w.length, bulkY m (w.getVert i).val = bulkY m p.val - (i : ℤ)) := by
  have h := integer_unit_segment_affine w.length (fun i => bulkY m (w.getVert i).val)
  apply (by simpa only [Walk.getVert_zero] using h)
  · intro i hi
    have hd := (bulk_adj_deltas m (w.adj_getVert_succ hi).2.1).1
    omega
  · intro i hi j hj heq
    have hpi : (bulkSegmentGraph m).Reachable p (w.getVert i) := ⟨w.take i⟩
    have hpj : (bulkSegmentGraph m).Reachable p (w.getVert j) := ⟨w.take j⟩
    have hαj := bulkSegment_alpha m hpj
    have heqsite := bulkRung_negative_Y_injective m
      (bulkSegment_reachable_rung m (hpj.symm.trans hpi)) (by omega) heq
    exact hw.getVert_injOn hi hj (Subtype.ext heqsite)

private theorem inward_bend_index (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q)
    (hspan : ∀ r, (bulkSegmentGraph m).Reachable p r → r ∈ w.support)
    (hpin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj p r ∧
      bulkRho m r.val < bulkRho m p.val)
    (hqin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj q r ∧
      bulkRho m r.val < bulkRho m q.val)
    (b : BulkVertex m) (hpb : (bulkSegmentGraph m).Reachable p b)
    (hbend : bulkY m b.val = 0 ∨ bulkZ b.val = 0) :
    ∃ i, 0 < i ∧ i < w.length ∧ w.getVert i = b := by
  have hbp : b ≠ p := by
    intro heq
    subst b
    obtain ⟨r, hadj, hlow⟩ := hpin
    have hup := bulk_bend_neighbour_up m hbend hadj.2
    omega
  have hbq : b ≠ q := by
    intro heq
    subst b
    obtain ⟨r, hadj, hlow⟩ := hqin
    have hup := bulk_bend_neighbour_up m hbend hadj.2
    omega
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hspan b hpb)
  refine ⟨i, ?_, ?_, hi⟩
  · by_contra h
    have hi0 : i = 0 := by omega
    rw [hi0, Walk.getVert_zero] at hi
    exact hbp hi.symm
  · by_contra h
    have hiend : i = w.length := by omega
    rw [hiend, Walk.getVert_length] at hi
    exact hbq hi.symm

theorem bulkSegment_inward_positive_endpoint_signs (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath)
    (hspan : ∀ r, (bulkSegmentGraph m).Reachable p r → r ∈ w.support)
    (hpin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj p r ∧
      bulkRho m r.val < bulkRho m p.val)
    (hqin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj q r ∧
      bulkRho m r.val < bulkRho m q.val) (hα : 0 < bulkAlpha m p.val) :
    (bulkZ p.val < 0 ∧ 0 < bulkZ q.val) ∨ (0 < bulkZ p.val ∧ bulkZ q.val < 0) := by
  obtain ⟨b, hpb, hbend, _⟩ := bulkSegment_inward_spanning_bend_xhat m w hw hspan hpin hqin
  have hbeq := bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p.val) hbend
    ((bulkBendPoint_reachable m p.val).symm.trans (bulkSegment_reachable_rung m hpb))
  have hbzero := bulkBendPoint_Z_zero_of_positive m p.val hα
  rw [hbeq] at hbzero
  obtain ⟨i, hi0, hil, hi⟩ := inward_bend_index m w hspan hpin hqin b hpb hbend
  have hsigns := integer_affine_zero_endpoint_signs w.length (fun j => bulkZ (w.getVert j).val)
    i hi0 hil (by change bulkZ (w.getVert i).val = 0; rw [hi]; exact hbzero)
    (by simpa only [Walk.getVert_zero] using bulkSegment_path_Z_affine m w hw hα)
  simpa only [Walk.getVert_zero, Walk.getVert_length] using hsigns

theorem bulkSegment_inward_negative_endpoint_signs (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath)
    (hspan : ∀ r, (bulkSegmentGraph m).Reachable p r → r ∈ w.support)
    (hpin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj p r ∧
      bulkRho m r.val < bulkRho m p.val)
    (hqin : ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj q r ∧
      bulkRho m r.val < bulkRho m q.val) (hα : bulkAlpha m p.val < 0) :
    (bulkY m p.val < 0 ∧ 0 < bulkY m q.val) ∨
      (0 < bulkY m p.val ∧ bulkY m q.val < 0) := by
  obtain ⟨b, hpb, hbend, _⟩ := bulkSegment_inward_spanning_bend_xhat m w hw hspan hpin hqin
  have hbeq := bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p.val) hbend
    ((bulkBendPoint_reachable m p.val).symm.trans (bulkSegment_reachable_rung m hpb))
  have hbzero := bulkBendPoint_Y_zero_of_negative m p.val hα
  rw [hbeq] at hbzero
  obtain ⟨i, hi0, hil, hi⟩ := inward_bend_index m w hspan hpin hqin b hpb hbend
  have hsigns := integer_affine_zero_endpoint_signs w.length (fun j => bulkY m (w.getVert j).val)
    i hi0 hil (by change bulkY m (w.getVert i).val = 0; rw [hi]; exact hbzero)
    (by simpa only [Walk.getVert_zero] using bulkSegment_path_Y_affine m w hw hα)
  simpa only [Walk.getVert_zero, Walk.getVert_length] using hsigns

end ProteinFolding.Tetrahedral

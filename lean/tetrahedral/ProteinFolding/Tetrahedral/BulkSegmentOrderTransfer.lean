import ProteinFolding.Tetrahedral.BulkSegmentCoordinateTransfer
import ProteinFolding.Tetrahedral.BulkSegmentOrderFacts

/-! Complete bounded component certificates preserve the corrected
lexicographic potential comparison under a common vertex translation. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegmentFiniteCheck_xhat_bounds (m : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (rank : Site → ℕ)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r) :
    2 * (bulkPatchVertex m v).val 0 - 2 * (D : ℤ) ≤ bulkSegmentXhat m p ∧
      bulkSegmentXhat m p ≤ 2 * (bulkPatchVertex m v).val 0 + 2 * (D : ℤ) := by
  let xmin := (bulkSegmentXValues m p).min' (bulkSegmentXValues_nonempty m p)
  let xmax := (bulkSegmentXValues m p).max' (bulkSegmentXValues_nonempty m p)
  have hmin : xmin ∈ A.image (fun r => r.val 0) := by
    rw [← bulkSegmentFiniteCheck_xValues m p A rank h]
    exact Finset.min'_mem _ _
  have hmax : xmax ∈ A.image (fun r => r.val 0) := by
    rw [← bulkSegmentFiniteCheck_xValues m p A rank h]
    exact Finset.max'_mem _ _
  obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hmin
  obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hmax
  have hub := abs_le.mp (hbox u hu 0)
  have hwb := abs_le.mp (hbox w hw 0)
  change 2 * (bulkPatchVertex m v).val 0 - 2 * (D : ℤ) ≤ xmin + xmax ∧
    xmin + xmax ≤ 2 * (bulkPatchVertex m v).val 0 + 2 * (D : ℤ)
  omega

theorem bulkReanchor_alpha_sign_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    (0 < bulkAlpha n (bulkReanchorSite m n v p) ↔ 0 < bulkAlpha m p) := by
  have hnew := bulkReanchorSite_in_box m n v D p hp
  have hα := (bulkReanchor_rho_alpha m n v D p hm hn hp).2
  fin_cases v
  · have heq : bulkAlpha n (bulkReanchorSite m n 0 p) = bulkAlpha m p := by
      simpa only [bulkVertexYExpansion, bulkVertexZExpansion, add_zero, sub_zero] using hα
    change (0 < bulkAlpha n (bulkReanchorSite m n 0 p) ↔ 0 < bulkAlpha m p)
    rw [heq]
  · exact iff_of_true
      (bulk_y_vertex_alpha_positive n 1 D _ hn (Or.inl rfl) hnew)
      (bulk_y_vertex_alpha_positive m 1 D p hm (Or.inl rfl) hp)
  · exact iff_of_false
      (not_lt.mpr (le_of_lt (bulk_z_vertex_alpha_negative n 2 D _ hn (Or.inl rfl) hnew)))
      (not_lt.mpr (le_of_lt (bulk_z_vertex_alpha_negative m 2 D p hm (Or.inl rfl) hp)))
  · exact iff_of_false
      (not_lt.mpr (le_of_lt (bulk_z_vertex_alpha_negative n 3 D _ hn (Or.inr rfl) hnew)))
      (not_lt.mpr (le_of_lt (bulk_z_vertex_alpha_negative m 3 D p hm (Or.inr rfl) hp)))
  · exact iff_of_true
      (bulk_y_vertex_alpha_positive n 4 D _ hn (Or.inr rfl) hnew)
      (bulk_y_vertex_alpha_positive m 4 D p hm (Or.inr rfl) hp)
  · have heq : bulkAlpha n (bulkReanchorSite m n 5 p) = bulkAlpha m p := by
      simpa only [bulkVertexYExpansion, bulkVertexZExpansion, add_zero, sub_zero] using hα
    change (0 < bulkAlpha n (bulkReanchorSite m n 5 p) ↔ 0 < bulkAlpha m p)
    rw [heq]

theorem bulkVertex_xhat_abs_difference (m n : ℕ) (v : Fin 6) (D : ℕ)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (x y x' y' : ℤ)
    (hx : x' = x + 2 * ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0))
    (hy : y' = y + 2 * ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0))
    (hxb : 2 * (bulkPatchVertex m v).val 0 - 2 * (D : ℤ) ≤ x ∧
      x ≤ 2 * (bulkPatchVertex m v).val 0 + 2 * (D : ℤ))
    (hyb : 2 * (bulkPatchVertex m v).val 0 - 2 * (D : ℤ) ≤ y ∧
      y ≤ 2 * (bulkPatchVertex m v).val 0 + 2 * (D : ℤ)) :
    |x'| - |y'| = |x| - |y| := by
  fin_cases v
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hx hy hxb hyb
    have hs : x' ≤ 0 ∧ y' ≤ 0 ∧ x ≤ 0 ∧ y ≤ 0 := by omega
    rw [abs_of_nonpos hs.1, abs_of_nonpos hs.2.1, abs_of_nonpos hs.2.2.1, abs_of_nonpos hs.2.2.2]
    omega
  · change x' = x + 0 at hx
    change y' = y + 0 at hy
    simp only [add_zero] at hx hy
    rw [hx, hy]
  · change x' = x + 0 at hx
    change y' = y + 0 at hy
    simp only [add_zero] at hx hy
    rw [hx, hy]
  · change x' = x + 0 at hx
    change y' = y + 0 at hy
    simp only [add_zero] at hx hy
    rw [hx, hy]
  · change x' = x + 0 at hx
    change y' = y + 0 at hy
    simp only [add_zero] at hx hy
    rw [hx, hy]
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hx hy hxb hyb
    have hs : 0 ≤ x' ∧ 0 ≤ y' ∧ 0 ≤ x ∧ 0 ≤ y := by omega
    rw [abs_of_nonneg hs.1, abs_of_nonneg hs.2.1, abs_of_nonneg hs.2.2.1, abs_of_nonneg hs.2.2.2]
    omega

theorem bulkSegment_vertex_potential_lt_iff (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A B : Finset Site) (p p' : BulkVertex m) (q q' : BulkVertex n)
    (rank rank' : Site → ℕ) (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (hbox' : ∀ r ∈ B, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank) (h' : BulkSegmentFiniteCheck m B p'.val rank')
    (hq : q.val = bulkReanchorSite m n v p.val) (hq' : q'.val = bulkReanchorSite m n v p'.val) :
    (bulkSegmentPotential n q < bulkSegmentPotential n q' ↔
      bulkSegmentPotential m p < bulkSegmentPotential m p') := by
  have hroot := hbox p.val h.1
  have hroot' := hbox' p'.val h'.1
  have hs := bulkReanchor_alpha_sign_iff m n v D p.val (by omega) (by omega) hroot
  have hs' := bulkReanchor_alpha_sign_iff m n v D p'.val (by omega) (by omega) hroot'
  rw [← hq] at hs
  rw [← hq'] at hs'
  have ha : bulkAlpha n q.val = bulkAlpha m p.val +
      (bulkVertexYExpansion m n v - bulkVertexZExpansion m n v) := by
    rw [hq, (bulkReanchor_rho_alpha m n v D p.val (by omega) (by omega) hroot).2]
    omega
  have ha' : bulkAlpha n q'.val = bulkAlpha m p'.val +
      (bulkVertexYExpansion m n v - bulkVertexZExpansion m n v) := by
    rw [hq', (bulkReanchor_rho_alpha m n v D p'.val (by omega) (by omega) hroot').2]
    omega
  have hx := bulkSegment_vertex_xhat_shift m n v D A p q rank hm hn hbox h hq
  have hx' := bulkSegment_vertex_xhat_shift m n v D B p' q' rank' hm hn hbox' h' hq'
  apply bulkSegmentPotential_lt_iff_of_statistics m n p p' q q'
    (bulkVertexYExpansion m n v - bulkVertexZExpansion m n v)
    (2 * ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0))
    (bulkSegment_vertex_row m n v D A p q rank hm hn hbox h hq)
    (bulkSegment_vertex_row m n v D B p' q' rank' hm hn hbox' h' hq')
    hs hs' ha ha' hx hx'
  exact bulkVertex_xhat_abs_difference m n v D (by omega) (by omega) _ _ _ _ hx hx'
    (bulkSegmentFiniteCheck_xhat_bounds m v D A p rank h hbox)
    (bulkSegmentFiniteCheck_xhat_bounds m v D B p' rank' h' hbox')

end ProteinFolding.Tetrahedral

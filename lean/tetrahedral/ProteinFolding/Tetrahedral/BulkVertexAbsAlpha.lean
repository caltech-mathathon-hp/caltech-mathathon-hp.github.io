import ProteinFolding.Tetrahedral.BulkSegmentCoordinateTransfer

/-! Absolute alpha changes by the radius increment at a y- or z-vertex. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkReanchor_middle_vertex_abs_alpha (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hv : 1 ≤ v.val ∧ v.val ≤ 4)
    (hp : InBulkVertexBox m v D p) :
    |bulkAlpha n (bulkReanchorSite m n v p)| = |bulkAlpha m p| + 2 * ((n : ℤ) - m) := by
  have hqbox := bulkReanchorSite_in_box m n v D p hp
  have hα := (bulkReanchor_rho_alpha m n v D p hm hn hp).2
  fin_cases v
  all_goals dsimp only at *
  · omega
  · have hpa := bulk_y_vertex_alpha_positive m 1 D p hm (Or.inl rfl) hp
    have hqa := bulk_y_vertex_alpha_positive n 1 D _ hn (Or.inl rfl) hqbox
    rw [abs_of_pos hpa, abs_of_pos hqa]
    simpa only [bulkVertexYExpansion, bulkVertexZExpansion, Fin.isValue, sub_zero] using hα
  · have hpa := bulk_z_vertex_alpha_negative m 2 D p hm (Or.inl rfl) hp
    have hqa := bulk_z_vertex_alpha_negative n 2 D _ hn (Or.inl rfl) hqbox
    rw [abs_of_neg hpa, abs_of_neg hqa]
    simp only [bulkVertexYExpansion, bulkVertexZExpansion, add_zero] at hα
    omega
  · have hpa := bulk_z_vertex_alpha_negative m 3 D p hm (Or.inr rfl) hp
    have hqa := bulk_z_vertex_alpha_negative n 3 D _ hn (Or.inr rfl) hqbox
    rw [abs_of_neg hpa, abs_of_neg hqa]
    simp only [bulkVertexYExpansion, bulkVertexZExpansion, add_zero] at hα
    omega
  · have hpa := bulk_y_vertex_alpha_positive m 4 D p hm (Or.inr rfl) hp
    have hqa := bulk_y_vertex_alpha_positive n 4 D _ hn (Or.inr rfl) hqbox
    rw [abs_of_pos hpa, abs_of_pos hqa]
    simpa only [bulkVertexYExpansion, bulkVertexZExpansion, Fin.isValue, sub_zero] using hα
  · omega

end ProteinFolding.Tetrahedral

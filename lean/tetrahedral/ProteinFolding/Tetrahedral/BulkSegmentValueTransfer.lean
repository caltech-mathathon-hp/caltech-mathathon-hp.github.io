import ProteinFolding.Tetrahedral.BulkSegmentWitnessValues
import ProteinFolding.Tetrahedral.BulkSegmentVertexTransfer

/-! Transport of exact segment statistics from complete finite certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegment_projected_xValues (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (h : (bulkSegmentSites m p).image Subtype.val = A) :
    bulkSegmentXValues m p = A.image (fun q => q.val 0) := by
  rw [← h, Finset.image_image]
  rfl

theorem bulkSegment_projected_row (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (h : (bulkSegmentSites m p).image Subtype.val = A) :
    BulkRowSegment m p ↔ ∃ q ∈ A, q ∈ bulkDamaged m ∧ bulkZ q = 0 := by
  unfold BulkRowSegment
  rw [← h]
  constructor
  · rintro ⟨q, hq, hd, hz⟩
    exact ⟨q.val, Finset.mem_image.mpr ⟨q, hq, rfl⟩, hd, hz⟩
  · rintro ⟨q, hq, hd, hz⟩
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨r, hr, hd, hz⟩

theorem bulkSegment_vertex_projected (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n) (rank : Site → ℕ)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    (bulkSegmentSites n q).image Subtype.val = A.image (bulkReanchorSite m n v) := by
  ext r
  rw [bulkSegmentSites_image_component, hq]
  exact (bulkSegmentFiniteCheck_vertex_component m n v D A p.val rank hm hn hbox h r).symm

theorem bulkReanchor_y_vertex_x (m n : ℕ) (v : Fin 6) (hv : v = 1 ∨ v = 4) (p : Site) :
    (bulkReanchorSite m n v p).val 0 = p.val 0 := by
  rw [bulkReanchorSite_coordinates]
  rcases hv with rfl | rfl <;>
    simp only [bulkPatchVertex, Fin.reduceFinMk, octVertexSite, octVertexCoordinates,
      octCentre, Fin.zero_eta, Fin.isValue, zero_ne_one, ↓reduceIte, zero_add, sub_zero, add_zero]

theorem bulkSegment_vertex_y_xValues (m n : ℕ) (v : Fin 6) (D : ℕ)
    (hv : v = 1 ∨ v = 4) (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n)
    (rank : Site → ℕ) (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    bulkSegmentXValues n q = bulkSegmentXValues m p := by
  rw [bulkSegment_projected_xValues n q _
      (bulkSegment_vertex_projected m n v D A p q rank hm hn hbox h hq),
    bulkSegmentFiniteCheck_xValues m p A rank h, Finset.image_image]
  congr 1
  funext r
  exact bulkReanchor_y_vertex_x m n v hv r

theorem bulkSegment_vertex_y_xhat (m n : ℕ) (v : Fin 6) (D : ℕ)
    (hv : v = 1 ∨ v = 4) (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n)
    (rank : Site → ℕ) (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    bulkSegmentXhat n q = bulkSegmentXhat m p := by
  unfold bulkSegmentXhat
  simp only [bulkSegment_vertex_y_xValues m n v D hv A p q rank hm hn hbox h hq]

theorem bulkSegment_vertex_row (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n) (rank : Site → ℕ)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    BulkRowSegment n q ↔ BulkRowSegment m p := by
  rw [bulkSegment_projected_row n q _
      (bulkSegment_vertex_projected m n v D A p q rank hm hn hbox h hq),
    bulkSegmentFiniteCheck_row m p A rank h]
  constructor
  · rintro ⟨r, hr, hd, hz⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨s, hs, ?_, ?_⟩
    · exact (bulkReanchor_damaged_iff m n v D s (by omega) (by omega) (hbox s hs)).mp hd
    · exact ((bulkReanchor_zeros m n v D s (by omega) (by omega) (hbox s hs)).2).mp hz
  · rintro ⟨r, hr, hd, hz⟩
    refine ⟨bulkReanchorSite m n v r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_, ?_⟩
    · exact (bulkReanchor_damaged_iff m n v D r (by omega) (by omega) (hbox r hr)).mpr hd
    · exact ((bulkReanchor_zeros m n v D r (by omega) (by omega) (hbox r hr)).2).mpr hz

end ProteinFolding.Tetrahedral

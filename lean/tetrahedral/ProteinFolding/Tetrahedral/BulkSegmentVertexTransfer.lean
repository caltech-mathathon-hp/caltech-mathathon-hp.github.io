import ProteinFolding.Tetrahedral.BulkSegmentCertificates

/-! Vertex translations preserve complete segment stars and therefore transport
whole certified segments, including the absence of any further continuation. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSiteSegmentGraph_adj_iff (m : ℕ) (p q : Site) :
    (bulkSiteSegmentGraph m).Adj p q ↔ bulkCoverBond m p q ∧ (bulkRungGraph m).Adj p q := by
  constructor
  · intro h
    exact ⟨h.1, bulkCoverBond_adj m h.1, h.2⟩
  · intro h
    exact ⟨h.1, h.2.2⟩

theorem bulkReanchor_segment_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n)
    (hp : InBulkVertexBox m v D p) (hq : InBulkVertexBox m v D q) :
    (bulkSiteSegmentGraph n).Adj (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔
      (bulkSiteSegmentGraph m).Adj p q := by
  rw [bulkSiteSegmentGraph_adj_iff, bulkSiteSegmentGraph_adj_iff,
    bulkReanchor_coverBond_iff m n v D p q hm hn hp hq,
    bulkReanchor_rung_iff m n v D p q (by omega) (by omega) hp hq]

theorem bulkReanchor_segment_map (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n) (hp : InBulkVertexBox m v D p)
    (q : Site) (hadj : (bulkSiteSegmentGraph m).Adj p q) :
    (bulkSiteSegmentGraph n).Adj (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) := by
  have hq := bulk_adjacent_in_vertex_box m v D hp (bulkCoverBond_adj m hadj.1)
  exact (bulkReanchor_segment_iff m n v (D + 1) p q (by omega) (by omega)
    (bulkVertexBox_mono m v (by omega) hp) hq).mpr hadj

theorem bulkReanchor_segment_complete (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n) (hp : InBulkVertexBox m v D p)
    (q : Site) (hadj : (bulkSiteSegmentGraph n).Adj (bulkReanchorSite m n v p) q) :
    ∃ r, (bulkSiteSegmentGraph m).Adj p r ∧ bulkReanchorSite m n v r = q := by
  have hq : q ∈ bulkCoverNeighbours n (bulkReanchorSite m n v p) :=
    (mem_bulkCoverNeighbours n _ q).mpr hadj.1
  rw [← bulkReanchor_coverNeighbours_image m n v D p hm hn hp] at hq
  obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hq
  have hcover : bulkCoverBond m p r := (mem_bulkCoverNeighbours m p r).mp hr
  have hrbox := bulk_adjacent_in_vertex_box m v D hp (bulkCoverBond_adj m hcover)
  refine ⟨r, ?_, hrq⟩
  apply (bulkReanchor_segment_iff m n v (D + 1) p r (by omega) (by omega)
    (bulkVertexBox_mono m v (by omega) hp) hrbox).mp
  rwa [hrq]

theorem bulkSegmentFiniteCheck_vertex_component (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (root : Site) (rank : Site → ℕ)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ p ∈ A, InBulkVertexBox m v D p)
    (h : BulkSegmentFiniteCheck m A root rank) (q : Site) :
    q ∈ A.image (bulkReanchorSite m n v) ↔
      (bulkSiteSegmentGraph n).Reachable (bulkReanchorSite m n v root) q := by
  apply bulkSegmentFiniteCheck_transport m n A root rank h (bulkReanchorSite m n v)
  · intro p hp r hadj
    exact bulkReanchor_segment_map m n v D p hm hn (hbox p hp) r hadj
  · intro p hp r hadj
    exact bulkReanchor_segment_complete m n v D p hm hn (hbox p hp) r hadj

end ProteinFolding.Tetrahedral

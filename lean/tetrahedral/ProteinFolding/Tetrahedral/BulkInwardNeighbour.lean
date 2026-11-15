import ProteinFolding.Tetrahedral.BulkSegmentEdgeTransfer
import ProteinFolding.Tetrahedral.BulkSegmentQuickCertificates
import ProteinFolding.Tetrahedral.BulkSegmentWitnessValues

/-! Existence and complete-star transport of a strictly inward segment
neighbour. The computational predicate supplies one of four directions. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def BulkHasInwardNeighbour (m : ℕ) (p : Site) : Prop :=
  ∃ q, (bulkSiteSegmentGraph m).Adj p q ∧ bulkRho m q < bulkRho m p

def BulkFastHasInwardNeighbour (m : ℕ) (p : Site) : Prop :=
  ∃ d : Fin 4, bulkQuickSegmentBond m p (step p d) ∧ bulkRho m (step p d) < bulkRho m p

instance (m : ℕ) (p : Site) : Decidable (BulkFastHasInwardNeighbour m p) := by
  unfold BulkFastHasInwardNeighbour
  infer_instance

theorem bulkFastHasInwardNeighbour_sound (m : ℕ) (p : Site)
    (h : BulkFastHasInwardNeighbour m p) : BulkHasInwardNeighbour m p := by
  obtain ⟨d, hd, hρ⟩ := h
  exact ⟨step p d, (bulkSiteSegmentGraph_fast m p (step p d)).mpr
    ((bulkQuickSegmentBond_iff m p (step p d)).mp hd), hρ⟩

theorem bulkHasInwardNeighbour_edge (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (h : BulkHasInwardNeighbour m p) :
    BulkHasInwardNeighbour M (bulkEdgeReanchor m M t T F p) := by
  obtain ⟨q, hq, hρ⟩ := h
  have hqbox := bulk_adjacent_in_edge_box m F t D hp (bulkCoverBond_adj m hq.1)
  have hpbox := bulkEdgeBox_mono m F t (show D ≤ D + 1 by omega) hp
  have hpρ := (bulkEdgeReanchor_relative_rho_alpha m M t T F (D + 1) p
    (by omega) (by omega) (by omega) (by omega) hpbox).1
  have hqρ := (bulkEdgeReanchor_relative_rho_alpha m M t T F (D + 1) q
    (by omega) (by omega) (by omega) (by omega) hqbox).1
  exact ⟨bulkEdgeReanchor m M t T F q,
    bulkEdgeReanchor_segment_map m M t T F D p ht htm hT hTM hp q hq, by omega⟩

theorem bulkHasInwardNeighbour_vertex (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n) (hp : InBulkVertexBox m v D p)
    (h : BulkHasInwardNeighbour m p) : BulkHasInwardNeighbour n (bulkReanchorSite m n v p) := by
  obtain ⟨q, hq, hρ⟩ := h
  have hqbox := bulk_adjacent_in_vertex_box m v D hp (bulkCoverBond_adj m hq.1)
  have hpbox := bulkVertexBox_mono m v (show D ≤ D + 1 by omega) hp
  have hpρ := (bulkReanchor_rho_alpha m n v (D + 1) p (by omega) (by omega) hpbox).1
  have hqρ := (bulkReanchor_rho_alpha m n v (D + 1) q (by omega) (by omega) hqbox).1
  exact ⟨bulkReanchorSite m n v q, bulkReanchor_segment_map m n v D p hm hn hp q hq, by omega⟩

theorem bulkHasInwardNeighbour_finite (m : ℕ) (p : BulkVertex m) (h : BulkHasInwardNeighbour m p.val) :
    ∃ q : BulkVertex m, (bulkSegmentGraph m).Adj p q ∧ bulkRho m q.val < bulkRho m p.val := by
  obtain ⟨q, hq, hρ⟩ := h
  have hqI : q ∈ bulkInterior m := hq.1.2.1
  exact ⟨⟨q, hqI⟩, (bulkSegmentGraph_site_adj m p ⟨q, hqI⟩).mpr hq, hρ⟩

end ProteinFolding.Tetrahedral

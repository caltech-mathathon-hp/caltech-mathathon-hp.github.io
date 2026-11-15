import ProteinFolding.Tetrahedral.BulkSegmentVertexTransfer
import ProteinFolding.Tetrahedral.BulkEdgeMergeTransfer

/-! Complete rung-segment stars transport along far edges. This transports
the entire finite component, including the absence of any continuation. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkEdgeReanchor_coverNeighbours_image (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkCoverNeighbours m p).image (bulkEdgeReanchor m M t T F) =
      bulkCoverNeighbours M (bulkEdgeReanchor m M t T F p) := by
  have hp' := bulkEdgeReanchor_in_box m M t T F D p hp
  have hnotOld := bulkFarEdgeBox_not_patchSupport m F t D p ht htm hp
  have hnotNew := bulkFarEdgeBox_not_patchSupport M F T D _ hT hTM hp'
  have hI := bulkEdgeReanchor_interior_iff m M t T F D p (by omega) (by omega) (by omega) (by omega) hp
  by_cases hpI : p ∈ bulkInterior m
  · rw [bulkCoverNeighbours_eq_merged_of_not_support m p hpI hnotOld,
      bulkCoverNeighbours_eq_merged_of_not_support M _ (hI.mpr hpI) hnotNew]
    exact bulkEdgeReanchor_mergedNeighbours_image m M t T F D p (by omega) (by omega)
      (by omega) (by omega) hp
  · have hpI' : bulkEdgeReanchor m M t T F p ∉ bulkInterior M := fun h => hpI (hI.mp h)
    rw [bulkCoverNeighbours_empty_of_not_interior m p hpI,
      bulkCoverNeighbours_empty_of_not_interior M _ hpI', Finset.image_empty]

theorem bulkEdgeReanchor_segment_map (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (q : Site) (hadj : (bulkSiteSegmentGraph m).Adj p q) :
    (bulkSiteSegmentGraph M).Adj (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) := by
  have hq := bulk_adjacent_in_edge_box m F t D hp (bulkCoverBond_adj m hadj.1)
  have hcover : bulkCoverBond M (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) := by
    apply (mem_bulkCoverNeighbours M _ _).mp
    rw [← bulkEdgeReanchor_coverNeighbours_image m M t T F D p ht htm hT hTM hp]
    exact Finset.mem_image.mpr ⟨q, (mem_bulkCoverNeighbours m p q).mpr hadj.1, rfl⟩
  apply (bulkSiteSegmentGraph_adj_iff M _ _).mpr
  refine ⟨hcover, ?_⟩
  apply (bulkEdgeReanchor_rung_iff m M t T F (D + 1) p q (by omega) (by omega)
    (by omega) (by omega) (bulkEdgeBox_mono m F t (by omega) hp) hq).mpr
  exact (bulkSiteSegmentGraph_adj_iff m p q).mp hadj |>.2

theorem bulkEdgeReanchor_segment_complete (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (q : Site)
    (hadj : (bulkSiteSegmentGraph M).Adj (bulkEdgeReanchor m M t T F p) q) :
    ∃ r, (bulkSiteSegmentGraph m).Adj p r ∧ bulkEdgeReanchor m M t T F r = q := by
  have hq := (mem_bulkCoverNeighbours M _ q).mpr hadj.1
  rw [← bulkEdgeReanchor_coverNeighbours_image m M t T F D p ht htm hT hTM hp] at hq
  obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hq
  have hcover := (mem_bulkCoverNeighbours m p r).mp hr
  have hrbox := bulk_adjacent_in_edge_box m F t D hp (bulkCoverBond_adj m hcover)
  refine ⟨r, (bulkSiteSegmentGraph_adj_iff m p r).mpr ⟨hcover, ?_⟩, hrq⟩
  apply (bulkEdgeReanchor_rung_iff m M t T F (D + 1) p r (by omega) (by omega)
    (by omega) (by omega) (bulkEdgeBox_mono m F t (by omega) hp) hrbox).mp
  rw [hrq]
  exact (bulkSiteSegmentGraph_adj_iff M _ _).mp hadj |>.2

theorem bulkSegmentFiniteCheck_edge_component (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ)
    (A : Finset Site) (root : Site) (rank : Site → ℕ)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hbox : ∀ p ∈ A, InBulkEdgeBox m F t D p)
    (h : BulkSegmentFiniteCheck m A root rank) (q : Site) :
    q ∈ A.image (bulkEdgeReanchor m M t T F) ↔
      (bulkSiteSegmentGraph M).Reachable (bulkEdgeReanchor m M t T F root) q := by
  apply bulkSegmentFiniteCheck_transport m M A root rank h (bulkEdgeReanchor m M t T F)
  · intro p hp r hadj
    exact bulkEdgeReanchor_segment_map m M t T F D p ht htm hT hTM (hbox p hp) r hadj
  · intro p hp r hadj
    exact bulkEdgeReanchor_segment_complete m M t T F D p ht htm hT hTM (hbox p hp) r hadj

end ProteinFolding.Tetrahedral

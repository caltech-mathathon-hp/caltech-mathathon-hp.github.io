import ProteinFolding.Tetrahedral.BulkFarEdgeReference
import ProteinFolding.Tetrahedral.BulkEdgeMergeTransfer
import ProteinFolding.Tetrahedral.BulkDegree

/-! The finite far-edge certificate applies to the full unbounded family. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeReanchor_anchor (m M t T : ℕ) (F : OctEdgeFrame) :
    bulkEdgeReanchor m M t T F (bulkEdgeAnchor m F t) = bulkEdgeAnchor M F T := by
  apply Subtype.ext
  funext k
  rw [bulkEdgeReanchor_coordinates]
  omega

theorem bulkEdgeReanchor_candidate (m M t T : ℕ) (F : OctEdgeFrame) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (hM : 1 ≤ M) :
    bulkEdgeReanchor m M t T F (bulkEdgeCandidate m F t odd d hm) = bulkEdgeCandidate M F T odd d hM := by
  cases odd <;> simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq,
    bulkEdgeReanchor_step, bulkEdgeReanchor_anchor]

theorem bulkEdgeCandidate_in_box (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) : InBulkEdgeBox m F t 2 (bulkEdgeCandidate m F t odd d hm) := by
  have hzero : InBulkEdgeBox m F t 0 (bulkEdgeAnchor m F t) := by intro k; simp
  cases odd
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    exact bulkEdgeBox_mono m F t (by omega)
      (bulk_adjacent_in_edge_box m F t 0 hzero (step_adj _ d))
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    exact bulk_adjacent_in_edge_box m F t 1
      (bulk_adjacent_in_edge_box m F t 0 hzero (step_adj _ F.a)) (step_adj _ d)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bulkFarEdge_damaged_degree (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) :
    (bulkCoverNeighbours m (bulkEdgeCandidate m F t odd d hm)).card = 2 := by
  have hp := bulkEdgeCandidate_in_box m F t odd d hm
  have hDm := (bulkEdgeReanchor_damaged_iff m 21 t 10 F 2 (bulkEdgeCandidate m F t odd d hm)
    (by omega) (by omega) (by decide) (by decide) hp).mpr hd
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hDm
  have href := bulkFarEdge_reference_damaged_degree F odd d ((bulkDamaged_fast_iff 21 _).mp hDm)
  rw [← bulkCoverNeighbours_fast_card] at href
  have hcard := bulkEdgeReanchor_coverNeighbours_card m 21 t 10 F 2 (bulkEdgeCandidate m F t odd d hm)
    ht htm (by decide) (by decide) hp
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hcard
  have hupper := bulkCoverNeighbours_card_le_two m (by omega) (bulkEdgeCandidate m F t odd d hm)
  omega

end ProteinFolding.Tetrahedral

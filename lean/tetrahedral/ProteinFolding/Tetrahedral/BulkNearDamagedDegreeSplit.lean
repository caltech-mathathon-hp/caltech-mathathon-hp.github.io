import ProteinFolding.Tetrahedral.BulkNearEdgeReferenceSplit
import ProteinFolding.Tetrahedral.BulkNearEdgeGeometry
import ProteinFolding.Tetrahedral.BulkDegree

/-! Uniform near-edge minimum degree using the split reference certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bulkNearEdge_damaged_degree_split (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 27 ≤ m) (ht : t ≤ 9) (hOne : 1 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) :
    (bulkCoverNeighbours m (bulkEdgeCandidate m F t odd d hOne)).card = 2 := by
  have hbox := bulkNearEdgeCandidate_in_start_box m F t odd d hOne ht
  have hDm := (bulkReanchor_damaged_iff m 50 (bulkEdgeStartIndex F) 20
    (bulkEdgeCandidate m F t odd d hOne) (by omega) (by decide) hbox).mpr hd
  rw [bulkVertexReanchor_candidate m 50 F t odd d hOne (by decide)] at hDm
  have href := bulkNearEdge_reference_damaged_degree_split F ⟨t, Nat.lt_succ_of_le ht⟩ odd d
    ((bulkDamaged_fast_iff 50 _).mp hDm)
  rw [← bulkCoverNeighbours_fast_card 50] at href
  have hcard := bulkReanchor_coverNeighbours_card m 50 (bulkEdgeStartIndex F) 20
    (bulkEdgeCandidate m F t odd d hOne) hm (by decide) hbox
  rw [bulkVertexReanchor_candidate m 50 F t odd d hOne (by decide)] at hcard
  have hupper := bulkCoverNeighbours_card_le_two m (by omega) (bulkEdgeCandidate m F t odd d hOne)
  apply Nat.le_antisymm hupper
  rw [← hcard]
  exact href

end ProteinFolding.Tetrahedral

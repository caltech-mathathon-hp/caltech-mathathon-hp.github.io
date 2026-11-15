import ProteinFolding.Tetrahedral.NearFieldBulkSecondRowGeometry
import ProteinFolding.Tetrahedral.NearFieldBulkSecondRowReferences
import ProteinFolding.Tetrahedral.ConstructionParameters

/-! N3 for the F' second row. Uniform vertex and edge transfer reduce the
entire unbounded family to the kernel-checked local reference points. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem bulk_secondRow_degree (m : ℕ) (hm : 30 ≤ m) (a b : ℕ)
    (hs : a + b + 1 + 2 = m + 2 * 0)
    (hp : faceSurfaceSite m 0 a b 1 hs ∈ bulkInterior m) :
    (bulkCoverNeighbours m (faceSurfaceSite m 0 a b 1 hs)).card = 2 := by
  by_cases hb : b ≤ 9
  · have hbox := secondRow_in_left_box m a b hs hb
    have hc := bulkReanchor_coverNeighbours_card m 50 2 23
      (faceSurfaceSite m 0 a b 1 hs) (by omega) (by decide) hbox
    have hI := (bulkReanchor_interior_iff m 50 2 23
      (faceSurfaceSite m 0 a b 1 hs) (by omega) (by decide) hbox).mpr hp
    rw [secondRow_left_reanchor m a b hs hb] at hc hI
    have hfast : bulkFastInterior 50 (secondRowLeftReference ⟨b, by omega⟩) :=
      (bulkInterior_fast_iff 50 _).mp hI
    have href := secondRowLeftReference_degree ⟨b, by omega⟩ hfast
    rw [bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans href
  by_cases ha : a ≤ 9
  · have hbox := secondRow_in_right_box m a b hs ha
    have hc := bulkReanchor_coverNeighbours_card m 50 4 23
      (faceSurfaceSite m 0 a b 1 hs) (by omega) (by decide) hbox
    have hI := (bulkReanchor_interior_iff m 50 4 23
      (faceSurfaceSite m 0 a b 1 hs) (by omega) (by decide) hbox).mpr hp
    rw [secondRow_right_reanchor m a b hs ha] at hc hI
    have hfast : bulkFastInterior 50 (secondRowRightReference ⟨a, by omega⟩) :=
      (bulkInterior_fast_iff 50 _).mp hI
    have href := secondRowRightReference_degree ⟨a, by omega⟩ hfast
    rw [bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans href
  · have hc := bulkEdgeReanchor_coverNeighbours_card m 23 (b + 1) 11 entryEdgeFrame 3
      (faceSurfaceSite m 0 a b 1 hs) (by omega) (by omega) (by decide) (by decide)
      (secondRow_in_edge_box m a b hs)
    rw [secondRow_edge_reanchor m a b hs, bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans secondRowFarReference_degree

theorem construction_bulk_secondRow_degree (p : ConstructionParameters) (a b : ℕ)
    (hs : a + b + 1 + 2 = p.side + 2 * 0)
    (hp : faceSurfaceSite p.side 0 a b 1 hs ∈ bulkInterior p.side) :
    (bulkCoverNeighbours p.side (faceSurfaceSite p.side 0 a b 1 hs)).card = 2 :=
  bulk_secondRow_degree p.side (by have h := p.side_ge; omega) a b hs hp

theorem construction_bulk_secondRow_not_end (p : ConstructionParameters) (a b : ℕ)
    (hs : a + b + 1 + 2 = p.side + 2 * 0)
    (hp : faceSurfaceSite p.side 0 a b 1 hs ∈ bulkInterior p.side) :
    (bulkCoverNeighbours p.side (faceSurfaceSite p.side 0 a b 1 hs)).card ≠ 1 := by
  rw [construction_bulk_secondRow_degree p a b hs hp]
  decide

end ProteinFolding.Tetrahedral.NearField

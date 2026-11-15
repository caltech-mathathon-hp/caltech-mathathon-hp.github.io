import ProteinFolding.Tetrahedral.NearFieldBulkARowGeometry
import ProteinFolding.Tetrahedral.NearFieldBulkARowReferences
import ProteinFolding.Tetrahedral.ConstructionParameters

/-! The A-side second-row clearance needed by borrowed frame linker caps. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem bulk_aSecondRow_degree (m : ℕ) (hm : 30 ≤ m) (t : ℕ)
    (hp : aSecondRowSite m t ∈ bulkInterior m) :
    (bulkCoverNeighbours m (aSecondRowSite m t)).card = 2 := by
  have htm := aSecondRow_index_bound m t hp
  by_cases ht : t ≤ 9
  · have hbox := aSecondRow_in_left_box m t ht
    have hc := bulkReanchor_coverNeighbours_card m 50 2 23 (aSecondRowSite m t)
      (by omega) (by decide) hbox
    have hI := (bulkReanchor_interior_iff m 50 2 23 (aSecondRowSite m t)
      (by omega) (by decide) hbox).mpr hp
    rw [aSecondRow_left_reanchor] at hc hI
    have href := aSecondRow_left_reference_degree ⟨t, by omega⟩ ((bulkInterior_fast_iff 50 _).mp hI)
    rw [bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans href
  by_cases hfar : t + 11 ≤ m
  · have hc := bulkEdgeReanchor_coverNeighbours_card m 21 t 10 entryEdgeFrame 2 (aSecondRowSite m t)
      (by omega) hfar (by decide) (by decide) (aSecondRow_in_edge_box m t (by omega))
    rw [aSecondRow_edge_reanchor m t (by omega), bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans aSecondRow_far_reference_degree
  · have hr : m - 1 - t ≤ 9 := by omega
    have hbox := aSecondRow_in_right_box m t htm hr
    have hc := bulkReanchor_coverNeighbours_card m 50 4 23 (aSecondRowSite m t)
      (by omega) (by decide) hbox
    have hI := (bulkReanchor_interior_iff m 50 4 23 (aSecondRowSite m t)
      (by omega) (by decide) hbox).mpr hp
    rw [aSecondRow_right_reanchor m t htm hr] at hc hI
    have href := aSecondRow_right_reference_degree ⟨m - 1 - t, by omega⟩
      ((bulkInterior_fast_iff 50 _).mp hI)
    rw [bulkCoverNeighbours_fast_card] at hc
    exact hc.symm.trans href

theorem construction_bulk_aSecondRow_degree (p : ConstructionParameters) (t : ℕ)
    (hp : aSecondRowSite p.side t ∈ bulkInterior p.side) :
    (bulkCoverNeighbours p.side (aSecondRowSite p.side t)).card = 2 :=
  bulk_aSecondRow_degree p.side (by have h := p.side_ge; omega) t hp

end ProteinFolding.Tetrahedral.NearField

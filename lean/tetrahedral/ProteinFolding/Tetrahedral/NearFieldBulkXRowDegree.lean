import ProteinFolding.Tetrahedral.NearFieldBulkXRowReferences
import ProteinFolding.Tetrahedral.NearFieldBulkXRowIndex
import ProteinFolding.Tetrahedral.NearFieldBulkXRowFastTransfer

/-! N3 for every X-plane edge, both orientations, and both sublattices.
All unbounded parameters are handled by proved local transfer. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem xRowSite_degree_of_fastInterior (m : ℕ) (hm : 30 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ)
    (hp : bulkFastInterior m (xRowSite m (by omega) k reverse small t)) :
    (bulkCoverNeighbours m (xRowSite m (by omega) k reverse small t)).card = 2 := by
  have hm1 : 1 ≤ m := by omega
  have htm := xRowSite_index_bound m hm1 k reverse small t hp.1
  by_cases ht : t ≤ 10
  · have hbox := xRowSite_in_left_box m hm1 k reverse small t ht
    have hc := bulkReanchor_coverNeighbours_card m 50 (xRowStartIndex k reverse) 23
      (xRowSite m hm1 k reverse small t) (by omega) (by decide) hbox
    have hI := (vertex_fastInterior_iff m 50 (xRowStartIndex k reverse) 23
      (xRowSite m hm1 k reverse small t) (by omega) (by decide) hbox).mpr hp
    rw [xRowSite_left_reanchor m 50 hm1 (by decide) k reverse small t] at hc hI
    have href := xRow_left_reference k reverse small ⟨t, Nat.lt_succ_of_le ht⟩ hI
    rw [bulkCoverNeighbours_fast_card 50] at hc
    exact hc.symm.trans href
  by_cases hfar : t + 12 ≤ m
  · have hbox := xRowSite_in_edge_box m hm1 k reverse small t
    have hc := bulkEdgeReanchor_coverNeighbours_card m 23 t 11 (xRowFrame k reverse) 3
      (xRowSite m hm1 k reverse small t) (by omega) hfar (by decide) (by decide) hbox
    have hI := (edge_fastInterior_iff m 23 t 11 (xRowFrame k reverse) 3
      (xRowSite m hm1 k reverse small t) (by omega) (by omega) (by decide) (by decide) hbox).mpr hp
    rw [xRowSite_edge_reanchor m 23 hm1 (by decide) k reverse small t 11] at hc hI
    have href := xRow_far_reference k reverse small hI
    rw [bulkCoverNeighbours_fast_card 23] at hc
    exact hc.symm.trans href
  · have hr : m - 1 - t ≤ 10 := by omega
    have hbox := xRowSite_in_right_box m hm1 k reverse small t htm hr
    have hc := bulkReanchor_coverNeighbours_card m 50 (xRowEndIndex k reverse) 23
      (xRowSite m hm1 k reverse small t) (by omega) (by decide) hbox
    have hI := (vertex_fastInterior_iff m 50 (xRowEndIndex k reverse) 23
      (xRowSite m hm1 k reverse small t) (by omega) (by decide) hbox).mpr hp
    rw [xRowSite_right_reanchor m hm1 k reverse small t htm hr] at hc hI
    have href := xRow_right_reference k reverse small ⟨m - 1 - t, Nat.lt_succ_of_le hr⟩ hI
    rw [bulkCoverNeighbours_fast_card 50] at hc
    exact hc.symm.trans href

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem xRowSite_degree (m : ℕ) (hm : 30 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ)
    (hp : xRowSite m (by omega) k reverse small t ∈ bulkInterior m) :
    (bulkCoverNeighbours m (xRowSite m (by omega) k reverse small t)).card = 2 :=
  xRowSite_degree_of_fastInterior m hm k reverse small t ((bulkInterior_fast_iff m _).mp hp)

end ProteinFolding.Tetrahedral.NearField

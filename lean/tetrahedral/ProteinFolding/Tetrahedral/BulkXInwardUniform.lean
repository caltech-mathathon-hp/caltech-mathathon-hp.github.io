import ProteinFolding.Tetrahedral.BulkXInwardReference
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! Every far X-joint endpoint points strictly inward along its actual
rung segment, including the index10 transition in either orientation. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkXInward_source (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 10 ≤ t) (htm : t + 11 ≤ m) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) :
    BulkHasInwardNeighbour m (bulkEdgeCandidate m F t odd d hm) := by
  have hbox := bulkEdgeCandidate_in_box m F t odd d hm
  have hDm := (bulkEdgeReanchor_damaged_iff m 21 t 10 F 2 (bulkEdgeCandidate m F t odd d hm)
    (by omega) (by omega) (by decide) (by decide) hbox).mpr hd
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hDm
  have href := bulkFastHasInwardNeighbour_sound 21 _
    (bulkXInward_reference_source F odd d hX ((bulkDamaged_fast_iff 21 _).mp hDm))
  have hgoal := bulkHasInwardNeighbour_edge 21 m 10 t F 2 _ (by decide) (by decide) ht htm
    (bulkEdgeCandidate_in_box 21 F 10 odd d (by decide)) href
  rwa [bulkEdgeReanchor_candidate 21 m 10 t F odd d (by decide) hm] at hgoal

theorem bulkXInward_target (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 11 ≤ t) (htm : t + 12 ≤ m) (hX : BulkXEdgeFrame F)
    (p : Site) (hp : bulkMerge m (bulkEdgeCandidate m F t odd d hm) p) : BulkHasInwardNeighbour m p := by
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step _ p).mp (bulkMerge_adj m hp)
  have hsource := bulkEdgeCandidate_in_box m F t odd d hm
  have htarget := bulk_adjacent_in_edge_box m F t 2 hsource (step_adj _ e)
  have hM := (bulkEdgeReanchor_merge_iff m 23 t 11 F 3 _ _
    (by omega) (by omega) (by decide) (by decide) (bulkEdgeBox_mono m F t (by decide) hsource) htarget).mpr hp
  rw [bulkEdgeReanchor_step, bulkEdgeReanchor_candidate m 23 t 11 F odd d hm (by decide)] at hM
  have href := bulkFastHasInwardNeighbour_sound 23 _
    (bulkXInward_reference_target F odd d e hX ((bulkMerge_fast_iff 23 _ _).mp hM))
  have hrefbox := bulk_adjacent_in_edge_box 23 F 11 2
    (bulkEdgeCandidate_in_box 23 F 11 odd d (by decide)) (step_adj _ e)
  have hgoal := bulkHasInwardNeighbour_edge 23 m 11 t F 3 _ (by decide) (by decide) ht htm hrefbox href
  rwa [bulkEdgeReanchor_step, bulkEdgeReanchor_candidate 23 m 11 t F odd d (by decide) hm] at hgoal

theorem bulkXInward_ten_source_box (m : ℕ) (F : OctEdgeFrame) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) : InBulkVertexBox m (bulkEdgeStartIndex F) 22 (bulkEdgeCandidate m F 10 odd d hm) := by
  have hb := bulkEdgeZigzag_in_start_box m F 20
  cases odd
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulkVertexBox_mono m (bulkEdgeStartIndex F) (by decide)
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) 20 hb (step_adj _ d))
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) 21
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) 20 hb (step_adj _ F.a)) (step_adj _ d)

theorem bulkXInward_target_ten (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (odd : Bool) (d : Fin 4)
    (hOne : 1 ≤ m) (hX : BulkXEdgeFrame F) (p : Site)
    (hp : bulkMerge m (bulkEdgeCandidate m F 10 odd d hOne) p) : BulkHasInwardNeighbour m p := by
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step _ p).mp (bulkMerge_adj m hp)
  have hsource := bulkXInward_ten_source_box m F odd d hOne
  have htarget := bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) 22 hsource (step_adj _ e)
  have hM := (bulkReanchor_merge_iff m 50 (bulkEdgeStartIndex F) 23 _ _ (by omega) (by decide)
    (bulkVertexBox_mono m _ (by decide) hsource) htarget).mpr hp
  rw [bulkReanchorSite_step, bulkVertexReanchor_candidate m 50 F 10 odd d hOne (by decide)] at hM
  have href := bulkFastHasInwardNeighbour_sound 50 _
    (bulkXInward_reference_target_ten F odd d e hX ((bulkMerge_fast_iff 50 _ _).mp hM))
  have hrefbox := bulk_adjacent_in_vertex_box 50 (bulkEdgeStartIndex F) 22
    (bulkXInward_ten_source_box 50 F odd d (by decide)) (step_adj _ e)
  have hgoal := bulkHasInwardNeighbour_vertex 50 m (bulkEdgeStartIndex F) 23 _ (by decide) (by omega) hrefbox href
  rwa [bulkReanchorSite_step, bulkVertexReanchor_candidate 50 m F 10 odd d (by decide) hOne] at hgoal

theorem bulkX_joint_inward_all_far (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : 10 ≤ t)
    (hrev : 10 ≤ if odd then m - 2 - t else m - 1 - t) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p) :
    BulkHasInwardNeighbour m p := by
  have hmargin : t + 11 ≤ m := by cases odd <;> simp at hrev <;> omega
  rcases hp with rfl | hp
  · exact bulkXInward_source m F t odd d hOne ht hmargin hX hd
  by_cases hten : t = 10
  · subst t
    exact bulkXInward_target_ten m hm F odd d hOne hX p hp
  have ht11 : 11 ≤ t := by omega
  by_cases hfar : t + 12 ≤ m
  · exact bulkXInward_target m F t odd d hOne ht11 hfar hX p hp
  have hXrev : BulkXEdgeFrame (bulkReverseEdgeFrame F) := by
    simpa only [BulkXEdgeFrame, bulkReverseEdgeFrame] using hX
  cases odd
  · change 10 ≤ m - 1 - t at hrev
    have hrevt : m - 1 - t = 10 := by omega
    have heq := bulkEdgeCandidate_reverse_even hOne F t (by omega) d
    rw [heq, hrevt] at hp
    exact bulkXInward_target_ten m hm (bulkReverseEdgeFrame F) false d hOne hXrev p hp
  · change 10 ≤ m - 2 - t at hrev
    omega

end ProteinFolding.Tetrahedral

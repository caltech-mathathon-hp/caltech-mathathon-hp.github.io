import ProteinFolding.Tetrahedral.BulkXInwardNearReference
import ProteinFolding.Tetrahedral.BulkVertexAbsAlpha
import ProteinFolding.Tetrahedral.BulkFarXAlpha

/-! Inward neighbours persist at indices8,9. A moderately small absolute
alpha excludes every smaller index in either orientation. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkXInward_near_source (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 2)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F (j.val + 8) odd d hOne ∈ bulkDamaged m) :
    BulkHasInwardNeighbour m (bulkEdgeCandidate m F (j.val + 8) odd d hOne) := by
  have hbox := bulkNearEdgeCandidate_in_start_box m F (j.val + 8) odd d hOne (by omega)
  have hDm := (bulkReanchor_damaged_iff m 50 (bulkEdgeStartIndex F) 20 _ (by omega) (by decide) hbox).mpr hd
  rw [bulkVertexReanchor_candidate m 50 F (j.val + 8) odd d hOne (by decide)] at hDm
  have href := bulkFastHasInwardNeighbour_sound 50 _
    (bulkXInward_near_reference_source F j odd d hX ((bulkDamaged_fast_iff 50 _).mp hDm))
  have hgoal := bulkHasInwardNeighbour_vertex 50 m (bulkEdgeStartIndex F) 20 _ (by decide) (by omega)
    (bulkNearEdgeCandidate_in_start_box 50 F (j.val + 8) odd d (by decide) (by omega)) href
  rwa [bulkVertexReanchor_candidate 50 m F (j.val + 8) odd d (by decide) hOne] at hgoal

theorem bulkXInward_near_target (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 2)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (hX : BulkXEdgeFrame F) (p : Site)
    (hp : bulkMerge m (bulkEdgeCandidate m F (j.val + 8) odd d hOne) p) : BulkHasInwardNeighbour m p := by
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step _ p).mp (bulkMerge_adj m hp)
  have hsource := bulkNearEdgeCandidate_in_start_box m F (j.val + 8) odd d hOne (by omega)
  have htarget := bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) 20 hsource (step_adj _ e)
  have hM := (bulkReanchor_merge_iff m 50 (bulkEdgeStartIndex F) 21 _ _ (by omega) (by decide)
    (bulkVertexBox_mono m _ (by decide) hsource) htarget).mpr hp
  rw [bulkReanchorSite_step, bulkVertexReanchor_candidate m 50 F (j.val + 8) odd d hOne (by decide)] at hM
  have href := bulkFastHasInwardNeighbour_sound 50 _
    (bulkXInward_near_reference_target F j odd d e hX ((bulkMerge_fast_iff 50 _ _).mp hM))
  have hrefbox := bulk_adjacent_in_vertex_box 50 (bulkEdgeStartIndex F) 20
    (bulkNearEdgeCandidate_in_start_box 50 F (j.val + 8) odd d (by decide) (by omega)) (step_adj _ e)
  have hgoal := bulkHasInwardNeighbour_vertex 50 m (bulkEdgeStartIndex F) 21 _ (by decide) (by omega) hrefbox href
  rwa [bulkReanchorSite_step, bulkVertexReanchor_candidate 50 m F (j.val + 8) odd d (by decide) hOne] at hgoal

theorem bulkXInward_near_transition (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : 8 ≤ t) (ht' : t ≤ 9) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p) :
    BulkHasInwardNeighbour m p := by
  let j : Fin 2 := ⟨t - 8, by omega⟩
  have heq : t = j.val + 8 := by dsimp [j]; omega
  rw [heq] at hd hp
  rcases hp with rfl | hp
  · exact bulkXInward_near_source m hm F j odd d hOne hX hd
  · exact bulkXInward_near_target m hm F j odd d hOne hX p hp

theorem bulkX_joint_inward_outside_seven (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : 8 ≤ t)
    (hrev : 8 ≤ if odd then m - 2 - t else m - 1 - t) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p) :
    BulkHasInwardNeighbour m p := by
  by_cases hnear : t ≤ 9
  · exact bulkXInward_near_transition m hm F t odd d hOne ht hnear hX hd p hp
  have ht10 : 10 ≤ t := by omega
  by_cases hrevFar : 10 ≤ if odd then m - 2 - t else m - 1 - t
  · exact bulkX_joint_inward_all_far m hm F t odd d hOne ht10 hrevFar hX hd p hp
  have hXrev : BulkXEdgeFrame (bulkReverseEdgeFrame F) := by
    simpa only [BulkXEdgeFrame, bulkReverseEdgeFrame] using hX
  cases odd
  · change 8 ≤ m - 1 - t at hrev
    change ¬10 ≤ m - 1 - t at hrevFar
    have heq := bulkEdgeCandidate_reverse_even hOne F t (by omega) d
    rw [heq] at hd hp
    exact bulkXInward_near_transition m hm (bulkReverseEdgeFrame F) _ false d hOne hrev (by omega) hXrev hd p hp
  · change 8 ≤ m - 2 - t at hrev
    change ¬10 ≤ m - 2 - t at hrevFar
    have heq := bulkEdgeCandidate_reverse_odd hOne F t (by omega) d
    rw [heq] at hd hp
    exact bulkXInward_near_transition m hm (bulkReverseEdgeFrame F) _ true d hOne hrev (by omega) hXrev hd p hp

theorem bulkXNear_source_alpha_lower (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : t ≤ 7) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) :
    octRadius m - 31 ≤ |bulkAlpha m (bulkEdgeCandidate m F t odd d hOne)| := by
  have hbox := bulkNearEdgeCandidate_in_start_box m F t odd d hOne (by omega)
  have hDm := (bulkReanchor_damaged_iff m 50 (bulkEdgeStartIndex F) 20 _ (by omega) (by decide) hbox).mpr hd
  rw [bulkVertexReanchor_candidate m 50 F t odd d hOne (by decide)] at hDm
  have href := bulkXNear_reference_alpha_lower F ⟨t, by omega⟩ odd d hX ((bulkDamaged_fast_iff 50 _).mp hDm)
  have hshift := bulkReanchor_middle_vertex_abs_alpha 50 m (bulkEdgeStartIndex F) 20 _
    (by decide) (by omega) (bulkXEdgeStart_middle F hX)
    (bulkNearEdgeCandidate_in_start_box 50 F t odd d (by decide) (by omega))
  rw [bulkVertexReanchor_candidate 50 m F t odd d (by decide) hOne] at hshift
  dsimp only at href
  unfold octRadius at href ⊢
  omega

theorem bulkX_joint_moderate_index_lower (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p)
    (hbound : |bulkAlpha m p| ≤ octRadius m - 35) : 8 ≤ t := by
  by_contra hnot
  have hlower := bulkXNear_source_alpha_lower m hm F t odd d hOne (by omega) hX hd
  have hupper : |bulkAlpha m (bulkEdgeCandidate m F t odd d hOne)| ≤ |bulkAlpha m p| + 2 := by
    rcases hp with hp | hp
    · rw [hp]
      omega
    · exact bulk_adj_alpha_abs_bound m (bulkMerge_adj m hp).symm
  omega

end ProteinFolding.Tetrahedral

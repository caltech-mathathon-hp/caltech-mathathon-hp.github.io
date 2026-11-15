import ProteinFolding.Tetrahedral.BulkVertexTransfer

/-! Frozen vertex patches commute with the bounded vertex translation. -/

namespace ProteinFolding.Tetrahedral

theorem bulkReanchor_patchRelativePair (m n : ℕ) (v : Fin 6) (p q : Site) :
    bulkPatchRelativePair n v (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) =
      bulkPatchRelativePair m v p q := by
  apply Prod.ext <;> funext k
  · change (bulkReanchorSite m n v p).val k - (bulkPatchVertex n v).val k =
      p.val k - (bulkPatchVertex m v).val k
    rw [bulkReanchorSite_coordinates]
    omega
  · change (bulkReanchorSite m n v q).val k - (bulkPatchVertex n v).val k =
      q.val k - (bulkPatchVertex m v).val k
    rw [bulkReanchorSite_coordinates]
    omega

set_option maxHeartbeats 1200000 in
theorem bulk_distinct_vertex_boxes_disjoint (m : ℕ) (v u : Fin 6) (D E : ℕ) (p : Site)
    (hvu : v ≠ u) (hsep : (D : ℤ) + E < octRadius m)
    (hv : InBulkVertexBox m v D p) (hu : InBulkVertexBox m u E p) : False := by
  have hv0 := abs_le.mp (hv 0)
  have hv1 := abs_le.mp (hv 1)
  have hv2 := abs_le.mp (hv 2)
  have hu0 := abs_le.mp (hu 0)
  have hu1 := abs_le.mp (hu 1)
  have hu2 := abs_le.mp (hu 2)
  fin_cases v <;> fin_cases u
  all_goals dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius]
    at hv0 hv1 hv2 hu0 hu1 hu2 hsep
  all_goals omega

theorem bulkPatchAdds_first_in_box (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchAdds v) : InBulkVertexBox m v 8 p := by
  intro k
  exact (bulkPatchAdds_within_eight v _ h k).1

theorem bulkPatchAdds_second_in_box (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchAdds v) : InBulkVertexBox m v 8 q := by
  intro k
  exact (bulkPatchAdds_within_eight v _ h k).2

theorem bulkPatchRemoves_first_in_box (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchRemoves v) : InBulkVertexBox m v 8 p := by
  intro k
  exact (bulkPatchRemoves_within_eight v _ h k).1

theorem bulkPatchRemoves_second_in_box (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchRemoves v) : InBulkVertexBox m v 8 q := by
  intro k
  exact (bulkPatchRemoves_within_eight v _ h k).2

theorem bulkReanchor_patchAdded_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkPatchAdded n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔ bulkPatchAdded m p q := by
  have hp' := bulkReanchorSite_in_box m n v D p hp
  have hsepM : (D : ℤ) + 8 < octRadius m := by unfold octRadius; omega
  have hsepN : (D : ℤ) + 8 < octRadius n := by unfold octRadius; omega
  constructor
  · rintro ⟨u, h | h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint n v u D 8 _ hne hsepN hp'
          (bulkPatchAdds_first_in_box n u _ _ h)
      subst u
      rw [bulkReanchor_patchRelativePair] at h
      exact ⟨v, Or.inl h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint n v u D 8 _ hne hsepN hp'
          (bulkPatchAdds_second_in_box n u _ _ h)
      subst u
      rw [bulkReanchor_patchRelativePair] at h
      exact ⟨v, Or.inr h⟩
  · rintro ⟨u, h | h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint m v u D 8 p hne hsepM hp
          (bulkPatchAdds_first_in_box m u _ _ h)
      subst u
      exact ⟨v, Or.inl (by rwa [bulkReanchor_patchRelativePair])⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint m v u D 8 p hne hsepM hp
          (bulkPatchAdds_second_in_box m u _ _ h)
      subst u
      exact ⟨v, Or.inr (by rwa [bulkReanchor_patchRelativePair])⟩

theorem bulkReanchor_patchRemoved_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkPatchRemoved n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔ bulkPatchRemoved m p q := by
  have hp' := bulkReanchorSite_in_box m n v D p hp
  have hsepM : (D : ℤ) + 8 < octRadius m := by unfold octRadius; omega
  have hsepN : (D : ℤ) + 8 < octRadius n := by unfold octRadius; omega
  constructor
  · rintro ⟨u, h | h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint n v u D 8 _ hne hsepN hp'
          (bulkPatchRemoves_first_in_box n u _ _ h)
      subst u
      rw [bulkReanchor_patchRelativePair] at h
      exact ⟨v, Or.inl h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint n v u D 8 _ hne hsepN hp'
          (bulkPatchRemoves_second_in_box n u _ _ h)
      subst u
      rw [bulkReanchor_patchRelativePair] at h
      exact ⟨v, Or.inr h⟩
  · rintro ⟨u, h | h⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint m v u D 8 p hne hsepM hp
          (bulkPatchRemoves_first_in_box m u _ _ h)
      subst u
      exact ⟨v, Or.inl (by rwa [bulkReanchor_patchRelativePair])⟩
    · have hu : v = u := by
        by_contra hne
        exact bulk_distinct_vertex_boxes_disjoint m v u D 8 p hne hsepM hp
          (bulkPatchRemoves_second_in_box m u _ _ h)
      subst u
      exact ⟨v, Or.inr (by rwa [bulkReanchor_patchRelativePair])⟩

theorem bulkReanchor_coverBond_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n)
    (hp : InBulkVertexBox m v D p) (hq : InBulkVertexBox m v D q) :
    bulkCoverBond n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔ bulkCoverBond m p q := by
  unfold bulkCoverBond
  rw [bulkReanchor_interior_iff m n v D p (by omega) (by omega) hp,
    bulkReanchor_interior_iff m n v D q (by omega) (by omega) hq,
    bulkReanchor_patchAdded_iff m n v D p q hm hn hp,
    bulkReanchor_patchRemoved_iff m n v D p q hm hn hp,
    bulkReanchor_mergedBond_iff m n v D p q (by omega) (by omega) hp hq]

theorem bulkReanchor_coverNeighbours_image (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkCoverNeighbours m p).image (bulkReanchorSite m n v) =
      bulkCoverNeighbours n (bulkReanchorSite m n v p) := by
  unfold bulkCoverNeighbours
  apply bulkReanchor_filtered_neighbours_image
  intro q hq
  have hqbox := bulk_adjacent_in_vertex_box m v D hp ((mem_neighbours p q).mp hq)
  exact bulkReanchor_coverBond_iff m n v (D + 1) p q (by omega) (by omega)
    (bulkVertexBox_mono m v (by omega) hp) hqbox

theorem bulkReanchor_coverNeighbours_card (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkCoverNeighbours n (bulkReanchorSite m n v p)).card = (bulkCoverNeighbours m p).card := by
  rw [← bulkReanchor_coverNeighbours_image m n v D p hm hn hp,
    Finset.card_image_of_injective _ (bulkReanchorSite_injective m n v)]

end ProteinFolding.Tetrahedral

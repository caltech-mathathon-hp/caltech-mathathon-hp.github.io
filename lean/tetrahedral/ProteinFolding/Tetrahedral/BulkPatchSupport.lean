import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Only a fixed finite list of sites can have their degree changed by a patch. -/

namespace ProteinFolding.Tetrahedral

def bulkPatchOffsets (v : Fin 6) : Finset Coordinates :=
  (bulkPatchAdds v ∪ bulkPatchRemoves v).biUnion (fun e => {e.1, e.2})

theorem bulkPatchOffsets_valid (v : Fin 6) : ∀ r ∈ bulkPatchOffsets v, IsLatticeSite r := by
  fin_cases v <;> decide

theorem bulkPatchOffsets_within_eight (v : Fin 6) :
    ∀ r ∈ bulkPatchOffsets v, ∀ k : Fin 3, |r k| ≤ 8 := by fin_cases v <;> decide

theorem bulkPatchVertex_one_val (v : Fin 6) (k : Fin 3) : (bulkPatchVertex 1 v).val k = 0 := by
  fin_cases v <;> fin_cases k <;> decide

def bulkPatchOffsetSite (m : ℕ) (v : Fin 6) (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) : Site :=
  bulkReanchorSite 1 m v ⟨r.val, bulkPatchOffsets_valid v r.val r.property⟩

theorem bulkPatchOffsetSite_coordinates (m : ℕ) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) (k : Fin 3) :
    (bulkPatchOffsetSite m v r).val k = r.val k + (bulkPatchVertex m v).val k := by
  unfold bulkPatchOffsetSite
  rw [bulkReanchorSite_coordinates, bulkPatchVertex_one_val]
  change r.val k - 0 + (bulkPatchVertex m v).val k = r.val k + (bulkPatchVertex m v).val k
  omega

theorem bulkPatchOffsetSite_in_box (m : ℕ) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) : InBulkVertexBox m v 8 (bulkPatchOffsetSite m v r) := by
  intro k
  rw [bulkPatchOffsetSite_coordinates]
  have heq : r.val k + (bulkPatchVertex m v).val k - (bulkPatchVertex m v).val k = r.val k := by omega
  rw [heq]
  exact bulkPatchOffsets_within_eight v r.val r.property k

theorem bulkReanchor_patchOffsetSite (m n : ℕ) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) :
    bulkReanchorSite m n v (bulkPatchOffsetSite m v r) = bulkPatchOffsetSite n v r := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates, bulkPatchOffsetSite_coordinates, bulkPatchOffsetSite_coordinates]
  omega

def bulkPatchSupport (m : ℕ) : Finset Site :=
  Finset.univ.biUnion (fun v : Fin 6 => (bulkPatchOffsets v).attach.image (bulkPatchOffsetSite m v))

theorem bulkPatchOffsetSite_of_relative (m : ℕ) (v : Fin 6) (p : Site)
    (h : (shiftSite (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) p).val ∈ bulkPatchOffsets v) :
    bulkPatchOffsetSite m v ⟨_, h⟩ = p := by
  apply Subtype.ext
  funext k
  rw [bulkPatchOffsetSite_coordinates]
  change (p.val k - (bulkPatchVertex m v).val k) + (bulkPatchVertex m v).val k = p.val k
  omega

theorem bulkPatchSupport_mem_of_relative (m : ℕ) (v : Fin 6) (p : Site)
    (h : (shiftSite (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) p).val ∈ bulkPatchOffsets v) :
    p ∈ bulkPatchSupport m := by
  apply Finset.mem_biUnion.mpr
  refine ⟨v, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  exact ⟨⟨_, h⟩, Finset.mem_attach _ _, bulkPatchOffsetSite_of_relative m v p h⟩

theorem bulkPatchSupport_added (m : ℕ) {p q : Site} (h : bulkPatchAdded m p q) :
    p ∈ bulkPatchSupport m ∧ q ∈ bulkPatchSupport m := by
  obtain ⟨v, h | h⟩ := h
  · constructor
    · apply bulkPatchSupport_mem_of_relative m v p
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inl h), by simp [bulkPatchRelativePair]⟩
    · apply bulkPatchSupport_mem_of_relative m v q
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inl h), by simp [bulkPatchRelativePair]⟩
  · constructor
    · apply bulkPatchSupport_mem_of_relative m v p
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inl h), by simp [bulkPatchRelativePair]⟩
    · apply bulkPatchSupport_mem_of_relative m v q
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inl h), by simp [bulkPatchRelativePair]⟩

theorem bulkPatchSupport_removed (m : ℕ) {p q : Site} (h : bulkPatchRemoved m p q) :
    p ∈ bulkPatchSupport m ∧ q ∈ bulkPatchSupport m := by
  obtain ⟨v, h | h⟩ := h
  · constructor
    · apply bulkPatchSupport_mem_of_relative m v p
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inr h), by simp [bulkPatchRelativePair]⟩
    · apply bulkPatchSupport_mem_of_relative m v q
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inr h), by simp [bulkPatchRelativePair]⟩
  · constructor
    · apply bulkPatchSupport_mem_of_relative m v p
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inr h), by simp [bulkPatchRelativePair]⟩
    · apply bulkPatchSupport_mem_of_relative m v q
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union.mpr (Or.inr h), by simp [bulkPatchRelativePair]⟩

theorem bulkCoverNeighbours_eq_merged_of_not_support (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hnot : p ∉ bulkPatchSupport m) :
    bulkCoverNeighbours m p = bulkMergedNeighbours m p := by
  ext q
  rw [mem_bulkCoverNeighbours, mem_bulkMergedNeighbours]
  have hAdd : ¬bulkPatchAdded m p q := fun h => hnot (bulkPatchSupport_added m h).1
  have hRem : ¬bulkPatchRemoved m p q := fun h => hnot (bulkPatchSupport_removed m h).1
  change bulkCoverBond m p q ↔ _
  simp only [bulkCoverBond, hp, hAdd, hRem, true_and, false_or, not_false_eq_true, and_true]

theorem bulkCoverNeighbours_card_le_two_of_not_support (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hnot : p ∉ bulkPatchSupport m) :
    (bulkCoverNeighbours m p).card ≤ 2 := by
  rw [bulkCoverNeighbours_eq_merged_of_not_support m p hp hnot]
  exact bulkMergedNeighbours_card_le_two m p

end ProteinFolding.Tetrahedral

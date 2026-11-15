import ProteinFolding.Tetrahedral.BulkFarEdgeReference
import ProteinFolding.Tetrahedral.BulkVertexPatches

/-! Near-start edge candidates remain in a fixed vertex box at every size. -/

namespace ProteinFolding.Tetrahedral

def bulkEdgeStartIndex (F : OctEdgeFrame) : Fin 6 :=
  if (F.k = 0 ∧ F.b = 1) ∨ (F.k = 1 ∧ F.b = 0) then 5
  else if (F.k = 0 ∧ F.b = 2) ∨ (F.k = 2 ∧ F.b = 0) then 4
  else if (F.k = 0 ∧ F.b = 3) ∨ (F.k = 3 ∧ F.b = 0) then 3
  else if (F.k = 1 ∧ F.b = 2) ∨ (F.k = 2 ∧ F.b = 1) then 2
  else if (F.k = 1 ∧ F.b = 3) ∨ (F.k = 3 ∧ F.b = 1) then 1 else 0

theorem bulkEdgeStart_eq_patchVertex (m : ℕ) (F : OctEdgeFrame) :
    octEdgeStart m F = bulkPatchVertex m (bulkEdgeStartIndex F) := by
  unfold octEdgeStart octVertexForFaces bulkEdgeStartIndex bulkPatchVertex
  split_ifs <;> rfl

theorem bulkVertexReanchor_forwardStep (m M : ℕ) (v : Fin 6) (a b : Fin 4) (p : Site) :
    bulkReanchorSite m M v (edgeForwardStep a b p) = edgeForwardStep a b (bulkReanchorSite m M v p) := by
  have hA := bulkReanchor_inA_iff m M v p
  by_cases hpA : InASublattice p.val
  · have hs : edgeForwardStep a b p = step p a := by rw [edgeForwardStep, if_pos hpA]
    have ht : edgeForwardStep a b (bulkReanchorSite m M v p) = step (bulkReanchorSite m M v p) a := by
      rw [edgeForwardStep, if_pos (hA.mpr hpA)]
    rw [hs, ht, bulkReanchorSite_step]
  · have hs : edgeForwardStep a b p = step p b := by rw [edgeForwardStep, if_neg hpA]
    have ht : edgeForwardStep a b (bulkReanchorSite m M v p) = step (bulkReanchorSite m M v p) b := by
      rw [edgeForwardStep, if_neg (fun h => hpA (hA.mp h))]
    rw [hs, ht, bulkReanchorSite_step]

theorem bulkVertexReanchor_edgeZigzag (m M : ℕ) (F : OctEdgeFrame) (r : ℕ) :
    bulkReanchorSite m M (bulkEdgeStartIndex F) (octEdgeZigzag m F r) = octEdgeZigzag M F r := by
  induction r with
  | zero =>
    change bulkReanchorSite m M (bulkEdgeStartIndex F) (octEdgeStart m F) = octEdgeStart M F
    rw [bulkEdgeStart_eq_patchVertex, bulkEdgeStart_eq_patchVertex]
    apply Subtype.ext
    funext k
    rw [bulkReanchorSite_coordinates]
    omega
  | succ r ih =>
    change bulkReanchorSite m M (bulkEdgeStartIndex F)
      (edgeForwardStep F.a F.b (octEdgeZigzag m F r)) = edgeForwardStep F.a F.b (octEdgeZigzag M F r)
    rw [bulkVertexReanchor_forwardStep, ih]

theorem bulkVertexReanchor_candidate (m M : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (hM : 1 ≤ M) :
    bulkReanchorSite m M (bulkEdgeStartIndex F) (bulkEdgeCandidate m F t odd d hm) =
      bulkEdgeCandidate M F t odd d hM := by
  cases odd <;> simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor,
    bulkReanchorSite_step, bulkVertexReanchor_edgeZigzag]

theorem bulkEdgeZigzag_in_start_box (m : ℕ) (F : OctEdgeFrame) (r : ℕ) :
    InBulkVertexBox m (bulkEdgeStartIndex F) r (octEdgeZigzag m F r) := by
  induction r with
  | zero =>
    intro k
    change |(octEdgeStart m F).val k - (bulkPatchVertex m (bulkEdgeStartIndex F)).val k| ≤ (0 : ℤ)
    rw [bulkEdgeStart_eq_patchVertex]
    simp
  | succ r ih => exact bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) r ih (octEdgeZigzag_adj m F r)

theorem bulkNearEdgeCandidate_in_start_box (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : t ≤ 9) : InBulkVertexBox m (bulkEdgeStartIndex F) 20 (bulkEdgeCandidate m F t odd d hm) := by
  have hb := bulkEdgeZigzag_in_start_box m F (2 * t)
  cases odd
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulkVertexBox_mono m (bulkEdgeStartIndex F) (by omega)
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) (2 * t) hb (step_adj _ d))
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulkVertexBox_mono m (bulkEdgeStartIndex F) (by omega)
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) (2 * t + 1)
        (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) (2 * t) hb (step_adj _ F.a)) (step_adj _ d))

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkNearEdgeGeometry

/-! Reversing edge orientation turns every near-end case into a near-start case. -/

namespace ProteinFolding.Tetrahedral

def bulkReverseEdgeFrame (F : OctEdgeFrame) : OctEdgeFrame :=
  ⟨F.k, F.j, F.b, F.a, F.kj, F.kb, F.ka, F.jb, F.ja, Ne.symm F.ab⟩

theorem bulkEdgeAnchor_reverse {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) (ht : t < m) :
    bulkEdgeAnchor m F t = bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 1 - t) := by
  have hOld := bulkEdgeAnchor_faces hm F t
  have hNew :
      tetraCoordinate m (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 1 - t)).val F.k = octRadius m ∧
      tetraCoordinate m (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 1 - t)).val F.j = -octRadius m ∧
      tetraCoordinate m (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 1 - t)).val F.b =
        -octRadius m + 4 * ((m - 1 - t : ℕ) : ℤ) ∧
      tetraCoordinate m (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 1 - t)).val F.a =
        octRadius m - 4 * ((m - 1 - t : ℕ) : ℤ) :=
    bulkEdgeAnchor_faces hm (bulkReverseEdgeFrame F) (m - 1 - t)
  have hindex : ((m - 1 - t : ℕ) : ℤ) + t = (m : ℤ) - 1 := by omega
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext i
  rcases F.index_cases i with rfl | rfl | rfl | rfl
  · exact hOld.1.trans hNew.1.symm
  · exact hOld.2.1.trans hNew.2.1.symm
  · have ho := hOld.2.2.1
    have hn := hNew.2.2.2
    dsimp [octRadius] at ho hn
    omega
  · have ho := hOld.2.2.2
    have hn := hNew.2.2.1
    dsimp [octRadius] at ho hn
    omega

theorem bulkEdgeAnchor_next (m : ℕ) (F : OctEdgeFrame) (t : ℕ) :
    step (bulkEdgeAnchor m F t) F.a = octEdgeZigzag m F (2 * t + 1) := by
  change step (bulkEdgeAnchor m F t) F.a = edgeForwardStep F.a F.b (bulkEdgeAnchor m F t)
  rw [edgeForwardStep, if_pos (bulkEdgeAnchor_inA m F t)]

theorem bulkEdgeAnchor_odd_reverse {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) (ht : t + 2 ≤ m) :
    step (bulkEdgeAnchor m F t) F.a =
      step (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 2 - t)) (bulkReverseEdgeFrame F).a := by
  have hOld :
      tetraCoordinate m (step (bulkEdgeAnchor m F t) F.a).val F.k = octRadius m - 1 ∧
      tetraCoordinate m (step (bulkEdgeAnchor m F t) F.a).val F.j = -octRadius m - 1 ∧
      tetraCoordinate m (step (bulkEdgeAnchor m F t) F.a).val F.a = -octRadius m + 3 + 4 * (t : ℤ) ∧
      tetraCoordinate m (step (bulkEdgeAnchor m F t) F.a).val F.b = octRadius m - 1 - 4 * (t : ℤ) := by
    simpa only [bulkEdgeAnchor_next, octRadius] using (octEdgeZigzag_odd hm F t).2
  have hNew :
      tetraCoordinate m (step (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 2 - t)) (bulkReverseEdgeFrame F).a).val F.k = octRadius m - 1 ∧
      tetraCoordinate m (step (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 2 - t)) (bulkReverseEdgeFrame F).a).val F.j = -octRadius m - 1 ∧
      tetraCoordinate m (step (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 2 - t)) (bulkReverseEdgeFrame F).a).val F.b =
        -octRadius m + 3 + 4 * ((m - 2 - t : ℕ) : ℤ) ∧
      tetraCoordinate m (step (bulkEdgeAnchor m (bulkReverseEdgeFrame F) (m - 2 - t)) (bulkReverseEdgeFrame F).a).val F.a =
        octRadius m - 1 - 4 * ((m - 2 - t : ℕ) : ℤ) := by
    simpa only [bulkEdgeAnchor_next, octRadius] using (octEdgeZigzag_odd hm (bulkReverseEdgeFrame F) (m - 2 - t)).2
  have hindex : ((m - 2 - t : ℕ) : ℤ) + t = (m : ℤ) - 2 := by omega
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext i
  rcases F.index_cases i with rfl | rfl | rfl | rfl
  · exact hOld.1.trans hNew.1.symm
  · exact hOld.2.1.trans hNew.2.1.symm
  · have ho := hOld.2.2.1
    have hn := hNew.2.2.2
    dsimp [octRadius] at ho hn
    omega
  · have ho := hOld.2.2.2
    have hn := hNew.2.2.1
    dsimp [octRadius] at ho hn
    omega

theorem bulkEdgeCandidate_reverse_even {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (ht : t < m) (d : Fin 4) :
    bulkEdgeCandidate m F t false d hm = bulkEdgeCandidate m (bulkReverseEdgeFrame F) (m - 1 - t) false d hm := by
  simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
  rw [bulkEdgeAnchor_reverse hm F t ht]

theorem bulkEdgeCandidate_reverse_odd {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (ht : t + 2 ≤ m) (d : Fin 4) :
    bulkEdgeCandidate m F t true d hm = bulkEdgeCandidate m (bulkReverseEdgeFrame F) (m - 2 - t) true d hm := by
  simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
  rw [bulkEdgeAnchor_odd_reverse hm F t ht]

end ProteinFolding.Tetrahedral

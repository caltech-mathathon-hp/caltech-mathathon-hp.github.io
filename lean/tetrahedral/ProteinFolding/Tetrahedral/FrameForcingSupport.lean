import ProteinFolding.Tetrahedral.FrameForcingDistinct
import ProteinFolding.Tetrahedral.BulkMerges

/-! The actual frame H support is an edge subset of the claimed exact size. -/

namespace ProteinFolding.Tetrahedral

def OctWordPath.toFold {m : ℕ} {word : Sequence} (P : OctWordPath m word) :
    Fold tetrahedralLattice word.length where
  pos i := P.site i.val
  injective_pos := by
    intro i j heq
    apply Fin.ext
    exact P.injective i.val i.isLt j.val j.isLt heq
  consecutive := by
    intro i j hij
    have h := P.adjacent i.val (by omega)
    simpa only [hij] using h

theorem OctWordPath.Hsupport_subset_oct {m : ℕ} {word : Sequence} (P : OctWordPath m word) :
    hSupport word P.toFold ⊆ octahedron m := by
  intro x hx
  obtain ⟨i, hH, rfl⟩ := (mem_hSupport word P.toFold x).mp hx
  exact P.H_mem i.val i.isLt (List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩)

theorem OctWordPath.Hsupport_subset_range {m : ℕ} {word : Sequence} (P : OctWordPath m word) :
    hSupport word P.toFold ⊆ (Finset.range word.length).image P.site := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := (mem_hSupport word P.toFold x).mp hx
  exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩

theorem OctWordPath.Hsupport_subset_of_letters {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (T : Finset Site) (hletters : ∀ i, word[i]? = some .H → P.site i ∈ T) :
    hSupport word P.toFold ⊆ T := by
  intro x hx
  obtain ⟨i, hH, rfl⟩ := (mem_hSupport word P.toFold x).mp hx
  exact hletters i.val (List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩)

theorem OctWordPath.Hsupport_subset_filter {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (T : Finset Site) (pred : Site → Prop) [DecidablePred pred]
    (hT : hSupport word P.toFold ⊆ T)
    (hpred : ∀ i, word[i]? = some .H → pred (P.site i)) :
    hSupport word P.toFold ⊆ T.filter pred := by
  intro x hx
  obtain ⟨i, hH, heq⟩ := (mem_hSupport word P.toFold x).mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hT hx, ?_⟩
  rw [← heq]
  exact hpred i.val (List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩)

theorem frameGapWord_H_converse (gaps : List ℕ) (i : ℕ)
    (hH : (frameGapWord gaps)[i]? = some .H) :
    ∃ j ≤ gaps.length, i = frameHOffset gaps j := by
  induction gaps generalizing i with
  | nil =>
    cases i with
    | zero => exact ⟨0, le_rfl, rfl⟩
    | succ i => simp [frameGapWord, frameGapTail] at hH
  | cons k gaps ih =>
    cases i with
    | zero => exact ⟨0, by simp, (frameHOffset_zero _).symm⟩
    | succ i =>
      rw [frameGapWord_cons, List.getElem?_cons_succ] at hH
      by_cases hi : i < k
      · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_replicate_of_lt hi] at hH
        cases hH
      · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)] at hH
        simp only [List.length_replicate] at hH
        obtain ⟨j, hj, hindex⟩ := ih (i - k) hH
        refine ⟨j + 1, by simp only [List.length_cons]; omega, ?_⟩
        rw [frameHOffset_cons_succ]
        omega

theorem capWord_H_converse (word : Sequence) (i : ℕ)
    (hH : (capWord word)[i]? = some .H) :
    ∃ j < word.length, i = j + 1 ∧ word[j]? = some .H := by
  cases i with
  | zero => simp [capWord] at hH
  | succ i =>
    rw [capWord, List.getElem?_cons_succ] at hH
    by_cases hi : i < word.length
    · rw [List.getElem?_append_left hi] at hH
      exact ⟨i, hi, rfl, hH⟩
    · rw [List.getElem?_append_right (by omega)] at hH
      cases hindex : i - word.length with
      | zero => simp [hindex] at hH
      | succ n => simp [hindex] at hH

theorem octEdgeZigzag_index_lt_of_mem (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hmem : octEdgeZigzag m F r ∈ octahedron m) : r < 2 * m - 1 := by
  have h := (octEdgeHeight4_bounds m F.a F.b hmem).2
  rw [octEdgeZigzag_height hm F] at h
  dsimp [octRadius] at h
  omega

theorem sum_map_take_le {α : Type*} (f : α → ℕ) (xs : List α) (j : ℕ) :
    ((xs.take j).map f).sum ≤ (xs.map f).sum := by
  have h : ((xs.take j).map f).sum + ((xs.drop j).map f).sum = (xs.map f).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  omega

theorem bulkDeletedEdges_mem_iff (m : ℕ) (x : Site) :
    x ∈ bulkDeletedEdges m ↔ x ∈ octahedron m ∧ bulkOnDeletedEdge m x := by
  simp only [bulkDeletedEdges, Finset.mem_filter]

namespace ConstructionParameters

theorem frame_word_H_cases (p : ConstructionParameters) (i : ℕ)
    (hH : p.frameWord[i]? = some .H) :
    (∃ j ≤ p.frameGaps1.length, i = 1 + frameHOffset p.frameGaps1 j) ∨
      (∃ j ≤ p.frameGaps2.length, i = p.framePart1.length + frameHOffset p.frameGaps2 j) := by
  rw [p.frameWord_eq_cap] at hH
  obtain ⟨j, hj, hi, hH⟩ := capWord_H_converse _ i hH
  by_cases hfirst : j < p.framePart1.length
  · rw [List.getElem?_append_left hfirst, p.framePart1_eq_gapWord] at hH
    obtain ⟨r, hr, hindex⟩ := frameGapWord_H_converse p.frameGaps1 j hH
    exact Or.inl ⟨r, hr, by omega⟩
  · rw [List.getElem?_append_right (by omega)] at hH
    have hH' : (frameGapWord p.frameGaps2)[j - p.framePart1.length + 1]? = some .H := by
      rw [frameGapWord, ← p.framePart2_eq_gapTail, List.getElem?_cons_succ]
      exact hH
    obtain ⟨r, hr, hindex⟩ := frameGapWord_H_converse p.frameGaps2 _ hH'
    exact Or.inr ⟨r, hr, by omega⟩

theorem frame_Hsupport_card_add (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    (hSupport p.frameWord P.toFold).card + 8 * p.bins + 16 = 4 * p.side := by
  rw [hSupport_card]
  exact p.frameWord_count

theorem frame_H_letter_edge_predicate (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (i : ℕ) (hH : p.frameWord[i]? = some .H) : bulkOnDeletedEdge p.side (P.site i) := by
  obtain ⟨F₁, F₂, _, _, _, hf₁, hf₂⟩ := p.frame_word_forced_edges P
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rcases p.frame_word_H_cases i hH with ⟨j, hj, hij⟩ | ⟨j, hj, hij⟩
  · have hsite : P.site i = octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum) := by
      rw [hij]
      exact hf₁ j hj
    refine ⟨F₁.k, F₁.j, F₁.kj, ?_⟩
    change OctEdgeSite p.side F₁.k F₁.j (P.site i)
    rw [hsite]
    apply octEdgeZigzag_mem hm F₁
    have h := sum_map_take_le frameGapAdvance p.frameGaps1 j
    rw [p.frameGaps1_budget] at h
    omega
  · have hsite : P.site i = octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum) := by
      rw [hij]
      exact hf₂ j hj
    refine ⟨F₂.k, F₂.j, F₂.kj, ?_⟩
    change OctEdgeSite p.side F₂.k F₂.j (P.site i)
    rw [hsite]
    apply octEdgeZigzag_mem hm F₂
    have h := sum_map_take_le frameGapAdvance p.frameGaps2 j
    rw [p.frameGaps2_budget] at h
    omega

theorem frame_Hsupport_subset_edges (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    hSupport p.frameWord P.toFold ⊆ bulkDeletedEdges p.side :=
  P.Hsupport_subset_filter (octahedron p.side) (bulkOnDeletedEdge p.side)
    P.Hsupport_subset_oct (p.frame_H_letter_edge_predicate P)

end ConstructionParameters

end ProteinFolding.Tetrahedral

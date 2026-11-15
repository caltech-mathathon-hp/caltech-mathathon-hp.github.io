import ProteinFolding.Tetrahedral.FrameForcingSupport

/-! Exactly three octahedral vertices belong to the forced frame H support. -/

namespace ProteinFolding.Tetrahedral

theorem OctWordPath.site_mem_Hsupport {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (i : ℕ) (hH : word[i]? = some .H) : P.site i ∈ hSupport word P.toFold := by
  obtain ⟨hi, hH⟩ := List.getElem?_eq_some_iff.mp hH
  exact H_position_in_hSupport word P.toFold ⟨i, hi⟩ hH

theorem octEdgeEnd_mem_vertices (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m F (2 * m - 2) ∈ octVertices m := by
  have hindex : 2 * (m - 1) = 2 * m - 2 := by omega
  have hpA : InASublattice (octEdgeZigzag m F (2 * m - 2)).val := by
    simpa only [hindex] using (octEdgeZigzag_even hm F (m - 1)).1
  have hp := (octEdgeSite_surface m (octEdgeZigzag_mem hm F (by omega : 2 * m - 2 < 2 * m - 1))).1
  have hfaces := octEdgeEnd_faces m hm F
  exact two_big_faces_mem_octVertices m hpA hp F.ka hfaces.1 hfaces.2.2.1

theorem octEdgeSite_vertex_endpoints (m : ℕ) (hm : 2 ≤ m) (F : OctEdgeFrame) (p : Site)
    (hpEdge : OctEdgeSite m F.k F.j p) (hpVertex : p ∈ octVertices m) :
    p = octEdgeStart m F ∨ p = octEdgeZigzag m F (2 * m - 2) := by
  have hm1 : 1 ≤ m := by omega
  have hpA := octVertices_inA hpVertex
  have hp := (octEdgeSite_surface m hpEdge).1
  have hRpos : 0 < octRadius m := by dsimp [octRadius]; omega
  have hk : tetraCoordinate m p.val F.k = octRadius m := by
    rcases hpEdge with h | h
    · exact h.1.2.2
    · exact (sublattices_disjoint _ hpA h.1.2.1).elim
  have hj : tetraCoordinate m p.val F.j = -octRadius m := by
    rcases hpEdge with h | h
    · exact h.2
    · exact (sublattices_disjoint _ hpA h.1.2.1).elim
  have hc := (two_dangling_iff_vertex hm hp).mpr hpVertex
  rw [octDanglingDirections_A m hpA hp] at hc
  obtain ⟨d, hd, hdk⟩ := Finset.exists_mem_ne (show 1 <
    (Finset.univ.filter (fun d : Fin 4 => tetraCoordinate m p.val d = octRadius m)).card by omega) F.k
  have hface := (Finset.mem_filter.mp hd).2
  have hsum := tetraCoordinate_sum_frame m F p.val
  rcases F.index_cases d with hd | hd | hd | hd
  · exact (hdk hd).elim
  · rw [hd] at hface
    omega
  · right
    rw [hd] at hface
    have hb : tetraCoordinate m p.val F.b = -octRadius m := by omega
    have hs := octEdgeEnd_faces m hm1 F
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext q
    rcases F.index_cases q with hq | hq | hq | hq
    · rw [hq]; exact hk.trans hs.1.symm
    · rw [hq]; exact hj.trans hs.2.1.symm
    · rw [hq]; exact hface.trans hs.2.2.1.symm
    · rw [hq]; exact hb.trans hs.2.2.2.symm
  · left
    rw [hd] at hface
    have ha : tetraCoordinate m p.val F.a = -octRadius m := by omega
    have hs := octEdgeStart_spec hm1 F
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext q
    rcases F.index_cases q with hq | hq | hq | hq
    · rw [hq]; exact hk.trans hs.2.1.symm
    · rw [hq]; exact hj.trans hs.2.2.1.symm
    · rw [hq]; exact ha.trans hs.2.2.2.1.symm
    · rw [hq]; exact hface.trans hs.2.2.2.2.symm

theorem octEdgeZigzag_vertex_endpoints (m : ℕ) (hm : 2 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hv : octEdgeZigzag m F r ∈ octVertices m) :
    octEdgeZigzag m F r = octEdgeStart m F ∨
      octEdgeZigzag m F r = octEdgeZigzag m F (2 * m - 2) := by
  have hm1 : 1 ≤ m := by omega
  have hp := octVertices_subset_octahedron hm1 hv
  exact octEdgeSite_vertex_endpoints m hm F _
    (octEdgeZigzag_mem hm1 F (octEdgeZigzag_index_lt_of_mem m hm1 F r hp)) hv

namespace ConstructionParameters

theorem frameEnd_index (p : ConstructionParameters) :
    p.frameWord.length - 2 = p.framePart1.length + frameHOffset p.frameGaps2 p.frameGaps2.length := by
  have hlen := frameGapWord_length p.frameGaps2
  have hword : frameGapWord p.frameGaps2 = .H :: p.framePart2 := by
    rw [frameGapWord, ← p.framePart2_eq_gapTail]
  rw [hword, List.length_cons] at hlen
  simp only [frameWord, List.length_append, List.length_cons, List.length_nil]
  omega

theorem frameWord_final_H (p : ConstructionParameters) :
    p.frameWord[p.frameWord.length - 2]? = some .H := by
  rw [p.frameEnd_index]
  exact p.frameWord_gap2_H p.frameGaps2.length le_rfl

def frameVertexSites (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) : Finset Site :=
  {P.site 1, P.site p.framePart1.length, P.site (p.frameWord.length - 2)}

theorem frameVertexSites_card (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    (p.frameVertexSites P).card = 3 := by
  have hmid := p.framePart1_length_ge_five
  have hspan := p.frame_middle_span_bound
  have hab : P.site 1 ≠ P.site p.framePart1.length := by
    intro h
    have h' := P.injective 1 (by omega) _ (by omega) h
    omega
  have hac : P.site 1 ≠ P.site (p.frameWord.length - 2) := by
    intro h
    have h' := P.injective 1 (by omega) _ (by omega) h
    omega
  have hbc : P.site p.framePart1.length ≠ P.site (p.frameWord.length - 2) := by
    intro h
    have h' := P.injective _ (by omega) _ (by omega) h
    omega
  simp [frameVertexSites, hab, hac, hbc]

theorem frame_Hsupport_inter_vertices (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    hSupport p.frameWord P.toFold ∩ octVertices p.side = p.frameVertexSites P := by
  obtain ⟨F₁, F₂, hs, he, hs₂, hf₁, hf₂⟩ := p.frame_word_forced_edges P
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  have hm1 : 1 ≤ p.side := by omega
  have he₂ : P.site (p.frameWord.length - 2) = octEdgeZigzag p.side F₂ (2 * p.side - 2) := by
    have h := hf₂ p.frameGaps2.length le_rfl
    rw [List.take_length, p.frameGaps2_budget] at h
    simpa only [← p.frameEnd_index] using h
  have hA : P.site 1 ∈ hSupport p.frameWord P.toFold ∩ octVertices p.side := by
    apply Finset.mem_inter.mpr
    constructor
    · apply P.site_mem_Hsupport
      simpa only [frameHOffset_zero, Nat.add_zero] using p.frameWord_gap1_H 0 (by omega)
    · rw [hs]
      exact octVertexForFaces_mem p.side F₁.k F₁.b
  have hB : P.site p.framePart1.length ∈ hSupport p.frameWord P.toFold ∩ octVertices p.side := by
    apply Finset.mem_inter.mpr
    constructor
    · exact P.site_mem_Hsupport _ p.frameWord_middle_H
    · rw [hs₂]
      exact octVertexForFaces_mem p.side F₂.k F₂.b
  have hC : P.site (p.frameWord.length - 2) ∈ hSupport p.frameWord P.toFold ∩ octVertices p.side := by
    apply Finset.mem_inter.mpr
    exact ⟨P.site_mem_Hsupport _ p.frameWord_final_H, by rw [he₂]; exact octEdgeEnd_mem_vertices _ hm1 F₂⟩
  apply Finset.Subset.antisymm
  · intro x hx
    have hx' := Finset.mem_inter.mp hx
    obtain ⟨i, hH, rfl⟩ := (mem_hSupport p.frameWord P.toFold x).mp hx'.1
    have hH' : p.frameWord[i.val]? = some .H := List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩
    rcases p.frame_word_H_cases i.val hH' with ⟨j, hj, hi⟩ | ⟨j, hj, hi⟩
    · have hsite : P.site i.val = octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum) := by
        rw [hi]; exact hf₁ j hj
      have hv : octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum) ∈ octVertices p.side := by
        rw [← hsite]; exact hx'.2
      rcases octEdgeZigzag_vertex_endpoints p.side hm F₁ _ hv with h | h
      · have heq := hsite.trans (h.trans hs.symm)
        simp [frameVertexSites, OctWordPath.toFold, heq]
      · have heq := hsite.trans (h.trans he.symm)
        simp [frameVertexSites, OctWordPath.toFold, heq]
    · have hsite : P.site i.val = octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum) := by
        rw [hi]; exact hf₂ j hj
      have hv : octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum) ∈ octVertices p.side := by
        rw [← hsite]; exact hx'.2
      rcases octEdgeZigzag_vertex_endpoints p.side hm F₂ _ hv with h | h
      · have heq := hsite.trans (h.trans hs₂.symm)
        simp [frameVertexSites, OctWordPath.toFold, heq]
      · have heq := hsite.trans (h.trans he₂.symm)
        simp [frameVertexSites, OctWordPath.toFold, heq]
  · intro x hx
    simp only [frameVertexSites, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC

theorem frame_Hsupport_inter_vertices_card (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    (hSupport p.frameWord P.toFold ∩ octVertices p.side).card = 3 := by
  rw [p.frame_Hsupport_inter_vertices P, p.frameVertexSites_card]

end ConstructionParameters

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FrameForcingGaps
import ProteinFolding.Tetrahedral.VertexDirections

/-! A full-budget frame chain between distinct vertices is forced onto one edge.
Antipodal endpoints are included in the hypotheses and excluded by the conclusion. -/

namespace ProteinFolding.Tetrahedral

theorem frameChain_between_vertices (m : ℕ) (hm : 2 ≤ m) (gaps : List ℕ)
    (site : ℕ → Site) (hallow : ∀ k ∈ gaps, FrameGapAllowed k)
    (hchain : OctFrameChain m gaps site)
    (hstart : site 0 ∈ octVertices m) (hend : site gaps.length ∈ octVertices m)
    (hne : site 0 ≠ site gaps.length)
    (hbudget : (gaps.map frameGapAdvance).sum = 2 * m - 2) :
    ∃ F : OctEdgeFrame, site 0 = octEdgeStart m F ∧
      (∀ j ≤ gaps.length, site j = octEdgeZigzag m F
        (((gaps.take j).map frameGapAdvance).sum)) ∧
      site gaps.length = octEdgeZigzag m F (2 * m - 2) := by
  obtain ⟨F, hs, he⟩ := distinct_vertices_edge_frame m hm hstart hend hne
  have hm1 : 1 ≤ m := by omega
  have hs0 : site 0 = octEdgeZigzag m F 0 := hs
  have hsheight := octEdgeZigzag_height hm1 F 0
  rw [← hs0] at hsheight
  have hheight : octEdgeHeight4 m F.a F.b (site gaps.length) -
      octEdgeHeight4 m F.a F.b (site 0) =
      4 * (((gaps.map frameGapAdvance).sum : ℕ) : ℤ) := by
    rw [hbudget]
    dsimp [octRadius] at he hsheight
    omega
  have hforced := frameChain_saturated_on_edge m hm1 gaps site hallow hchain F 0
    (by omega) hs0 hheight
  refine ⟨F, hs, ?_, ?_⟩
  · intro j hj
    simpa only [Nat.zero_add] using (hforced j hj).2
  · have h := (hforced gaps.length le_rfl).2
    simpa only [List.take_length, hbudget, Nat.zero_add] using h

end ProteinFolding.Tetrahedral

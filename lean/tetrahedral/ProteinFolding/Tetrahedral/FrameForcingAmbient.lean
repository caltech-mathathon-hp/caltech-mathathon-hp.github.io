import ProteinFolding.Tetrahedral.FrameForcingFrameVertices
import ProteinFolding.Tetrahedral.FrameForcingDimerAvoid
import ProteinFolding.Tetrahedral.FrameForcingMatchingGraph
import ProteinFolding.Tetrahedral.BulkEdgeCount
import ProteinFolding.Tetrahedral.BulkSurfaceDegree

/-! Exactly 2D+1 edge sites remain after the frame and the six vertices.
The actual D dimer pairs fill every isolated even subset of these sites. -/

namespace ProteinFolding.Tetrahedral

theorem foldDimerPairs_subset_edges (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) :
    (foldDimerPairs S f).covered ⊆ bulkDeletedEdges m := by
  intro x hx
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, t, hkt, hleft, hright⟩ := foldDimerPairs_on_edge S f m hsupport a
  cases b with
  | false => exact Finset.mem_filter.mpr ⟨(octEdgeSite_surface m hleft).1, k, t, hkt, hleft⟩
  | true => exact Finset.mem_filter.mpr ⟨(octEdgeSite_surface m hright).1, k, t, hkt, hright⟩

namespace ConstructionParameters

def frameRemainingEdges (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) : Finset Site :=
  bulkDeletedEdges p.side \ (hSupport p.frameWord P.toFold ∪ octVertices p.side)

theorem frameRemainingEdges_card (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    (p.frameRemainingEdges P).card = 2 * p.reductionDimerCount + 1 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hsub : hSupport p.frameWord P.toFold ∪ octVertices p.side ⊆ bulkDeletedEdges p.side :=
    Finset.union_subset (p.frame_Hsupport_subset_edges P) (octVertices_subset_bulkDeleted (by omega))
  have hrest := Finset.card_sdiff_add_card_eq_card hsub
  change (p.frameRemainingEdges P).card + (hSupport p.frameWord P.toFold ∪ octVertices p.side).card =
    (bulkDeletedEdges p.side).card at hrest
  have hunion := Finset.card_union_add_card_inter (hSupport p.frameWord P.toFold) (octVertices p.side)
  rw [p.frame_Hsupport_inter_vertices_card P, octVertices_card (by omega : 2 ≤ p.side)] at hunion
  have hedge := bulkDeletedEdges_card_add hm
  have hframe := p.frame_Hsupport_card_add P
  unfold reductionDimerCount
  omega

theorem actual_dimers_subset_remaining (p : ConstructionParameters) (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (hsupport : hSupport S f = octahedron p.side)
    (hvertices : (phpIndices S).image f.pos = octVertices p.side) (pre post : Sequence)
    (heq : S = pre ++ p.frameWord ++ post) :
    (foldDimerPairs S f).covered ⊆ p.frameRemainingEdges
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq) := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq
  have hcapEq : S = pre ++ capWord (p.framePart1 ++ p.framePart2) ++ post := by
    rw [← p.frameWord_eq_cap]
    exact heq
  have hzero : dimerStartCount (capWord (p.framePart1 ++ p.framePart2)) = 0 := by
    rw [← p.frameWord_eq_cap, p.frameWord_dimerStartCount]
  have havoid := foldDimerPairs_avoid_capped_occurrence S f pre (p.framePart1 ++ p.framePart2) post hcapEq hzero
  have havoidFull : Disjoint (foldDimerPairs S f).covered ((Finset.range p.frameWord.length).image P.site) := by
    simpa only [← p.frameWord_eq_cap] using havoid
  have havoidVertices := foldDimerPairs_avoid_vertices S f p.side hvertices
  exact subset_sdiff_union_of_disjoint _ _ _ _
    (foldDimerPairs_subset_edges S f p.side hsupport)
    (havoidFull.mono_right P.Hsupport_subset_range) havoidVertices

/-- This applies in either frame incidence, before the first monomer is pinned.
Only isolation and even cardinality remain to be checked for a concrete slot. -/
theorem reductionWord_even_component_covered (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (W : Finset Site)
    (hW : W ⊆ p.frameRemainingEdges (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq))
    (hEven : W.card % 2 = 0)
    (hclosed : ∀ x ∈ W, ∀ y ∈ p.frameRemainingEdges
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq),
      tetrahedralLattice.Adj x y → y ∈ W) :
    W ⊆ (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered := by
  let S := p.reductionWord items bulkLengths gaps
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq
  let F := foldDimerPairs S f
  have hsub := p.actual_dimers_subset_remaining S f hsupport hvertices pre post heq
  have hD : Fintype.card (DimerOccurrence S) = p.reductionDimerCount := by
    rw [Fintype.card_coe, dimerStartIndices_card]
    exact p.reductionWord_dimerStartCount items bulkLengths gaps htotal hbulk
  exact F.even_component_fully_covered_of_graph (p.frameRemainingEdges P) W hsub
    (by rw [p.frameRemainingEdges_card P, hD]) hW hEven (foldDimerPairs_adjacent S f) hclosed

end ConstructionParameters

end ProteinFolding.Tetrahedral

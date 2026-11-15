import ProteinFolding.Tetrahedral.FrameForcingMatching
import ProteinFolding.Tetrahedral.Geometry

/-! Predicate-first matching consumers for actual geometric finite sets. -/

namespace ProteinFolding.Tetrahedral

theorem subset_sdiff_union_of_disjoint {α : Type*} [DecidableEq α]
    (C V H W : Finset α) (hsub : C ⊆ V) (hH : Disjoint C H) (hW : Disjoint C W) :
    C ⊆ V \ (H ∪ W) := by
  intro x hx
  apply Finset.mem_sdiff.mpr
  refine ⟨hsub hx, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact Finset.disjoint_left.mp hH hx h
  · exact Finset.disjoint_left.mp hW hx h

theorem FinitePairFamily.even_component_fully_covered_of_graph {ι : Type*} [Fintype ι]
    (F : FinitePairFamily ι Site) (V W : Finset Site) (hsub : F.covered ⊆ V)
    (hcard : V.card ≤ 2 * Fintype.card ι + 1) (hWV : W ⊆ V) (hEven : W.card % 2 = 0)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (hclosed : ∀ x ∈ W, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ W) : W ⊆ F.covered := by
  apply F.even_component_fully_covered V W hsub hcard hWV hEven
  intro i
  have hleft : F.point (i, false) ∈ V := hsub (Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, rfl⟩)
  have hright : F.point (i, true) ∈ V := hsub (Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, rfl⟩)
  exact ⟨fun h => hclosed _ h _ hright (hadj i), fun h => hclosed _ h _ hleft (hadj i).symm⟩

end ProteinFolding.Tetrahedral

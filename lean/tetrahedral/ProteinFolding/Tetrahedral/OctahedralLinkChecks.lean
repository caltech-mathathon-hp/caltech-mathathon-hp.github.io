import ProteinFolding.Tetrahedral.OctahedralLinkAdvance

namespace ProteinFolding.Tetrahedral

example {m : ℕ} (L : OctExteriorLink m 4) (F : OctEdgeFrame) :
    octEdgeHeight4 m F.a F.b (L.site 4) - octEdgeHeight4 m F.a F.b (L.site 0) ≤ 8 := by
  have h := exterior_link_advance_bound (k := 3) L F.ab
  exact h

example {m : ℕ} (L : OctExteriorLink m 7) (F : OctEdgeFrame) :
    octEdgeHeight4 m F.a F.b (L.site 7) - octEdgeHeight4 m F.a F.b (L.site 0) ≤ 12 := by
  have h := exterior_even_P_link_advance_bound (k := 6) L F.ab (by decide)
  exact h

example {m : ℕ} (L : OctExteriorLink m 11) (F : OctEdgeFrame) :
    octEdgeHeight4 m F.a F.b (L.site 11) - octEdgeHeight4 m F.a F.b (L.site 0) ≤ 28 := by
  have h := exterior_even_P_link_advance_bound (k := 10) L F.ab (by decide)
  exact h

#print axioms OctExteriorLink.ofPath
#print axioms OctExteriorLink.cancellations_ge_one
#print axioms OctExteriorLink.cancellations_ge_two_odd_length
#print axioms OctExteriorLink.neutral_counts_eq_of_minimal_loss
#print axioms exterior_link_advance_bound
#print axioms exterior_even_P_link_advance_bound
#print axioms exterior_odd_P_link_maximiser_on_edge
#print axioms exterior_even_P_link_maximiser_on_edge
#print axioms exterior_odd_P_link_maximiser_index
#print axioms exterior_even_P_link_maximiser_index

end ProteinFolding.Tetrahedral

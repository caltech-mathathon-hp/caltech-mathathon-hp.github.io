import ProteinFolding.Tetrahedral.FoldRigidity
import ProteinFolding.Tetrahedral.OctahedralEdgeFacts

/-! The local dimer-forcing step in Section 7. A hydrophobic residue with
a P chain neighbour lies on the surface; a flanked HH run lies on an edge. -/

namespace ProteinFolding.Tetrahedral

theorem H_with_P_neighbour_surface (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (m : ℕ)
    (hsupport : hSupport S f = octahedron m)
    (i j : Fin S.length) (hi : S.get i = .H) (hj : S.get j = .P)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    OctSurfaceSite m (f.pos i) := by
  obtain ⟨hH, hP⟩ := HP_chain_bond_external S f m hsupport i j hi hj hij
  refine ⟨hH, ?_⟩
  rw [octDanglingDirections_card_eq_external]
  exact Finset.card_pos.mpr ⟨f.pos j, hP⟩

/-- Both endpoints of a maximal HH run occupy a common octahedral edge. -/
theorem flanked_dimer_on_edge (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m)
    (l i j r : Fin S.length) (hl : S.get l = .P) (hi : S.get i = .H)
    (hj : S.get j = .H) (hr : S.get r = .P)
    (hli : l.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hjr : j.val + 1 = r.val) :
    ∃ k t, k ≠ t ∧ OctEdgeSite m k t (f.pos i) ∧ OctEdgeSite m k t (f.pos j) := by
  have hsurfI := H_with_P_neighbour_surface S f m hsupport i l hi hl (Or.inr hli)
  have hsurfJ := H_with_P_neighbour_surface S f m hsupport j r hj hr (Or.inl hjr)
  have hadj := f.consecutive i j hij
  rcases (f.pos i).property with hpA | hpB
  · obtain ⟨k, t, hkt, hI, hJ⟩ := bonded_surface_sites_on_edge m hpA hsurfI hsurfJ hadj
    exact ⟨k, t, hkt, Or.inl hI, Or.inr hJ⟩
  · have hqA : InASublattice (f.pos j).val := by
      rcases adj_sublattices hadj with hab | hba
      · exact (sublattices_disjoint (f.pos i).val hab.1 hpB).elim
      · exact hba.2
    obtain ⟨k, t, hkt, hJ, hI⟩ :=
      bonded_surface_sites_on_edge m hqA hsurfJ hsurfI hadj.symm
    exact ⟨k, t, hkt, Or.inr hI, Or.inl hJ⟩

end ProteinFolding.Tetrahedral

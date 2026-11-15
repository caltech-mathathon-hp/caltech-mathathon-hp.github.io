import ProteinFolding.Tetrahedral.FrameForcingSeparatorCentre
import ProteinFolding.Tetrahedral.FrameForcingSupport

/-! The PHHP edge argument applies to local word occurrences, without
assuming their local H support fills the entire octahedron. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem OctWordPath.dimer_on_edge {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (i : ℕ) (hi : IsDimerStart word i) :
    ∃ k t, k ≠ t ∧ OctEdgeSite m k t (P.site (i + 1)) ∧
      OctEdgeSite m k t (P.site (i + 2)) := by
  have hbound := (List.getElem?_eq_some_iff.mp hi.2.2.2).choose
  have hI : OctSurfaceSite m (P.site (i + 1)) := by
    refine ⟨P.H_mem _ (by omega) hi.2.1, ?_⟩
    rw [octDanglingDirections_card_eq_external]
    apply Finset.card_pos.mpr
    exact ⟨P.site i, Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr
      (P.adjacent i (by omega)).symm, P.P_out i (by omega) hi.1⟩⟩
  have hJ : OctSurfaceSite m (P.site (i + 2)) := by
    refine ⟨P.H_mem _ (by omega) hi.2.2.1, ?_⟩
    rw [octDanglingDirections_card_eq_external]
    apply Finset.card_pos.mpr
    exact ⟨P.site (i + 3), Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr
      (by simpa only [Nat.add_assoc] using P.adjacent (i + 2) (by omega)),
        P.P_out _ hbound hi.2.2.2⟩⟩
  have hadj : tetrahedralLattice.Adj (P.site (i + 1)) (P.site (i + 2)) := by
    simpa only [Nat.add_assoc] using P.adjacent (i + 1) (by omega)
  rcases (P.site (i + 1)).property with hpA | hpB
  · obtain ⟨k, t, hkt, hleft, hright⟩ := bonded_surface_sites_on_edge m hpA hI hJ hadj
    exact ⟨k, t, hkt, Or.inl hleft, Or.inr hright⟩
  · have hqA : InASublattice (P.site (i + 2)).val := by
      rcases adj_sublattices hadj with h | h
      · exact (sublattices_disjoint _ h.1 hpB).elim
      · exact h.2
    obtain ⟨k, t, hkt, hright, hleft⟩ := bonded_surface_sites_on_edge m hqA hJ hI hadj.symm
    exact ⟨k, t, hkt, Or.inr hleft, Or.inl hright⟩

theorem OctWordPath.dimer_sites_deleted {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (i : ℕ) (hi : IsDimerStart word i) :
    P.site (i + 1) ∈ bulkDeletedEdges m ∧ P.site (i + 2) ∈ bulkDeletedEdges m := by
  obtain ⟨k, t, hkt, hleft, hright⟩ := P.dimer_on_edge i hi
  exact ⟨Finset.mem_filter.mpr ⟨(octEdgeSite_surface m hleft).1, k, t, hkt, hleft⟩,
    Finset.mem_filter.mpr ⟨(octEdgeSite_surface m hright).1, k, t, hkt, hright⟩⟩

theorem ConstructionParameters.separator_centre_factor (p : ConstructionParameters)
    (k : ℕ) (hk : k ≤ p.bins) :
    ∃ pre post, capWord (p.separatorWord k) = pre ++ capWord (dimerChain 2) ++ post ∧
      pre.length = p.entryTether k + 2 := by
  let c := (ReductionDimerProvenance.separatorBody p [] k hk).catalogue
  obtain ⟨i, hq, _, hp⟩ := ReductionDimerProvenance.separator_centre_offset p [] k hk
  change c.q i = 2 at hq
  change (c.pre i).length = p.entryTether k + 2 at hp
  refine ⟨c.pre i, c.post i, ?_, hp⟩
  simpa only [hq] using c.factor i

end ProteinFolding.Tetrahedral

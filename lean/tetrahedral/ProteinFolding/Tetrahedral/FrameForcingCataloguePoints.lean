import ProteinFolding.Tetrahedral.FrameForcingExitExhaustion

/-! Extract a physical anchor slot from the catalogue site-union equalities. -/

namespace ProteinFolding.Tetrahedral.DimerCatalogue

variable {α : Type} {S : Sequence}

theorem chainPairs_point_mem (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (i : c.Index) (j : Fin (c.q i)) (b : Bool) :
    (c.chainPairs f i).point (j, b) ∈ c.chainSites f i :=
  Finset.mem_image.mpr ⟨(j, b), Finset.mem_univ _, rfl⟩

theorem chain_point_in_slot {κ : Type*} [Fintype κ]
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (I : Finset c.Index) (E : κ → Finset Site)
    (heq : I.biUnion (c.chainSites f) = Finset.univ.biUnion E)
    (i : c.Index) (hi : i ∈ I) (j : Fin (c.q i)) (b : Bool) :
    ∃ k, (c.chainPairs f i).point (j, b) ∈ E k := by
  have hx : (c.chainPairs f i).point (j, b) ∈ I.biUnion (c.chainSites f) :=
    Finset.mem_biUnion.mpr ⟨i, hi, c.chainPairs_point_mem f i j b⟩
  rw [heq] at hx
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
  exact ⟨k, hk⟩

end ProteinFolding.Tetrahedral.DimerCatalogue

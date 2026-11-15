import ProteinFolding.Tetrahedral.ReductionDimerProvenanceCatalogue
import ProteinFolding.Tetrahedral.FrameForcingEntryExhaustion

/-! A catalogue partitions the actual HH sites into disjoint whole chains.
All geometric component conclusions use the actual written chain factors. -/

namespace ProteinFolding.Tetrahedral.DimerCatalogue

variable {α : Type} {S : Sequence}

def chainPairs (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length) (i : c.Index) :
    FinitePairFamily (Fin (c.q i)) Site := factorDimerPairs S f (c.pre i) (c.post i) (c.q i) (c.factor i)

def chainSites (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length) (i : c.Index) : Finset Site :=
  (c.chainPairs f i).covered

theorem chainSites_card (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length) (i : c.Index) :
    (c.chainSites f i).card = 2 * c.q i := by
  exact (c.chainPairs f i).covered_card.trans (by rw [Fintype.card_fin])

theorem chainSites_subset (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length) (i : c.Index) :
    c.chainSites f i ⊆ (foldDimerPairs S f).covered := factorDimerPairs_subset S f _ _ _ _

theorem chainSites_cover (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (x : Site) (hx : x ∈ (foldDimerPairs S f).covered) : ∃ i, x ∈ c.chainSites f i := by
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, j, heq⟩ := c.occurrence_complete a
  refine ⟨i, Finset.mem_image.mpr ⟨(j, b), Finset.mem_univ _, ?_⟩⟩
  change (foldDimerPairs S f).point (c.occurrence ⟨i, j⟩, b) = _
  rw [heq]

theorem chainSites_disjoint (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (i j : c.Index) (hij : i ≠ j) : Disjoint (c.chainSites f i) (c.chainSites f j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨d, e⟩, _, heq⟩ := Finset.mem_image.mp hy
  have hpoint : (foldDimerPairs S f).point (c.occurrence ⟨j, d⟩, e) =
      (foldDimerPairs S f).point (c.occurrence ⟨i, a⟩, b) := heq
  have hocc := congrArg Prod.fst ((foldDimerPairs S f).injective hpoint)
  have hindices := congrArg Sigma.fst (c.occurrence_injective hocc)
  exact hij hindices.symm

theorem chainSites_component (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (V W : Finset Site)
    (hsub : (foldDimerPairs S f).covered ⊆ V)
    (hclosedA : ∀ x ∈ W, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ W)
    (hclosedT : ∀ x ∈ W, ∀ y ∈ V, OctTriangularNeighbours m x y → y ∈ W)
    (i : c.Index) (hmeet : (c.chainSites f i ∩ W).Nonempty) : c.chainSites f i ⊆ W := by
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hxC
  exact (c.chainPairs f i).chain_component_all (c.q i) V W ((c.chainSites_subset f i).trans hsub)
    (fun j => foldDimerPairs_adjacent S f (factorDimerOccurrence S (c.pre i) (c.post i) (c.q i) (c.factor i) j))
    (factorDimerPairs_link S f m hsupport (c.pre i) (c.post i) (c.q i) (c.factor i))
    hclosedA hclosedT ⟨a, b, hxW⟩

end ProteinFolding.Tetrahedral.DimerCatalogue

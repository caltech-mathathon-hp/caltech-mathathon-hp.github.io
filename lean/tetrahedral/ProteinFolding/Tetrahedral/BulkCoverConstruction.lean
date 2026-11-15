import ProteinFolding.Tetrahedral.BulkMerges
import ProteinFolding.Tetrahedral.BulkPatches

/-! The finite graph actually specified by the canonical bulk-cover algorithm.
Its global path-cover properties are separate proof obligations. -/

namespace ProteinFolding.Tetrahedral

theorem bulkPatchAdded_symm (m : ℕ) {p q : Site} (h : bulkPatchAdded m p q) :
    bulkPatchAdded m q p := by
  obtain ⟨v, h | h⟩ := h
  · exact ⟨v, Or.inr h⟩
  · exact ⟨v, Or.inl h⟩

theorem bulkPatchRemoved_symm (m : ℕ) {p q : Site} (h : bulkPatchRemoved m p q) :
    bulkPatchRemoved m q p := by
  obtain ⟨v, h | h⟩ := h
  · exact ⟨v, Or.inr h⟩
  · exact ⟨v, Or.inl h⟩

def bulkMergedBond (m : ℕ) (p q : Site) : Prop :=
  (bulkRungGraph m).Adj p q ∨ bulkMerge m p q ∨ bulkMerge m q p

instance (m : ℕ) (p q : Site) : Decidable (bulkMergedBond m p q) := by
  unfold bulkMergedBond bulkRungGraph
  infer_instance

theorem bulkMergedBond_adj (m : ℕ) {p q : Site} (h : bulkMergedBond m p q) :
    tetrahedralLattice.Adj p q := by
  rcases h with h | h | h
  · exact h.1
  · exact bulkMerge_adj m h
  · exact (bulkMerge_adj m h).symm

def bulkCoverBond (m : ℕ) (p q : Site) : Prop :=
  p ∈ bulkInterior m ∧ q ∈ bulkInterior m ∧
    (bulkPatchAdded m p q ∨ (bulkMergedBond m p q ∧ ¬bulkPatchRemoved m p q))

instance (m : ℕ) (p q : Site) : Decidable (bulkCoverBond m p q) := by
  unfold bulkCoverBond bulkPatchAdded bulkPatchRemoved
  infer_instance

theorem bulkCoverBond_adj (m : ℕ) {p q : Site} (h : bulkCoverBond m p q) :
    tetrahedralLattice.Adj p q := by
  rcases h.2.2 with h | h
  · exact bulkPatchAdded_adj m h
  · exact bulkMergedBond_adj m h.1

theorem bulkCoverBond_symm (m : ℕ) {p q : Site} (h : bulkCoverBond m p q) :
    bulkCoverBond m q p := by
  refine ⟨h.2.1, h.1, ?_⟩
  rcases h.2.2 with h | ⟨h, hnot⟩
  · exact Or.inl (bulkPatchAdded_symm m h)
  · right
    refine ⟨?_, fun hrev => hnot (bulkPatchRemoved_symm m hrev)⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

def bulkCoverGraph (m : ℕ) : SimpleGraph Site where
  Adj := bulkCoverBond m
  symm := by intro p q; exact bulkCoverBond_symm m
  loopless := by intro p h; exact tetrahedralLattice.loopless p (bulkCoverBond_adj m h)

instance (m : ℕ) : DecidableRel (bulkCoverGraph m).Adj := fun p q =>
  inferInstanceAs (Decidable (bulkCoverBond m p q))

theorem bulkCoverGraph_le_lattice (m : ℕ) : bulkCoverGraph m ≤ tetrahedralLattice := by
  intro p q h
  exact bulkCoverBond_adj m h

theorem bulkCoverGraph_support (m : ℕ) {p q : Site} (h : (bulkCoverGraph m).Adj p q) :
    p ∈ bulkInterior m ∧ q ∈ bulkInterior m := ⟨h.1, h.2.1⟩

def bulkCoverNeighbours (m : ℕ) (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => (bulkCoverGraph m).Adj p q)

theorem mem_bulkCoverNeighbours (m : ℕ) (p q : Site) :
    q ∈ bulkCoverNeighbours m p ↔ (bulkCoverGraph m).Adj p q := by
  simp only [bulkCoverNeighbours, Finset.mem_filter, mem_neighbours]
  exact and_iff_right_of_imp (bulkCoverBond_adj m)

theorem bulkCoverNeighbours_finite_bound (m : ℕ) (p : Site) :
    (bulkCoverNeighbours m p).card ≤ 4 := by
  have h := Finset.card_le_card (Finset.filter_subset (fun q => (bulkCoverGraph m).Adj p q)
    (neighbours p))
  simpa only [card_neighbours] using h

end ProteinFolding.Tetrahedral

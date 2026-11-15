import ProteinFolding.Tetrahedral.BulkSegmentCertificates

/-! A computational form of segment certificates. The rho test precedes the
cover test, so checking closure never evaluates irrelevant non-rung merges.
A supplied predecessor also avoids a search through the whole support. -/

namespace ProteinFolding.Tetrahedral

def bulkQuickSegmentBond (m : ℕ) (p q : Site) : Prop :=
  bulkRho m p ≠ bulkRho m q ∧ bulkFastCoverBond m p q

instance (m : ℕ) (p q : Site) : Decidable (bulkQuickSegmentBond m p q) := by
  unfold bulkQuickSegmentBond
  infer_instance

theorem bulkQuickSegmentBond_iff (m : ℕ) (p q : Site) :
    bulkQuickSegmentBond m p q ↔ bulkFastSegmentBond m p q := and_comm

def BulkSegmentQuickCheck (m : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (prev : Site → Site) : Prop :=
  root ∈ A ∧
    (∀ p ∈ A, bulkFastInterior m p) ∧
    (∀ p ∈ A, p ≠ root →
      prev p ∈ A ∧ bulkQuickSegmentBond m p (prev p) ∧ rank (prev p) < rank p) ∧
    (∀ p ∈ A, ∀ d : Fin 4,
      bulkQuickSegmentBond m p (step p d) → step p d ∈ A)

instance (m : ℕ) (A : Finset Site) (root : Site) (rank : Site → ℕ) (prev : Site → Site) :
    Decidable (BulkSegmentQuickCheck m A root rank prev) := by
  unfold BulkSegmentQuickCheck
  infer_instance

theorem bulkSegmentQuickCheck_sound (m : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (prev : Site → Site) (h : BulkSegmentQuickCheck m A root rank prev) :
    BulkSegmentFiniteCheck m A root rank := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro p hp hne
    have hprev := h.2.2.1 p hp hne
    exact ⟨prev p, hprev.1, (bulkQuickSegmentBond_iff m p (prev p)).mp hprev.2.1, hprev.2.2⟩
  · intro p hp d hbond
    exact h.2.2.2 p hp d ((bulkQuickSegmentBond_iff m p _).mpr hbond)

end ProteinFolding.Tetrahedral

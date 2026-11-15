import ProteinFolding.Tetrahedral.BulkFastLocal
import ProteinFolding.Tetrahedral.ClosedComponentCertificate

/-! Finite certificates identify complete constant-alpha segments of the actual
canonical cover. A certificate checks the complete four-neighbour star, rather
than only the listed bonds, so no unlisted continuation can escape its support. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

def bulkSiteSegmentGraph (m : ℕ) : SimpleGraph Site where
  Adj p q := bulkCoverBond m p q ∧ bulkRho m p ≠ bulkRho m q
  symm := by intro p q h; exact ⟨bulkCoverBond_symm m h.1, Ne.symm h.2⟩
  loopless := by intro p h; exact h.2 rfl

instance (m : ℕ) : DecidableRel (bulkSiteSegmentGraph m).Adj := by
  intro p q
  unfold bulkSiteSegmentGraph
  infer_instance

def bulkFastSegmentBond (m : ℕ) (p q : Site) : Prop :=
  bulkFastCoverBond m p q ∧ bulkRho m p ≠ bulkRho m q

instance (m : ℕ) (p q : Site) : Decidable (bulkFastSegmentBond m p q) := by
  unfold bulkFastSegmentBond
  infer_instance

theorem bulkSiteSegmentGraph_fast (m : ℕ) (p q : Site) :
    (bulkSiteSegmentGraph m).Adj p q ↔ bulkFastSegmentBond m p q := by
  exact and_congr (bulkCoverBond_fast_iff m p q) Iff.rfl

def BulkSegmentFiniteCheck (m : ℕ) (A : Finset Site) (root : Site) (rank : Site → ℕ) : Prop :=
  root ∈ A ∧
    (∀ p ∈ A, bulkFastInterior m p) ∧
    (∀ p ∈ A, p ≠ root → ∃ q ∈ A, bulkFastSegmentBond m p q ∧ rank q < rank p) ∧
    (∀ p ∈ A, ∀ d : Fin 4,
      bulkFastSegmentBond m p (step p d) → step p d ∈ A)

instance (m : ℕ) (A : Finset Site) (root : Site) (rank : Site → ℕ) :
    Decidable (BulkSegmentFiniteCheck m A root rank) := by
  unfold BulkSegmentFiniteCheck
  infer_instance

theorem bulkSegmentFiniteCheck_connected (m : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A root rank) :
    ∀ p ∈ A, (bulkSiteSegmentGraph m).Reachable root p := by
  intro p hp
  have hmain : ∀ n, ∀ q ∈ A, rank q = n → (bulkSiteSegmentGraph m).Reachable root q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hq hrank
      by_cases heq : q = root
      · subst q
        exact .refl _
      · obtain ⟨r, hr, hqr, hlt⟩ := h.2.2.1 q hq heq
        have hrreach := ih (rank r) (by omega) r hr rfl
        have hAdj := (bulkSiteSegmentGraph_fast m q r).mpr hqr
        exact hrreach.trans hAdj.symm.reachable
  exact hmain (rank p) p hp rfl

theorem bulkSegmentFiniteCheck_closed (m : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A root rank) :
    ∀ p ∈ A, ∀ q, (bulkSiteSegmentGraph m).Adj p q → q ∈ A := by
  intro p hp q hpq
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp (bulkCoverBond_adj m hpq.1)
  exact h.2.2.2 p hp d ((bulkSiteSegmentGraph_fast m p _).mp hpq)

theorem bulkSegmentFiniteCheck_component (m : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A root rank) (q : Site) :
    q ∈ A ↔ (bulkSiteSegmentGraph m).Reachable root q :=
  finset_component_iff (bulkSiteSegmentGraph m) A root h.1
    (bulkSegmentFiniteCheck_closed m A root rank h)
    (bulkSegmentFiniteCheck_connected m A root rank h) q

theorem bulkSegmentFiniteCheck_transport (m M : ℕ) (A : Finset Site) (root : Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A root rank) (f : Site → Site)
    (hmap : ∀ p ∈ A, ∀ q, (bulkSiteSegmentGraph m).Adj p q →
      (bulkSiteSegmentGraph M).Adj (f p) (f q))
    (hcomplete : ∀ p ∈ A, ∀ q, (bulkSiteSegmentGraph M).Adj (f p) q →
      ∃ r, (bulkSiteSegmentGraph m).Adj p r ∧ f r = q) (q : Site) :
    q ∈ A.image f ↔ (bulkSiteSegmentGraph M).Reachable (f root) q :=
  finset_image_component_iff_of_complete_stars
    (bulkSiteSegmentGraph m) (bulkSiteSegmentGraph M) A root f h.1
    (bulkSegmentFiniteCheck_closed m A root rank h)
    (bulkSegmentFiniteCheck_connected m A root rank h) hmap hcomplete q

end ProteinFolding.Tetrahedral

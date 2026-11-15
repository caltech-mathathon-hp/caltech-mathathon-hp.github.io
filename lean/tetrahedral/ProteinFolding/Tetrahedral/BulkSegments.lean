import ProteinFolding.Tetrahedral.PathCoverExtraction
import ProteinFolding.Tetrahedral.BulkLineX
import Mathlib.Data.Prod.Lex

/-! Actual constant-alpha segments and the manuscript's lexicographic potential. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

def bulkSegmentGraph (m : ℕ) : SimpleGraph (BulkVertex m) where
  Adj p q := (bulkFiniteGraph m).Adj p q ∧ (bulkRungGraph m).Adj p.val q.val
  symm := by intro p q h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := by intro p h; exact (bulkFiniteGraph m).loopless p h.1

instance (m : ℕ) : DecidableRel (bulkSegmentGraph m).Adj := by
  intro p q
  unfold bulkSegmentGraph bulkRungGraph
  infer_instance

def bulkSegmentRungHom (m : ℕ) : bulkSegmentGraph m →g bulkRungGraph m where
  toFun := Subtype.val
  map_rel' := fun h => h.2

theorem bulkSegmentGraph_acyclic (m : ℕ) : (bulkSegmentGraph m).IsAcyclic :=
  (bulkRungGraph_acyclic m).comap (bulkSegmentRungHom m) Subtype.val_injective

theorem bulkSegmentGraph_degree_le_two (m : ℕ) (p : BulkVertex m) :
    (bulkSegmentGraph m).degree p ≤ 2 := by
  have hsub : ((bulkSegmentGraph m).neighborFinset p).image Subtype.val ⊆ bulkRungNeighbours m p.val := by
    intro q
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
    rintro ⟨r, hr, rfl⟩
    exact (bulkRungGraph_adj_iff m p.val r.val).mp hr.2
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree, bulkRungNeighbours_card] at hcard

theorem bulkSegment_reachable_rung (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) : (bulkRungGraph m).Reachable p.val q.val := by
  obtain ⟨w⟩ := h
  exact ⟨w.map (bulkSegmentRungHom m)⟩

theorem bulkSegment_alpha (m : ℕ) {p q : BulkVertex m} (h : (bulkSegmentGraph m).Reachable p q) :
    bulkAlpha m q.val = bulkAlpha m p.val := by
  obtain ⟨w⟩ := bulkSegment_reachable_rung m h
  exact bulkWalk_alpha m w

noncomputable def bulkSegmentSites (m : ℕ) (p : BulkVertex m) : Finset (BulkVertex m) := by
  classical
  exact Finset.univ.filter (fun q => (bulkSegmentGraph m).Reachable p q)

theorem mem_bulkSegmentSites (m : ℕ) (p q : BulkVertex m) :
    q ∈ bulkSegmentSites m p ↔ (bulkSegmentGraph m).Reachable p q := by
  classical
  simp only [bulkSegmentSites, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bulkSegmentSites_nonempty (m : ℕ) (p : BulkVertex m) : (bulkSegmentSites m p).Nonempty :=
  ⟨p, (mem_bulkSegmentSites m p p).mpr (.refl p)⟩

theorem bulkSegmentSites_eq_of_reachable (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) : bulkSegmentSites m p = bulkSegmentSites m q := by
  ext r
  rw [mem_bulkSegmentSites, mem_bulkSegmentSites]
  exact ⟨fun hr => h.symm.trans hr, fun hr => h.trans hr⟩

noncomputable def bulkSegmentXValues (m : ℕ) (p : BulkVertex m) : Finset ℤ :=
  (bulkSegmentSites m p).image (fun q => q.val.val 0)

theorem bulkSegmentXValues_nonempty (m : ℕ) (p : BulkVertex m) : (bulkSegmentXValues m p).Nonempty :=
  (bulkSegmentSites_nonempty m p).image _

noncomputable def bulkSegmentXhat (m : ℕ) (p : BulkVertex m) : ℤ :=
  (bulkSegmentXValues m p).min' (bulkSegmentXValues_nonempty m p) +
    (bulkSegmentXValues m p).max' (bulkSegmentXValues_nonempty m p)

def BulkRowSegment (m : ℕ) (p : BulkVertex m) : Prop :=
  ∃ q ∈ bulkSegmentSites m p, q.val ∈ bulkDamaged m ∧ bulkZ q.val = 0

abbrev BulkSegmentOrder := ℕ ×ₗ (ℤ ×ₗ ℤ)

noncomputable def bulkSegmentPotential (m : ℕ) (p : BulkVertex m) : BulkSegmentOrder := by
  classical
  exact if BulkRowSegment m p then toLex (2, toLex (|bulkSegmentXhat m p|, 0))
    else if 0 < bulkAlpha m p.val then toLex (1, toLex (bulkAlpha m p.val, bulkSegmentXhat m p))
    else toLex (0, toLex (bulkSegmentXhat m p, 0))

theorem bulkSegmentPotential_eq (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) : bulkSegmentPotential m p = bulkSegmentPotential m q := by
  have hSites := bulkSegmentSites_eq_of_reachable m h
  have hAlpha := bulkSegment_alpha m h
  have hX : bulkSegmentXhat m p = bulkSegmentXhat m q := by
    unfold bulkSegmentXhat bulkSegmentXValues
    simp only [hSites]
  have hRow : BulkRowSegment m p ↔ BulkRowSegment m q := by unfold BulkRowSegment; rw [hSites]
  have hRowEq : BulkRowSegment m p = BulkRowSegment m q := propext hRow
  unfold bulkSegmentPotential
  simp only [hAlpha, hX]
  rw [hRowEq]

theorem bulkNonrung_alpha_step (m : ℕ) {p q : Site}
    (h : tetrahedralLattice.Adj p q) (hρ : bulkRho m p = bulkRho m q) :
    bulkAlpha m q = bulkAlpha m p + 2 ∨ bulkAlpha m q = bulkAlpha m p - 2 := by
  have hd := bulk_adj_deltas m h
  have hy : bulkY m q = bulkY m p + 1 ∨ bulkY m q = bulkY m p - 1 := by omega
  have hz : bulkZ q = bulkZ p + 1 ∨ bulkZ q = bulkZ p - 1 := by omega
  have hay := abs_unit_adjacent (bulkY m p) (bulkY m q) hy
  have haz := abs_unit_adjacent (bulkZ p) (bulkZ q) hz
  unfold bulkRho at hρ
  unfold bulkAlpha
  omega

theorem bulkCover_joint_distinct_segments (m : ℕ) {p q : BulkVertex m}
    (h : (bulkFiniteGraph m).Adj p q) (hn : ¬(bulkRungGraph m).Adj p.val q.val) :
    ¬(bulkSegmentGraph m).Reachable p q := by
  intro hreach
  have hAdj := bulkCoverBond_adj m h
  have hρ : bulkRho m p.val = bulkRho m q.val := by
    by_contra hne
    exact hn ⟨hAdj, hne⟩
  have hstep := bulkNonrung_alpha_step m hAdj hρ
  have hAlpha := bulkSegment_alpha m hreach
  change bulkAlpha m q.val = bulkAlpha m p.val + 2 ∨
    bulkAlpha m q.val = bulkAlpha m p.val - 2 at hstep
  change bulkAlpha m q.val = bulkAlpha m p.val at hAlpha
  omega

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.ReductionTM2CanonicalCounts
import ProteinFolding.Tetrahedral.ReductionSoundnessPacking

/-! Packing extraction for the actual closed source-only reduction. The
remaining graph hypothesis is precisely acyclicity of its fixed bulk graph.
The forward geometric constructor needs only the displayed exact H support. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem guard_of_accepts (I : Packing.Instance) (h : (reduction I).Accepts) :
    Guard.sourceGuard I = true := by
  cases hg : Guard.sourceGuard I
  · exact False.elim (rejects_invalid I hg h)
  · rfl

theorem accepts_iff_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    (reduction I).Accepts ↔
      ∃ f : Fold tetrahedralLattice (reduction I).sequence.length,
        hSupport (reduction I).sequence f = octahedron (PackingSource.parameters I hw).side := by
  change HPStringFold (reduction I).sequence (reduction I).minBonds ↔ _
  rw [threshold_eq I hw ht]
  exact octahedral_threshold_iff_oct_support _ (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (hydrophobicCount_eq I hw ht ha)

theorem accepts_of_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (f : Fold tetrahedralLattice (reduction I).sequence.length)
    (hf : hSupport (reduction I).sequence f = octahedron (PackingSource.parameters I hw).side) :
    (reduction I).Accepts :=
  (accepts_iff_support I hw ht ha).2 ⟨f, hf⟩

theorem accepts_of_support_subset (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (f : Fold tetrahedralLattice (reduction I).sequence.length)
    (hf : hSupport (reduction I).sequence f ⊆ octahedron (PackingSource.parameters I hw).side) :
    (reduction I).Accepts := by
  apply accepts_of_support I hw ht ha f
  apply Finset.eq_of_subset_of_card_le hf
  rw [octahedron_card, hSupport_card, hydrophobicCount_eq I hw ht ha]

theorem accepts_of_prescribed_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (f : Fold tetrahedralLattice ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)).length)
    (hf : hSupport ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)) f =
        octahedron (PackingSource.parameters I hw).side) : (reduction I).Accepts := by
  have hc := hydrophobicCount_eq I hw ht ha
  rw [sequence_eq I hw ht] at hc
  change HPStringFold (reduction I).sequence (reduction I).minBonds
  rw [sequence_eq I hw ht, threshold_eq I hw ht]
  exact (octahedral_threshold_iff_oct_support _ (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) hc).2 ⟨f, hf⟩

theorem accepts_of_prescribed_support_subset (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (f : Fold tetrahedralLattice ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)).length)
    (hf : hSupport ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)) f ⊆
        octahedron (PackingSource.parameters I hw).side) : (reduction I).Accepts := by
  apply accepts_of_prescribed_support I hw ht ha f
  apply Finset.eq_of_subset_of_card_le hf
  have hc := hydrophobicCount_eq I hw ht ha
  rw [sequence_eq I hw ht] at hc
  rw [octahedron_card, hSupport_card, hc]

theorem source_of_accepts_valid (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (h : (reduction I).Accepts) : PackingSource.Accepts I := by
  change HPStringFold (reduction I).sequence (reduction I).minBonds at h
  rw [sequence_eq I hw ht, threshold_eq I hw ht] at h
  obtain ⟨parts, hparts⟩ := (PackingSource.parameters I hw).reductionWord_threshold_packing
    I.sizes (BulkScan.lengths (Raw.side (I.bins, I.capacity)))
    ((PackingSource.parameters I hw).prescribedLinkerGap I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I))
    ht hw.2.2 (bulk_mass I hw ha) (bulk_lengths_ge_three I hw ha) h
  exact ⟨hw, ht, parts, hparts⟩

theorem source_of_accepts (I : Packing.Instance)
    (ha : ∀ hw : Packing.WellFormed I, (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (h : (reduction I).Accepts) : PackingSource.Accepts I := by
  obtain ⟨hw, ht⟩ := (Guard.sourceGuard_eq_true I).1 (guard_of_accepts I h)
  exact source_of_accepts_valid I hw ht (ha hw) h

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

import ProteinFolding.Tetrahedral.NearFieldCanonicalMixedFamily
import ProteinFolding.Tetrahedral.ReductionTM2CanonicalSoundness

/-! Concrete forward construction for the closed source-only reduction. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

theorem canonical_prescribed_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    ∃ f : Fold tetrahedralLattice
      ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
        (ReductionTM2.BulkScan.lengths (PackingSource.parameters I hw).side) (ReductionTM2.Canonical.flags I)).length,
      hSupport ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
        (ReductionTM2.BulkScan.lengths (PackingSource.parameters I hw).side) (ReductionTM2.Canonical.flags I)) f =
          octahedron (PackingSource.parameters I hw).side := by
  let p := PackingSource.parameters I hw
  apply (canonicalMixedFamily I hw d ha).reduction_fold_exists
    (p.reductionUnitBodies I.sizes (ReductionTM2.BulkScan.lengths p.side)) rfl
  · exact canonicalRoutingUnits_words p I.sizes d ha
  · exact canonicalRoutingUnits_hSupport_subset_oct p I.sizes d ha
  · change hydrophobicCount (p.prescribedReductionWord I.sizes (ReductionTM2.BulkScan.lengths p.side)
      (ReductionTM2.Canonical.flags I)) = octahedralNumber p.side
    exact p.prescribedReductionWord_hydrophobicCount I.sizes _ _ ht (ReductionTM2.Canonical.bulk_mass I hw ha)

theorem canonical_accepts_of_packedBins (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    (ReductionTM2.Canonical.reduction I).Accepts := by
  obtain ⟨f, hf⟩ := canonical_prescribed_support I hw ht d ha
  exact ReductionTM2.Canonical.accepts_of_prescribed_support I hw ht ha f hf

def packedBinsOfExact (I : Packing.Instance) (hw : Packing.WellFormed I)
    (parts : List (List ℕ)) (hparts : Packing.Exact I parts) :
    PackedBins (PackingSource.parameters I hw) I.sizes where
  parts := parts
  length_eq := hparts.1
  perm := hparts.2.1
  loads := hparts.2.2
  positive := hw.2.2

theorem canonical_accepts_of_packing (I : Packing.Instance) (hI : PackingSource.Accepts I)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hI.1).side).IsAcyclic) :
    (ReductionTM2.Canonical.reduction I).Accepts := by
  obtain ⟨parts, hparts⟩ := hI.2.2
  exact canonical_accepts_of_packedBins I hI.1 hI.2.1 (packedBinsOfExact I hI.1 parts hparts) ha

end ProteinFolding.Tetrahedral.NearField

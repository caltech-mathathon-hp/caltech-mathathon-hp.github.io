import ProteinFolding.Tetrahedral.ReductionTM2Canonical
import ProteinFolding.Tetrahedral.ReductionTM2BulkScanMass

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

theorem bulk_lengths_ge_three (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (n : ℕ) (hn : n ∈ BulkScan.lengths (Raw.side (I.bins, I.capacity))) : 3 ≤ n := by
  have hm := (PackingSource.parameters I hw).side_ge
  exact BulkScan.lengths_ge_three (PackingSource.parameters I hw).side (by omega) ha n hn

theorem bulk_mass (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    24 * (PackingSource.parameters I hw).side + (BulkScan.lengths (Raw.side (I.bins, I.capacity))).sum =
      octahedralNumber (PackingSource.parameters I hw).side + 42 := by
  have hm := (PackingSource.parameters I hw).side_ge
  simpa only [Nat.add_comm] using
    BulkScan.lengths_mass (PackingSource.parameters I hw).side (by omega) ha

theorem hydrophobicCount_eq (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    hydrophobicCount (reduction I).sequence = octahedralNumber (PackingSource.parameters I hw).side := by
  rw [sequence_eq I hw ht]
  exact (PackingSource.parameters I hw).prescribedReductionWord_hydrophobicCount I.sizes _ _ ht (bulk_mass I hw ha)

theorem phpIndices_card (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    (phpIndices (reduction I).sequence).card = 6 := by
  rw [sequence_eq I hw ht]
  exact (PackingSource.parameters I hw).prescribedReductionWord_phpIndices_card I.sizes _ _
    (bulk_lengths_ge_three I hw ha)

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

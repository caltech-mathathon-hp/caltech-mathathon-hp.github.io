import ProteinFolding.Tetrahedral.ReductionTM2CanonicalActual
import ProteinFolding.Tetrahedral.ReductionTM2CanonicalSoundness

/-! Final backward correctness and forward support-to-threshold bridge after
discharging the actual graph theorem. The remaining completeness theorem
must construct the physical prescribed fold; no constructor is assumed here. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

set_option maxHeartbeats 2000000

theorem reduction_sound (I : Packing.Instance) (h : (reduction I).Accepts) : PackingSource.Accepts I :=
  source_of_accepts I (source_bulk_acyclic I) h

theorem reduction_accepts_iff_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity) :
    (reduction I).Accepts ↔ ∃ f : Fold tetrahedralLattice (reduction I).sequence.length,
      hSupport (reduction I).sequence f = octahedron (PackingSource.parameters I hw).side :=
  accepts_iff_support I hw ht (source_bulk_acyclic I hw)

theorem reduction_accepts_of_prescribed_support (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (f : Fold tetrahedralLattice ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)).length)
    (hf : hSupport ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)) f =
        octahedron (PackingSource.parameters I hw).side) : (reduction I).Accepts :=
  accepts_of_prescribed_support I hw ht (source_bulk_acyclic I hw) f hf

theorem reduction_accepts_of_prescribed_support_subset (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity)
    (f : Fold tetrahedralLattice ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)).length)
    (hf : hSupport ((PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I)) f ⊆
        octahedron (PackingSource.parameters I hw).side) : (reduction I).Accepts :=
  accepts_of_prescribed_support_subset I hw ht (source_bulk_acyclic I hw) f hf

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

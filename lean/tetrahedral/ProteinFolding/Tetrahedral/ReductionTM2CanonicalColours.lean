import ProteinFolding.Tetrahedral.ReductionTM2Canonical
import ProteinFolding.Tetrahedral.ReductionTM2ColourFlagFacts
import ProteinFolding.Tetrahedral.ReductionTM2BulkRuntimeFamily

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

set_option maxHeartbeats 2000000

noncomputable def unitColours (I : Packing.Instance) : List ColourFlags.Colours :=
  PrefixColours.nonbulk frameColours ringColours I ++ BulkScan.colours (Raw.side (I.bins, I.capacity))

theorem flags_length_unitColours (I : Packing.Instance) : (flags I).length = (unitColours I).length :=
  ColourFlags.flags_length false _

theorem flags_next (I : Packing.Instance) (i : ℕ) (hi : i + 1 < (unitColours I).length) :
    (flags I)[i + 1]'(by rw [flags_length_unitColours]; exact hi) =
      (((unitColours I)[i]'(by omega)).2 == ((unitColours I)[i + 1]'hi).1) :=
  ColourFlags.flags_next false (unitColours I) i hi

def bulkColourIndex (I : Packing.Instance)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) : Fin (unitColours I).length :=
  ⟨(PrefixColours.nonbulk frameColours ringColours I).length + j.val, by
    have hj := (BulkScan.colourIndex (Raw.side (I.bins, I.capacity)) j).isLt
    change j.val < (BulkScan.colours (Raw.side (I.bins, I.capacity))).length at hj
    change (PrefixColours.nonbulk frameColours ringColours I).length + j.val <
      (PrefixColours.nonbulk frameColours ringColours I ++ BulkScan.colours (Raw.side (I.bins, I.capacity))).length
    rw [List.length_append]
    exact Nat.add_lt_add_left hj _⟩

theorem unitColours_bulk (I : Packing.Instance)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) :
    (unitColours I).get (bulkColourIndex I j) =
      (BulkScan.colours (Raw.side (I.bins, I.capacity))).get (BulkScan.colourIndex _ j) := by
  simpa only [unitColours, bulkColourIndex, List.get_eq_getElem, Nat.add_comm] using
    (List.getElem_append_right' (PrefixColours.nonbulk frameColours ringColours I)
      (l₂ := BulkScan.colours (Raw.side (I.bins, I.capacity)))
      (i := j.val) (BulkScan.colourIndex _ j).isLt).symm

theorem unitColours_bulk_physical (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) :
    (unitColours I).get (bulkColourIndex I j) =
      (FarField.colour (BulkScan.runtimeFirst (PackingSource.parameters I hw).side
        (by have h := (PackingSource.parameters I hw).side_ge; omega) ha j),
       FarField.colour (BulkScan.runtimeLast (PackingSource.parameters I hw).side
        (by have h := (PackingSource.parameters I hw).side_ge; omega) ha j)) := by
  rw [unitColours_bulk]
  exact (BulkScan.runtimeFold_colours (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) ha j).symm

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

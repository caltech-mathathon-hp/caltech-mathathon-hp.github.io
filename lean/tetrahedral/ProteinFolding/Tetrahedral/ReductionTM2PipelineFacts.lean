import ProteinFolding.Tetrahedral.ReductionTM2PrefixColours

namespace ProteinFolding.Tetrahedral.ReductionTM2

theorem ColourFlags.flags_length (seed : Bool) (cs : List ColourFlags.Colours) :
    (ColourFlags.flags (seed, cs)).length = cs.length := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih => rw [ColourFlags.flags_cons, List.length_cons, ih, List.length_cons]

theorem PrefixColours.prefix_length (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours)
    (hr : rings.length = 3) (I : Packing.Instance) :
    (PrefixColours.nonbulk frame rings I).length = I.bins + I.sizes.length + 10 := by
  simp only [PrefixColours.nonbulk, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate, hr]
  omega

theorem BulkScan.lengths_length (m : ℕ) : (BulkScan.lengths m).length = (BulkScan.records m).length := by
  simp only [BulkScan.lengths, List.length_map]

theorem BulkScan.colours_length (m : ℕ) : (BulkScan.colours m).length = (BulkScan.records m).length := by
  simp only [BulkScan.colours, List.length_map]

theorem PrefixColours.flags_length (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours)
    (hr : rings.length = 3) (I : Packing.Instance) :
    (ColourFlags.flags (false, PrefixColours.nonbulk frame rings I ++
      BulkScan.colours (Raw.side (I.bins, I.capacity)))).length =
        I.bins + I.sizes.length + (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length + 10 := by
  rw [ColourFlags.flags_length, List.length_append, PrefixColours.prefix_length frame rings hr I,
    BulkScan.colours_length, BulkScan.lengths_length]
  omega

theorem PrefixColours.reduction_sequence (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours)
    (I : Packing.Instance) (hw : Packing.WellFormed I) (ht : I.sizes.sum = I.bins * I.capacity) :
    (PrefixColours.reduction frame rings I).sequence =
      (PackingSource.parameters I hw).prescribedReductionWord I.sizes
        (BulkScan.lengths (Raw.side (I.bins, I.capacity)))
        (ColourFlags.flags (false, PrefixColours.nonbulk frame rings I ++ BulkScan.colours (Raw.side (I.bins, I.capacity)))) := by
  have hg : Guard.sourceGuard I = true := (Guard.sourceGuard_eq_true I).2 ⟨hw, ht⟩
  change (guardedPreparedInstance _).sequence = _
  rw [guardedPreparedInstance_of_guard _ hg]
  exact preparedInstance_sequence I hw _ _

theorem PrefixColours.reduction_threshold (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours)
    (I : Packing.Instance) (hw : Packing.WellFormed I) (ht : I.sizes.sum = I.bins * I.capacity) :
    (PrefixColours.reduction frame rings I).minBonds =
      2 * (octahedralNumber (PackingSource.parameters I hw).side : ℤ) -
        2 * ((PackingSource.parameters I hw).side ^ 2 : ℕ) := by
  have hg : Guard.sourceGuard I = true := (Guard.sourceGuard_eq_true I).2 ⟨hw, ht⟩
  change (guardedPreparedInstance _).minBonds = _
  rw [guardedPreparedInstance_of_guard _ hg]
  exact preparedInstance_threshold I hw _ _

end ProteinFolding.Tetrahedral.ReductionTM2

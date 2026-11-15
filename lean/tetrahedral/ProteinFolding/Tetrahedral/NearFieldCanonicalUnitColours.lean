import ProteinFolding.Tetrahedral.NearFieldCanonicalCappedUnits
import ProteinFolding.Tetrahedral.NearFieldCappedUnitColours
import ProteinFolding.Tetrahedral.NearFieldNonbulkEndpointColours
import ProteinFolding.Tetrahedral.ReductionTM2CanonicalColours

/-! The selected physical columns have exactly the colours computed by the
canonical reduction, including after the item occurrences are reordered. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

theorem singletonCappedUnit_ownerColours (p : ConstructionParameters) (i : Fin 3) :
    (singletonCappedUnit p i).ownerColours = (true, true) := by
  change (FarField.colour (canonicalSingletonOwner p.side i),
    FarField.colour (canonicalSingletonOwner p.side i)) = (true, true)
  exact Prod.ext (ownerColour_A (canonicalSingletonOwner_inA p.side i))
    (ownerColour_A (canonicalSingletonOwner_inA p.side i))

theorem frameCappedUnit_ownerColours (p : ConstructionParameters) :
    (frameCappedUnit p).ownerColours = (true, true) := by
  change (FarField.colour (frameFirstColumn p).owner, FarField.colour (frameLastColumn p).owner) = (true, true)
  exact frameEndpointColumn_owner_colours p

theorem separatorCappedUnit_ownerColours (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    (separatorCappedUnit p k).ownerColours = (true, true) := by
  change (FarField.colour (selectedEntryColumn p (some k)).owner,
    FarField.colour (exitCapColumn p k.val (by have h := k.isLt; omega)).owner) = (true, true)
  exact Prod.ext (selectedEntryColumn_owner_colour p (some k))
    (exitCapColumn_owner_colour p k.val (by have h := k.isLt; omega))

theorem leftCappedUnit_ownerColours (p : ConstructionParameters) :
    (leftCappedUnit p).ownerColours = (true, true) := by
  change (FarField.colour (selectedEntryColumn p none).owner, FarField.colour (leftLastColumn p).owner) = (true, true)
  have hl : FarField.colour (leftLastColumn p).owner = true := by
    rw [leftLastColumn_owner]
    exact ownerColour_A (leftFillerLastH_inA p)
  rw [selectedEntryColumn_owner_colour p none, hl]

theorem itemCappedUnit_ownerColours (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (itemCappedUnit p k before s hk hs hload).ownerColours = (true, true) := by
  change (FarField.colour (itemFirstColumn p k before s hk hs hload).owner,
    FarField.colour (itemLastColumn p k before s hk hs hload).owner) = (true, true)
  exact itemColumn_owner_colours p (itemTrackBase p k before) (p.itemDimers s)
    (by dsimp [itemTrackBase]; omega)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (itemFirstColumn_owner p k before s hk hs hload) (itemLastColumn_owner p k before s hk hs hload)

theorem rightCappedUnit_ownerColours (p : ConstructionParameters) :
    (rightCappedUnit p).ownerColours = (true, false) := by
  change (FarField.colour (rightFirstColumn p).owner, FarField.colour (rightFinalColumn p).owner) = (true, false)
  exact rightFillerColumn_owner_colours p (rightFirstColumn p) (rightFinalColumn p) rfl (rightFinalColumn_track_owner p)

theorem ringCappedUnit_ownerColours (p : ConstructionParameters) (i : Fin 3) :
    (ringCappedUnit p i).ownerColours = (false, false) := by
  change (FarField.colour (canonicalRingColumn p i 0).owner, FarField.colour (canonicalRingColumn p i 1).owner) = (false, false)
  exact Prod.ext (ownerColour_B (canonicalRingColumn_owner_inB p i 0))
    (ownerColour_B (canonicalRingColumn_owner_inB p i 1))

theorem bulkCappedUnit_ownerColours (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    (bulkCappedUnit p ha j).ownerColours =
      (ReductionTM2.BulkScan.colours p.side).get (ReductionTM2.BulkScan.colourIndex p.side j) := by
  change (FarField.colour (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j).owner,
    FarField.colour (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j).owner) = _
  rw [ReductionTM2.BulkScan.firstColumn_owner, ReductionTM2.BulkScan.lastColumn_owner]
  exact ReductionTM2.BulkScan.runtimeFold_colours p.side (by have h := p.side_ge; omega) ha j

theorem terminalColumn_owner_colour (p : ConstructionParameters) : FarField.colour (terminalColumn p).owner = false := by
  apply ownerColour_B
  rw [terminalColumn_owner]
  exact initialTerminal_inB p

private theorem ownerColours_map_constant {m : ℕ} (us : List (CappedUnit m)) (c : Bool × Bool)
    (h : ∀ u ∈ us, u.ownerColours = c) : us.map CappedUnit.ownerColours = List.replicate us.length c := by
  revert h
  induction us with
  | nil => intro _; rfl
  | cons u us ih =>
    intro h
    have hu := h u (by simp)
    have ht := ih (fun v hv => h v (by simp only [List.mem_cons]; exact Or.inr hv))
    simp only [List.map_cons, hu, List.length_cons, List.replicate_succ, ht]

theorem taggedSingletonUnits_ownerColours (p : ConstructionParameters) :
    (taggedSingletonUnits p).map CappedUnit.ownerColours = [(true, true), (true, true), (true, true)] := by
  simp only [taggedSingletonUnits, List.map_cons, List.map_nil, singletonCappedUnit_ownerColours]

theorem taggedSeparatorUnits_ownerColours (p : ConstructionParameters) :
    (taggedSeparatorUnits p).map CappedUnit.ownerColours = List.replicate (p.bins + 1) (true, true) := by
  have h := ownerColours_map_constant (taggedSeparatorUnits p) (true, true) (by
    intro u hu
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
    exact separatorCappedUnit_ownerColours p k)
  simpa only [taggedSeparatorUnits, List.length_ofFn] using h

theorem PackedBins.taggedItems_ownerColours {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : d.taggedItems.map CappedUnit.ownerColours = List.replicate items.length (true, true) := by
  have h := ownerColours_map_constant d.taggedItems (true, true) (by
    apply d.taggedItems_selectedProperty (fun u => u.ownerColours = (true, true))
    intro k i
    exact itemCappedUnit_ownerColours p k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i)
      (d.bin_lt k) (d.part_positive k _ (List.get_mem _ _))
      (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i))
  have hlen := congrArg List.length d.taggedItems_bodies
  simp only [List.length_map] at hlen
  rw [hlen] at h
  exact h

theorem taggedRingUnits_ownerColours (p : ConstructionParameters) :
    (taggedRingUnits p).map CappedUnit.ownerColours = List.replicate 3 (false, false) := by
  simp only [taggedRingUnits, List.map_cons, List.map_nil, ringCappedUnit_ownerColours]
  rfl

theorem taggedBulkUnits_ownerColours (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (taggedBulkUnits p ha).map CappedUnit.ownerColours = ReductionTM2.BulkScan.colours p.side := by
  rw [taggedBulkUnits, List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact (ReductionTM2.BulkScan.colours_length_lengths p.side).symm
  · intro i hi hj
    let j : Fin (ReductionTM2.BulkScan.lengths p.side).length := ⟨i, by simpa only [List.length_ofFn] using hi⟩
    have h := bulkCappedUnit_ownerColours p ha j
    simpa only [List.getElem_ofFn, Function.comp_def, List.get_eq_getElem,
      ReductionTM2.BulkScan.colourIndex, j] using h

theorem canonicalTaggedBodies_ownerColours (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalTaggedBodies p items d ha).map CappedUnit.ownerColours =
      [(true, true), (true, true), (true, true), (true, true)] ++
        List.replicate (p.bins + 1) (true, true) ++ [(true, true)] ++
        List.replicate items.length (true, true) ++ [(true, false)] ++
        List.replicate 3 (false, false) ++ ReductionTM2.BulkScan.colours p.side := by
  simp only [canonicalTaggedBodies, List.map_append, List.map_cons,
    taggedSingletonUnits_ownerColours, taggedSeparatorUnits_ownerColours, d.taggedItems_ownerColours,
    taggedRingUnits_ownerColours, taggedBulkUnits_ownerColours, frameCappedUnit_ownerColours,
    leftCappedUnit_ownerColours, rightCappedUnit_ownerColours, List.append_assoc,
    List.cons_append, List.nil_append]

theorem canonicalTaggedBodies_unitColours (I : Packing.Instance) (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    (canonicalTaggedBodies (PackingSource.parameters I hw) I.sizes d ha).map CappedUnit.ownerColours =
      ReductionTM2.Canonical.unitColours I := by
  rw [canonicalTaggedBodies_ownerColours]
  unfold ReductionTM2.Canonical.unitColours ReductionTM2.PrefixColours.nonbulk
    ReductionTM2.Canonical.frameColours ReductionTM2.Canonical.ringColours
  have hs := ReductionTM2.Raw.side_parameters (PackingSource.parameters I hw)
  change ReductionTM2.Raw.side (I.bins, I.capacity) = (PackingSource.parameters I hw).side at hs
  rw [hs]
  rfl

end ProteinFolding.Tetrahedral.NearField

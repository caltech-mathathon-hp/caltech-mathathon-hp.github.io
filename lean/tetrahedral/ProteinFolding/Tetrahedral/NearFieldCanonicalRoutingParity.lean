import ProteinFolding.Tetrahedral.NearFieldCanonicalRoutingUnits
import ProteinFolding.Tetrahedral.NearFieldCanonicalUnitColours
import ProteinFolding.Tetrahedral.ReductionTM2LinkerParity

/-! The parity flags computed by the reduction describe the selected physical
column owners in their actual source order. They therefore give the required
parity for the exact prescribed linker lengths. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem selectedUnitWireColumn_computed_flag {m n : ℕ} (bs : Fin n → CappedUnit m)
    (C : DanglingColumn m) (e : FarField.Pairing (2 * n) n) (seed : Bool)
    (hseed : FarField.colour C.owner = seed) (r : Fin n) :
    (ReductionTM2.ColourFlags.flags
      (seed, List.ofFn (fun j => (bs j).ownerColours)))[r.val]?.getD false =
      (FarField.colour (selectedUnitWireColumn bs C e (e.first r)).owner ==
        FarField.colour (selectedUnitWireColumn bs C e (e.second r)).owner) := by
  cases n with
  | zero => exact Fin.elim0 r
  | succ n =>
    by_cases hr : r.val = 0
    · have hr0 : r = (0 : Fin (n + 1)) := Fin.ext hr
      subst r
      rw [selectedUnitWireColumn_first_zero bs C e 0 rfl,
        selectedUnitWireColumn_second, hseed, List.ofFn_succ,
        ReductionTM2.ColourFlags.flags_cons]
      rfl
    · rw [selectedUnitWireColumn_first_nonzero bs C e r hr,
        selectedUnitWireColumn_second]
      have hi : r.val - 1 + 1 <
          (List.ofFn (fun j => (bs j).ownerColours)).length := by
        simp only [List.length_ofFn]
        have h := r.isLt
        omega
      have hflag : r.val < (ReductionTM2.ColourFlags.flags
          (seed, List.ofFn (fun j => (bs j).ownerColours))).length := by
        rw [ReductionTM2.ColourFlags.flags_length, List.length_ofFn]
        exact r.isLt
      have hnext := ReductionTM2.ColourFlags.flags_next seed
        (List.ofFn (fun j => (bs j).ownerColours)) (r.val - 1) hi
      have heq : r.val - 1 + 1 = r.val := by omega
      simp only [heq] at hnext
      rw [List.getElem?_eq_getElem hflag, Option.getD_some, hnext]
      simp only [List.getElem_ofFn]
      rfl

theorem canonicalCappedBodyAt_ownerColours (I : Packing.Instance)
    (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    List.ofFn (fun j => (canonicalCappedBodyAt (PackingSource.parameters I hw)
      I.sizes d ha j).ownerColours) = ReductionTM2.Canonical.unitColours I := by
  have h := congrArg (List.map CappedUnit.ownerColours)
    (canonicalCappedBodyAt_list (PackingSource.parameters I hw) I.sizes d ha)
  rw [List.map_ofFn] at h
  exact h.trans (canonicalTaggedBodies_unitColours I hw d ha)

theorem canonicalCappedBodyAt_flags (I : Packing.Instance)
    (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    ReductionTM2.Canonical.flags I = ReductionTM2.ColourFlags.flags
      (false, List.ofFn (fun j => (canonicalCappedBodyAt (PackingSource.parameters I hw)
        I.sizes d ha j).ownerColours)) := by
  rw [canonicalCappedBodyAt_ownerColours I hw d ha]
  rfl

theorem canonicalSelectedWire_flag (I : Packing.Instance)
    (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount (PackingSource.parameters I hw) I.sizes)
      (canonicalBodyCount (PackingSource.parameters I hw) I.sizes))
    (r : Fin (canonicalBodyCount (PackingSource.parameters I hw) I.sizes)) :
    (ReductionTM2.Canonical.flags I)[r.val]?.getD false =
      (FarField.colour (selectedUnitWireColumn
        (canonicalCappedBodyAt (PackingSource.parameters I hw) I.sizes d ha)
        (terminalColumn (PackingSource.parameters I hw)) e (e.first r)).owner ==
      FarField.colour (selectedUnitWireColumn
        (canonicalCappedBodyAt (PackingSource.parameters I hw) I.sizes d ha)
        (terminalColumn (PackingSource.parameters I hw)) e (e.second r)).owner) := by
  rw [canonicalCappedBodyAt_flags I hw d ha]
  exact selectedUnitWireColumn_computed_flag _ _ e false
    (terminalColumn_owner_colour (PackingSource.parameters I hw)) r

theorem canonicalSelectedWire_capParity (I : Packing.Instance)
    (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount (PackingSource.parameters I hw) I.sizes)
      (canonicalBodyCount (PackingSource.parameters I hw) I.sizes))
    (r : Fin (canonicalBodyCount (PackingSource.parameters I hw) I.sizes)) :
    FarField.CapParity
      (wireCapSite (canonicalRoutingUnits (PackingSource.parameters I hw) I.sizes d ha) e (e.first r))
      (wireCapSite (canonicalRoutingUnits (PackingSource.parameters I hw) I.sizes d ha) e (e.second r))
      ((PackingSource.parameters I hw).longLinkerLength
        (2 * canonicalBodyCount (PackingSource.parameters I hw) I.sizes)
        ((ReductionTM2.Canonical.flags I)[r.val]?.getD false)) :=
  selectedUnitWireColumn_capParity (terminalWordPiece (PackingSource.parameters I hw))
    (canonicalCappedBodyAt (PackingSource.parameters I hw) I.sizes d ha)
    (terminalColumn (PackingSource.parameters I hw)) rfl e (PackingSource.parameters I hw)
    (2 * canonicalBodyCount (PackingSource.parameters I hw) I.sizes) r _
    (canonicalSelectedWire_flag I hw d ha e r)

theorem canonicalSelectedWire_prescribedGap_capParity (I : Packing.Instance)
    (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount (PackingSource.parameters I hw) I.sizes)
      (canonicalBodyCount (PackingSource.parameters I hw) I.sizes))
    (r : Fin (canonicalBodyCount (PackingSource.parameters I hw) I.sizes)) :
    FarField.CapParity
      (wireCapSite (canonicalRoutingUnits (PackingSource.parameters I hw) I.sizes d ha) e (e.first r))
      (wireCapSite (canonicalRoutingUnits (PackingSource.parameters I hw) I.sizes d ha) e (e.second r))
      ((PackingSource.parameters I hw).prescribedLinkerGap I.sizes
        (ReductionTM2.BulkScan.lengths (PackingSource.parameters I hw).side)
        (ReductionTM2.Canonical.flags I) r.val + 2) := by
  rw [ConstructionParameters.prescribedLinkerGap_add_two]
  exact canonicalSelectedWire_capParity I hw d ha e r

end ProteinFolding.Tetrahedral.NearField

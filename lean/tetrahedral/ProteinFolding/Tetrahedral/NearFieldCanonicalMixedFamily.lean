import ProteinFolding.Tetrahedral.NearFieldCanonicalRoutingUnits
import ProteinFolding.Tetrahedral.NearFieldCanonicalRoutingParity
import ProteinFolding.Tetrahedral.NearFieldCanonicalSelectedWireClearance
import ProteinFolding.Tetrahedral.NearFieldMixedAssembly
import ProteinFolding.Tetrahedral.ReductionTM2LinkerParity

/-! The actual finite routing family: every field is supplied by the concrete
canonical local folds, selected columns and computed source parity bits. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

noncomputable def canonicalMixedFamily (I : Packing.Instance) (hw : Packing.WellFormed I)
    (d : PackedBins (PackingSource.parameters I hw) I.sizes)
    (ha : (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic) :
    MixedUnitFamily (PackingSource.parameters I hw).side
      (canonicalBodyCount (PackingSource.parameters I hw) I.sizes) := by
  let p := PackingSource.parameters I hw
  let n := canonicalBodyCount p I.sizes
  let bs := canonicalCappedBodyAt p I.sizes d ha
  let e := unitCapPairing n
  let us := canonicalRoutingUnits p I.sizes d ha
  let O : Set Site := {x | ∃ q ∈ canonicalUnitPieces p I.sizes d ha, x ∈ foldSites q.fold}
  refine {
    units := us
    pairwise := canonicalRoutingUnits_disjoint p I.sizes d ha
    lengths := canonicalRoutingUnits_length_ge_two p I.sizes d ha
    last_dangling := canonicalRoutingUnits_last_dangling p I.sizes d ha
    first_dangling := canonicalRoutingUnits_first_dangling p I.sizes d ha
    pairing := e
    columns := selectedUnitWireColumn bs (terminalColumn p) e
    seeds_injective := canonicalSelectedWire_seed_injective p I.sizes d ha e
    cap_adjacent := selectedUnitWireColumn_adjacent (terminalWordPiece p) bs (terminalColumn p) rfl e
    obstacles := O
    unit_sites := ?_
    low := ?_
    clear := ?_
    linkerLength := fun r => p.longLinkerLength (2 * n) ((ReductionTM2.Canonical.flags I)[r.val]?.getD false)
    linker_large := ?_
    linker_three := ?_
    linker_parity := ?_
    gaps := p.prescribedLinkerGap I.sizes (ReductionTM2.BulkScan.lengths p.side) (ReductionTM2.Canonical.flags I)
    gaps_eq := ?_ }
  · intro i x hx
    exact ⟨us i, canonicalRoutingUnits_mem p I.sizes d ha i, hx⟩
  · rintro x ⟨q, hq, hx⟩
    exact canonicalUnitPieces_rho_bound p I.sizes d ha q hq x hx
  · intro a t ht hx
    rcases hx with ⟨q, hq, hx⟩
    obtain ⟨i, hi⟩ := (mem_foldSites q.fold _).mp hx
    exact canonicalSelectedWire_clear p I.sizes d ha e a q hq i t ht hi
  · intro r
    exact ReductionTM2.longLinkerLength_uniform_bound p (2 * n) _
  · intro r
    dsimp [ConstructionParameters.longLinkerLength, ConstructionParameters.baseLinkerLength]
    omega
  · intro r
    exact canonicalSelectedWire_capParity I hw d ha e r
  · intro r
    rfl

end ProteinFolding.Tetrahedral.NearField

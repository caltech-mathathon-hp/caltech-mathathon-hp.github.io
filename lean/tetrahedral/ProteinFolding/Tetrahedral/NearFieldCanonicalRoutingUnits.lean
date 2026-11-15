import ProteinFolding.Tetrahedral.NearFieldCanonicalPairwise
import ProteinFolding.Tetrahedral.NearFieldCanonicalUnitSupport
import ProteinFolding.Tetrahedral.NearFieldCanonicalCatalogueSeeds
import ProteinFolding.Tetrahedral.NearFieldCappedUnitRouting

/-! The actual source-ordered capped body table in the finite routing API.
Its terminal, words, geometric disjointness and locality are concrete. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable def canonicalBodyCount (p : ConstructionParameters) (items : List ℕ) : ℕ :=
  (p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length

theorem canonicalTaggedBodies_length (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalTaggedBodies p items d ha).length = canonicalBodyCount p items := by
  have h := congrArg List.length (canonicalTaggedBodies_bodies p items d ha)
  simpa only [List.length_map] using h

noncomputable def canonicalCappedBodyAt (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin (canonicalBodyCount p items)) : CappedUnit p.side :=
  (canonicalTaggedBodies p items d ha).get (Fin.cast (canonicalTaggedBodies_length p items d ha).symm i)

theorem canonicalCappedBodyAt_mem (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin (canonicalBodyCount p items)) :
    canonicalCappedBodyAt p items d ha i ∈ canonicalTaggedBodies p items d ha := List.get_mem _ _

theorem canonicalCappedBodyAt_list (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    List.ofFn (canonicalCappedBodyAt p items d ha) = canonicalTaggedBodies p items d ha := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, canonicalTaggedBodies_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

theorem canonicalCappedBodyAt_bodies (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (List.ofFn (canonicalCappedBodyAt p items d ha)).map CappedUnit.body =
      p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side) := by
  rw [canonicalCappedBodyAt_list]
  exact canonicalTaggedBodies_bodies p items d ha

noncomputable def canonicalRoutingUnits (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    Fin (canonicalBodyCount p items + 1) → PositionedWord :=
  cappedRoutingUnits (terminalWordPiece p) (canonicalCappedBodyAt p items d ha)

theorem canonicalRoutingUnits_list (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    List.ofFn (canonicalRoutingUnits p items d ha) = canonicalUnitPieces p items d ha := by
  rw [List.ofFn_succ]
  change terminalWordPiece p ::
    List.ofFn (fun i => (canonicalCappedBodyAt p items d ha i).piece) = _
  have he := List.map_ofFn (f := canonicalCappedBodyAt p items d ha) (g := CappedUnit.piece)
  simp only [Function.comp_def] at he
  rw [← he, canonicalCappedBodyAt_list]
  rfl

theorem canonicalRoutingUnits_mem (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin (canonicalBodyCount p items + 1)) :
    canonicalRoutingUnits p items d ha i ∈ canonicalUnitPieces p items d ha := by
  rw [← canonicalRoutingUnits_list]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem canonicalRoutingUnits_words (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (List.ofFn (canonicalRoutingUnits p items d ha)).map PositionedWord.word = [.H, .P] ::
      (p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).map capWord := by
  rw [canonicalRoutingUnits_list]
  exact canonicalUnitPieces_words p items d ha

theorem canonicalRoutingUnits_disjoint (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i j : Fin (canonicalBodyCount p items + 1)) (hne : i ≠ j) :
    WordsDisjoint (canonicalRoutingUnits p items d ha i) (canonicalRoutingUnits p items d ha j) := by
  have hp : (List.ofFn (canonicalRoutingUnits p items d ha)).Pairwise WordsDisjoint := by
    rw [canonicalRoutingUnits_list]
    exact canonicalUnitPieces_pairwise p items d ha
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact List.pairwise_ofFn.mp hp (i := i) (j := j) hij
  · exact (List.pairwise_ofFn.mp hp (i := j) (j := i) hji).symm

theorem canonicalRoutingUnits_length_ge_two (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    ∀ i, 2 ≤ (canonicalRoutingUnits p items d ha i).word.length :=
  cappedRoutingUnits_length_ge_two (terminalWordPiece p) (canonicalCappedBodyAt p items d ha)
    (by change 2 ≤ 2; decide)

theorem canonicalRoutingUnits_last_dangling (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    ∀ i, IsDangling p.side (canonicalRoutingUnits p items d ha i).last :=
  cappedRoutingUnits_last_dangling (terminalWordPiece p) (canonicalCappedBodyAt p items d ha) (terminalColumn p) rfl

theorem canonicalRoutingUnits_first_dangling (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    ∀ i, 0 < i.val → IsDangling p.side (canonicalRoutingUnits p items d ha i).first :=
  cappedRoutingUnits_first_dangling (terminalWordPiece p) (canonicalCappedBodyAt p items d ha)

theorem canonicalRoutingUnits_hSupport_subset_oct (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin (canonicalBodyCount p items + 1)) :
    hSupport (canonicalRoutingUnits p items d ha i).word
      (canonicalRoutingUnits p items d ha i).fold ⊆ octahedron p.side :=
  canonicalUnitPieces_hSupport_subset_oct p items d ha _ (canonicalRoutingUnits_mem p items d ha i)

theorem canonicalRoutingUnits_rho_bound (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin (canonicalBodyCount p items + 1)) (x : Site)
    (hx : x ∈ foldSites (canonicalRoutingUnits p items d ha i).fold) :
    FarField.rho (octRadius p.side) x < 20 * (p.side : ℤ) + 21 :=
  canonicalUnitPieces_rho_bound p items d ha _ (canonicalRoutingUnits_mem p items d ha i) x hx

theorem canonicalSelectedWire_seed_injective (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount p items) (canonicalBodyCount p items)) :
    Function.Injective (fun a =>
      (selectedUnitWireColumn (canonicalCappedBodyAt p items d ha) (terminalColumn p) e a).seed) :=
  actualSelectedWire_seed_injective p items d ha (canonicalCappedBodyAt p items d ha)
    (canonicalCappedBodyAt_mem p items d ha) (canonicalRoutingUnits_disjoint p items d ha) e

end ProteinFolding.Tetrahedral.NearField

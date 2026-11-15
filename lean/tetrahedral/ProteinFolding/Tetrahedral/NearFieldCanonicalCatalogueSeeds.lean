import ProteinFolding.Tetrahedral.NearFieldCanonicalSelectedCapData
import ProteinFolding.Tetrahedral.NearFieldCappedUnitRouting

/-! Actual catalogue seed injectivity follows from physical cap injectivity.
No seed-injectivity or column-clearance premise is supplied. -/

namespace ProteinFolding.Tetrahedral.NearField

def physicalCapCatalogue {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m) :
    Option (Fin n × Bool) → Site
  | none => terminal.last
  | some a => wordEndpoint (bs a.1).piece a.2

private def physicalCapLabel {n : ℕ} : Option (Fin n × Bool) → Fin (n + 1) × Bool
  | none => (0, false)
  | some a => (a.1.succ, a.2)

private theorem physicalCapLabel_injective (n : ℕ) : Function.Injective (@physicalCapLabel n) := by
  intro a b heq
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hv := congrArg (fun a : Fin (n + 1) × Bool => a.1.val) heq
      change 0 = b.1.val + 1 at hv
      omega
  | some a =>
    cases b with
    | none =>
      have hv := congrArg (fun a : Fin (n + 1) × Bool => a.1.val) heq
      change a.1.val + 1 = 0 at hv
      omega
    | some b =>
      have hv := congrArg (fun a : Fin (n + 1) × Bool => a.1.val) heq
      have hb := congrArg (fun a : Fin (n + 1) × Bool => a.2) heq
      change a.1.val + 1 = b.1.val + 1 at hv
      change a.2 = b.2 at hb
      apply congrArg Option.some
      exact Prod.ext (Fin.ext (by omega)) hb

private theorem physicalCapCatalogue_eq {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (a : Option (Fin n × Bool)) : physicalCapCatalogue terminal bs a =
      wordEndpoint (cappedRoutingUnits terminal bs (physicalCapLabel a).1) (physicalCapLabel a).2 := by
  cases a <;> rfl

theorem physicalCapCatalogue_injective {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (ht : 2 ≤ terminal.word.length)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (cappedRoutingUnits terminal bs i) (cappedRoutingUnits terminal bs j)) :
    Function.Injective (physicalCapCatalogue terminal bs) := by
  have hends := unitEndpointFamily_injective (cappedRoutingUnits terminal bs) hpair
    (cappedRoutingUnits_length_ge_two terminal bs ht)
  intro a b heq
  apply physicalCapLabel_injective n
  apply hends
  exact (physicalCapCatalogue_eq terminal bs a).symm.trans
    (heq.trans (physicalCapCatalogue_eq terminal bs b))

theorem actualCatalogue_selectedCapData (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    {n : ℕ} (bs : Fin n → CappedUnit p.side)
    (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha) (a : Option (Fin n × Bool)) :
    SelectedCapData p (physicalCapCatalogue (terminalWordPiece p) bs a)
      (cappedUnitColumnCatalogue bs (terminalColumn p) a) := by
  cases a with
  | none => exact terminal_selectedCapData p
  | some a => exact canonicalTaggedBody_selectedCapData p items d ha (bs a.1) (hbs a.1) a.2

theorem actualCatalogue_seed_injective (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    {n : ℕ} (bs : Fin n → CappedUnit p.side)
    (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (cappedRoutingUnits (terminalWordPiece p) bs i)
      (cappedRoutingUnits (terminalWordPiece p) bs j)) :
    Function.Injective (fun a => (cappedUnitColumnCatalogue bs (terminalColumn p) a).seed) :=
  selectedColumns_seed_injective_of_capData p (physicalCapCatalogue (terminalWordPiece p) bs)
    (cappedUnitColumnCatalogue bs (terminalColumn p))
    (physicalCapCatalogue_injective (terminalWordPiece p) bs (by change 2 ≤ 2; decide) hpair)
    (actualCatalogue_selectedCapData p items d ha bs hbs)

theorem actualSelectedWire_seed_injective (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    {n : ℕ} (bs : Fin n → CappedUnit p.side)
    (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (cappedRoutingUnits (terminalWordPiece p) bs i)
      (cappedRoutingUnits (terminalWordPiece p) bs j)) (e : FarField.Pairing (2 * n) n) :
    Function.Injective (fun a => (selectedUnitWireColumn bs (terminalColumn p) e a).seed) :=
  selectedUnitWireColumn_seed_injective bs (terminalColumn p) e
    (actualCatalogue_seed_injective p items d ha bs hbs hpair)

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldSelectedEntryOwners
import ProteinFolding.Tetrahedral.NearFieldCappedUnitData

/-! Ordinary cap seeds name their actual local cap. Borrowed entry seeds
are distinguished from all ordinary seeds by their degree-two interior owner. -/

namespace ProteinFolding.Tetrahedral.NearField

inductive SelectedCapData (p : ConstructionParameters) (cap : Site) (C : DanglingColumn p.side) : Prop where
  | borrowed (i : EntryCapIndex p) (column_eq : C = selectedEntryColumn p i)
      (cap_eq : cap = entryCapSite p i)
  | ordinary (cap_eq : C.seed = cap)
      (owner_kind : C.owner ∈ bulkDeletedEdges p.side ∨ (bulkCoverNeighbours p.side C.owner).card = 1)

theorem selectedCap_eq_of_seed_eq (p : ConstructionParameters) {a b : Site}
    {C D : DanglingColumn p.side} (hC : SelectedCapData p a C) (hD : SelectedCapData p b D)
    (heq : C.seed = D.seed) : a = b := by
  cases hC with
  | borrowed i hCi hai =>
    cases hD with
    | borrowed j hDj hbj =>
      have hs : (selectedEntryColumn p i).seed = (selectedEntryColumn p j).seed := by
        simpa only [hCi, hDj] using heq
      have hij : i = j := by
        by_contra hne
        exact selectedEntryColumn_seeds_ne p i j hne hs
      exact hai.trans ((congrArg (entryCapSite p) hij).trans hbj.symm)
    | ordinary hdb hd =>
      have hs : (selectedEntryColumn p i).seed = D.seed := by simpa only [hCi] using heq
      rcases hd with hd | hd
      · with_reducible exact False.elim (Ne.elim (selectedEntryColumn_seed_ne_deletedColumn p i D hd) hs)
      · with_reducible exact False.elim (Ne.elim (selectedEntryColumn_seed_ne_bulkEndpoint p i D hd) hs)
  | ordinary hca hc =>
    cases hD with
    | borrowed j hDj hbj =>
      have hs : (selectedEntryColumn p j).seed = C.seed := by simpa only [hDj] using heq.symm
      rcases hc with hc | hc
      · with_reducible exact False.elim (Ne.elim (selectedEntryColumn_seed_ne_deletedColumn p j C hc) hs)
      · with_reducible exact False.elim (Ne.elim (selectedEntryColumn_seed_ne_bulkEndpoint p j C hc) hs)
    | ordinary hdb hd => exact hca.symm.trans (heq.trans hdb)

theorem selectedColumns_seed_injective_of_capData (p : ConstructionParameters) {ι : Type*}
    (caps : ι → Site) (columns : ι → DanglingColumn p.side) (hcaps : Function.Injective caps)
    (hdata : ∀ i, SelectedCapData p (caps i) (columns i)) :
    Function.Injective (fun i => (columns i).seed) := by
  intro i j heq
  exact hcaps (selectedCap_eq_of_seed_eq p (hdata i) (hdata j) heq)

theorem CappedUnit.ofColumns_selectedCapData (p : ConstructionParameters) (body : Sequence)
    (piece : PositionedWord) (hword : piece.word = capWord body) (C D : DanglingColumn p.side)
    (hfirst : piece.first = C.seed) (hlast : piece.last = D.seed)
    (hC : C.owner ∈ bulkDeletedEdges p.side ∨ (bulkCoverNeighbours p.side C.owner).card = 1)
    (hD : D.owner ∈ bulkDeletedEdges p.side ∨ (bulkCoverNeighbours p.side D.owner).card = 1) (b : Bool) :
    SelectedCapData p (wordEndpoint (CappedUnit.ofColumns body piece hword C D hfirst hlast).piece b)
      ((CappedUnit.ofColumns body piece hword C D hfirst hlast).column b) := by
  cases b
  · exact SelectedCapData.ordinary hlast.symm hD
  · exact SelectedCapData.ordinary hfirst.symm hC

end ProteinFolding.Tetrahedral.NearField

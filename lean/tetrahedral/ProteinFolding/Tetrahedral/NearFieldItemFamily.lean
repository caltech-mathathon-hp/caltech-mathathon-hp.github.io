import ProteinFolding.Tetrahedral.NearFieldCanonicalTrackPieces
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly

/-! Disjoint packed item occurrences separate their full capped words. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem cappedIntervalDimerFolds_disjoint {m : ℕ} (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (base n base' n' : ℕ) (hn : 0 < n) (hn' : 0 < n') (reverse reverse' : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (hroom' : base' + 2 * n' ≤ 2 * m - 1)
    (hdis : Disjoint (edgeDimerHsites m F base (n - 1)) (edgeDimerHsites m G base' (n' - 1)))
    (C D C' D' : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (hC' : C'.owner = octEdgeZigzag m G (dimerHIndex base' reverse' 0 0))
    (hD' : D'.owner = octEdgeZigzag m G (dimerHIndex base' reverse' (n' - 1) 1)) :
    Disjoint (foldSites (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD))
      (foldSites (cappedIntervalDimerFold hm G base' n' hn' reverse' hroom' C' D' hC' hD')) := by
  rw [cappedIntervalDimerFold_sites, cappedIntervalDimerFold_sites]
  exact cappedEdgeDimerFolds_disjoint hm F G base (n - 1) base' (n' - 1)
    reverse reverse' (by omega) (by omega) hdis C D C' D' hC hD hC' hD'

theorem canonicalItemPieces_disjoint_of_Hsites (p : ConstructionParameters)
    (k a s l b t : ℕ) (hk : k < p.bins) (hl : l < p.bins) (hs : 0 < s) (ht : 0 < t)
    (hload : a + s ≤ p.capacity) (hload' : b + t ≤ p.capacity)
    (hdis : Disjoint
      (edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p k a) (p.itemDimers s - 1))
      (edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p l b) (p.itemDimers t - 1))) :
    WordsDisjoint (canonicalItemPiece p k a s hk hs hload)
      (canonicalItemPiece p l b t hl ht hload') := by
  exact cappedIntervalDimerFolds_disjoint (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame trackEdgeFrame (itemTrackBase p k a) (p.itemDimers s)
    (itemTrackBase p l b) (p.itemDimers t)
    (by have h := p.itemDimers_ge s hs; omega) (by have h := p.itemDimers_ge t ht; omega)
    false false (itemTrackBase_room p k a s hk hload) (itemTrackBase_room p l b t hl hload')
    hdis (itemFirstColumn p k a s hk hs hload) (itemLastColumn p k a s hk hs hload)
    (itemFirstColumn p l b t hl ht hload') (itemLastColumn p l b t hl ht hload')
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k a s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k a s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p l b t hl ht hload')
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge t ht; omega) (p.itemDimers_even t)]
        exact itemLastColumn_owner p l b t hl ht hload')

def packedItemPiece (p : ConstructionParameters) (k : ℕ) (hk : k < p.bins) (items : List ℕ)
    (hpos : ∀ s ∈ items, 0 < s) (hload : items.sum = p.capacity) (i : Fin items.length) : PositionedWord :=
  canonicalItemPiece p k (itemPrefix items i) (items.get i) hk (hpos _ (List.get_mem _ _))
    (by rw [← hload]; exact itemPrefix_load items i)

theorem packedItemPiece_word (p : ConstructionParameters) (k : ℕ) (hk : k < p.bins) (items : List ℕ)
    (hpos : ∀ s ∈ items, 0 < s) (hload : items.sum = p.capacity) (i : Fin items.length) :
    (packedItemPiece p k hk items hpos hload i).word = capWord (dimerChain (p.itemDimers (items.get i))) := rfl

theorem packedItemPieces_disjoint_same_bin (p : ConstructionParameters) (k : ℕ) (hk : k < p.bins)
    (items : List ℕ) (hpos : ∀ s ∈ items, 0 < s) (hload : items.sum = p.capacity)
    (i j : Fin items.length) (hne : i ≠ j) :
    WordsDisjoint (packedItemPiece p k hk items hpos hload i) (packedItemPiece p k hk items hpos hload j) :=
  canonicalItemPieces_disjoint_of_Hsites p k (itemPrefix items i) (items.get i)
    k (itemPrefix items j) (items.get j) hk hk
    (hpos _ (List.get_mem _ _)) (hpos _ (List.get_mem _ _))
    (by rw [← hload]; exact itemPrefix_load items i)
    (by rw [← hload]; exact itemPrefix_load items j)
    (packedItemHsites_disjoint_same_bin p k items hpos i j hne)

theorem packedItemPieces_disjoint_bins (p : ConstructionParameters) (k l : ℕ)
    (hk : k < p.bins) (hl : l < p.bins) (hkl : k < l)
    (items others : List ℕ) (hpos : ∀ s ∈ items, 0 < s) (hpos' : ∀ s ∈ others, 0 < s)
    (hload : items.sum = p.capacity) (hload' : others.sum = p.capacity)
    (i : Fin items.length) (j : Fin others.length) :
    WordsDisjoint (packedItemPiece p k hk items hpos hload i) (packedItemPiece p l hl others hpos' hload' j) :=
  canonicalItemPieces_disjoint_of_Hsites p k (itemPrefix items i) (items.get i)
    l (itemPrefix others j) (others.get j) hk hl
    (hpos _ (List.get_mem _ _)) (hpos' _ (List.get_mem _ _))
    (by rw [← hload]; exact itemPrefix_load items i)
    (by rw [← hload']; exact itemPrefix_load others j)
    (packedItemHsites_disjoint_bins p k l hkl items others hpos hpos' hload i j)

end ProteinFolding.Tetrahedral.NearField

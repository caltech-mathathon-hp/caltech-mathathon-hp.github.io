import ProteinFolding.Tetrahedral.FrameForcingItemMultiset

/-! Eligible catalogue indices give a finite occurrence set whose values
are exactly the input multiset. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def ReductionChainTag.isItem : ReductionChainTag → Bool
  | .item _ => true
  | _ => false

def ReductionChainTag.itemValue : ReductionChainTag → ℕ
  | .item s => s
  | _ => 0

theorem ReductionChainTag.item_size_of_admissible (p : ConstructionParameters) (items : List ℕ)
    (tag : ReductionChainTag) (q : ℕ) (h : tag.Admissible p items q)
    (hi : tag.isItem = true) (hpos : ∀ s ∈ items, 0 < s) :
    0 < tag.itemValue ∧ q = p.scale * tag.itemValue := by
  rcases h with ⟨hq, ht⟩
  cases tag <;> simp only [ReductionChainTag.isItem, Bool.false_eq_true] at hi
  case item s =>
    exact ⟨hpos s ht, by simpa only [ReductionChainTag.size, ConstructionParameters.itemDimers,
      ReductionChainTag.itemValue] using hq⟩

noncomputable def DimerCatalogue.itemIndices {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) : Finset c.Index := by
  classical
  exact (@Finset.univ c.Index c.finiteIndex).filter (fun i => (c.tag i).isItem = true)

theorem DimerCatalogue.itemValues_perm_indices {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) :
    c.itemValues.Perm (c.itemIndices.toList.map (fun i => (c.tag i).itemValue)) := by
  classical
  let U := (@Finset.univ c.Index c.finiteIndex)
  have hflat (xs : List c.Index) : xs.flatMap (fun i => (c.tag i).itemValues) =
      (xs.filter (fun i => (c.tag i).isItem)).map (fun i => (c.tag i).itemValue) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      rw [List.flatMap_cons, ih]
      cases ht : c.tag i <;> simp [ht, ReductionChainTag.itemValues, ReductionChainTag.isItem,
        ReductionChainTag.itemValue]
  have hindices : (U.toList.filter (fun i => (c.tag i).isItem)).Perm c.itemIndices.toList := by
    apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList U).filter _)
      (Finset.nodup_toList c.itemIndices)).mpr
    intro i
    simp [U, DimerCatalogue.itemIndices]
  change (U.toList.flatMap (fun i => (c.tag i).itemValues)).Perm _
  rw [hflat]
  exact hindices.map (fun i => (c.tag i).itemValue)

theorem ReductionDimerProvenance.items_perm_indices (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    let c := (catalogue p items bulkLengths gaps hbulk).val
    items.Perm (c.itemIndices.toList.map (fun i => (c.tag i).itemValue)) := by
  exact (catalogue_itemValues_perm p items bulkLengths gaps hbulk).symm.trans
    ((catalogue p items bulkLengths gaps hbulk).val.itemValues_perm_indices)

theorem ReductionDimerProvenance.item_index_size (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hpos : ∀ s ∈ items, 0 < s)
    (i : (catalogue p items bulkLengths gaps hbulk).val.Index)
    (hi : i ∈ (catalogue p items bulkLengths gaps hbulk).val.itemIndices) :
    0 < ((catalogue p items bulkLengths gaps hbulk).val.tag i).itemValue ∧
      (catalogue p items bulkLengths gaps hbulk).val.q i =
        p.scale * ((catalogue p items bulkLengths gaps hbulk).val.tag i).itemValue := by
  classical
  let c := (catalogue p items bulkLengths gaps hbulk).val
  have hitem : (c.tag i).isItem = true := (Finset.mem_filter.mp hi).2
  exact ReductionChainTag.item_size_of_admissible p items (c.tag i) (c.q i)
    ((catalogue p items bulkLengths gaps hbulk).property i) hitem hpos

end ProteinFolding.Tetrahedral

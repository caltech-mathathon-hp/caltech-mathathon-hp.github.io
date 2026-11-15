import ProteinFolding.Tetrahedral.NearFieldItemIntervals
import ProteinFolding.Tetrahedral.NearFieldSeparatorFamilyChains

/-! Occurrence-preserving item placements use before sums inside each full
bin. Equal item values retain distinct list indices and disjoint intervals. -/

namespace ProteinFolding.Tetrahedral.NearField

def itemPrefix (items : List ℕ) (i : Fin items.length) : ℕ := (items.take i.val).sum

theorem nat_sum_take_le (items : List ℕ) (i : ℕ) : (items.take i).sum ≤ items.sum := by
  have h := congrArg List.sum (List.take_append_drop i items)
  rw [List.sum_append] at h
  omega

theorem nat_sum_take_mono (items : List ℕ) (i j : ℕ) (hij : i ≤ j) :
    (items.take i).sum ≤ (items.take j).sum := by
  have h := nat_sum_take_le (items.take j) i
  rw [List.take_take, Nat.min_eq_left hij] at h
  exact h

theorem itemPrefix_step (items : List ℕ) (i : Fin items.length) :
    (items.take (i.val + 1)).sum = itemPrefix items i + items.get i := by
  rw [List.take_succ_eq_append_getElem i.isLt, List.sum_append, List.sum_singleton]
  rfl

theorem itemPrefix_load (items : List ℕ) (i : Fin items.length) :
    itemPrefix items i + items.get i ≤ items.sum := by
  rw [← itemPrefix_step]
  exact nat_sum_take_le items _

theorem itemPrefix_end_le_next (items : List ℕ) (i j : Fin items.length) (hij : i.val < j.val) :
    itemPrefix items i + items.get i ≤ itemPrefix items j := by
  have h := nat_sum_take_mono items (i.val + 1) j.val (by omega)
  rw [itemPrefix_step] at h
  exact h

theorem itemTrackBase_prefix_separated (p : ConstructionParameters) (k a s b : ℕ) (h : a + s ≤ b) :
    itemTrackBase p k a + 2 * p.itemDimers s ≤ itemTrackBase p k b := by
  have hs := Nat.mul_le_mul_left p.scale h
  rw [Nat.mul_add] at hs
  change p.scale * a + p.itemDimers s ≤ p.scale * b at hs
  dsimp [itemTrackBase]
  omega

def packedItemHsites (p : ConstructionParameters) (k : ℕ) (items : List ℕ) (i : Fin items.length) : Finset Site :=
  edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p k (itemPrefix items i)) (p.itemDimers (items.get i) - 1)

theorem packedItemHsites_disjoint_same_bin (p : ConstructionParameters) (k : ℕ) (items : List ℕ)
    (hpos : ∀ s ∈ items, 0 < s) (i j : Fin items.length) (hne : i ≠ j) :
    Disjoint (packedItemHsites p k items i) (packedItemHsites p k items j) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hi := p.itemDimers_ge (items.get i) (hpos _ (List.get_mem _ _))
  have hj := p.itemDimers_ge (items.get j) (hpos _ (List.get_mem _ _))
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · apply edgeDimerHsites_disjoint_intervals hm trackEdgeFrame
    left
    have h := itemTrackBase_prefix_separated p k _ _ _ (itemPrefix_end_le_next items i j hij)
    omega
  · apply edgeDimerHsites_disjoint_intervals hm trackEdgeFrame
    right
    have h := itemTrackBase_prefix_separated p k _ _ _ (itemPrefix_end_le_next items j i hji)
    omega

theorem packedItemHsites_disjoint_bins (p : ConstructionParameters) (k l : ℕ) (hk : k < l)
    (items others : List ℕ) (hpos : ∀ s ∈ items, 0 < s) (hpos' : ∀ s ∈ others, 0 < s)
    (hload : items.sum = p.capacity) (i : Fin items.length) (j : Fin others.length) :
    Disjoint (packedItemHsites p k items i) (packedItemHsites p l others j) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hi := p.itemDimers_ge (items.get i) (hpos _ (List.get_mem _ _))
  have hj := p.itemDimers_ge (others.get j) (hpos' _ (List.get_mem _ _))
  have hiload := itemPrefix_load items i
  rw [hload] at hiload
  have hend := itemTrackBase_end_le p k _ _ hiload
  have hsep := p.separatorIndex_mono (show k + 1 ≤ l by omega)
  have hlo : 2 * p.separatorIndex l ≤ itemTrackBase p l (itemPrefix others j) := by
    dsimp [itemTrackBase]
    omega
  apply edgeDimerHsites_disjoint_intervals hm trackEdgeFrame
  left
  omega

end ProteinFolding.Tetrahedral.NearField

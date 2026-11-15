import ProteinFolding.Tetrahedral.ReductionDimerProvenanceCounts
import ProteinFolding.Cubic.Proofs.PackingFromLabels

/-! Item tags preserve the input multiset, including repeated sizes.
This lets finite catalogue bin assignments recover genuine source packings. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def ReductionChainTag.itemValues : ReductionChainTag → List ℕ
  | .item s => [s]
  | _ => []

noncomputable def DimerCatalogue.itemValues {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) : List ℕ := by
  classical
  exact (@Finset.univ c.Index c.finiteIndex).toList.flatMap (fun i => (c.tag i).itemValues)

theorem DimerCatalogue.itemValues_count {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) (s : ℕ) :
    c.itemValues.count s = c.weightSum (fun tag _ => tag.itemValues.count s) := by
  classical
  rw [DimerCatalogue.itemValues, List.count_flatMap,
    ← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  rfl

theorem ReductionDimerProvenance.catalogue_itemValues_perm (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (catalogue p items bulkLengths gaps hbulk).val.itemValues.Perm items := by
  classical
  apply List.perm_iff_count.mpr
  intro s
  rw [DimerCatalogue.itemValues_count, catalogue_weightSum_formula]
  simp only [ReductionChainTag.itemValues, List.count_nil, List.count_singleton, Nat.add_zero]
  induction items with
  | nil => simp
  | cons a items ih => simp_all [List.count_cons, Nat.add_comm]

end ProteinFolding.Tetrahedral

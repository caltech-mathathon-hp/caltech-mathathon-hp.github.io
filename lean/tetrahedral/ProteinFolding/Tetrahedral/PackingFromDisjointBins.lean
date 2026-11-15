import ProteinFolding.Cubic.Proofs.PackingFromLabels
import Mathlib.Algebra.BigOperators.Fin

/-! Positive item occurrences in disjoint exactly full buckets exhaust
the input when the total load is KB.  The output is a genuine list packing. -/

namespace ProteinFolding.Packing

open scoped BigOperators

theorem exact_of_disjoint_full_buckets (I : Instance)
    (hpos : ∀ s ∈ I.sizes, 0 < s)
    (htotal : I.sizes.sum = I.capacity * I.bins)
    (bucket : Fin I.bins → Finset (Fin I.sizes.length))
    (hdisjoint : ∀ b c, b ≠ c → Disjoint (bucket b) (bucket c))
    (hload : ∀ b, (∑ i ∈ bucket b, I.sizes.get i) = I.capacity) :
    ∃ parts, Exact I parts := by
  classical
  let U := Finset.univ.biUnion bucket
  have hpair : (Finset.univ : Finset (Fin I.bins)).toSet.PairwiseDisjoint bucket := by
    intro b _ c _ hbc
    exact hdisjoint b c hbc
  have hsumU : (∑ i ∈ U, I.sizes.get i) = I.capacity * I.bins := by
    dsimp only [U]
    rw [Finset.sum_biUnion hpair]
    simp only [hload, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hsumAll : (∑ i : Fin I.sizes.length, I.sizes.get i) = I.capacity * I.bins := by
    simpa only [List.get_eq_getElem, Fin.sum_univ_getElem] using htotal
  have hcover (i : Fin I.sizes.length) : ∃ b, i ∈ bucket b := by
    by_contra hnot
    have hi : i ∉ U := by
      intro hi
      obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hi
      exact hnot ⟨b, hb⟩
    have hstrict : (∑ j ∈ U, I.sizes.get j) < ∑ j : Fin I.sizes.length, I.sizes.get j := by
      apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i) hi
      · exact hpos _ (List.get_mem I.sizes i)
      · intro j _ _
        exact Nat.zero_le _
    omega
  let label (i : Fin I.sizes.length) : Fin I.bins := Classical.choose (hcover i)
  have hlabel (i : Fin I.sizes.length) : i ∈ bucket (label i) := Classical.choose_spec (hcover i)
  refine ⟨labelledParts I.sizes label, exact_of_label_sums I label htotal ?_⟩
  intro b
  have hsubset : (Finset.univ.filter (fun i => label i = b)) ⊆ bucket b := by
    intro i hi
    have heq := (Finset.mem_filter.mp hi).2
    simpa only [heq] using hlabel i
  calc
    (∑ i : Fin I.sizes.length with label i = b, I.sizes.get i) ≤
        ∑ i ∈ bucket b, I.sizes.get i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro i _ _
      exact Nat.zero_le _
    _ = I.capacity := hload b

end ProteinFolding.Packing

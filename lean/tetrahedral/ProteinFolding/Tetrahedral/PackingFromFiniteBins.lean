import ProteinFolding.Tetrahedral.PackingFromDisjointBins

/-! Packing extraction from arbitrary finite occurrence indices.  The
eligible values may be any permutation of the input, so catalogue indices
can be used directly without identifying equal-sized item occurrences. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem packing_of_finite_full_buckets {ι : Type*} [DecidableEq ι]
    (items : List ℕ) (B K : ℕ) (eligible : Finset ι) (size : ι → ℕ)
    (hperm : items.Perm (eligible.toList.map size))
    (hpos : ∀ i ∈ eligible, 0 < size i) (htotal : items.sum = B * K)
    (bucket : Fin K → Finset ι) (hsub : ∀ b, bucket b ⊆ eligible)
    (hdisjoint : ∀ b c, b ≠ c → Disjoint (bucket b) (bucket c))
    (hload : ∀ b, (∑ i ∈ bucket b, size i) = B) :
    ∃ parts : List (List ℕ), parts.length = K ∧ items.Perm parts.flatten ∧
      ∀ part ∈ parts, part.sum = B := by
  classical
  let U := Finset.univ.biUnion bucket
  have hUsub : U ⊆ eligible := by
    intro i hi
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hi
    exact hsub b hb
  have hpair : (Finset.univ : Finset (Fin K)).toSet.PairwiseDisjoint bucket := by
    intro b _ c _ hbc
    exact hdisjoint b c hbc
  have hsumU : (∑ i ∈ U, size i) = B * K := by
    dsimp only [U]
    rw [Finset.sum_biUnion hpair]
    simp only [hload, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hsumAll : (∑ i ∈ eligible, size i) = B * K := by
    have hs := hperm.sum_eq
    rw [← List.sum_toFinset size (Finset.nodup_toList eligible), Finset.toList_toFinset] at hs
    exact hs.symm.trans htotal
  have hU : U = eligible := by
    apply Finset.Subset.antisymm hUsub
    intro i hi
    by_contra hni
    have hstrict := Finset.sum_lt_sum_of_subset hUsub hi hni (hpos i hi)
      (fun j _ _ => Nat.zero_le (size j))
    omega
  let indices : List ι := (List.finRange K).flatMap (fun b => (bucket b).toList)
  have hnodup : indices.Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun b _ => Finset.nodup_toList _, ?_⟩
    apply (List.nodup_finRange K).imp
    intro b c hbc
    apply List.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp (hdisjoint b c hbc)
      (Finset.mem_toList.mp hi) (Finset.mem_toList.mp hj)
  have hindices : indices.Perm eligible.toList := by
    apply (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList eligible)).mpr
    intro i
    simp only [indices, List.mem_flatMap, List.mem_finRange, true_and, Finset.mem_toList]
    change (∃ b, i ∈ bucket b) ↔ i ∈ eligible
    rw [← hU]
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and]
  let parts := (List.finRange K).map (fun b => (bucket b).toList.map size)
  refine ⟨parts, by simp [parts], ?_, ?_⟩
  · have hp := hindices.map size
    change (((List.finRange K).flatMap (fun b => (bucket b).toList)).map size).Perm
      (eligible.toList.map size) at hp
    rw [List.map_flatMap] at hp
    have hp' : parts.flatten.Perm (eligible.toList.map size) := by
      simpa only [parts, List.flatMap_def] using hp
    exact hperm.trans hp'.symm
  · intro part hp
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
    rw [← List.sum_toFinset size (Finset.nodup_toList (bucket b)), Finset.toList_toFinset]
    exact hload b

end ProteinFolding.Tetrahedral

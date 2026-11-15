import ProteinFolding.Tetrahedral.RawProfile

/-! Ordered compression witnesses, retaining the keys needed for rigidity. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def RawKeysConvex (A : Finset ℤ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ k : ℤ, i ≤ k → k ≤ j → k ∈ A

theorem rawKeysConvex_singleton (b : ℤ) : RawKeysConvex {b} := by
  intro i hi j hj k hik hkj
  have hi' : i = b := by simpa using hi
  have hj' : j = b := by simpa using hj
  have hk : k = b := by omega
  simp [hk]

theorem rawKeysConvex_insert (A : Finset ℤ) (b : ℤ) (hmax : ∀ k ∈ A, k < b)
    (hconv : RawKeysConvex A) (hprev : b - 1 ∈ A) : RawKeysConvex (insert b A) := by
  intro i hi j hj k hik hkj
  rcases Finset.mem_insert.mp hi with hib | hiA
  · have hjle : j ≤ b := by
      rcases Finset.mem_insert.mp hj with hjb | hjA
      · omega
      · exact le_of_lt (hmax j hjA)
    have hk : k = b := by omega
    simp [hk]
  · rcases Finset.mem_insert.mp hj with hjb | hjA
    · by_cases hk : k = b
      · simp [hk]
      · exact Finset.mem_insert_of_mem (hconv i hiA (b - 1) hprev k hik (by omega))
    · exact Finset.mem_insert_of_mem (hconv i hiA j hjA k hik hkj)

structure RawProfileWitness (C : ℕ) (β : ℤ → ℕ) (A : Finset ℤ) where
  composition : PositiveComposition
  lastKey : ℤ
  last_mem : lastKey ∈ A
  last_max : ∀ j ∈ A, j ≤ lastKey
  mass_eq : composition.mass = ∑ j ∈ A, β j
  last_eq : composition.lastPart = β lastKey
  value_le : rawProfileValue C A β ≤ profileValue C 0 composition
  keys : List ℤ
  keys_set : keys.toFinset = A
  keys_sorted : keys.Pairwise (fun i j => i < j)
  parts_eq : composition.parts = keys.map β
  equality_convex : (∑ j ∈ A, β j) ≤ C →
    rawProfileValue C A β = profileValue C 0 composition → RawKeysConvex A

theorem rawProfile_witness_exists (C : ℕ) (β : ℤ → ℕ) (A : Finset ℤ)
    (hne : A.Nonempty) (hβ : ∀ k ∈ A, 0 < β k) :
    Nonempty (RawProfileWitness C β A) := by
  induction A using Finset.induction_on_max with
  | h0 => simp at hne
  | step b A hmax ih =>
    have hbnot : b ∉ A := by intro hb; exact lt_irrefl b (hmax b hb)
    have hbpos : 0 < β b := hβ b (Finset.mem_insert_self _ _)
    rcases A.eq_empty_or_nonempty with hnil | hA
    · subst A
      refine ⟨{
        composition := .single (β b) hbpos
        lastKey := b
        last_mem := by simp
        last_max := ?_
        mass_eq := by simp [PositiveComposition.mass]
        last_eq := rfl
        value_le := ?_
        keys := [b]
        keys_set := by simp
        keys_sorted := by simp
        parts_eq := rfl
        equality_convex := ?_ }⟩
      · intro j hj
        have hj' : j = b := by simpa using hj
        omega
      · simpa [profileValue] using (rawProfileValue_singleton C β b).le
      · intro _ _
        simpa using rawKeysConvex_singleton b
    · obtain ⟨w⟩ := ih hA (fun j hj => hβ j (Finset.mem_insert_of_mem hj))
      have hnewval : rawProfileValue C (insert b A) β ≤
          profileValue C 0 (.snoc w.composition (β b) hbpos) := by
        rw [rawProfileValue_insert_max C β A b hmax]
        change rawProfileValue C A β + _ ≤ profileValue C 0 w.composition +
          min (min (0 + w.composition.mass) (C - (0 + w.composition.mass)))
            (w.composition.lastPart * β b)
        simp only [Nat.zero_add]
        by_cases hprev : b - 1 ∈ A
        · have hlast : w.lastKey = b - 1 := by
            have h₁ := w.last_max (b - 1) hprev
            have h₂ := hmax w.lastKey w.last_mem
            omega
          rw [if_pos hprev, w.mass_eq, w.last_eq, hlast]
          exact Nat.add_le_add_right w.value_le _
        · rw [if_neg hprev, Nat.add_zero]
          have h := w.value_le
          omega
      refine ⟨{
        composition := .snoc w.composition (β b) hbpos
        lastKey := b
        last_mem := Finset.mem_insert_self _ _
        last_max := ?_
        mass_eq := ?_
        last_eq := rfl
        value_le := hnewval
        keys := w.keys ++ [b]
        keys_set := ?_
        keys_sorted := ?_
        parts_eq := ?_
        equality_convex := ?_ }⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_rfl
        · exact le_of_lt (hmax j hj)
      · simp [PositiveComposition.mass, Finset.sum_insert hbnot, w.mass_eq, Nat.add_comm]
      · ext j
        simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, Finset.mem_insert]
        have hj : j ∈ w.keys ↔ j ∈ A := by
          have hs : j ∈ w.keys.toFinset ↔ j ∈ A := by rw [w.keys_set]
          exact List.mem_toFinset.symm.trans hs
        rw [hj]
        exact or_comm
      · apply List.pairwise_append.mpr
        refine ⟨w.keys_sorted, by simp, ?_⟩
        intro i hi j hj
        have hj' : j = b := by simpa using hj
        subst j
        have hiA : i ∈ A := by
          have hm : i ∈ w.keys.toFinset := List.mem_toFinset.mpr hi
          simpa only [w.keys_set] using hm
        exact hmax i hiA
      · simp [PositiveComposition.parts, w.parts_eq, List.map_append]
      · intro hC heq
        have hC' : β b + (∑ j ∈ A, β j) ≤ C := by
          simpa only [Finset.sum_insert hbnot] using hC
        have hprefix : 0 < ∑ j ∈ A, β j := by
          rw [← w.mass_eq]
          exact w.composition.mass_pos
        have hroom : 0 < C - ∑ j ∈ A, β j := by omega
        have hprod : 0 < β w.lastKey * β b :=
          Nat.mul_pos (hβ w.lastKey (Finset.mem_insert_of_mem w.last_mem)) hbpos
        have hcap : 0 < min (min (∑ j ∈ A, β j) (C - ∑ j ∈ A, β j))
            (β w.lastKey * β b) := lt_min (lt_min hprefix hroom) hprod
        rw [rawProfileValue_insert_max C β A b hmax] at heq
        change rawProfileValue C A β + _ = profileValue C 0 w.composition +
          min (min (0 + w.composition.mass) (C - (0 + w.composition.mass)))
            (w.composition.lastPart * β b) at heq
        simp only [Nat.zero_add, w.mass_eq, w.last_eq] at heq
        have hprev : b - 1 ∈ A := by
          by_contra hnot
          rw [if_neg hnot, Nat.add_zero] at heq
          have h := w.value_le
          omega
        have hlast : w.lastKey = b - 1 := by
          have h₁ := w.last_max (b - 1) hprev
          have h₂ := hmax w.lastKey w.last_mem
          omega
        rw [if_pos hprev, hlast] at heq
        have heqold : rawProfileValue C A β = profileValue C 0 w.composition := by omega
        exact rawKeysConvex_insert A b hmax (w.equality_convex (by omega) heqold) hprev

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FrameForcingChainExhaustion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exactly as many two-site slots as singleton chains exhausts those chains.
This is independent of the order in which the slots are visited. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem disjoint_biUnion_fixed_card {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (C : ι → Finset α) (n : ℕ)
    (hcard : ∀ i ∈ I, (C i).card = n)
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j)) :
    (I.biUnion C).card = n * I.card := by
  classical
  rw [Finset.card_biUnion]
  · calc
      ∑ i ∈ I, (C i).card = ∑ _i ∈ I, n := Finset.sum_congr rfl hcard
      _ = n * I.card := by simp [Nat.mul_comm]
  · exact hdisjoint

theorem two_slot_family_exhausts_singletons {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]
    (C : ι → Finset α) (q : ι → ℕ) (E : κ → Finset α)
    (hpositive : ∀ i, 0 < q i) (hCcard : ∀ i, (C i).card = 2 * q i)
    (hCdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hEcard : ∀ k, (E k).card = 2)
    (hEdisjoint : ∀ k l, k ≠ l → Disjoint (E k) (E l))
    (hcover : ∀ k, ∀ x ∈ E k, ∃ i, x ∈ C i)
    (hclosed : ∀ k i, (C i ∩ E k).Nonempty → C i ⊆ E k)
    (hcount : (Finset.univ.filter (fun i => q i = 1)).card = Fintype.card κ) :
    (Finset.univ.filter (fun i => q i = 1)).biUnion C = Finset.univ.biUnion E := by
  classical
  let I := Finset.univ.filter (fun i => q i = 1)
  have hsub : Finset.univ.biUnion E ⊆ I.biUnion C := by
    intro x hx
    obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hxi⟩ := hcover k x hxk
    have hCi := hclosed k i ⟨x, Finset.mem_inter.mpr ⟨hxi, hxk⟩⟩
    have hle := Finset.card_le_card hCi
    rw [hCcard i, hEcard k] at hle
    have hqi : q i = 1 := by have hp := hpositive i; omega
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqi⟩, hxi⟩
  have hIcard : (I.biUnion C).card = 2 * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card I C 2]
    · exact congrArg (fun n => 2 * n) hcount
    · intro i hi
      rw [hCcard i, (Finset.mem_filter.mp hi).2]
    · intro i _ j _ hij
      exact hCdisjoint i j hij
  have hEunion : (Finset.univ.biUnion E).card = 2 * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card Finset.univ E 2]
    · simp
    · intro k _
      exact hEcard k
    · intro k _ l _ hkl
      exact hEdisjoint k l hkl
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hIcard, hEunion])).symm

end ProteinFolding.Tetrahedral

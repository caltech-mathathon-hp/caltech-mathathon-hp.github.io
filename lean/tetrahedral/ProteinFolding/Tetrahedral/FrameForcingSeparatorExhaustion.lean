import ProteinFolding.Tetrahedral.FrameForcingEntryExhaustion

/-! The K+1 disjoint four-site separator blocks exhaust the K+1 declared
size-two chains.  This is the cardinality step needed before extracting bins. -/

namespace ProteinFolding.Tetrahedral

theorem four_blocks_exhaust_double_chains {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]
    (C : ι → Finset α) (q : ι → ℕ) (W : κ → Finset α)
    (hCcard : ∀ i, (C i).card = 2 * q i)
    (hCdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hWcard : ∀ k, (W k).card = 4)
    (hWdisjoint : ∀ k l, k ≠ l → Disjoint (W k) (W l))
    (hsubset : ∀ k, W k ⊆ (Finset.univ.filter (fun i => q i = 2)).biUnion C)
    (hcount : (Finset.univ.filter (fun i => q i = 2)).card = Fintype.card κ) :
    (Finset.univ.filter (fun i => q i = 2)).biUnion C = Finset.univ.biUnion W := by
  classical
  let I := Finset.univ.filter (fun i => q i = 2)
  have hsub : Finset.univ.biUnion W ⊆ I.biUnion C := by
    intro x hx
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
    exact hsubset k hk
  have hIcard : (I.biUnion C).card = 4 * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card I C 4]
    · exact congrArg (4 * ·) hcount
    · intro i hi
      rw [hCcard i, (Finset.mem_filter.mp hi).2]
    · intro i _ j _ hne
      exact hCdisjoint i j hne
  have hWunion : (Finset.univ.biUnion W).card = 4 * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card Finset.univ W 4]
    · simp
    · intro k _
      exact hWcard k
    · intro k _ l _ hne
      exact hWdisjoint k l hne
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hIcard, hWunion])).symm

end ProteinFolding.Tetrahedral

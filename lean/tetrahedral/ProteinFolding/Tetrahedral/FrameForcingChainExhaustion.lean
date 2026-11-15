import ProteinFolding.Tetrahedral.FrameForcingMatching

/-! Finite cardinality consequences for an isolated six-site slot partitioned
into complete, disjoint dimer chains. -/

namespace ProteinFolding.Tetrahedral

theorem six_component_one_three_chain {ι α : Type*} [DecidableEq α]
    (C : ι → Finset α) (q : ι → ℕ) (W : Finset α)
    (hW : W.card = 6) (hpositive : ∀ i, 0 < q i) (hcard : ∀ i, (C i).card = 2 * q i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : ∀ x ∈ W, ∃ i, x ∈ C i)
    (hclosed : ∀ i, (C i ∩ W).Nonempty → C i ⊆ W)
    (hnoOne : ∀ i, q i = 1 → Disjoint (C i) W) :
    ∃ i, q i = 3 ∧ C i = W := by
  have hnW : W.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hnW
  obtain ⟨i, hxi⟩ := hcover x hx
  have hCi : C i ⊆ W := hclosed i ⟨x, Finset.mem_inter.mpr ⟨hxi, hx⟩⟩
  have hqi : 2 * q i ≤ 6 := by
    simpa only [hcard i, hW] using Finset.card_le_card hCi
  have hqi1 : q i ≠ 1 := by
    intro heq
    exact Finset.disjoint_left.mp (hnoOne i heq) hxi hx
  have hqi3 : q i = 3 := by
    by_contra hbad
    have hi2 : q i = 2 := by have hp := hpositive i; omega
    have hCcard : (C i).card = 4 := by rw [hcard i, hi2]
    obtain ⟨y, hyW, hyCi⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show (C i).card < W.card by omega)
    obtain ⟨j, hyj⟩ := hcover y hyW
    have hCj : C j ⊆ W := hclosed j ⟨y, Finset.mem_inter.mpr ⟨hyj, hyW⟩⟩
    have hij : i ≠ j := by intro heq; subst j; exact hyCi hyj
    have hqj1 : q j ≠ 1 := by
      intro heq
      exact Finset.disjoint_left.mp (hnoOne j heq) hyj hyW
    have hsum := Finset.card_le_card (Finset.union_subset hCi hCj)
    rw [Finset.card_union_of_disjoint (hdisjoint i j hij), hCcard, hcard j, hW] at hsum
    have hp := hpositive j
    omega
  refine ⟨i, hqi3, ?_⟩
  apply Finset.eq_of_subset_of_card_le hCi
  rw [hcard i, hqi3, hW]

end ProteinFolding.Tetrahedral

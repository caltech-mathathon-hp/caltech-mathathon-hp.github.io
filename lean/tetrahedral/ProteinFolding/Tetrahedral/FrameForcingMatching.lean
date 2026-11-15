import ProteinFolding.Tetrahedral.PathMatching
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

/-! The parity argument that fills the even slots before the terminal corner
is identified, avoiding a circular ordering of the soundness steps. -/

namespace ProteinFolding.Tetrahedral

structure FinitePairFamily (ι α : Type*) where
  point : ι × Bool → α
  injective : Function.Injective point

namespace FinitePairFamily

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

def covered (F : FinitePairFamily ι α) : Finset α := Finset.univ.image F.point

theorem covered_card (F : FinitePairFamily ι α) :
    F.covered.card = 2 * Fintype.card ι := by
  rw [covered, Finset.card_image_of_injective _ F.injective]
  simp [Fintype.card_prod, Nat.mul_comm]

theorem covered_inter_card (F : FinitePairFamily ι α) (W : Finset α)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W) :
    ∃ n : ℕ, (F.covered ∩ W).card = 2 * n := by
  let I : Finset ι := Finset.univ.filter (fun i => F.point (i, false) ∈ W)
  have himage : (I ×ˢ (Finset.univ : Finset Bool)).image F.point = F.covered ∩ W := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, b⟩, hib, rfl⟩ := Finset.mem_image.mp hx
      have hi := (Finset.mem_filter.mp (Finset.mem_product.mp hib).1).2
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩, ?_⟩
      cases b with
      | false => exact hi
      | true => exact (hclosed i).mp hi
    · intro hx
      have h := Finset.mem_inter.mp hx
      obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp h.1
      apply Finset.mem_image.mpr
      refine ⟨(i, b), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases b with
      | false => exact h.2
      | true => exact (hclosed i).mpr h.2
  refine ⟨I.card, ?_⟩
  rw [← himage, Finset.card_image_of_injective _ F.injective, Finset.card_product]
  simp [Nat.mul_comm]

theorem uncovered_card_le_one (F : FinitePairFamily ι α) (V : Finset α)
    (hsub : F.covered ⊆ V) (hcard : V.card ≤ 2 * Fintype.card ι + 1) :
    (V \ F.covered).card ≤ 1 := by
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [F.covered_card] at h
  omega

/-- An isolated even component must be fully covered when at most one site
of the whole ambient set is uncovered by the disjoint pairs. -/
theorem even_component_fully_covered (F : FinitePairFamily ι α) (V W : Finset α)
    (hsub : F.covered ⊆ V) (hcard : V.card ≤ 2 * Fintype.card ι + 1)
    (hWV : W ⊆ V) (hWeven : W.card % 2 = 0)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W) :
    W ⊆ F.covered := by
  have hmissing := F.uncovered_card_le_one V hsub hcard
  have hmissingW : (W \ F.covered).card ≤ 1 := by
    have hsub' : W \ F.covered ⊆ V \ F.covered := by
      intro x hx
      have h := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hWV h.1, h.2⟩
    exact (Finset.card_le_card hsub').trans hmissing
  obtain ⟨n, hn⟩ := F.covered_inter_card W hclosed
  have hpartition := Finset.card_sdiff_add_card_inter W F.covered
  rw [Finset.inter_comm] at hpartition
  rw [hn] at hpartition
  have hzero : (W \ F.covered).card = 0 := by omega
  have heq : W \ F.covered = ∅ := Finset.card_eq_zero.mp hzero
  exact Finset.sdiff_eq_empty_iff_subset.mp heq

end FinitePairFamily

end ProteinFolding.Tetrahedral

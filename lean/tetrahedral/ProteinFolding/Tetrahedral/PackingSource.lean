import ProteinFolding.Cubic.Proofs.SATPackingComputable
import ProteinFolding.Common.CookLevinProofUniversal

/-! The unary exact-capacity packing source for Section 6.
The existing finite-machine SAT reduction always emits even items, so its
proved hardness also applies to the exact-capacity problem without an evenness
restriction. The source Cook--Levin theorem is proved in Common. -/

namespace ProteinFolding.Tetrahedral.PackingSource

open Computability Turing

abbrev Instance := ProteinFolding.Packing.Instance

abbrev instanceEncoding := ProteinFolding.Packing.instanceEncoding

/-- Positive item sizes, positive capacity and number of bins, total load KB,
and an occurrence-preserving partition into exactly full bins. -/
def Accepts (I : Instance) : Prop :=
  Packing.WellFormed I ∧ I.sizes.sum = I.bins * I.capacity ∧
    ∃ parts : List (List ℕ), Packing.Exact I parts

theorem accepts_iff (I : Instance) : Accepts I ↔
    0 < I.bins ∧ 0 < I.capacity ∧ (∀ s ∈ I.sizes, 0 < s) ∧
      I.sizes.sum = I.bins * I.capacity ∧
      ∃ parts : List (List ℕ), parts.length = I.bins ∧
        I.sizes.Perm parts.flatten ∧ ∀ p ∈ parts, p.sum = I.capacity := by
  simp only [Accepts, Packing.WellFormed, Packing.Exact]
  tauto

theorem instanceEncoding_length (I : Instance) :
    (instanceEncoding.encode I).length =
      I.sizes.sum + I.sizes.length + I.capacity + I.bins + 2 :=
  Packing.instanceEncoding_length I

theorem modified_iff_accepts_of_even (I : Instance)
    (heven : ∀ s ∈ I.sizes, Even s) : Packing.ModifiedAccepts I ↔ Accepts I := by
  constructor
  · rintro ⟨hw, _, htotal, parts, hparts⟩
    exact ⟨hw, by simpa only [Nat.mul_comm] using htotal, parts, hparts⟩
  · rintro ⟨hw, htotal, parts, hparts⟩
    exact ⟨hw, heven, by simpa only [Nat.mul_comm] using htotal, parts, hparts⟩

theorem sortedToModified_items_even (I : ThreeDimensionalMatching.Instance) :
    ∀ s ∈ (MatchingPacking.sortedToModified I).sizes, Even s := by
  intro s hs
  unfold MatchingPacking.sortedToModified at hs
  split at hs
  · split at hs
    · exact MatchingPacking.yesPacking_accepts.2.1 s hs
    · change s ∈ List.map (2 * ·) (MatchingPacking.sortedRawInstance I).sizes at hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
      exact ⟨a, by omega⟩
  · simp [MatchingPacking.noPacking] at hs

/-- The source function is unchanged from the existing polynomial-time
CNF-to-unary-packing machine. -/
abbrev fromCNF := SATPacking.cnfToSortedModified

theorem fromCNF_correct (φ : SAT.CNF) : Accepts (fromCNF φ) ↔ SAT.Satisfiable φ :=
  (modified_iff_accepts_of_even (fromCNF φ)
    (sortedToModified_items_even (ThreeDimensionalMatching.SourceQueries.cnfToBlockMatching φ))).symm.trans
      (SATPacking.cnfToSortedModified_correct φ)

noncomputable def fromCNF_computable :
    TM2ComputableInPolyTime SAT.cnfEncoding instanceEncoding fromCNF :=
  SATPacking.cnfToSortedModifiedComputable

theorem fromCNF_karp :
    KarpReduces SAT.cnfEncoding instanceEncoding SAT.Satisfiable Accepts :=
  ⟨fromCNF, ⟨fromCNF_computable⟩, fun φ => (fromCNF_correct φ).symm⟩

/-- Unconditional strong unary exact-packing hardness, in the project's
universal finite-machine definition of NP-hardness. -/
theorem unary_exact_capacity_npHard : NPHard instanceEncoding Accepts :=
  npHard_of_cookLevin_reduction SAT.CookLevinUniversal.cookLevin fromCNF_karp

#print axioms unary_exact_capacity_npHard

end ProteinFolding.Tetrahedral.PackingSource

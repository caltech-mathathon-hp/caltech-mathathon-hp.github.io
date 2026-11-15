import ProteinFolding.Common.CookLevinProofFiniteFamilyCompiler

/-! Actual selection from finitely many polynomial machines using a unary
index. The controller compares the index with each fixed exceptional value;
all indices above a fixed bound use the final child machine. -/

namespace ProteinFolding.SAT.CookLevinClampedCompiler

open Computability Turing TM2CompositionPoly CookLevinFiniteCompiler

theorem exceptionPatch {X Y : Type} (ex : FinEncoding X) (ey : FinEncoding Y)
    (index : X → ℕ) (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat index)
    (f : ℕ → X → Y) (h : ∀ i, TM2ComputableInPolyTime ex ey (f i))
    (fallback : ℕ) (s : Finset ℕ) :
    ∃ g : X → Y, Nonempty (TM2ComputableInPolyTime ex ey g) ∧
      ∀ x, g x = if index x ∈ s then f (index x) x else f fallback x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨f fallback, ⟨h fallback⟩, by simp⟩
  | @insert i s his ih =>
    obtain ⟨g, ⟨hg⟩, he⟩ := ih
    let g' : X → Y := fun x => if index x = i then f i x else g x
    have hm : TM2ComputableInPolyTime ex ey g' := by
      let hp := compose hi (fixedEqualityComputable unaryFinEncodingNat i)
      let hc := TM2Conditional.iteComputable hp (h i) hg
      simpa only [g', Function.comp_def, decide_eq_true_eq] using hc
    refine ⟨g', ⟨hm⟩, ?_⟩
    intro x
    by_cases hxi : index x = i
    · simp [g', hxi]
    · simp [g', hxi, he]

noncomputable def clampedFamilyComputable {X Y : Type} (ex : FinEncoding X)
    (ey : FinEncoding Y) (index : X → ℕ)
    (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat index)
    (bound : ℕ) (f : ℕ → X → Y) (h : ∀ i, TM2ComputableInPolyTime ex ey (f i)) :
    TM2ComputableInPolyTime ex ey (fun x => f (min (index x) bound) x) := by
  classical
  have hm : Nonempty (TM2ComputableInPolyTime ex ey (fun x => f (min (index x) bound) x)) := by
    obtain ⟨g, ⟨hg⟩, he⟩ := exceptionPatch ex ey index hi f h bound (Finset.range bound)
    have same : g = (fun x => f (min (index x) bound) x) := by
      funext x
      rw [he x]
      by_cases hb : index x < bound
      · simp only [Finset.mem_range, hb, if_true, Nat.min_eq_left (Nat.le_of_lt hb)]
      · simp only [Finset.mem_range, hb, if_false, Nat.min_eq_right (Nat.le_of_not_gt hb)]
    rw [← same]
    exact ⟨hg⟩
  exact Classical.choice hm

end ProteinFolding.SAT.CookLevinClampedCompiler

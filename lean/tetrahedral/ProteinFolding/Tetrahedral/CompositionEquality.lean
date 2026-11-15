import ProteinFolding.Tetrahedral.LargePart

/-! Equality in the small-part branch of Lemma 5.3. -/

namespace ProteinFolding.Tetrahedral

/-- A window with exactly its initial square-root slope cannot cross the
next square breakpoint. -/
theorem rootSum_linear_window_end (a l : ℕ)
    (heq : rootSum (a + l) = rootSum a + Nat.sqrt a * l) :
    a + l ≤ (Nat.sqrt a + 1) ^ 2 := by
  have hw := rootWindow_enhanced_lower a l
  have hm := rootSum_mono (Nat.le_add_right a l)
  have hs := add_nextSquareDistance a
  unfold rootWindow at hw
  omega

/-- Type I of Lemma 5.3, with the already-bounded prefix hypothesis explicit.
The prefix bound is discharged by the one-sided upper-bound theorem. -/
theorem small_part_optimality_conditions (p : PositiveComposition) (l : ℕ)
    (hl : 0 < l) (ht : p.lastPart ≤ Nat.sqrt p.mass)
    (hp : p.value ≤ rootSum p.mass)
    (heq : (PositiveComposition.snoc p l hl).value = rootSum (p.mass + l)) :
    p.value = rootSum p.mass ∧ p.lastPart = Nat.sqrt p.mass ∧
      Nat.sqrt p.mass * l ≤ p.mass ∧ p.mass + l ≤ (Nat.sqrt p.mass + 1) ^ 2 := by
  change p.value + min p.mass (p.lastPart * l) = rootSum (p.mass + l) at heq
  have hstep := rootSum_small_part_step p.mass p.lastPart l ht
  have hnumeric : rootSum p.mass + min p.mass (p.lastPart * l) =
      rootSum (p.mass + l) := by omega
  obtain ⟨hpart, hproduct, hwindow⟩ :=
    rootSum_small_part_equality p.mass p.lastPart l ht hl hnumeric
  exact ⟨by omega, hpart, hproduct, rootSum_linear_window_end p.mass l hwindow⟩

end ProteinFolding.Tetrahedral

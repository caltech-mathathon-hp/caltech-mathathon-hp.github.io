import ProteinFolding.Tetrahedral.BackwardInitial
import ProteinFolding.Tetrahedral.BackwardInduction
import ProteinFolding.Tetrahedral.CanonicalComposition
import ProteinFolding.Tetrahedral.CompositionEquality
import ProteinFolding.Tetrahedral.LargePartEquality

/-! Unconditional one-sided optimisation and its local equality alternatives. -/

namespace ProteinFolding.Tetrahedral

/-- Lemma 5.1(iii)–(iv), now with its initial case and induction discharged. -/
theorem backwardRootBound : BackwardRootBound :=
  backwardRootBound_of_initial backward_initial

/-- The inequality of Lemma 5.1, with no unproved arithmetic hypotheses. -/
theorem largePartStep : LargePartStep := largePartStep_of_backwardRootBound backwardRootBound

/-- The upper bound in Lemma 5.2, without a remaining transition premise. -/
theorem oneSided_le_rootSum (c : PositiveComposition) : c.value ≤ rootSum c.mass :=
  oneSided_le_rootSum_of_largePartStep largePartStep c

/-- F(x) is the attained maximum over positive compositions of x. -/
theorem oneSided_optimum (x : ℕ) (hx : 0 < x) :
    ∃ c : PositiveComposition, c.mass = x ∧ c.value = rootSum x ∧
      ∀ d : PositiveComposition, d.mass = x → d.value ≤ c.value := by
  obtain ⟨c, hmass, hvalue⟩ := exists_composition_attaining_rootSum x hx
  refine ⟨c, hmass, hvalue, ?_⟩
  intro d hd
  rw [hvalue]
  simpa only [hd] using oneSided_le_rootSum d

theorem backwardRootBound_strict (a t : ℕ) (ha : 0 < a) (ht : Nat.sqrt a < t)
    (hta : t ≤ a) (hsmall : a - Nat.sqrt a ^ 2 < Nat.sqrt a) :
    rootSum (a - t) + (a - t) + a < rootSum a + Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t) := by
  have hinit := backward_initial_strict a ha (by omega) hsmall
  have hinitial : rootSum (a - (Nat.sqrt a + 1)) + (a - (Nat.sqrt a + 1)) + a + 1 ≤
      rootSum a + Nat.sqrt a * (a / (Nat.sqrt a + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a)
          (a / (Nat.sqrt a + 1)) (a % (Nat.sqrt a + 1)) := by omega
  have h := backwardRootBound_from_initial_with_slack a 1 hinitial t ht hta
  omega

theorem large_part_equality_size (a t l : ℕ) (ha : 0 < a) (ht : Nat.sqrt a < t)
    (hta : t ≤ a)
    (heq : rootSum (a - t) + (a - t) + min a (t * l) = rootSum (a + l)) :
    Nat.sqrt a ^ 2 + Nat.sqrt a ≤ a := by
  by_contra hnot
  have hlo := Nat.sqrt_le' a
  have hsmall : a - Nat.sqrt a ^ 2 < Nat.sqrt a := by omega
  have hleft := backwardRootBound_strict a t ha ht hta hsmall
  have hdecomp : a = (a / t) * t + a % t := by nlinarith [Nat.mod_add_div a t]
  have htwo := largePart_two_point_bound a (Nat.sqrt a) t (a / t) (a % t)
    (nextSquareDistance a) l hdecomp (by omega)
  have hright := rootWindow_enhanced_lower a l
  have hmono := rootSum_mono (Nat.le_add_right a l)
  unfold rootWindow at hright
  omega

/-- Optimality in the large branch forces equality in the numerical step. -/
theorem optimal_large_numeric (p : PositiveComposition) (l : ℕ) (hl : 0 < l)
    (ht : Nat.sqrt p.mass < p.lastPart)
    (heq : (PositiveComposition.snoc p l hl).value = rootSum (p.mass + l)) :
    rootSum (p.mass - p.lastPart) + (p.mass - p.lastPart) +
      min p.mass (p.lastPart * l) = rootSum (p.mass + l) := by
  have hstep := largePartStep p.mass p.lastPart l p.mass_pos ht p.lastPart_le_mass hl
  cases p with
  | single t htpos =>
    simpa [PositiveComposition.mass, PositiveComposition.lastPart,
      PositiveComposition.value, rootSum_zero] using heq
  | snoc q t htpos =>
    have hq := oneSided_le_rootSum q
    have hmin := min_le_left q.mass (q.lastPart * t)
    change q.value + min q.mass (q.lastPart * t) + min (q.mass + t) (t * l) =
      rootSum (q.mass + t + l) at heq
    simp only [PositiveComposition.mass, PositiveComposition.lastPart,
      Nat.add_sub_cancel] at hstep ⊢
    omega

/-- Lemma 5.3: the two local alternatives for an optimal composition. -/
theorem optimal_snoc_cases (p : PositiveComposition) (l : ℕ) (hl : 0 < l)
    (heq : (PositiveComposition.snoc p l hl).value = rootSum (p.mass + l)) :
    (p.lastPart = Nat.sqrt p.mass ∧ Nat.sqrt p.mass * l ≤ p.mass ∧
      p.mass + l ≤ (Nat.sqrt p.mass + 1) ^ 2 ∧ p.value = rootSum p.mass) ∨
    (Nat.sqrt p.mass < p.lastPart ∧ Nat.sqrt p.mass ^ 2 + Nat.sqrt p.mass ≤ p.mass ∧
      l ≤ Nat.sqrt p.mass) := by
  by_cases hsmall : p.lastPart ≤ Nat.sqrt p.mass
  · obtain ⟨hprefix, hpart, hprod, hend⟩ :=
      small_part_optimality_conditions p l hl hsmall (oneSided_le_rootSum p) heq
    exact Or.inl ⟨hpart, hprod, hend, hprefix⟩
  · have ht : Nat.sqrt p.mass < p.lastPart := by omega
    have hn := optimal_large_numeric p l hl ht heq
    exact Or.inr ⟨ht, large_part_equality_size p.mass p.lastPart l p.mass_pos ht
      p.lastPart_le_mass hn, large_part_equality_length backwardRootBound p.mass p.lastPart l
      p.mass_pos ht p.lastPart_le_mass hn⟩

end ProteinFolding.Tetrahedral

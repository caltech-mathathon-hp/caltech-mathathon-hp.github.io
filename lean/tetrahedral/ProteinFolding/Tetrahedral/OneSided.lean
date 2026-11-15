import ProteinFolding.Tetrahedral.RootSum

/-!
# The one-sided composition problem in Section 5.3

Positive compositions are built by appending a positive final part. Their
value follows exactly the breakpoint recurrence in Lemma 5.2. The theorem
below reduces the upper bound to the large-part arithmetic step of Lemma 5.1.
That step is recorded as a Prop-valued target and is NOT assumed globally.
Its proof, the attainment construction and the equality cases remain open.
-/

namespace ProteinFolding.Tetrahedral

inductive PositiveComposition where
  | single (part : ℕ) (positive : 0 < part)
  | snoc (init : PositiveComposition) (part : ℕ) (positive : 0 < part)

namespace PositiveComposition

def mass : PositiveComposition → ℕ
  | .single p _ => p
  | .snoc c p _ => c.mass + p

def lastPart : PositiveComposition → ℕ
  | .single p _ => p
  | .snoc _ p _ => p

def parts : PositiveComposition → List ℕ
  | .single p _ => [p]
  | .snoc c p _ => c.parts ++ [p]

/-- U(β): sum of min(breakpoint, product of the two adjacent parts). -/
def value : PositiveComposition → ℕ
  | .single _ _ => 0
  | .snoc c p _ => c.value + min c.mass (c.lastPart * p)

theorem mass_pos (c : PositiveComposition) : 0 < c.mass := by
  cases c with
  | single p hp => exact hp
  | snoc c p hp => simp only [mass]; omega

theorem lastPart_pos (c : PositiveComposition) : 0 < c.lastPart := by
  cases c with
  | single p hp => exact hp
  | snoc c p hp => exact hp

theorem lastPart_le_mass (c : PositiveComposition) : c.lastPart ≤ c.mass := by
  cases c with
  | single p _ => exact le_rfl
  | snoc c p _ => simp only [lastPart, mass]; omega

theorem parts_sum (c : PositiveComposition) : c.parts.sum = c.mass := by
  induction c with
  | single p _ => simp [parts, mass]
  | snoc c p _ ih => simp [parts, mass, ih]

theorem parts_positive (c : PositiveComposition) : ∀ p ∈ c.parts, 0 < p := by
  induction c with
  | single p hp => simpa [parts] using hp
  | snoc c p hp ih =>
    intro q hq
    simp only [parts, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact ih q hq
    · exact hp

end PositiveComposition

/-- The inequality part of Lemma 5.1, after telescoping the two F-windows.
This definition records an unproved proof target, not an axiom or a theorem. -/
def LargePartStep : Prop := ∀ a t l : ℕ, 0 < a → Nat.sqrt a < t → t ≤ a → 0 < l →
  rootSum (a - t) + (a - t) + min a (t * l) ≤ rootSum (a + l)

/-- Lemma 5.2's upper-bound argument, with its exact remaining arithmetic
dependency explicit. No proof of `LargePartStep` is claimed by this theorem. -/
theorem oneSided_le_rootSum_of_largePartStep (hstar : LargePartStep)
    (c : PositiveComposition) : c.value ≤ rootSum c.mass := by
  cases c with
  | single p _ => exact Nat.zero_le _
  | snoc p l hl =>
    by_cases hsmall : p.lastPart ≤ Nat.sqrt p.mass
    · have ih := oneSided_le_rootSum_of_largePartStep hstar p
      have hs := rootSum_small_part_step p.mass p.lastPart l hsmall
      change p.value + min p.mass (p.lastPart * l) ≤ rootSum (p.mass + l)
      omega
    · cases p with
      | single t ht =>
        have hs := hstar t t l ht (by simpa [PositiveComposition.lastPart,
          PositiveComposition.mass] using hsmall) le_rfl hl
        simpa [PositiveComposition.value, PositiveComposition.mass,
          PositiveComposition.lastPart, rootSum_zero] using hs
      | snoc p t ht =>
        have ih := oneSided_le_rootSum_of_largePartStep hstar p
        have hs := hstar (p.mass + t) t l (by omega)
          (by simpa [PositiveComposition.lastPart, PositiveComposition.mass]
            using hsmall) (by omega) hl
        rw [Nat.add_sub_cancel] at hs
        have hmin := min_le_left p.mass (p.lastPart * t)
        change p.value + min p.mass (p.lastPart * t) + min (p.mass + t) (t * l) ≤
          rootSum (p.mass + t + l)
        omega
termination_by c.mass
decreasing_by all_goals (simp_all [PositiveComposition.mass] <;> omega)

end ProteinFolding.Tetrahedral

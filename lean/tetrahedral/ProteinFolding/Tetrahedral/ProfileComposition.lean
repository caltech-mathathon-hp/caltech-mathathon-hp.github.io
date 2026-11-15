import ProteinFolding.Tetrahedral.Optimization

/-! The two-sided composition functional of Section 5.2 and its splitting laws. -/

namespace ProteinFolding.Tetrahedral

namespace PositiveComposition

def firstPart : PositiveComposition → ℕ
  | .single p _ => p
  | .snoc c _ _ => c.firstPart

def append (c : PositiveComposition) : PositiveComposition → PositiveComposition
  | .single p hp => .snoc c p hp
  | .snoc d p hp => .snoc (append c d) p hp

theorem append_mass (c d : PositiveComposition) : (c.append d).mass = c.mass + d.mass := by
  induction d with
  | single p hp => rfl
  | snoc d p hp ih => simp [append, mass, ih, Nat.add_assoc]

theorem append_last (c d : PositiveComposition) : (c.append d).lastPart = d.lastPart := by
  cases d <;> rfl

theorem append_first (c d : PositiveComposition) : (c.append d).firstPart = c.firstPart := by
  induction d with
  | single p hp => rfl
  | snoc d p hp ih => exact ih

theorem append_parts (c d : PositiveComposition) : (c.append d).parts = c.parts ++ d.parts := by
  induction d with
  | single p hp => rfl
  | snoc d p hp ih => simp [append, parts, ih, List.append_assoc]

def reverse : PositiveComposition → PositiveComposition
  | .single p hp => .single p hp
  | .snoc c p hp => (PositiveComposition.single p hp).append c.reverse

theorem reverse_mass (c : PositiveComposition) : c.reverse.mass = c.mass := by
  induction c with
  | single p hp => rfl
  | snoc c p hp ih => simp [reverse, append_mass, mass, ih, Nat.add_comm]

theorem reverse_first (c : PositiveComposition) : c.reverse.firstPart = c.lastPart := by
  cases c with
  | single p hp => rfl
  | snoc c p hp => simp [reverse, append_first, firstPart, lastPart]

theorem reverse_last (c : PositiveComposition) : c.reverse.lastPart = c.firstPart := by
  induction c with
  | single p hp => rfl
  | snoc c p hp ih => simp [reverse, append_last, firstPart, ih]

theorem reverse_parts (c : PositiveComposition) : c.reverse.parts = c.parts.reverse := by
  induction c with
  | single p hp => rfl
  | snoc c p hp ih => simp [reverse, append_parts, parts, ih, List.reverse_append]

end PositiveComposition

/-- Capped breakpoint value with a specified starting offset. -/
def profileValue (C offset : ℕ) : PositiveComposition → ℕ
  | .single _ _ => 0
  | .snoc c p _ => profileValue C offset c +
      min (min (offset + c.mass) (C - (offset + c.mass))) (c.lastPart * p)

/-- V(β), with C equal to the total mass of the composition. -/
def twoSidedValue (c : PositiveComposition) : ℕ := profileValue c.mass 0 c

theorem profileValue_append (C offset : ℕ) (c d : PositiveComposition) :
    profileValue C offset (c.append d) = profileValue C offset c +
      min (min (offset + c.mass) (C - (offset + c.mass))) (c.lastPart * d.firstPart) +
      profileValue C (offset + c.mass) d := by
  induction d with
  | single p hp => simp [PositiveComposition.append, profileValue,
      PositiveComposition.firstPart]
  | snoc d p hp ih =>
    simp only [PositiveComposition.append, profileValue, PositiveComposition.append_mass,
      PositiveComposition.append_last, PositiveComposition.firstPart, ih]
    simp only [Nat.add_assoc]

theorem profileValue_le_oneSided (C : ℕ) (c : PositiveComposition) :
    profileValue C 0 c ≤ c.value := by
  induction c with
  | single p hp => exact le_rfl
  | snoc c p hp ih =>
    have hmin : min (min c.mass (C - c.mass)) (c.lastPart * p) ≤
        min c.mass (c.lastPart * p) := min_le_min (min_le_left _ _) le_rfl
    simpa only [profileValue, PositiveComposition.value, Nat.zero_add] using Nat.add_le_add ih hmin

/-- Reversal exchanges the two distances to the ends of the interval [0,C]. -/
theorem profileValue_mirror (C offset : ℕ) (c : PositiveComposition)
    (hC : offset + c.mass ≤ C) :
    profileValue C offset c = profileValue C (C - offset - c.mass) c.reverse := by
  induction c generalizing offset with
  | single p hp => rfl
  | snoc c p hp ih =>
    have hc : offset + c.mass ≤ C := by change offset + (c.mass + p) ≤ C at hC; omega
    have hrest : C - offset - (c.mass + p) + p = C - offset - c.mass := by
      change offset + (c.mass + p) ≤ C at hC
      omega
    have hflip : min (C - offset - c.mass) (C - (C - offset - c.mass)) =
        min (offset + c.mass) (C - (offset + c.mass)) := by
      have hfirst : C - offset - c.mass = C - (offset + c.mass) := by omega
      have hsecond : C - (C - offset - c.mass) = offset + c.mass := by omega
      rw [hsecond, hfirst]
      exact min_comm _ _
    simp only [PositiveComposition.reverse, PositiveComposition.mass, profileValue_append,
      profileValue, PositiveComposition.lastPart, PositiveComposition.reverse_first,
      Nat.zero_add]
    rw [hrest, ← ih offset hc]
    rw [hflip]
    simp only [Nat.mul_comm, Nat.add_comm]

theorem twoSidedValue_reverse (c : PositiveComposition) : twoSidedValue c.reverse = twoSidedValue c := by
  unfold twoSidedValue
  rw [PositiveComposition.reverse_mass]
  have h := profileValue_mirror c.mass 0 c (by omega)
  simpa using h.symm

theorem profileValue_mono_cap (c : PositiveComposition) (offset C D : ℕ) (hCD : C ≤ D) :
    profileValue C offset c ≤ profileValue D offset c := by
  induction c with
  | single p hp => exact le_rfl
  | snoc c p hp ih =>
    have hcap := Nat.sub_le_sub_right hCD (offset + c.mass)
    have hmin : min (min (offset + c.mass) (C - (offset + c.mass))) (c.lastPart * p) ≤
        min (min (offset + c.mass) (D - (offset + c.mass))) (c.lastPart * p) :=
      min_le_min (min_le_min le_rfl hcap) le_rfl
    exact Nat.add_le_add ih hmin

/-- Appending any positive part strictly increases the two-sided value:
the cap grows monotonically and the new breakpoint contributes positively. -/
theorem twoSidedValue_snoc_strict (c : PositiveComposition) (p : ℕ) (hp : 0 < p) :
    twoSidedValue c < twoSidedValue (.snoc c p hp) := by
  have hmono := profileValue_mono_cap c 0 c.mass (c.mass + p) (by omega)
  have hprod := Nat.mul_pos c.lastPart_pos hp
  have hterm : 0 < min (min c.mass p) (c.lastPart * p) :=
    lt_min (lt_min c.mass_pos hp) hprod
  change profileValue c.mass 0 c < profileValue (c.mass + p) 0 c +
    min (min (0 + c.mass) (c.mass + p - (0 + c.mass))) (c.lastPart * p)
  simp only [Nat.zero_add, Nat.add_sub_cancel_left]
  omega

end ProteinFolding.Tetrahedral

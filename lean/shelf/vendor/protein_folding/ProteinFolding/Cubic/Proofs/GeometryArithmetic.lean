import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Natural-number AM--GM and its rigidity case, for lattice projection counts.
The proof uses only polynomial identities and finite order case splits. -/

namespace ProteinFolding.CubicGeometry.Arithmetic

theorem sorted_gap (a u v : ℕ) :
    (a + (a + u) + (a + u + v)) ^ 3 =
      27 * a * (a + u) * (a + u + v) +
        9 * a * u ^ 2 + 9 * a * u * v + 9 * a * v ^ 2 +
        8 * u ^ 3 + 12 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3 := by ring

theorem sorted_cube_bound (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbc
  rw [sorted_gap]
  omega

theorem sorted_rigidity (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (h : (a + b + c) ^ 3 ≤ 27 * a * b * c) : a = b ∧ b = c := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbc
  rw [sorted_gap] at h
  have hu : u ^ 3 = 0 := by omega
  have hv : v ^ 3 = 0 := by omega
  have hu0 : u = 0 := by simpa using hu
  have hv0 : v = 0 := by simpa using hv
  simp [hu0, hv0]

theorem sorted_triple (A B C : ℕ) :
    ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ a + b + c = A + B + C ∧ a * b * c = A * B * C ∧
      (A = a ∨ A = b ∨ A = c) ∧ (B = a ∨ B = b ∨ B = c) ∧ (C = a ∨ C = b ∨ C = c) := by
  rcases le_total A B with hab | hba
  · rcases le_total B C with hbc | hcb
    · exact ⟨A, B, C, hab, hbc, rfl, rfl, by simp, by simp, by simp⟩
    · rcases le_total A C with hac | hca
      · exact ⟨A, C, B, hac, hcb, by omega, by ac_rfl, by simp, by simp, by simp⟩
      · exact ⟨C, A, B, hca, hab, by omega, by ac_rfl, by simp, by simp, by simp⟩
  · rcases le_total A C with hac | hca
    · exact ⟨B, A, C, hba, hac, by omega, by ac_rfl, by simp, by simp, by simp⟩
    · rcases le_total B C with hbc | hcb
      · exact ⟨B, C, A, hbc, hca, by omega, by ac_rfl, by simp, by simp, by simp⟩
      · exact ⟨C, B, A, hcb, hba, by omega, by ac_rfl, by simp, by simp, by simp⟩

theorem cube_bound (A B C : ℕ) : 27 * A * B * C ≤ (A + B + C) ^ 3 := by
  obtain ⟨a, b, c, hab, hbc, hs, hp, _⟩ := sorted_triple A B C
  have h := sorted_cube_bound a b c hab hbc
  calc
    27 * A * B * C = 27 * (a * b * c) := by rw [hp]; ring
    _ ≤ (a + b + c) ^ 3 := by simpa only [Nat.mul_assoc] using h
    _ = (A + B + C) ^ 3 := by rw [hs]

theorem product_rigidity (A B C d : ℕ) (hp : d ^ 3 ≤ A * B * C)
    (hs : A + B + C ≤ 3 * d) : A = d ∧ B = d ∧ C = d := by
  obtain ⟨a, b, c, hab, hbc, hsum, hprod, hA, hB, hC⟩ := sorted_triple A B C
  have hpow := Nat.pow_le_pow_left hs 3
  have hrigid : (a + b + c) ^ 3 ≤ 27 * a * b * c := by
    calc
      (a + b + c) ^ 3 = (A + B + C) ^ 3 := by rw [hsum]
      _ ≤ (3 * d) ^ 3 := hpow
      _ = 27 * d ^ 3 := by ring
      _ ≤ 27 * (A * B * C) := Nat.mul_le_mul_left 27 hp
      _ = 27 * a * b * c := by rw [← hprod]; ring
  obtain ⟨heq1, heq2⟩ := sorted_rigidity a b c hab hbc hrigid
  have heq : a = d := by
    have hcube : d ^ 3 ≤ a ^ 3 := by
      calc
        d ^ 3 ≤ A * B * C := hp
        _ = a * b * c := hprod.symm
        _ = a ^ 3 := by rw [← heq2, ← heq1]; ring
    have had : a ≤ d := by omega
    by_contra hne
    have halt : a < d := by omega
    have hstrict := Nat.pow_lt_pow_left halt (by decide : 3 ≠ 0)
    omega
  omega

theorem three_mul_le_sum (A B C d : ℕ) (hp : d ^ 3 ≤ A * B * C) :
    3 * d ≤ A + B + C := by
  have hbound := cube_bound A B C
  by_contra h
  have hlt : A + B + C < 3 * d := by omega
  have hstrict := Nat.pow_lt_pow_left hlt (by decide : 3 ≠ 0)
  nlinarith

end ProteinFolding.CubicGeometry.Arithmetic

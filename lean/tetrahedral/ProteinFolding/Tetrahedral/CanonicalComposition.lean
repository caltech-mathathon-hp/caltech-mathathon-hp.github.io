import ProteinFolding.Tetrahedral.OneSided

/-!
# Attainment in the one-sided composition problem

The canonical square composition c_m = (1,1,2,2,...,m-1,m-1,m)
has mass m² and value F(m²). Truncating the next two parts gives a
composition attaining F(x) at every positive integer x (Lemma 5.2).
-/

namespace ProteinFolding.Tetrahedral

open PositiveComposition

/-- `canonicalSquare n` is c_(n+1), so an empty composition is unnecessary. -/
def canonicalSquare : ℕ → PositiveComposition
  | 0 => .single 1 (by decide)
  | n + 1 => .snoc (.snoc (canonicalSquare n) (n + 1) (by omega)) (n + 2) (by omega)

theorem canonicalSquare_last (n : ℕ) : (canonicalSquare n).lastPart = n + 1 := by
  cases n <;> rfl

theorem canonicalSquare_mass (n : ℕ) : (canonicalSquare n).mass = (n + 1) ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (canonicalSquare n).mass + (n + 1) + (n + 2) = (n + 1 + 1) ^ 2
    rw [ih]
    ring

theorem canonicalSquare_value (n : ℕ) : (canonicalSquare n).value = rootSum ((n + 1) ^ 2) := by
  induction n with
  | zero => simp [canonicalSquare, value, rootSum]
  | succ n ih =>
    change (canonicalSquare n).value +
      min (canonicalSquare n).mass ((canonicalSquare n).lastPart * (n + 1)) +
      min ((canonicalSquare n).mass + (n + 1)) ((n + 1) * (n + 2)) = _
    rw [canonicalSquare_mass, canonicalSquare_last, ih]
    have hp : (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
    have hq : (n + 1) * (n + 2) = (n + 1) ^ 2 + (n + 1) := by ring
    rw [hp, hq, min_self, min_self]
    rw [rootSum_square_succ (n + 1)]
    ring

/-- Every positive size admits a composition whose value is exactly F(size).
This attainment statement does not assume the large-part upper bound. -/
theorem exists_composition_attaining_rootSum (x : ℕ) (hx : 0 < x) :
    ∃ c : PositiveComposition, c.mass = x ∧ c.value = rootSum x := by
  let s := Nat.sqrt x
  let r := x - s ^ 2
  have hs : 0 < s := Nat.sqrt_pos.mpr hx
  have hsquare : s ^ 2 ≤ x := Nat.sqrt_le' x
  have hupper : x < (s + 1) ^ 2 := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' x
  have hparts : x = s ^ 2 + r := by dsimp [r]; omega
  have hr : r ≤ 2 * s := by nlinarith
  let c := canonicalSquare (s - 1)
  have hindex : s - 1 + 1 = s := by omega
  have hmass : c.mass = s ^ 2 := by dsimp [c]; rw [canonicalSquare_mass, hindex]
  have hlast : c.lastPart = s := by dsimp [c]; rw [canonicalSquare_last, hindex]
  have hvalue : c.value = rootSum (s ^ 2) := by dsimp [c]; rw [canonicalSquare_value, hindex]
  have hF : rootSum x = rootSum (s ^ 2) + s * r := by
    rw [hparts]
    exact rootSum_square_block s r (by omega)
  by_cases hrzero : r = 0
  · refine ⟨c, ?_, ?_⟩
    · omega
    · rw [hvalue, hF, hrzero, Nat.mul_zero, Nat.add_zero]
  · by_cases hrsmall : r ≤ s
    · refine ⟨.snoc c r (by omega), ?_, ?_⟩
      · change c.mass + r = x
        omega
      · change c.value + min c.mass (c.lastPart * r) = rootSum x
        rw [hvalue, hmass, hlast, min_eq_right (by nlinarith), hF]
    · refine ⟨.snoc (.snoc c s hs) (r - s) (by omega), ?_, ?_⟩
      · change c.mass + s + (r - s) = x
        omega
      · change c.value + min c.mass (c.lastPart * s) +
          min (c.mass + s) (s * (r - s)) = rootSum x
        rw [hvalue, hmass, hlast]
        have hsprod : s * s = s ^ 2 := by ring
        have hsmall : r - s ≤ s := by omega
        have hmulsmall := Nat.mul_le_mul_left s hsmall
        rw [hsprod, min_self, min_eq_right (by nlinarith [hmulsmall])]
        rw [hF]
        have hdecomp : r = s + (r - s) := by omega
        have hmul := congrArg (fun z => s * z) hdecomp
        dsimp only at hmul
        rw [Nat.mul_add] at hmul
        nlinarith

end ProteinFolding.Tetrahedral

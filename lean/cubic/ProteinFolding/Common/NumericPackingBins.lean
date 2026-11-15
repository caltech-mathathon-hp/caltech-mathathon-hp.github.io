import ProteinFolding.Common.NumericPackingTokens

/-! Decoding exact bins in the bounded numerical matching gadget. The input
packing imposes no type or cardinality restriction on a bin: both are derived
from its numerical load. Real/dummy synchronization is then supplied by
`selector_quad_iff`. -/

namespace ProteinFolding.NumericPacking

theorem sum_value_digits (n : ℕ) (ts : List Token) :
    (ts.map (Token.value n)).sum = ts.length * offset n +
      digits (base n) ((ts.map (Token.xDigit n)).sum) ((ts.map (Token.yDigit n)).sum)
        ((ts.map (Token.zDigit n)).sum) ((ts.map Token.status).sum) ((ts.map Token.kind).sum) := by
  induction ts with
  | nil => simp [digits, radix]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Token.value_eq, ih, digits, radix]
    ring

theorem sum_projection_le (ts : List Token) (f : Token → ℕ) (bound : ℕ)
    (hf : ∀ t ∈ ts, f t ≤ bound) : (ts.map f).sum ≤ ts.length * bound := by
  have h := sum_upper_bound (ts.map f) bound (by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hf t ht)
  simpa only [List.length_map] using h

/-- All five numerical columns can be recovered without carries. -/
theorem exact_bin_digits (n : ℕ) (ts : List Token)
    (hv : ∀ t ∈ ts, t.Valid n) (hsum : (ts.map (Token.value n)).sum = capacity n) :
    (ts.map (Token.xDigit n)).sum = n ∧ (ts.map (Token.yDigit n)).sum = n ∧
      (ts.map (Token.zDigit n)).sum = n ∧ (ts.map Token.status).sum = 3 ∧
        (ts.map Token.kind).sum = 15 := by
  have hlen := exact_bin_length n ts hv hsum
  have hx : (ts.map (Token.xDigit n)).sum ≤ 4 * n := by
    simpa only [hlen] using sum_projection_le ts (Token.xDigit n) n
      (fun t ht => (t.digit_bounds n (hv t ht)).1)
  have hy : (ts.map (Token.yDigit n)).sum ≤ 4 * n := by
    simpa only [hlen] using sum_projection_le ts (Token.yDigit n) n
      (fun t ht => (t.digit_bounds n (hv t ht)).2.1)
  have hz : (ts.map (Token.zDigit n)).sum ≤ 4 * n := by
    simpa only [hlen] using sum_projection_le ts (Token.zDigit n) n
      (fun t ht => (t.digit_bounds n (hv t ht)).2.2.1)
  have hs : (ts.map Token.status).sum ≤ 12 := by
    simpa only [hlen] using sum_projection_le ts Token.status 3
      (fun t ht => (t.digit_bounds n (hv t ht)).2.2.2.1)
  have hk : (ts.map Token.kind).sum ≤ 32 := by
    simpa only [hlen] using sum_projection_le ts Token.kind 8
      (fun t ht => (t.digit_bounds n (hv t ht)).2.2.2.2)
  rw [sum_value_digits, hlen] at hsum
  have he : radix (base n) [(ts.map (Token.xDigit n)).sum, (ts.map (Token.yDigit n)).sum,
      (ts.map (Token.zDigit n)).sum, (ts.map Token.status).sum, (ts.map Token.kind).sum] =
      radix (base n) [n, n, n, 3, 15] := Nat.add_left_cancel hsum
  have hd : [(ts.map (Token.xDigit n)).sum, (ts.map (Token.yDigit n)).sum,
      (ts.map (Token.zDigit n)).sum, (ts.map Token.status).sum, (ts.map Token.kind).sum] =
      [n, n, n, 3, 15] := by
    refine radix_injective (base_pos n)
      [(ts.map (Token.xDigit n)).sum, (ts.map (Token.yDigit n)).sum,
        (ts.map (Token.zDigit n)).sum, (ts.map Token.status).sum, (ts.map Token.kind).sum]
      [n, n, n, 3, 15] rfl ?_ ?_ he
    all_goals intro d hd
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    all_goals rcases hd with rfl | rfl | rfl | rfl | rfl <;> dsimp [base] <;> omega
  simpa only [List.cons.injEq, and_true] using hd

def kindCount (k : ℕ) (ts : List Token) : ℕ := (ts.filter (fun t => t.kind == k)).length

theorem kindCount_length (ts : List Token) :
    kindCount 1 ts + kindCount 2 ts + kindCount 4 ts + kindCount 8 ts = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [kindCount, Token.kind] at * <;> omega

theorem kindCount_sum (ts : List Token) :
    (ts.map Token.kind).sum =
      kindCount 1 ts + 2 * kindCount 2 ts + 4 * kindCount 4 ts + 8 * kindCount 8 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [kindCount, Token.kind] at * <;> omega

/-- Every exact bin contains exactly one selector and one X, Y and Z token. -/
theorem exact_bin_kind_counts (n : ℕ) (ts : List Token)
    (hv : ∀ t ∈ ts, t.Valid n) (hsum : (ts.map (Token.value n)).sum = capacity n) :
    kindCount 1 ts = 1 ∧ kindCount 2 ts = 1 ∧ kindCount 4 ts = 1 ∧ kindCount 8 ts = 1 := by
  have hlen := exact_bin_length n ts hv hsum
  have hk := (exact_bin_digits n ts hv hsum).2.2.2.2
  rw [kindCount_sum] at hk
  apply kind_counts_forced _ _ _ _ _ hk
  rw [kindCount_length, hlen]

end ProteinFolding.NumericPacking

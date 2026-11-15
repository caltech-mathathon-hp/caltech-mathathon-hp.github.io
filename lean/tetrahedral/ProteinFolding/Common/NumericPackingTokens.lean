import ProteinFolding.Common.NumericPacking
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Four item types for the bounded matching-to-packing construction.
Each item has magnitude below twice `(8n+64)^6`. Exact bins contain four
items; this is proved from numerical bounds, rather than imposed on packing
witnesses. The type digit subsequently forces one item of each kind. -/

namespace ProteinFolding.NumericPacking

inductive Token where
  | x : ℕ → Bool → Token
  | y : ℕ → Bool → Token
  | z : ℕ → Bool → Token
  | triple : ℕ → ℕ → ℕ → Token
  deriving DecidableEq, Repr

def Token.Valid (n : ℕ) : Token → Prop
  | .x i _ | .y i _ | .z i _ => i < n
  | .triple i j k => i < n ∧ j < n ∧ k < n

def Token.kind : Token → ℕ
  | .x _ _ => 1 | .y _ _ => 2 | .z _ _ => 4 | .triple _ _ _ => 8

def Token.status : Token → ℕ
  | .x _ r => if r then 1 else 0
  | .y _ r => if r then 2 else 0
  | .z _ r => if r then 0 else 3
  | .triple _ _ _ => 0

def Token.xDigit (n : ℕ) : Token → ℕ
  | .x i _ => i + 1 | .triple i _ _ => n - (i + 1) | _ => 0

def Token.yDigit (n : ℕ) : Token → ℕ
  | .y i _ => i + 1 | .triple _ i _ => n - (i + 1) | _ => 0

def Token.zDigit (n : ℕ) : Token → ℕ
  | .z i _ => i + 1 | .triple _ _ i => n - (i + 1) | _ => 0

def Token.value (n : ℕ) : Token → ℕ
  | .x i r => xToken n i r
  | .y i r => yToken n i r
  | .z i r => zToken n i r
  | .triple i j k => selector n i j k

theorem Token.value_eq (n : ℕ) (t : Token) :
    t.value n = offset n + digits (base n) (t.xDigit n) (t.yDigit n) (t.zDigit n)
      t.status t.kind := by cases t <;> rfl

theorem Token.digit_bounds (n : ℕ) (t : Token) (h : t.Valid n) :
    t.xDigit n ≤ n ∧ t.yDigit n ≤ n ∧ t.zDigit n ≤ n ∧
      t.status ≤ 3 ∧ t.kind ≤ 8 := by
  cases t with
  | x i r => cases r <;> simp_all [Token.Valid, Token.xDigit, Token.yDigit, Token.zDigit,
      Token.status, Token.kind] <;> omega
  | y i r => cases r <;> simp_all [Token.Valid, Token.xDigit, Token.yDigit, Token.zDigit,
      Token.status, Token.kind] <;> omega
  | z i r => cases r <;> simp_all [Token.Valid, Token.xDigit, Token.yDigit, Token.zDigit,
      Token.status, Token.kind] <;> omega
  | triple i j k => simp_all [Token.Valid, Token.xDigit, Token.yDigit, Token.zDigit,
      Token.status, Token.kind]

theorem offset_dominates (n : ℕ) : 3 * base n ^ 5 < offset n := by
  have hb : 3 < base n := by dsimp [base]; omega
  have hp : 0 < base n ^ 5 := Nat.pow_pos (base_pos n)
  change 3 * base n ^ 5 < base n ^ 5 * base n
  nlinarith

theorem Token.value_bounds (n : ℕ) (t : Token) (h : t.Valid n) :
    offset n ≤ t.value n ∧ t.value n < offset n + base n ^ 5 := by
  rw [Token.value_eq]
  refine ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ?_ _⟩
  obtain ⟨hx, hy, hz, hs, hk⟩ := t.digit_bounds n h
  apply radix_lt_pow (base_pos n)
    [t.xDigit n, t.yDigit n, t.zDigit n, t.status, t.kind]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> dsimp [base] <;> omega

/-- These bounds give polynomial magnitude, not merely binary code length. -/
theorem Token.value_polynomial_bound (n : ℕ) (t : Token) (h : t.Valid n) :
    t.value n < 2 * (8 * n + 64) ^ 6 := by
  obtain ⟨_, hu⟩ := t.value_bounds n h
  have hd := offset_dominates n
  change t.value n < 2 * offset n
  omega

theorem sum_lower_bound (xs : List ℕ) (lo : ℕ) (h : ∀ x ∈ xs, lo ≤ x) :
    xs.length * lo ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    nlinarith

theorem sum_upper_bound (xs : List ℕ) (hi : ℕ) (h : ∀ x ∈ xs, x ≤ hi) :
    xs.sum ≤ xs.length * hi := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    nlinarith

/-- Exact packing cannot use fewer or more than four of these items per bin. -/
theorem exact_bin_length (n : ℕ) (ts : List Token)
    (hv : ∀ t ∈ ts, t.Valid n) (hsum : (ts.map (Token.value n)).sum = capacity n) :
    ts.length = 4 := by
  have hlo : ts.length * offset n ≤ capacity n := by
    rw [← hsum]
    have h := sum_lower_bound (ts.map (Token.value n)) (offset n) (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact (t.value_bounds n (hv t ht)).1)
    simpa only [List.length_map] using h
  have hhi : capacity n ≤ ts.length * (offset n + base n ^ 5) := by
    rw [← hsum]
    have h := sum_upper_bound (ts.map (Token.value n)) (offset n + base n ^ 5) (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact (t.value_bounds n (hv t ht)).2.le)
    simpa only [List.length_map] using h
  have hcap := capacity_lt_five_offsets n
  have hdom := offset_dominates n
  have hbase : 4 * offset n ≤ capacity n := Nat.le_add_right _ _
  have hlenlo : 4 ≤ ts.length := by
    by_contra hn
    have hlen : ts.length ≤ 3 := by omega
    have hm := Nat.mul_le_mul_right (offset n + base n ^ 5) hlen
    nlinarith
  have hlenhi : ts.length ≤ 4 := by
    by_contra hn
    have hlen : 5 ≤ ts.length := by omega
    have hm := Nat.mul_le_mul_right (offset n) hlen
    omega
  omega

/-- The type sum 15 and the four-item bound force one token of every kind. -/
theorem kind_counts_forced (x y z t : ℕ)
    (hlen : x + y + z + t ≤ 4) (hsum : x + 2 * y + 4 * z + 8 * t = 15) :
    x = 1 ∧ y = 1 ∧ z = 1 ∧ t = 1 := by omega

end ProteinFolding.NumericPacking

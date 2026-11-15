import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Bounded numerical gadgets for the strong-hardness chain.

Three-dimensional matching can be represented by one selector and three
element tokens per bin. The status digit 1,2,0 for real X,Y,Z tokens, versus
0,0,3 for dummy tokens, forces all three choices to be real or all dummy.
Only five radix digits are used, so the resulting numbers have polynomial
magnitude. This file proves the arithmetic gadget, not the full reduction or
any hardness claim. -/

namespace ProteinFolding.NumericPacking

def radix (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + b * radix b ds

theorem radix_injective {b : ℕ} (hb : 0 < b) (xs ys : List ℕ)
    (hlen : xs.length = ys.length)
    (hx : ∀ d ∈ xs, d < b) (hy : ∀ d ∈ ys, d < b)
    (he : radix b xs = radix b ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxy : x = y := by
        have hm := congrArg (fun n => n % b) he
        simpa only [radix, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (hx x (by simp)), Nat.mod_eq_of_lt (hy y (by simp))] using hm
      have htail : radix b xs = radix b ys := by
        have hd := congrArg (fun n => n / b) he
        simpa only [radix, Nat.add_mul_div_left _ _ hb,
          Nat.div_eq_of_lt (hx x (by simp)), Nat.div_eq_of_lt (hy y (by simp)), Nat.zero_add] using hd
      exact congrArg₂ List.cons hxy (ih ys (by simpa using hlen)
        (fun d hd => hx d (by simp [hd])) (fun d hd => hy d (by simp [hd])) htail)

theorem radix_lt_pow {b : ℕ} (_hb : 0 < b) (ds : List ℕ)
    (hds : ∀ d ∈ ds, d < b) : radix b ds < b ^ ds.length := by
  induction ds with
  | nil => simp [radix]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have ht := ih (fun a ha => hds a (by simp [ha]))
    change d + b * radix b ds < b ^ (ds.length + 1)
    calc
      d + b * radix b ds < b + b * radix b ds := Nat.add_lt_add_right hd _
      _ = b * (radix b ds + 1) := by ring
      _ ≤ b * b ^ ds.length := Nat.mul_le_mul_left b (by omega)
      _ = b ^ (ds.length + 1) := by rw [Nat.pow_succ]; ring

def base (n : ℕ) : ℕ := 8 * n + 64

def offset (n : ℕ) : ℕ := base n ^ 6

def digits (b x y z status kind : ℕ) : ℕ := radix b [x, y, z, status, kind]

def xToken (n i : ℕ) (real : Bool) : ℕ :=
  offset n + digits (base n) (i + 1) 0 0 (if real then 1 else 0) 1

def yToken (n j : ℕ) (real : Bool) : ℕ :=
  offset n + digits (base n) 0 (j + 1) 0 (if real then 2 else 0) 2

def zToken (n k : ℕ) (real : Bool) : ℕ :=
  offset n + digits (base n) 0 0 (k + 1) (if real then 0 else 3) 4

def selector (n i j k : ℕ) : ℕ :=
  offset n + digits (base n) (n - (i + 1)) (n - (j + 1)) (n - (k + 1)) 0 8

def capacity (n : ℕ) : ℕ :=
  4 * offset n + digits (base n) n n n 3 15

theorem base_pos (n : ℕ) : 0 < base n := by simp [base]

theorem offset_pos (n : ℕ) : 0 < offset n := by
  exact Nat.pow_pos (base_pos n)

theorem status_sync (rx ry rz : Bool) :
    (if rx then 1 else 0) + (if ry then 2 else 0) + (if rz then 0 else 3) = (3 : ℕ) ↔
      rx = ry ∧ ry = rz := by
  cases rx <;> cases ry <;> cases rz <;> decide

/-- A selector and three element tokens fill a bin exactly when all three
indices match the selector and their real/dummy choices agree. -/
theorem selector_quad_iff (n i j k a b c : ℕ)
    (hi : i < n) (hj : j < n) (hk : k < n)
    (ha : a < n) (hb : b < n) (hc : c < n) (rx ry rz : Bool) :
    selector n i j k + xToken n a rx + yToken n b ry + zToken n c rz = capacity n ↔
      a = i ∧ b = j ∧ c = k ∧ rx = ry ∧ ry = rz := by
  let s := (if rx then 1 else 0) + (if ry then 2 else 0) + (if rz then 0 else 3)
  have hs : s ≤ 6 := by dsimp [s]; cases rx <;> cases ry <;> cases rz <;> decide
  have hsum : selector n i j k + xToken n a rx + yToken n b ry + zToken n c rz =
      4 * offset n + digits (base n)
        (n - (i + 1) + (a + 1)) (n - (j + 1) + (b + 1))
        (n - (k + 1) + (c + 1)) s 15 := by
    dsimp [selector, xToken, yToken, zToken, digits, radix, s]
    ring
  rw [hsum]
  change 4 * offset n + _ = 4 * offset n + digits (base n) n n n 3 15 ↔ _
  rw [Nat.add_left_cancel_iff]
  constructor
  · intro he
    have hdigits : [n - (i + 1) + (a + 1), n - (j + 1) + (b + 1),
        n - (k + 1) + (c + 1), s, 15] = [n, n, n, 3, 15] := by
      refine radix_injective (base_pos n)
        [n - (i + 1) + (a + 1), n - (j + 1) + (b + 1), n - (k + 1) + (c + 1), s, 15]
        [n, n, n, 3, 15] rfl ?_ ?_ he
      all_goals intro d hd
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      all_goals rcases hd with rfl | rfl | rfl | rfl | rfl <;> dsimp [base] <;> omega
    simp only [List.cons.injEq, and_true] at hdigits
    obtain ⟨hx, hy, hz, hstatus⟩ := hdigits
    have hsync := (status_sync rx ry rz).mp hstatus
    exact ⟨by omega, by omega, by omega, hsync⟩
  · rintro ⟨heqa, heqb, heqc, hxy, hyz⟩
    rw [heqa, heqb, heqc]
    have hstatus : s = 3 := (status_sync rx ry rz).mpr ⟨hxy, hyz⟩
    have hx : n - (i + 1) + (i + 1) = n := by omega
    have hy : n - (j + 1) + (j + 1) = n := by omega
    have hz : n - (k + 1) + (k + 1) = n := by omega
    rw [hx, hy, hz, hstatus]

theorem capacity_lt_five_offsets (n : ℕ) : capacity n < 5 * offset n := by
  have hl : digits (base n) n n n 3 15 < base n ^ 5 := by
    apply radix_lt_pow (base_pos n) [n, n, n, 3, 15]
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> dsimp [base] <;> omega
  have hp : base n ^ 5 ≤ offset n := by
    have hb : 1 ≤ base n := by have := base_pos n; omega
    exact pow_le_pow_right₀ hb (by decide : 5 ≤ 6)
  dsimp [capacity]
  omega

theorem xToken_ge_offset (n i : ℕ) (r : Bool) : offset n ≤ xToken n i r := Nat.le_add_right _ _
theorem yToken_ge_offset (n i : ℕ) (r : Bool) : offset n ≤ yToken n i r := Nat.le_add_right _ _
theorem zToken_ge_offset (n i : ℕ) (r : Bool) : offset n ≤ zToken n i r := Nat.le_add_right _ _
theorem selector_ge_offset (n i j k : ℕ) : offset n ≤ selector n i j k := Nat.le_add_right _ _

end ProteinFolding.NumericPacking

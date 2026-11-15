import ProteinFolding.Tetrahedral.RootSum

/-! The discrete convexity estimate for the large central part in Claim U. -/

namespace ProteinFolding.Tetrahedral

def rootG (y : ℕ) : ℕ := rootSum y + y

@[simp] theorem rootG_zero : rootG 0 = 0 := by simp [rootG]

theorem rootG_succ (y : ℕ) : rootG (y + 1) = rootG y + Nat.sqrt y + 1 := by
  unfold rootG
  rw [rootSum_succ]
  omega

theorem rootG_mono : Monotone rootG := by
  intro a b hab
  have h := rootSum_mono hab
  unfold rootG
  omega

theorem rootG_convex_transfer_one (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    rootG a + rootG b ≤ rootG (a - 1) + rootG (b + 1) := by
  have heq : a = a - 1 + 1 := by omega
  have hleft : rootG a = rootG (a - 1) + Nat.sqrt (a - 1) + 1 := by
    calc
      rootG a = rootG (a - 1 + 1) := congrArg rootG heq
      _ = _ := rootG_succ _
  have hright := rootG_succ b
  have hsqrt := Nat.sqrt_le_sqrt (show a - 1 ≤ b by omega)
  omega

theorem rootG_convex_transfer (a b n : ℕ) (hab : a ≤ b) (hn : n ≤ a) :
    rootG a + rootG b ≤ rootG (a - n) + rootG (b + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (show n ≤ a by omega)
    have hstep := rootG_convex_transfer_one (a - n) (b + n) (by omega) (by omega)
    have hleft : a - n - 1 = a - (n + 1) := by omega
    have hright : b + n + 1 = b + (n + 1) := by omega
    rw [hleft, hright] at hstep
    exact hprev.trans hstep

theorem rootG_endpoint_bound_ordered (U V a b : ℕ) (hab : a ≤ b)
    (_ha : a ≤ U) (hb : b ≤ U) (hsum : a + b ≤ U + V) :
    rootG a + rootG b ≤ rootG U + rootG V := by
  let d := min a (U - b)
  have hd : d ≤ a := min_le_left _ _
  have htransfer := rootG_convex_transfer a b d hab hd
  by_cases hfill : U - b ≤ a
  · have heq : d = U - b := min_eq_right hfill
    have hright : b + d = U := by omega
    have hleft : a - d ≤ V := by omega
    have hmono := rootG_mono hleft
    rw [hright] at htransfer
    omega
  · have heq : d = a := min_eq_left (by omega)
    rw [heq, Nat.sub_self, rootG_zero, zero_add] at htransfer
    have hmono := rootG_mono (show b + a ≤ U by omega)
    omega

/-- Under a fixed coordinate cap and a sum cap, convexity places the maximum
at the two endpoints. This formulation also covers zero endpoint values. -/
theorem rootG_endpoint_bound (U V a b : ℕ)
    (ha : a ≤ U) (hb : b ≤ U) (hsum : a + b ≤ U + V) :
    rootG a + rootG b ≤ rootG U + rootG V := by
  rcases le_total a b with hab | hba
  · exact rootG_endpoint_bound_ordered U V a b hab ha hb hsum
  · have h := rootG_endpoint_bound_ordered U V b a hba hb ha (by omega)
    omega

theorem square_sub_one_sqrt (m : ℕ) (hm : 0 < m) : Nat.sqrt (m ^ 2 - 1) = m - 1 := by
  cases m with
  | zero => omega
  | succ n =>
    have heq : (n + 1) ^ 2 - 1 = n ^ 2 + 2 * n := by
      have hsub := Nat.sub_add_cancel (show 1 ≤ (n + 1) ^ 2 by nlinarith)
      nlinarith
    change Nat.sqrt ((n + 1) ^ 2 - 1) = n
    rw [heq]
    exact Nat.sqrt_add_eq' n (by omega)

theorem rootSum_square_sub_one (m : ℕ) (hm : 0 < m) :
    rootSum (m ^ 2 - 1) + (m - 1) = rootSum (m ^ 2) := by
  have hpos : 0 < m ^ 2 := by nlinarith
  have heq : m ^ 2 - 1 + 1 = m ^ 2 := by omega
  have h := rootSum_succ (m ^ 2 - 1)
  rw [heq, square_sub_one_sqrt m hm] at h
  exact h.symm

theorem rootSum_square_sub_self (m : ℕ) (hm : 0 < m) :
    rootSum (m ^ 2 - m) + m * (m - 1) = rootSum (m ^ 2) := by
  cases m with
  | zero => omega
  | succ n =>
    have heq : (n + 1) ^ 2 - (n + 1) = n ^ 2 + n := by
      have hsub := Nat.sub_add_cancel (show n + 1 ≤ (n + 1) ^ 2 by nlinarith)
      nlinarith
    have hstart := rootSum_square_block n n (by omega)
    have hend := rootSum_square_succ n
    change rootSum ((n + 1) ^ 2 - (n + 1)) + (n + 1) * n = rootSum ((n + 1) ^ 2)
    rw [heq, hstart, hend]
    ring

/-- Exact evaluation of the endpoint sum in Claim U, avoiding subtraction. -/
theorem rootG_square_endpoints_add (m : ℕ) (hm : 0 < m) :
    rootG (m ^ 2 - 1) + rootG (m ^ 2 - m) + m = 2 * rootSum (m ^ 2) + m ^ 2 := by
  have h₁ := rootSum_square_sub_one m hm
  have h₂ := rootSum_square_sub_self m hm
  have hsquare : m ≤ m ^ 2 := by nlinarith
  have hsub₁ := Nat.sub_add_cancel (show 1 ≤ m ^ 2 by omega)
  have hsub₂ := Nat.sub_add_cancel hsquare
  have hpred : m - 1 + 1 = m := by omega
  have hmul := congrArg (fun x => m * x) hpred
  dsimp only at hmul
  rw [Nat.mul_add, Nat.mul_one] at hmul
  unfold rootG
  nlinarith

theorem rootG_square_endpoints_formula (m : ℕ) (hm : 0 < m) :
    rootG (m ^ 2 - 1) + rootG (m ^ 2 - m) = 2 * rootSum (m ^ 2) + m ^ 2 - m := by
  have h := rootG_square_endpoints_add m hm
  omega

theorem rootG_square_endpoints_lt_octahedralNumber (m : ℕ) (hm : 0 < m) :
    rootG (m ^ 2 - 1) + rootG (m ^ 2 - m) < octahedralNumber m := by
  have h := rootG_square_endpoints_add m hm
  unfold octahedralNumber
  omega

/-- The large-central-part case: the maximum occurs at deficits {1,m}. -/
theorem rootG_large_central_part_bound (m v v' : ℕ) (hm : 0 < m)
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hvm : v ≤ m ^ 2) (hv'm : v' ≤ m ^ 2)
    (hsum : m + 1 ≤ v + v') :
    rootG (m ^ 2 - v) + rootG (m ^ 2 - v') ≤
      rootG (m ^ 2 - 1) + rootG (m ^ 2 - m) := by
  have hmM : m ≤ m ^ 2 := by nlinarith
  apply rootG_endpoint_bound
  · omega
  · omega
  · omega

/-- The strict bound required by Claim U when the middle part has length ≥m+1. -/
theorem rootG_large_central_part_lt (m v v' : ℕ) (hm : 0 < m)
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hvm : v ≤ m ^ 2) (hv'm : v' ≤ m ^ 2)
    (hsum : m + 1 ≤ v + v') :
    rootG (m ^ 2 - v) + rootG (m ^ 2 - v') < octahedralNumber m :=
  (rootG_large_central_part_bound m v v' hm hv hv' hvm hv'm hsum).trans_lt
    (rootG_square_endpoints_lt_octahedralNumber m hm)

/-- The small-central-part numerical estimate, Claim U Case B with b<m. -/
theorem rootSum_small_central_part_lt (m v v' : ℕ) (hm : 0 < m)
    (hsum : v + v' < m) :
    rootSum (m ^ 2 + v) + rootSum (m ^ 2 + v') < octahedralNumber m := by
  have hleft := rootSum_square_block m v (by omega)
  have hright := rootSum_square_block m v' (by omega)
  have hprod := Nat.mul_lt_mul_of_pos_left hsum hm
  rw [Nat.mul_add] at hprod
  rw [hleft, hright]
  unfold octahedralNumber
  nlinarith

/-- At b=m the elementary one-sided bound is exactly N_m; F2 is needed to
exclude equality in the actual composition argument. -/
theorem rootSum_middle_central_part_eq (m v v' : ℕ) (hsum : v + v' = m) :
    rootSum (m ^ 2 + v) + rootSum (m ^ 2 + v') = octahedralNumber m := by
  have hleft := rootSum_square_block m v (by omega)
  have hright := rootSum_square_block m v' (by omega)
  rw [hleft, hright]
  unfold octahedralNumber
  have hprod := congrArg (fun x => m * x) hsum
  dsimp only at hprod
  rw [Nat.mul_add] at hprod
  nlinarith

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.LargePart

/-! The exact backward-window values at t = floor(sqrt(a)) + 1,
the base computation in Lemma 5.1(iii). -/

namespace ProteinFolding.Tetrahedral

theorem rootWindow_base_high (s r : ℕ) (hr : s + 1 ≤ r) (hr' : r ≤ 2 * s) :
    rootWindow (s ^ 2 + r - (s + 1)) (s ^ 2 + r) = s * (s + 1) := by
  have hstart : s ^ 2 + r - (s + 1) = s ^ 2 + (r - (s + 1)) := by omega
  have hend := rootSum_square_block s r (by omega)
  have hbegin := rootSum_square_block s (r - (s + 1)) (by omega)
  have hparts : r = (r - (s + 1)) + (s + 1) := by omega
  have hmul := congrArg (fun x => s * x) hparts
  dsimp only at hmul
  rw [Nat.mul_add] at hmul
  unfold rootWindow
  rw [hstart, hend, hbegin]
  omega

theorem rootWindow_base_low (s r : ℕ) (hs : 0 < s) (hr : r ≤ s)
    (hsize : s + 1 ≤ s ^ 2 + r) :
    rootWindow (s ^ 2 + r - (s + 1)) (s ^ 2 + r) + 1 = s ^ 2 + r := by
  cases s with
  | zero => omega
  | succ n =>
    have hn : 1 ≤ n + r := by
      cases n with
      | zero => change 2 ≤ 1 + r at hsize; omega
      | succ n => omega
    let j := n + r - 1
    have hj : j + 1 = n + r := by dsimp [j]; omega
    have hstart : (n + 1) ^ 2 + r - (n + 2) = n ^ 2 + j := by
      have hsub := Nat.sub_add_cancel hsize
      change (n + 1) ^ 2 + r - (n + 2) + (n + 2) = (n + 1) ^ 2 + r at hsub
      nlinarith
    have hjbound : j ≤ 2 * n + 1 := by dsimp [j]; omega
    have hend := rootSum_square_block (n + 1) r (by omega)
    have hsquare := rootSum_square_succ n
    have hbegin := rootSum_square_block n j hjbound
    have hmul := congrArg (fun x => n * x) hj
    dsimp only at hmul
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    have heq : rootSum ((n + 1) ^ 2 + r) + 1 =
        rootSum ((n + 1) ^ 2 + r - (n + 2)) + ((n + 1) ^ 2 + r) := by
      rw [hstart, hend, hsquare, hbegin]
      nlinarith
    have hmono := rootSum_mono (Nat.sub_le ((n + 1) ^ 2 + r) (n + 2))
    change rootWindow ((n + 1) ^ 2 + r - (n + 2)) ((n + 1) ^ 2 + r) + 1 = _
    unfold rootWindow
    omega

end ProteinFolding.Tetrahedral

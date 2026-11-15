import ProteinFolding.Tetrahedral.BulkBendUniqueness
import Mathlib.Logic.Function.Iterate

/-! Alternating X coordinates and the explicit outward parametrisation of each line. -/

namespace ProteinFolding.Tetrahedral

theorem bulkArmNext_reverse (sy sz : ℤ) (p : Site) :
    bulkArmNext (-sy) (-sz) (bulkArmNext sy sz p) = p := by
  by_cases hpA : InASublattice p.val
  · have hfirst : bulkArmNext sy sz p = step p (bulkQuadrantDirection sy sz) := by
      rw [bulkArmNext, if_pos hpA]
    rw [hfirst, bulkArmNext,
      if_neg ((inB_iff_not_inA _).mp (step_in_B hpA _)), neg_neg, neg_neg, step_step]
  · have hpB := (inB_iff_not_inA p).mpr hpA
    have hfirst : bulkArmNext sy sz p = step p (bulkQuadrantDirection (-sy) (-sz)) := by
      rw [bulkArmNext, if_neg hpA]
    rw [hfirst, bulkArmNext, if_pos (step_in_A hpB _), step_step]

theorem bulkArmNext_two_x (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site) :
    (bulkArmNext sy sz (bulkArmNext sy sz p)).val 0 = p.val 0 := by
  have h1 := (bulkArmNext_coordinates sy sz hsy hsz p).2.2
  have h2 := (bulkArmNext_coordinates sy sz hsy hsz (bulkArmNext sy sz p)).2.2
  have hcolor := adj_not_same_sublattice (bulkArmNext_adj sy sz p).symm
  by_cases hpA : InASublattice p.val
  · have hqA : ¬InASublattice (bulkArmNext sy sz p).val := fun h => (hcolor.mp h) hpA
    rw [if_pos hpA] at h1
    rw [if_neg hqA] at h2
    omega
  · have hqA := hcolor.mpr hpA
    rw [if_neg hpA] at h1
    rw [if_pos hqA] at h2
    omega

theorem bulkArmNext_two_color (sy sz : ℤ) (p : Site) :
    InASublattice (bulkArmNext sy sz (bulkArmNext sy sz p)).val ↔ InASublattice p.val := by
  have h1 := adj_not_same_sublattice (bulkArmNext_adj sy sz p)
  have h2 := adj_not_same_sublattice (bulkArmNext_adj sy sz (bulkArmNext sy sz p))
  simpa only [not_not] using (h1.trans (not_congr h2)).symm

theorem bulkArmPoint_two_x (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (p : Site) (n : ℕ) : (bulkArmPoint sy sz p (n + 2)).val 0 = (bulkArmPoint sy sz p n).val 0 :=
  bulkArmNext_two_x sy sz hsy hsz _

theorem bulkArmPoint_x_even (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (p : Site) (n : ℕ) : (bulkArmPoint sy sz p (2 * n)).val 0 = p.val 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hidx : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [hidx, bulkArmPoint_two_x sy sz hsy hsz, ih]

theorem bulkArmPoint_even_color (sy sz : ℤ) (p : Site) (n : ℕ) :
    InASublattice (bulkArmPoint sy sz p (2 * n)).val ↔ InASublattice p.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hidx : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [hidx]
    change InASublattice (bulkArmNext sy sz (bulkArmNext sy sz (bulkArmPoint sy sz p (2 * n)))).val ↔ _
    rw [bulkArmNext_two_color, ih]

theorem bulkArmPoint_x_odd (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (p : Site) (n : ℕ) : (bulkArmPoint sy sz p (2 * n + 1)).val 0 =
      p.val 0 + if InASublattice p.val then sy * sz else -(sy * sz) := by
  have hc := (bulkArmNext_coordinates sy sz hsy hsz (bulkArmPoint sy sz p (2 * n))).2.2
  have heven := bulkArmPoint_x_even sy sz hsy hsz p n
  have hcolor := bulkArmPoint_even_color sy sz p n
  change (bulkArmNext sy sz (bulkArmPoint sy sz p (2 * n))).val 0 = _
  rw [hc, heven]
  by_cases hp : InASublattice p.val
  · rw [if_pos hp, if_pos (hcolor.mpr hp)]
  · rw [if_neg hp, if_neg (fun h => hp (hcolor.mp h))]

theorem bulkArmPoint_x_bound (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (p : Site) (n : ℕ) : |(bulkArmPoint sy sz p n).val 0 - p.val 0| ≤ 1 := by
  by_cases hn : n % 2 = 0
  · have hidx : n = 2 * (n / 2) := by omega
    rw [hidx, bulkArmPoint_x_even sy sz hsy hsz]
    simp
  · have hidx : n = 2 * (n / 2) + 1 := by omega
    rw [hidx, bulkArmPoint_x_odd sy sz hsy hsz]
    rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl <;> split_ifs <;> simp

theorem bulkArmPoint_eq_iterate (sy sz : ℤ) (p : Site) (n : ℕ) :
    bulkArmPoint sy sz p n = (bulkArmNext sy sz)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bulkArmNext sy sz (bulkArmPoint sy sz p n) = _
    rw [Function.iterate_succ_apply', ih]

theorem bulkArmPoint_reverse (sy sz : ℤ) (p : Site) (n : ℕ) :
    bulkArmPoint sy sz (bulkArmPoint (-sy) (-sz) p n) n = p := by
  have hi : Function.LeftInverse (bulkArmNext sy sz) (bulkArmNext (-sy) (-sz)) := by
    intro q
    simpa only [neg_neg] using bulkArmNext_reverse (-sy) (-sz) q
  simp only [bulkArmPoint_eq_iterate]
  exact hi.iterate n p

theorem bulkBendPoint_outward (m : ℕ) (p : Site) :
    bulkArmPoint (bulkYSign m p) (bulkZSign p) (bulkBendPoint m p) (bulkBendDistance m p) = p :=
  bulkArmPoint_reverse _ _ p _

theorem bulkSite_x_near_bend (m : ℕ) (p : Site) : |p.val 0 - (bulkBendPoint m p).val 0| ≤ 1 := by
  have h := bulkArmPoint_x_bound (bulkYSign m p) (bulkZSign p) (bulkYSign_unit m p) (bulkZSign_unit p)
    (bulkBendPoint m p) (bulkBendDistance m p)
  rwa [bulkBendPoint_outward] at h

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.OctahedralBoundary
import Mathlib.Tactic.Ring

/-! Explicit infinite arms for the bent foliation in Section 8.1. -/

namespace ProteinFolding.Tetrahedral

def bulkY (m : ℕ) (p : Site) : ℤ := p.val 1 - octRadius m
def bulkZ (p : Site) : ℤ := p.val 2 - 1
def bulkRho (m : ℕ) (p : Site) : ℤ := |bulkY m p| + |bulkZ p|
def bulkAlpha (m : ℕ) (p : Site) : ℤ := |bulkY m p| - |bulkZ p|

theorem bulk_coordinates_not_both_zero (m : ℕ) (p : Site) :
    bulkY m p ≠ 0 ∨ bulkZ p ≠ 0 := by
  rcases p.property with hp | hp
  · right
    have hz := hp.1 2
    dsimp [bulkZ]
    omega
  · left
    have hy := hp.1 1
    dsimp [bulkY, octRadius]
    omega

theorem bulkRho_positive (m : ℕ) (p : Site) : 0 < bulkRho m p := by
  have h := bulk_coordinates_not_both_zero m p
  have hy := abs_nonneg (bulkY m p)
  have hz := abs_nonneg (bulkZ p)
  have hy0 : |bulkY m p| = 0 ↔ bulkY m p = 0 := abs_eq_zero
  have hz0 : |bulkZ p| = 0 ↔ bulkZ p = 0 := abs_eq_zero
  unfold bulkRho
  omega

def bulkQuadrantDirection (sy sz : ℤ) : Fin 4 :=
  if sy = 1 then if sz = 1 then 0 else 2 else if sz = 1 then 3 else 1

theorem bulkQuadrantDirection_coordinates (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) :
    bondVector (bulkQuadrantDirection sy sz) 0 = sy * sz ∧
      bondVector (bulkQuadrantDirection sy sz) 1 = sy ∧
      bondVector (bulkQuadrantDirection sy sz) 2 = sz := by
  rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl <;> decide

def bulkArmNext (sy sz : ℤ) (p : Site) : Site :=
  step p (if InASublattice p.val then bulkQuadrantDirection sy sz
    else bulkQuadrantDirection (-sy) (-sz))

theorem bulkArmNext_adj (sy sz : ℤ) (p : Site) :
    tetrahedralLattice.Adj p (bulkArmNext sy sz p) := step_adj p _

theorem bulkArmNext_coordinates (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site) :
    (bulkArmNext sy sz p).val 1 = p.val 1 + sy ∧
      (bulkArmNext sy sz p).val 2 = p.val 2 + sz ∧
      (bulkArmNext sy sz p).val 0 = p.val 0 +
        (if InASublattice p.val then sy * sz else -(sy * sz)) := by
  have hnegsy : -sy = 1 ∨ -sy = -1 := by omega
  have hnegsz : -sz = 1 ∨ -sz = -1 := by omega
  by_cases hp : InASublattice p.val
  · have hd := bulkQuadrantDirection_coordinates sy sz hsy hsz
    simp only [bulkArmNext, if_pos hp, step_val_of_A p hp]
    exact ⟨by rw [hd.2.1], by rw [hd.2.2], by rw [hd.1]⟩
  · have hpB := (inB_iff_not_inA p).mpr hp
    have hd := bulkQuadrantDirection_coordinates (-sy) (-sz) hnegsy hnegsz
    simp only [bulkArmNext, if_neg hp, step_val_of_B p hpB]
    refine ⟨?_, ?_, ?_⟩
    · dsimp
      rw [hd.2.1]
      omega
    · dsimp
      rw [hd.2.2]
      omega
    · dsimp
      rw [hd.1]
      ring

def bulkArmPoint (sy sz : ℤ) (p : Site) : ℕ → Site
  | 0 => p
  | n + 1 => bulkArmNext sy sz (bulkArmPoint sy sz p n)

@[simp] theorem bulkArmPoint_zero (sy sz : ℤ) (p : Site) : bulkArmPoint sy sz p 0 = p := rfl

theorem bulkArmPoint_adj (sy sz : ℤ) (p : Site) (n : ℕ) :
    tetrahedralLattice.Adj (bulkArmPoint sy sz p n) (bulkArmPoint sy sz p (n + 1)) :=
  bulkArmNext_adj sy sz _

theorem bulkArmPoint_y (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site) (n : ℕ) :
    bulkY m (bulkArmPoint sy sz p n) = bulkY m p + (n : ℤ) * sy := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (bulkArmNext_coordinates sy sz hsy hsz (bulkArmPoint sy sz p n)).1
    change (bulkArmNext sy sz (bulkArmPoint sy sz p n)).val 1 - octRadius m = _
    rw [h]
    rw [show (bulkArmPoint sy sz p n).val 1 + sy - octRadius m =
      ((bulkArmPoint sy sz p n).val 1 - octRadius m) + sy by ring]
    change bulkY m (bulkArmPoint sy sz p n) + sy = _
    rw [ih]
    push_cast
    ring

theorem bulkArmPoint_z (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site) (n : ℕ) :
    bulkZ (bulkArmPoint sy sz p n) = bulkZ p + (n : ℤ) * sz := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (bulkArmNext_coordinates sy sz hsy hsz (bulkArmPoint sy sz p n)).2.1
    change (bulkArmNext sy sz (bulkArmPoint sy sz p n)).val 2 - 1 = _
    rw [h]
    rw [show (bulkArmPoint sy sz p n).val 2 + sz - 1 =
      ((bulkArmPoint sy sz p n).val 2 - 1) + sz by ring]
    change bulkZ (bulkArmPoint sy sz p n) + sz = _
    rw [ih]
    push_cast
    ring

theorem abs_eq_unit_mul (s y : ℤ) (hs : s = 1 ∨ s = -1) (hy : 0 ≤ s * y) :
    |y| = s * y := by
  rcases hs with rfl | rfl
  · have h : 0 ≤ y := by omega
    rw [abs_of_nonneg h]
    ring
  · have h : y ≤ 0 := by omega
    rw [abs_of_nonpos h]
    ring

theorem bulkArmPoint_quadrant_distances (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site)
    (hy : 0 ≤ sy * bulkY m p) (hz : 0 ≤ sz * bulkZ p) (n : ℕ) :
    |bulkY m (bulkArmPoint sy sz p n)| = |bulkY m p| + n ∧
      |bulkZ (bulkArmPoint sy sz p n)| = |bulkZ p| + n := by
  have hyN : sy * bulkY m (bulkArmPoint sy sz p n) = sy * bulkY m p + n := by
    rw [bulkArmPoint_y m sy sz hsy hsz]
    rcases hsy with rfl | rfl <;> ring
  have hzN : sz * bulkZ (bulkArmPoint sy sz p n) = sz * bulkZ p + n := by
    rw [bulkArmPoint_z sy sz hsy hsz]
    rcases hsz with rfl | rfl <;> ring
  rw [abs_eq_unit_mul sy (bulkY m (bulkArmPoint sy sz p n)) hsy (by omega),
    abs_eq_unit_mul sy (bulkY m p) hsy hy,
    abs_eq_unit_mul sz (bulkZ (bulkArmPoint sy sz p n)) hsz (by omega),
    abs_eq_unit_mul sz (bulkZ p) hsz hz]
  exact ⟨hyN, hzN⟩

theorem bulkArmPoint_rho_alpha (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site)
    (hy : 0 ≤ sy * bulkY m p) (hz : 0 ≤ sz * bulkZ p) (n : ℕ) :
    bulkRho m (bulkArmPoint sy sz p n) = bulkRho m p + 2 * n ∧
      bulkAlpha m (bulkArmPoint sy sz p n) = bulkAlpha m p := by
  have h := bulkArmPoint_quadrant_distances m sy sz hsy hsz p hy hz n
  dsimp [bulkRho, bulkAlpha]
  rw [h.1, h.2]
  constructor <;> omega

theorem bulkArmPoint_injective (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site)
    (hy : 0 ≤ sy * bulkY m p) (hz : 0 ≤ sz * bulkZ p) :
    Function.Injective (bulkArmPoint sy sz p) := by
  intro i j heq
  have hi := (bulkArmPoint_rho_alpha m sy sz hsy hsz p hy hz i).1
  have hj := (bulkArmPoint_rho_alpha m sy sz hsy hsz p hy hz j).1
  rw [heq] at hi
  omega

end ProteinFolding.Tetrahedral

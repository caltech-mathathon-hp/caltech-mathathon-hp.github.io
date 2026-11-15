import ProteinFolding.Cubic.Proofs.CertificatesDirections
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An explicit Hamiltonian snake through a rectangular face. Successive rows
are traversed in opposite directions. The construction is an equivalence with
the rectangle's cells, so coverage and injectivity hold for every size; when
the width is positive, consecutive indices are cubic-lattice neighbours. -/

namespace ProteinFolding.CubicPackingSnake

open CubicCertificates

def rowFlip (h w : ℕ) : (Fin h × Fin w) ≃ (Fin h × Fin w) where
  toFun p := (p.1, if p.1.val % 2 = 0 then p.2 else p.2.rev)
  invFun p := (p.1, if p.1.val % 2 = 0 then p.2 else p.2.rev)
  left_inv p := by obtain ⟨y, x⟩ := p; dsimp; split_ifs <;> simp
  right_inv p := by obtain ⟨y, x⟩ := p; dsimp; split_ifs <;> simp

def rectangleCells (h w : ℕ) : Fin (h * w) ≃ (Fin h × Fin w) :=
  finProdFinEquiv.symm.trans (rowFlip h w)

def gridPoint {h w : ℕ} (p : Fin h × Fin w) : Site
  | 0 => p.2.val
  | 1 => p.1.val
  | 2 => 0

theorem gridPoint_injective (h w : ℕ) : Function.Injective (@gridPoint h w) := by
  intro p q he
  have hx := congrFun he 0
  have hy := congrFun he 1
  apply Prod.ext <;> apply Fin.ext <;> dsimp [gridPoint] at hx hy <;> omega

def rectanglePos (h w : ℕ) (i : Fin (h * w)) : Site := gridPoint (rectangleCells h w i)

theorem rectanglePos_x (h w : ℕ) (i : Fin (h * w)) :
    rectanglePos h w i 0 =
      ((if (i.val / w) % 2 = 0 then i.val % w else w - (i.val % w + 1) : ℕ) : ℤ) := by
  unfold rectanglePos rectangleCells rowFlip gridPoint
  dsimp
  split_ifs <;> rfl

theorem rectanglePos_y (h w : ℕ) (i : Fin (h * w)) :
    rectanglePos h w i 1 = (i.val / w : ℕ) := rfl

theorem rectanglePos_z (h w : ℕ) (i : Fin (h * w)) : rectanglePos h w i 2 = 0 := rfl

theorem rectanglePos_injective (h w : ℕ) : Function.Injective (rectanglePos h w) :=
  (gridPoint_injective h w).comp (rectangleCells h w).injective

theorem rectanglePos_surjective_cells (h w : ℕ) (p : Fin h × Fin w) :
    ∃ i : Fin (h * w), rectanglePos h w i = gridPoint p :=
  ⟨(rectangleCells h w).symm p, congrArg gridPoint ((rectangleCells h w).apply_symm_apply p)⟩

theorem rectanglePos_image (h w : ℕ) :
    Finset.univ.image (rectanglePos h w) = (Finset.univ : Finset (Fin h × Fin w)).image gridPoint := by
  ext p
  constructor
  · rintro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨rectangleCells h w i, Finset.mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i, hi⟩ := rectanglePos_surjective_cells h w c
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

/-- The successor either stays within its row or advances exactly one row
and resets its column. This proof uses ordinary quotient/remainder arithmetic. -/
theorem successor_divmod (w k : ℕ) (hw : 0 < w) :
    ((k + 1) / w = k / w ∧ (k + 1) % w = k % w + 1) ∨
      ((k + 1) / w = k / w + 1 ∧ (k + 1) % w = 0 ∧ k % w + 1 = w) := by
  have hr := Nat.mod_lt k hw
  have hd := Nat.mod_add_div k w
  by_cases hlt : k % w + 1 < w
  · left
    have he : k + 1 = k % w + 1 + w * (k / w) := by omega
    rw [he, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hlt, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    exact ⟨rfl, rfl⟩
  · right
    have hend : k % w + 1 = w := by omega
    have he : k + 1 = w * (k / w + 1) := by nlinarith
    rw [he, Nat.mul_div_cancel_left _ hw, Nat.mul_mod_right]
    exact ⟨rfl, rfl, hend⟩

theorem rectanglePos_adjacent (h w : ℕ) (hw : 0 < w) (i j : Fin (h * w))
    (hij : i.val + 1 = j.val) : cubicLattice.Adj (rectanglePos h w i) (rectanglePos h w j) := by
  have hr := Nat.mod_lt i.val hw
  obtain ⟨hrow, hcol⟩ | ⟨hrow, hcol, hend⟩ := successor_divmod w i.val hw
  · rw [hij] at hrow hcol
    change latticeDistance _ _ = 1
    rw [distance_eq, rectanglePos_x, rectanglePos_x, rectanglePos_y, rectanglePos_y,
      rectanglePos_z, rectanglePos_z, hrow, hcol]
    by_cases hp : (i.val / w) % 2 = 0
    · simp [hp]
    · have hnext : i.val % w + 1 < w := by
        have hjr := Nat.mod_lt j.val hw
        rw [hcol] at hjr
        exact hjr
      have hx : ((w - (i.val % w + 1) : ℕ) : ℤ) -
          ((w - (i.val % w + 1 + 1) : ℕ) : ℤ) = 1 := by omega
      simp [hp, hx]
  · rw [hij] at hrow hcol
    have hx : rectanglePos h w i 0 = rectanglePos h w j 0 := by
      rw [rectanglePos_x, rectanglePos_x, hrow, hcol]
      split_ifs <;> omega
    have hy : rectanglePos h w i 1 - rectanglePos h w j 1 = -1 := by
      rw [rectanglePos_y, rectanglePos_y, hrow]
      omega
    change latticeDistance _ _ = 1
    rw [distance_eq, hx, hy, rectanglePos_z, rectanglePos_z]
    simp

/-- A Hamiltonian fold of the h-by-w rectangle at height zero. -/
def rectangleFold (h w : ℕ) (hw : 0 < w) : Fold cubicLattice (h * w) where
  pos := rectanglePos h w
  injective_pos := rectanglePos_injective h w
  consecutive := fun i j hij => rectanglePos_adjacent h w hw i j hij

def firstIndex (h w : ℕ) (hh : 0 < h) (hw : 0 < w) : Fin (h * w) := ⟨0, Nat.mul_pos hh hw⟩
def lastIndex (h w : ℕ) (hh : 0 < h) (hw : 0 < w) : Fin (h * w) :=
  ⟨h * w - 1, by have hp := Nat.mul_pos hh hw; omega⟩

theorem rectanglePos_first (h w : ℕ) (hh : 0 < h) (hw : 0 < w) :
    rectanglePos h w (firstIndex h w hh hw) = fun _ => 0 := by
  apply site_ext
  · rw [rectanglePos_x]
    simp [firstIndex]
  · rw [rectanglePos_y]
    simp [firstIndex]
  · rfl

theorem last_divmod (h w : ℕ) (hh : 0 < h) (hw : 0 < w) :
    (h * w - 1) / w = h - 1 ∧ (h * w - 1) % w = w - 1 := by
  have hh1 : h - 1 + 1 = h := by omega
  have hw1 : w - 1 + 1 = w := by omega
  have hp := Nat.mul_pos hh hw
  have hp1 : h * w - 1 + 1 = h * w := by omega
  have hm : (h - 1) * w + w = h * w := by
    calc
      _ = (h - 1 + 1) * w := by ring
      _ = _ := by rw [hh1]
  have he : h * w - 1 = w - 1 + w * (h - 1) := by nlinarith
  have hlt : w - 1 < w := by omega
  rw [he, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hlt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  exact ⟨rfl, rfl⟩

/-- With an even number of rows, the two endpoints have the same x coordinate.
This is the collinear-port property used for even-width item strips. -/
theorem rectanglePos_last_even (h w : ℕ) (hh : 0 < h) (hw : 0 < w) (heven : h % 2 = 0) :
    rectanglePos h w (lastIndex h w hh hw) =
      fun k => if k = 1 then ((h - 1 : ℕ) : ℤ) else 0 := by
  obtain ⟨hd, hm⟩ := last_divmod h w hh hw
  have hparity : (h - 1) % 2 ≠ 0 := by omega
  have hw1 : w - 1 + 1 = w := by omega
  apply site_ext
  · rw [rectanglePos_x]
    change ((if ((h * w - 1) / w) % 2 = 0 then (h * w - 1) % w
      else w - ((h * w - 1) % w + 1) : ℕ) : ℤ) = 0
    rw [hd, hm, if_neg hparity, hw1, Nat.sub_self]
    rfl
  · rw [rectanglePos_y]
    change (((h * w - 1) / w : ℕ) : ℤ) = ((h - 1 : ℕ) : ℤ)
    rw [hd]
  · rfl

end ProteinFolding.CubicPackingSnake

import ProteinFolding.Tetrahedral.ColumnsSigns
import ProteinFolding.Tetrahedral.OctahedralExteriorLinks

/-! Coordinate and injectivity facts for the infinite column arms. -/

namespace ProteinFolding.Tetrahedral

theorem bulkArmNext_charge (sy sz : ℤ) (p : Site) :
    siteCharge (bulkArmNext sy sz p) = 1 - siteCharge p := siteCharge_step p _

theorem bulkArmNext_x_charge (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1)
    (hsz : sz = 1 ∨ sz = -1) (p : Site) :
    (bulkArmNext sy sz p).val 0 = p.val 0 +
      (siteCharge (bulkArmNext sy sz p) - siteCharge p) * (sy * sz) := by
  have hx := (bulkArmNext_coordinates sy sz hsy hsz p).2.2
  rw [bulkArmNext_charge]
  rcases p.property with hpA | hpB
  · rw [siteCharge_A hpA, if_pos hpA] at *
    rw [hx]
    ring
  · rw [siteCharge_B hpB, if_neg ((inB_iff_not_inA p).mp hpB)] at *
    rw [hx]
    ring

theorem bulkArmPoint_x_charge (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1)
    (hsz : sz = 1 ∨ sz = -1) (p : Site) (n : ℕ) :
    (bulkArmPoint sy sz p n).val 0 = p.val 0 +
      (siteCharge (bulkArmPoint sy sz p n) - siteCharge p) * (sy * sz) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx := bulkArmNext_x_charge sy sz hsy hsz (bulkArmPoint sy sz p n)
    change (bulkArmNext sy sz (bulkArmPoint sy sz p n)).val 0 = p.val 0 +
      (siteCharge (bulkArmNext sy sz (bulkArmPoint sy sz p n)) - siteCharge p) * (sy * sz)
    rw [hx, ih]
    ring

theorem bulkArmPoint_charge (sy sz : ℤ) (p : Site) (n : ℕ) :
    siteCharge (bulkArmPoint sy sz p n) =
      if n % 2 = 0 then siteCharge p else 1 - siteCharge p := by
  let d : ℕ → Fin 4 := fun i => if InASublattice (bulkArmPoint sy sz p i).val then
    bulkQuadrantDirection sy sz else bulkQuadrantDirection (-sy) (-sz)
  have hstep : ∀ i < n, bulkArmPoint sy sz p (i + 1) = step (bulkArmPoint sy sz p i) (d i) := by
    intro i _
    rfl
  have h := path_siteCharge_mod (bulkArmPoint sy sz p) d n hstep
  have hp := siteCharge_bounds p
  have hq := siteCharge_bounds (bulkArmPoint sy sz p n)
  change (siteCharge (bulkArmPoint sy sz p n) + (n : ℤ)) % 2 = siteCharge p at h
  split_ifs <;> omega

theorem bulkArmNext_injective (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1)
    (hsz : sz = 1 ∨ sz = -1) : Function.Injective (bulkArmNext sy sz) := by
  intro p q heq
  have hc := congrArg siteCharge heq
  have hcp := bulkArmNext_charge sy sz p
  have hcq := bulkArmNext_charge sy sz q
  have hcharge : siteCharge p = siteCharge q := by omega
  have hpx := bulkArmNext_x_charge sy sz hsy hsz p
  have hqx := bulkArmNext_x_charge sy sz hsy hsz q
  rw [heq, hcharge] at hpx
  have hp := bulkArmNext_coordinates sy sz hsy hsz p
  have hq := bulkArmNext_coordinates sy sz hsy hsz q
  have hpy := hp.1
  have hpz := hp.2.1
  have hqy := hq.1
  have hqz := hq.2.1
  rw [heq] at hpy hpz
  apply Subtype.ext
  funext k
  fin_cases k
  · change p.val 0 = q.val 0
    omega
  · change p.val 1 = q.val 1
    omega
  · change p.val 2 = q.val 2
    omega

theorem bulkArmPoint_seed_injective (sy sz : ℤ) (hsy : sy = 1 ∨ sy = -1)
    (hsz : sz = 1 ∨ sz = -1) (n : ℕ) :
    Function.Injective (fun p => bulkArmPoint sy sz p n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    intro p q heq
    apply ih
    exact bulkArmNext_injective sy sz hsy hsz heq

theorem bulkArmPoint_add (sy sz : ℤ) (p : Site) (n k : ℕ) :
    bulkArmPoint sy sz p (n + k) = bulkArmPoint sy sz (bulkArmPoint sy sz p n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change bulkArmNext sy sz (bulkArmPoint sy sz p (n + k)) =
      bulkArmNext sy sz (bulkArmPoint sy sz (bulkArmPoint sy sz p n) k)
    rw [ih]

theorem bigFace_armNext_delta (m : ℕ) (d : Fin 4) (p : Site) :
    tetraCoordinate m (bulkArmNext (bigFaceY d) (bigFaceZ d) p).val d =
      tetraCoordinate m p.val d + if InASublattice p.val then 3 else 1 := by
  rcases p.property with hpA | hpB
  · rw [bulkArmNext, if_pos hpA, bigFace_quadrant_direction,
      tetraCoordinate_step_A m hpA, if_pos rfl, if_pos hpA]
  · rw [bulkArmNext, if_neg ((inB_iff_not_inA p).mp hpB), smallFace_quadrant_direction,
      tetraCoordinate_step_B m hpB, if_neg (Ne.symm (columnOpposite_ne d)),
      if_neg ((inB_iff_not_inA p).mp hpB)]

theorem smallFace_armNext_delta (m : ℕ) (d : Fin 4) (p : Site) :
    tetraCoordinate m (bulkArmNext (-bigFaceY d) (-bigFaceZ d) p).val d =
      tetraCoordinate m p.val d - if InASublattice p.val then 1 else 3 := by
  rcases p.property with hpA | hpB
  · rw [bulkArmNext, if_pos hpA, smallFace_quadrant_direction,
      tetraCoordinate_step_A m hpA, if_neg (Ne.symm (columnOpposite_ne d)), if_pos hpA]
    omega
  · rw [bulkArmNext, if_neg ((inB_iff_not_inA p).mp hpB), neg_neg, neg_neg,
      bigFace_quadrant_direction, tetraCoordinate_step_B m hpB, if_pos rfl,
      if_neg ((inB_iff_not_inA p).mp hpB)]
    omega

theorem bigFace_armPoint_growth (m : ℕ) (d : Fin 4) (p : Site) (n : ℕ) :
    tetraCoordinate m p.val d + (n : ℤ) ≤
      tetraCoordinate m (bulkArmPoint (bigFaceY d) (bigFaceZ d) p n).val d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := bigFace_armNext_delta m d (bulkArmPoint (bigFaceY d) (bigFaceZ d) p n)
    change _ ≤ tetraCoordinate m (bulkArmNext (bigFaceY d) (bigFaceZ d)
      (bulkArmPoint (bigFaceY d) (bigFaceZ d) p n)).val d
    rw [h]
    split_ifs <;> push_cast <;> omega

theorem smallFace_armPoint_growth (m : ℕ) (d : Fin 4) (p : Site) (n : ℕ) :
    tetraCoordinate m (bulkArmPoint (-bigFaceY d) (-bigFaceZ d) p n).val d ≤
      tetraCoordinate m p.val d - (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := smallFace_armNext_delta m d (bulkArmPoint (-bigFaceY d) (-bigFaceZ d) p n)
    change tetraCoordinate m (bulkArmNext (-bigFaceY d) (-bigFaceZ d)
      (bulkArmPoint (-bigFaceY d) (-bigFaceZ d) p n)).val d ≤ _
    rw [h]
    split_ifs <;> push_cast <;> omega

end ProteinFolding.Tetrahedral

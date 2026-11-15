import ProteinFolding.Cubic.Proofs.PackingSnakeLayers
import ProteinFolding.Cubic.Proofs.GeometryBasics
import Mathlib.Tactic.FinCases

/-! Explicit cuboid and cube-interior Hamiltonian snakes. The cube interior
is the translate {1,...,d}³. Reflection makes its first point (d,d,d); for even
d its last point is (d,d,1), exactly the two bulk endpoints used by the frame.
This file constructs the interior walk; adding the two surface holes and P
bridges is a separate part of the complete folding construction. -/

namespace ProteinFolding.CubicPackingSnake

open CubicCertificates

def cuboidCells (layers h w : ℕ) : Fin (layers * (h * w)) ≃ (Fin layers × (Fin h × Fin w)) :=
  (rectangleCells layers (h * w)).trans (Equiv.prodCongr (Equiv.refl _) (rectangleCells h w))

def grid3Point {layers h w : ℕ} (p : Fin layers × (Fin h × Fin w)) : Site
  | 0 => p.2.2.val
  | 1 => p.2.1.val
  | 2 => p.1.val

theorem grid3Point_injective (layers h w : ℕ) : Function.Injective (@grid3Point layers h w) := by
  intro p q he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  apply Prod.ext
  · apply Fin.ext; dsimp [grid3Point] at hz; omega
  · apply Prod.ext
    · apply Fin.ext; dsimp [grid3Point] at hy; omega
    · apply Fin.ext; dsimp [grid3Point] at hx; omega

def cuboidPos (layers h w : ℕ) (i : Fin (layers * (h * w))) : Site :=
  grid3Point (cuboidCells layers h w i)

theorem cuboidPos_eq_layered (layers h w : ℕ) (hw : 0 < w) (i : Fin (layers * (h * w))) :
    cuboidPos layers h w i = layeredPos layers (rectangleFold h w hw) i := by
  apply site_ext <;> rfl

theorem cuboidPos_injective (layers h w : ℕ) : Function.Injective (cuboidPos layers h w) :=
  (grid3Point_injective layers h w).comp (cuboidCells layers h w).injective

theorem cuboidPos_adjacent (layers h w : ℕ) (hh : 0 < h) (hw : 0 < w)
    (i j : Fin (layers * (h * w))) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (cuboidPos layers h w i) (cuboidPos layers h w j) := by
  rw [cuboidPos_eq_layered layers h w hw i, cuboidPos_eq_layered layers h w hw j]
  exact layeredPos_adjacent layers (rectangleFold h w hw) (Nat.mul_pos hh hw)
    (fun k => rectanglePos_z h w k) i j hij

def cuboidFold (layers h w : ℕ) (hh : 0 < h) (hw : 0 < w) : Fold cubicLattice (layers * (h * w)) where
  pos := cuboidPos layers h w
  injective_pos := cuboidPos_injective layers h w
  consecutive := fun i j hij => cuboidPos_adjacent layers h w hh hw i j hij

theorem cuboidPos_in_cube (d : ℕ) (i : Fin (d * (d * d))) :
    cuboidPos d d d i ∈ cube (fun _ => 0) d := by
  intro k
  have hx := (cuboidCells d d d i).2.2.isLt
  have hy := (cuboidCells d d d i).2.1.isLt
  have hz := (cuboidCells d d d i).1.isLt
  fin_cases k <;> change 0 ≤ (_ : ℤ) ∧ (_ : ℤ) < 0 + (d : ℤ) <;>
    dsimp [cuboidPos, grid3Point] <;> omega

/-- The explicit snake visits every cube site, including all boundary sites,
exactly once. No extremal-counting or existence assumption is used. -/
theorem cuboidPos_cube_iff (d : ℕ) (p : Site) :
    (∃ i : Fin (d * (d * d)), cuboidPos d d d i = p) ↔ p ∈ cube (fun _ => 0) d := by
  constructor
  · rintro ⟨i, rfl⟩
    exact cuboidPos_in_cube d i
  · intro hp
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp ((CubicGeometry.mem_cubeFinset (fun _ => 0) d p).mpr hp)
    let cell : Fin d × (Fin d × Fin d) := (q 2, (q 1, q 0))
    refine ⟨(cuboidCells d d d).symm cell, ?_⟩
    change grid3Point ((cuboidCells d d d) ((cuboidCells d d d).symm cell)) = p
    rw [Equiv.apply_symm_apply, ← hq]
    apply site_ext <;> simp [grid3Point, cell, CubicGeometry.cubePoint]

theorem cuboidPos_first (layers h w : ℕ) (hl : 0 < layers) (hh : 0 < h) (hw : 0 < w) :
    cuboidPos layers h w (firstIndex layers (h * w) hl (Nat.mul_pos hh hw)) = fun _ => 0 := by
  rw [cuboidPos_eq_layered layers h w hw,
    layeredPos_first layers (rectangleFold h w hw) hl (Nat.mul_pos hh hw)]
  have hbase := rectanglePos_first h w hh hw
  change rectanglePos h w ⟨0, Nat.mul_pos hh hw⟩ = (fun _ => 0) at hbase
  change atHeight (rectanglePos h w ⟨0, Nat.mul_pos hh hw⟩) 0 = _
  rw [hbase]
  apply site_ext <;> rfl

theorem cuboidPos_last_even (layers h w : ℕ) (hl : 0 < layers) (hh : 0 < h) (hw : 0 < w)
    (heven : layers % 2 = 0) :
    cuboidPos layers h w (lastIndex layers (h * w) hl (Nat.mul_pos hh hw)) =
      fun k => if k = 2 then ((layers - 1 : ℕ) : ℤ) else 0 := by
  rw [cuboidPos_eq_layered layers h w hw,
    layeredPos_last_even layers (rectangleFold h w hw) hl (Nat.mul_pos hh hw) heven]
  have hbase := rectanglePos_first h w hh hw
  change rectanglePos h w ⟨0, Nat.mul_pos hh hw⟩ = (fun _ => 0) at hbase
  change atHeight (rectanglePos h w ⟨0, Nat.mul_pos hh hw⟩) _ = _
  rw [hbase]
  apply site_ext <;> rfl

def reflect (a p : Site) : Site := fun k => a k - p k

theorem reflect_injective (a : Site) : Function.Injective (reflect a) := by
  intro p q he
  funext k
  have hk := congrFun he k
  dsimp [reflect] at hk
  omega

theorem reflect_involutive (a p : Site) : reflect a (reflect a p) = p := by
  funext k
  simp [reflect]

theorem latticeDistance_reflect (a p q : Site) :
    latticeDistance (reflect a p) (reflect a q) = latticeDistance p q := by
  unfold latticeDistance
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [reflect]
  rw [show a k - p k - (a k - q k) = -(p k - q k) by ring, Int.natAbs_neg]

theorem reflect_adj (a p q : Site) (ha : cubicLattice.Adj p q) :
    cubicLattice.Adj (reflect a p) (reflect a q) := by
  change latticeDistance _ _ = 1
  rw [latticeDistance_reflect]
  exact ha

def interiorPos (d : ℕ) (i : Fin (d * (d * d))) : Site := reflect (fun _ => d) (cuboidPos d d d i)

def interiorFold (d : ℕ) (hd : 0 < d) : Fold cubicLattice (d * (d * d)) where
  pos := interiorPos d
  injective_pos := (reflect_injective _).comp (cuboidPos_injective d d d)
  consecutive := fun i j hij => reflect_adj _ _ _ (cuboidPos_adjacent d d d hd hd i j hij)

theorem interiorPos_cube_iff (d : ℕ) (p : Site) :
    (∃ i : Fin (d * (d * d)), interiorPos d i = p) ↔ p ∈ cube (fun _ => 1) d := by
  constructor
  · rintro ⟨i, rfl⟩
    have hp := cuboidPos_in_cube d i
    intro k
    have hk := hp k
    dsimp only at hk
    change (1 : ℤ) ≤ (d : ℤ) - cuboidPos d d d i k ∧
      (d : ℤ) - cuboidPos d d d i k < 1 + (d : ℤ)
    omega
  · intro hp
    have hr : reflect (fun _ => (d : ℤ)) p ∈ cube (fun _ => 0) d := by
      intro k
      have hk := hp k
      dsimp only at hk
      change (0 : ℤ) ≤ (d : ℤ) - p k ∧ (d : ℤ) - p k < 0 + (d : ℤ)
      omega
    obtain ⟨i, hi⟩ := (cuboidPos_cube_iff d _).mpr hr
    refine ⟨i, ?_⟩
    change reflect _ (cuboidPos d d d i) = p
    rw [hi, reflect_involutive]

theorem interiorPos_first (d : ℕ) (hd : 0 < d) :
    interiorPos d (firstIndex d (d * d) hd (Nat.mul_pos hd hd)) = fun _ => (d : ℤ) := by
  rw [interiorPos, cuboidPos_first d d d hd hd hd]
  funext k
  simp [reflect]

theorem interiorPos_last_even (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    interiorPos d (lastIndex d (d * d) hd (Nat.mul_pos hd hd)) =
      fun k => if k = 2 then (1 : ℤ) else (d : ℤ) := by
  rw [interiorPos, cuboidPos_last_even d d d hd hd hd heven]
  apply site_ext <;> simp [reflect]
  omega

end ProteinFolding.CubicPackingSnake

import ProteinFolding.Cubic.Proofs.PackingAttachedDisjoint
import ProteinFolding.Cubic.Proofs.PackingRoutingRectangle
import ProteinFolding.Common.FoldConcatenation
import ProteinFolding.Cubic.Proofs.PackingBlockAssembly

/-! Complete literal straight E and F blocks used to construct the packing
walls. The E blocks alternate the two exterior normals, fixing both endpoint
P sites in the front plane at height -1. -/

namespace ProteinFolding.CubicPackingWalls

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting

def lineRow (y : ℤ) (increasing : Bool) (k : ℕ) : ℤ :=
  if increasing then y + k else y - k

def verticalPos (x y : ℤ) (increasing : Bool) (t : ℕ) (i : Fin t) : Site :=
  point x (lineRow y increasing i.val) 0

theorem verticalPos_injective (x y : ℤ) (increasing : Bool) (t : ℕ) :
    Function.Injective (verticalPos x y increasing t) := by
  intro i j he
  have hy := congrFun he 1
  dsimp [verticalPos, point, lineRow] at hy
  apply Fin.ext
  cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy <;> omega

theorem verticalPos_adjacent (x y : ℤ) (increasing : Bool) (t : ℕ)
    (i j : Fin t) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (verticalPos x y increasing t i) (verticalPos x y increasing t j) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  dsimp [verticalPos, point, lineRow]
  cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

def verticalFold (x y : ℤ) (increasing : Bool) (t : ℕ) : Fold cubicLattice t where
  pos := verticalPos x y increasing t
  injective_pos := verticalPos_injective x y increasing t
  consecutive := verticalPos_adjacent x y increasing t

def railX (d : ℕ) (right : Bool) : ℤ := if right then d + 1 else 0
def railOut (right : Bool) : Fin 6 := if right then 0 else 1

theorem rail_inside (d t : ℕ) (right increasing : Bool) (y : ℤ)
    (hrows : ∀ i : Fin t, 0 ≤ lineRow y increasing i.val ∧ lineRow y increasing i.val ≤ d + 1)
    (i : Fin t) : (verticalFold (railX d right) y increasing t).pos i ∈ cube (fun _ => 0) (d + 2) := by
  have hy := hrows i
  intro k
  match k with
  | 0 => change (0 : ℤ) ≤ railX d right ∧ railX d right < 0 + ((d + 2 : ℕ) : ℤ)
         cases right <;> dsimp [railX] <;> omega
  | 1 => change (0 : ℤ) ≤ lineRow y increasing i.val ∧ _
         change (0 : ℤ) ≤ lineRow y increasing i.val ∧ lineRow y increasing i.val < 0 + ((d + 2 : ℕ) : ℤ)
         omega
  | 2 => change (0 : ℤ) ≤ 0 ∧ 0 < 0 + ((d + 2 : ℕ) : ℤ)
         omega

theorem rail_front_outside (d t : ℕ) (right increasing : Bool) (y : ℤ) (i : Fin t) :
    step ((verticalFold (railX d right) y increasing t).pos i) 5 ∉ cube (fun _ => 0) (d + 2) := by
  intro hp
  have hz := (hp 2).1
  change (0 : ℤ) ≤ -1 at hz
  omega

theorem rail_outer_outside (d t : ℕ) (right increasing : Bool) (y : ℤ) (i : Fin t) :
    step ((verticalFold (railX d right) y increasing t).pos i) (railOut right) ∉
      cube (fun _ => 0) (d + 2) := by
  intro hp
  have hx := hp 0
  cases right <;> dsimp [step, verticalFold, verticalPos, point, railOut, railX] at hx <;> omega

/-- An even straight rail block with both endpoint P sites facing outwards
from the packing face. Its full image is attached to its specified H path. -/
theorem railWord_exists (d t : ℕ) (right increasing : Bool) (y : ℤ)
    (ht : 0 < t) (heven : t % 2 = 0)
    (hrows : ∀ i : Fin t, 0 ≤ lineRow y increasing i.val ∧ lineRow y increasing i.val ≤ d + 1) :
    ∃ f : Fold cubicLattice (edgeWord t).length,
      AttachedTo (fun _ => 0) (d + 2) f (verticalFold (railX d right) y increasing t).pos ∧
      hydrophobicSites (edgeWord t) f = Set.range (verticalFold (railX d right) y increasing t).pos ∧
      f.pos (edgeFirstIndex t ht) = point (railX d right) y (-1) ∧
      f.pos (edgeLastIndex t ht) = point (railX d right) (lineRow y increasing (t - 1)) (-1) := by
  let base := verticalFold (railX d right) y increasing t
  have hin : ∀ i, base.pos i ∈ cube (fun _ => 0) (d + 2) := rail_inside d t right increasing y hrows
  have hd : (5 : Fin 6) ≠ railOut right := by cases right <;> decide
  obtain ⟨f, hs, hp, hf, hl⟩ := edgeWord_even_lift_exists t ht heven base
    (fun _ => 0) (d + 2) hin 5 (railOut right) hd
    (rail_front_outside d t right increasing y) (rail_outer_outside d t right increasing y)
  refine ⟨f, edgeWord_fold_attached t f base (fun _ => 0) (d + 2) hs hin hp, hs, ?_, ?_⟩
  · rw [hf]
    apply site_ext <;> dsimp [base, verticalFold, verticalPos, point, lineRow, step]
    cases increasing <;> simp
  · rw [hl]
    apply site_ext <;> rfl

def horizontalPos (d : ℕ) (y : ℤ) (increasing : Bool) (i : Fin d) : Site :=
  point (if increasing then (i.val : ℤ) + 1 else (d : ℤ) - i.val) y 0

theorem horizontalPos_injective (d : ℕ) (y : ℤ) (increasing : Bool) :
    Function.Injective (horizontalPos d y increasing) := by
  intro i j he
  have hx := congrFun he 0
  dsimp [horizontalPos, point] at hx
  apply Fin.ext
  cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx <;> omega

theorem horizontalPos_adjacent (d : ℕ) (y : ℤ) (increasing : Bool)
    (i j : Fin d) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (horizontalPos d y increasing i) (horizontalPos d y increasing j) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  dsimp [horizontalPos, point]
  cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

def horizontalFold (d : ℕ) (y : ℤ) (increasing : Bool) : Fold cubicLattice d where
  pos := horizontalPos d y increasing
  injective_pos := horizontalPos_injective d y increasing
  consecutive := horizontalPos_adjacent d y increasing

def faceLineWordFold (d : ℕ) (y : ℤ) (increasing : Bool) (heven : 2 ∣ d) :
    Fold cubicLattice (faceWord d).length :=
  faceLift d heven (horizontalFold d y increasing) (fun _ => rfl)

theorem horizontal_inside (d : ℕ) (y : ℤ) (increasing : Bool)
    (hy : 0 ≤ y ∧ y ≤ d + 1) (i : Fin d) :
    (horizontalFold d y increasing).pos i ∈ cube (fun _ => 0) (d + 2) := by
  have hi := i.isLt
  intro k
  match k with
  | 0 => change (0 : ℤ) ≤ (if increasing then (i.val : ℤ) + 1 else (d : ℤ) - i.val) ∧
           (if increasing then (i.val : ℤ) + 1 else (d : ℤ) - i.val) < 0 + ((d + 2 : ℕ) : ℤ)
         cases increasing <;> dsimp <;> omega
  | 1 => change (0 : ℤ) ≤ y ∧ y < 0 + ((d + 2 : ℕ) : ℤ)
         omega
  | 2 => change (0 : ℤ) ≤ 0 ∧ 0 < 0 + ((d + 2 : ℕ) : ℤ)
         omega

theorem faceLineWord_attached (d : ℕ) (y : ℤ) (increasing : Bool)
    (heven : 2 ∣ d) (hy : 0 ≤ y ∧ y ≤ d + 1) :
    AttachedTo (fun _ => 0) (d + 2) (faceLineWordFold d y increasing heven)
      (horizontalFold d y increasing).pos :=
  faceLift_attached d heven (horizontalFold d y increasing) (fun _ => rfl) (d + 2)
    (horizontal_inside d y increasing hy)

theorem faceLineWord_first (d : ℕ) (y : ℤ) (increasing : Bool) (hd : 0 < d) (heven : 2 ∣ d) :
    (faceLineWordFold d y increasing heven).pos (faceFirstIndex d heven hd) =
      point (if increasing then 1 else (d : ℤ)) y (-1) := by
  change faceLiftPos _ _ _ _ = _
  rw [faceLiftPos_first]
  apply site_ext <;> dsimp [CubicPackingSnake.atHeight, horizontalFold, horizontalPos, point]
  cases increasing <;> rfl

theorem faceLineWord_last (d : ℕ) (y : ℤ) (increasing : Bool) (hd : 0 < d) (heven : 2 ∣ d) :
    (faceLineWordFold d y increasing heven).pos (faceLastIndex d heven hd) =
      point (if increasing then (d : ℤ) else 1) y (-1) := by
  change faceLiftPos _ _ _ _ = _
  rw [faceLiftPos_last]
  apply site_ext <;> dsimp [CubicPackingSnake.atHeight, horizontalFold, horizontalPos, point]
  cases increasing <;> dsimp <;> omega

theorem railWord_ends_exists (d t : ℕ) (right increasing : Bool) (y : ℤ)
    (ht : 0 < t) (heven : t % 2 = 0)
    (hrows : ∀ i : Fin t, 0 ≤ lineRow y increasing i.val ∧ lineRow y increasing i.val ≤ d + 1) :
    ∃ f : Fold cubicLattice (edgeWord t).length,
      AttachedTo (fun _ => 0) (d + 2) f (verticalFold (railX d right) y increasing t).pos ∧
      hydrophobicSites (edgeWord t) f = Set.range (verticalFold (railX d right) y increasing t).pos ∧
      HasEnds f (point (railX d right) y (-1))
        (point (railX d right) (lineRow y increasing (t - 1)) (-1)) := by
  obtain ⟨f, ha, hs, hf, hl⟩ := railWord_exists d t right increasing y ht heven hrows
  refine ⟨f, ha, hs, ?_⟩
  have hlen := edgeWord_length t
  exact hasEnds_of_indices f (by omega) _ _ hf hl

theorem faceLineWord_hasEnds (d : ℕ) (y : ℤ) (increasing : Bool) (hd : 0 < d) (heven : 2 ∣ d) :
    HasEnds (faceLineWordFold d y increasing heven)
      (point (if increasing then 1 else (d : ℤ)) y (-1))
      (point (if increasing then (d : ℤ) else 1) y (-1)) := by
  have hlen := faceWord_length d heven
  exact hasEnds_of_indices _ (by omega) _ _ (faceLineWord_first d y increasing hd heven)
    (faceLineWord_last d y increasing hd heven)

theorem vertical_horizontal_disjoint (d t : ℕ) (x y z : ℤ) (inc₁ inc₂ : Bool)
    (hx : x = 0 ∨ x = d + 1) (i : Fin t) (j : Fin d) :
    (verticalFold x y inc₁ t).pos i ≠ (horizontalFold d z inc₂).pos j := by
  intro he
  have h := congrFun he 0
  have hj := j.isLt
  change x = (if inc₂ then (j.val : ℤ) + 1 else (d : ℤ) - j.val) at h
  cases inc₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  all_goals rcases hx with rfl | rfl <;> omega

theorem vertical_rails_disjoint (t u : ℕ) (x x' y y' : ℤ) (inc inc' : Bool)
    (hx : x ≠ x') (i : Fin t) (j : Fin u) :
    (verticalFold x y inc t).pos i ≠ (verticalFold x' y' inc' u).pos j := by
  intro he
  exact hx (congrFun he 0)

theorem horizontal_rows_disjoint (d : ℕ) (y y' : ℤ) (inc inc' : Bool)
    (hy : y ≠ y') (i j : Fin d) :
    (horizontalFold d y inc).pos i ≠ (horizontalFold d y' inc').pos j := by
  intro he
  exact hy (congrFun he 1)

end ProteinFolding.CubicPackingWalls

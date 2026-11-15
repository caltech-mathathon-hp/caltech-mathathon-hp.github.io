import ProteinFolding.Cubic.Proofs.PackingWallUnitFold

/-! The fixed P bridges between wall units (depth two) and gap E₂ blocks
(depth three). Their lengths are exactly the literal source-word lengths. -/

namespace ProteinFolding.CubicPackingWalls

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting

def rowBridgePos (x y z : ℤ) (increasing : Bool) (t : ℕ) (i : Fin t) : Site :=
  point x (lineRow y increasing i.val) z

def rowBridgeFold (x y z : ℤ) (increasing : Bool) (t : ℕ) : Fold cubicLattice t where
  pos := rowBridgePos x y z increasing t
  injective_pos := by
    intro i j he
    have hy := congrFun he 1
    dsimp [rowBridgePos, point, lineRow] at hy
    apply Fin.ext
    cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy <;> omega
  consecutive i j hij := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [rowBridgePos, point, lineRow]
    cases increasing <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

def straightPBridge (x y z : ℤ) (increasing : Bool) (t : ℕ) :
    Fold cubicLattice (List.replicate t Residue.P).length :=
  (rowBridgeFold x y z increasing t).onLength (List.length_replicate ..)

theorem straightPBridge_ends (x y z : ℤ) (increasing : Bool) (t : ℕ) (ht : 0 < t) :
    HasEnds (straightPBridge x y z increasing t) (point x y z)
      (point x (lineRow y increasing (t - 1)) z) := by
  apply hasEnds_of_indices _ (by simp [ht])
  · apply site_ext <;> dsimp [straightPBridge, Fold.onLength, rowBridgeFold, rowBridgePos, point, lineRow]
    cases increasing <;> simp
  · apply site_ext <;> dsimp [straightPBridge, Fold.onLength, rowBridgeFold, rowBridgePos, point]
    simp

theorem straightPBridge_height (x y z : ℤ) (increasing : Bool) (t : ℕ)
    (i : Fin (List.replicate t Residue.P).length) :
    (straightPBridge x y z increasing t).pos i 2 = z := rfl

theorem replicateP_H_sites (t : ℕ) (f : Fold cubicLattice (List.replicate t Residue.P).length) :
    hydrophobicSites (List.replicate t Residue.P) f = ∅ := by
  ext p
  constructor
  · rintro ⟨i, hi, _⟩
    have he : (List.replicate t Residue.P).get i = .P := by simp
    rw [he] at hi
    cases hi
  · exact False.elim

def unitPBridge (d A : ℕ) (top : ℤ) :
    Fold cubicLattice (List.replicate (2 * A) Residue.P).length :=
  straightPBridge (d + 1) (top - A - 2) (-2) false (2 * A)

theorem unitPBridge_ends (d A : ℕ) (top : ℤ) (hA : 0 < A) :
    HasEnds (unitPBridge d A top) (point (d + 1) (top - A - 2) (-2))
      (point (d + 1) (top - 3 * A - 1) (-2)) := by
  have he := straightPBridge_ends (d + 1) (top - A - 2) (-2) false (2 * A) (by omega)
  have hy : lineRow (top - A - 2) false (2 * A - 1) = top - 3 * A - 1 := by
    dsimp [lineRow]
    omega
  rwa [hy] at he

def bentBridgePos (x y : ℤ) (b : ℕ) (i : Fin (b + 2)) : Site :=
  if i.val = 0 then point x y (-2)
  else if i.val ≤ b then point x (y + i.val - 1) (-3)
  else point x (y + b - 1) (-2)

def bentBridgeFold (x y : ℤ) (b : ℕ) (hb : 2 ≤ b) : Fold cubicLattice (b + 2) where
  pos := bentBridgePos x y b
  injective_pos := by
    intro i j he
    have hi := i.isLt
    have hj := j.isLt
    unfold bentBridgePos at he
    split_ifs at he <;> have hy := congrFun he 1 <;> have hz := congrFun he 2 <;>
      dsimp only [point] at hy hz <;> apply Fin.ext <;> omega
  consecutive i j hij := by
    have hi := i.isLt
    have hj := j.isLt
    change latticeDistance (bentBridgePos _ _ _ _) (bentBridgePos _ _ _ _) = 1
    unfold bentBridgePos
    split_ifs <;> try omega
    all_goals rw [distance_eq]; dsimp only [point]; omega

def gapPBridge (d A : ℕ) (y : ℤ) :
    Fold cubicLattice (List.replicate (2 * A + 4) Residue.P).length :=
  (bentBridgeFold (d + 1) y (2 * A + 2) (by omega)).onLength (by simp)

theorem gapPBridge_ends (d A : ℕ) (y : ℤ) :
    HasEnds (gapPBridge d A y) (point (d + 1) y (-2))
      (point (d + 1) (y + 2 * A + 1) (-2)) := by
  apply hasEnds_of_indices _ (by simp)
  · rfl
  · dsimp only [gapPBridge, Fold.onLength, bentBridgeFold]
    unfold bentBridgePos
    have h₀ : ¬(2 * A + 4 - 1 = 0) := by omega
    have h₁ : ¬(2 * A + 4 - 1 ≤ 2 * A + 2) := by omega
    simp only [Fin.coe_cast, List.length_replicate, if_neg h₀, if_neg h₁]
    congr 1
    omega

theorem gapPBridge_location (d A : ℕ) (y : ℤ)
    (i : Fin (List.replicate (2 * A + 4) Residue.P).length) :
    (gapPBridge d A y).pos i 0 = d + 1 ∧
    y ≤ (gapPBridge d A y).pos i 1 ∧ (gapPBridge d A y).pos i 1 ≤ y + 2 * A + 1 ∧
    ((gapPBridge d A y).pos i 2 = -2 ∨ (gapPBridge d A y).pos i 2 = -3) := by
  have hi := i.isLt
  simp only [List.length_replicate] at hi
  change _ ∧ _ ∧ _ ∧ (bentBridgePos _ _ _ _ 2 = -2 ∨ bentBridgePos _ _ _ _ 2 = -3)
  dsimp only [gapPBridge, Fold.onLength, bentBridgeFold]
  unfold bentBridgePos
  split_ifs <;> dsimp only [point] <;> omega

end ProteinFolding.CubicPackingWalls

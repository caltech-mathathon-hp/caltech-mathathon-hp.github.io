import ProteinFolding.Cubic.Proofs.PackingSnakeCuboid
import ProteinFolding.Cubic.Proofs.PackingFaceLift
import Mathlib.Data.Fin.Rev

/-! Explicit even-width item strips on the packing face. Reflection and
reversal of the rectangular snake place both terminals on the line x=d.
The lifted literal F word uses only the strip's face sites and their exterior
neighbours at height -1. This is a construction from a packing, not a
restriction on the shapes allowed in an arbitrary perfect folding. -/

namespace ProteinFolding.CubicPackingItems

open CubicCertificates CubicPacking CubicPackingSnake CubicPackingLift

def stripIndex (d width : ℕ) (i : Fin (d * width)) : Fin (width * d) :=
  (Fin.cast (Nat.mul_comm d width) i).rev

theorem stripIndex_injective (d width : ℕ) : Function.Injective (stripIndex d width) := by
  intro i j hij
  have hv := congrArg Fin.val (Fin.rev_injective hij)
  exact Fin.ext hv

theorem stripIndex_surjective (d width : ℕ) : Function.Surjective (stripIndex d width) := by
  intro j
  refine ⟨Fin.cast (Nat.mul_comm width d) j.rev, ?_⟩
  apply Fin.ext
  simp only [stripIndex, Fin.val_rev, Fin.coe_cast]
  have hj := j.isLt
  omega

def stripCorner (d : ℕ) (upper : ℤ) : Site
  | 0 => d
  | 1 => upper
  | 2 => 0

def stripPos (d width : ℕ) (upper : ℤ) (i : Fin (d * width)) : Site :=
  reflect (stripCorner d upper) (rectanglePos width d (stripIndex d width i))

theorem stripPos_injective (d width : ℕ) (upper : ℤ) :
    Function.Injective (stripPos d width upper) :=
  (reflect_injective _).comp ((rectanglePos_injective width d).comp (stripIndex_injective d width))

theorem stripPos_adjacent (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (i j : Fin (d * width)) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (stripPos d width upper i) (stripPos d width upper j) := by
  apply reflect_adj
  exact (rectanglePos_adjacent width d hd _ _ (by
    simp only [stripIndex, Fin.val_rev, Fin.coe_cast]
    have hi := i.isLt
    have hj := j.isLt
    have hm : width * d = d * width := Nat.mul_comm _ _
    omega)).symm

def stripFold (d width : ℕ) (upper : ℤ) (hd : 0 < d) : Fold cubicLattice (d * width) where
  pos := stripPos d width upper
  injective_pos := stripPos_injective d width upper
  consecutive := stripPos_adjacent d width upper hd

theorem stripPos_plane (d width : ℕ) (upper : ℤ) (i : Fin (d * width)) :
    stripPos d width upper i 2 = 0 := by
  change 0 - rectanglePos width d (stripIndex d width i) 2 = 0
  rw [rectanglePos_z]
  rfl

/-- The strip occupies precisely its rectangular set of face sites. -/
theorem stripPos_image (d width : ℕ) (upper : ℤ) (p : Site) :
    (∃ i, stripPos d width upper i = p) ↔
      1 ≤ p 0 ∧ p 0 ≤ d ∧ upper - width < p 1 ∧ p 1 ≤ upper ∧ p 2 = 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    let c := rectangleCells width d (stripIndex d width i)
    have hx := c.2.isLt
    have hy := c.1.isLt
    change 1 ≤ (d : ℤ) - c.2.val ∧ (d : ℤ) - c.2.val ≤ d ∧
      upper - width < upper - c.1.val ∧ upper - c.1.val ≤ upper ∧ (0 : ℤ) - 0 = 0
    omega
  · rintro ⟨hx₁, hx₂, hy₁, hy₂, hz⟩
    let y : Fin width := ⟨(upper - p 1).toNat, by omega⟩
    let x : Fin d := ⟨((d : ℤ) - p 0).toNat, by omega⟩
    obtain ⟨k, hk⟩ := rectanglePos_surjective_cells width d (y, x)
    obtain ⟨i, hi⟩ := stripIndex_surjective d width k
    refine ⟨i, ?_⟩
    unfold stripPos
    rw [hi, hk]
    apply site_ext
    · change (d : ℤ) - (((d : ℤ) - p 0).toNat : ℤ) = p 0
      omega
    · change upper - ((upper - p 1).toNat : ℤ) = p 1
      omega
    · change (0 : ℤ) - 0 = p 2
      omega

def stripFirst (d width : ℕ) (hd : 0 < d) (hw : 0 < width) : Fin (d * width) :=
  ⟨0, Nat.mul_pos hd hw⟩

def stripLast (d width : ℕ) (hd : 0 < d) (hw : 0 < width) : Fin (d * width) :=
  ⟨d * width - 1, by have hp := Nat.mul_pos hd hw; omega⟩

theorem stripPos_first (d width : ℕ) (upper : ℤ) (hd : 0 < d) (hw : 0 < width)
    (heven : width % 2 = 0) :
    stripPos d width upper (stripFirst d width hd hw) =
      fun k => if k = 0 then (d : ℤ) else if k = 1 then upper - width + 1 else 0 := by
  have hi : stripIndex d width (stripFirst d width hd hw) = lastIndex width d hw hd := by
    apply Fin.ext
    simp only [stripIndex, stripFirst, Fin.val_rev, Fin.coe_cast, lastIndex]
  unfold stripPos
  rw [hi, rectanglePos_last_even width d hw hd heven]
  apply site_ext <;> dsimp [reflect, stripCorner] <;> omega

theorem stripPos_last (d width : ℕ) (upper : ℤ) (hd : 0 < d) (hw : 0 < width) :
    stripPos d width upper (stripLast d width hd hw) = stripCorner d upper := by
  have hi : stripIndex d width (stripLast d width hd hw) = firstIndex width d hw hd := by
    apply Fin.ext
    simp only [stripIndex, stripLast, Fin.val_rev, Fin.coe_cast, firstIndex]
    have hp := Nat.mul_pos hd hw
    have hm : width * d = d * width := Nat.mul_comm _ _
    omega
  unfold stripPos
  rw [hi, rectanglePos_first width d hw hd]
  funext k
  simp [reflect]

/-- The literal item word `F_(d*width)` on the chosen rectangular strip. -/
def stripWordFold (d width : ℕ) (upper : ℤ) (hd : 0 < d) (heven : 2 ∣ d * width) :
    Fold cubicLattice (faceWord (d * width)).length :=
  faceLift (d * width) heven (stripFold d width upper hd) (stripPos_plane d width upper)

theorem stripWordFold_H_sites (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (heven : 2 ∣ d * width) (p : Site) :
    p ∈ hydrophobicSites (faceWord (d * width)) (stripWordFold d width upper hd heven) ↔
      1 ≤ p 0 ∧ p 0 ≤ d ∧ upper - width < p 1 ∧ p 1 ≤ upper ∧ p 2 = 0 := by
  rw [stripWordFold, faceLift_hydrophobicSites]
  exact stripPos_image d width upper p

/-- All residues of this item stay over the strip, at heights zero and -1. -/
theorem stripWordFold_location (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (heven : 2 ∣ d * width) (i : Fin (faceWord (d * width)).length) :
    1 ≤ (stripWordFold d width upper hd heven).pos i 0 ∧
    (stripWordFold d width upper hd heven).pos i 0 ≤ d ∧
    upper - width < (stripWordFold d width upper hd heven).pos i 1 ∧
    (stripWordFold d width upper hd heven).pos i 1 ≤ upper ∧
    ((stripWordFold d width upper hd heven).pos i 2 = 0 ∨
      (stripWordFold d width upper hd heven).pos i 2 = -1) := by
  have hb := (stripPos_image d width upper
    ((stripFold d width upper hd).pos (faceBaseIndex (d * width) heven i))).mp ⟨_, rfl⟩
  change _ ∧ _ ∧ _ ∧ _ ∧ (faceHeight i.val = 0 ∨ faceHeight i.val = -1)
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  unfold faceHeight
  split_ifs <;> simp

theorem stripWordFold_first (d width : ℕ) (upper : ℤ)
    (hd : 0 < d) (hw : 0 < width) (heven : width % 2 = 0)
    (hprod : 2 ∣ d * width) :
    (stripWordFold d width upper hd hprod).pos
      (faceFirstIndex (d * width) hprod (Nat.mul_pos hd hw)) =
      fun k => if k = 0 then (d : ℤ) else if k = 1 then upper - width + 1 else -1 := by
  change faceLiftPos _ _ _ _ = _
  rw [faceLiftPos_first]
  change atHeight (stripPos d width upper (stripFirst d width hd hw)) (-1) = _
  rw [stripPos_first d width upper hd hw heven]
  apply site_ext <;> rfl

theorem stripWordFold_last (d width : ℕ) (upper : ℤ)
    (hd : 0 < d) (hw : 0 < width) (hprod : 2 ∣ d * width) :
    (stripWordFold d width upper hd hprod).pos
      (faceLastIndex (d * width) hprod (Nat.mul_pos hd hw)) =
      fun k => if k = 0 then (d : ℤ) else if k = 1 then upper else -1 := by
  change faceLiftPos _ _ _ _ = _
  rw [faceLiftPos_last]
  change atHeight (stripPos d width upper (stripLast d width hd hw)) (-1) = _
  rw [stripPos_last d width upper hd hw]
  apply site_ext <;> rfl

/-- Even widths give an even initial port row and an odd final port row.
This is exactly the parity needed for the odd-length exterior connectors. -/
theorem strip_port_parity (width : ℕ) (upper : ℤ)
    (heven : width % 2 = 0) (hupper : upper % 2 = 1) :
    (upper - width + 1) % 2 = 0 ∧ upper % 2 = 1 := by omega

theorem strip_ports_distinct (width : ℕ) (upper : ℤ)
    (_hw : 0 < width) (heven : width % 2 = 0) : upper - width + 1 ≠ upper := by omega

/-- Separation of row intervals separates every residue, including the P
attachments of both complete literal F words. -/
theorem stripWordFolds_disjoint (d width₁ width₂ : ℕ) (upper₁ upper₂ : ℤ)
    (hd : 0 < d) (heven₁ : 2 ∣ d * width₁) (heven₂ : 2 ∣ d * width₂)
    (hsep : upper₁ ≤ upper₂ - width₂ ∨ upper₂ ≤ upper₁ - width₁)
    (i : Fin (faceWord (d * width₁)).length) (j : Fin (faceWord (d * width₂)).length) :
    (stripWordFold d width₁ upper₁ hd heven₁).pos i ≠
      (stripWordFold d width₂ upper₂ hd heven₂).pos j := by
  intro he
  have hy := congrFun he 1
  have hi := stripWordFold_location d width₁ upper₁ hd heven₁ i
  have hj := stripWordFold_location d width₂ upper₂ hd heven₂ j
  rcases hsep with hsep | hsep <;> omega

theorem stripWordFold_H_in_cube (d width : ℕ) (upper : ℤ) (hd : 0 < d)
    (heven : 2 ∣ d * width) (hlower : 0 ≤ upper - width) (hupper : upper ≤ d)
    (p : Site) (hp : p ∈ hydrophobicSites (faceWord (d * width))
      (stripWordFold d width upper hd heven)) : p ∈ cube (fun _ => 0) (d + 2) := by
  have hp' := (stripWordFold_H_sites d width upper hd heven p).mp hp
  intro k
  match k with
  | 0 => change (0 : ℤ) ≤ p 0 ∧ p 0 < 0 + ((d + 2 : ℕ) : ℤ); omega
  | 1 => change (0 : ℤ) ≤ p 1 ∧ p 1 < 0 + ((d + 2 : ℕ) : ℤ); omega
  | 2 => change (0 : ℤ) ≤ p 2 ∧ p 2 < 0 + ((d + 2 : ℕ) : ℤ); omega

end ProteinFolding.CubicPackingItems

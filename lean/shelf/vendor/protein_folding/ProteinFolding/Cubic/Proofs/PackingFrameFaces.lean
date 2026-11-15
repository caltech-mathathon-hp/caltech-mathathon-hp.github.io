import ProteinFolding.Cubic.Proofs.PackingTopFace

/-! The four complete `F_(d²)` face components, in their exact prefix order
and snake orientations: back, left, bottom and right. The signed coordinate
maps carry the generic face lift's exterior P layer onto the outward side of
each cube face. No statement about an arbitrary perfect fold is assumed. -/

namespace ProteinFolding.CubicPackingFrameFaces

open CubicCertificates CubicPacking CubicPackingSnake CubicPackingLift
open CubicPackingTopFace (point)

inductive Face where
  | back | left | bottom | right
  deriving DecidableEq, Fintype

def faceMap (d : ℕ) : Face → Site → Site
  | .back, p => point (d - p 1) (1 + p 0) (d + 1 - p 2)
  | .left, p => point (p 2) (d - p 1) (d - p 0)
  | .bottom, p => point (1 + p 1) (p 2) (d - p 0)
  | .right, p => point (d + 1 - p 2) (1 + p 1) (d - p 0)

theorem faceMap_injective (d : ℕ) (f : Face) : Function.Injective (faceMap d f) := by
  intro p q he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  cases f <;> apply site_ext <;> dsimp [faceMap, point] at hx hy hz <;> omega

theorem faceMap_adj (d : ℕ) (f : Face) (p q : Site) (ha : cubicLattice.Adj p q) :
    cubicLattice.Adj (faceMap d f p) (faceMap d f q) := by
  change latticeDistance _ _ = 1 at ha ⊢
  rw [distance_eq] at ha ⊢
  have hsub (a x y : ℤ) : a - x - (a - y) = -(x - y) := by ring
  have hadd (a x y : ℤ) : a + x - (a + y) = x - y := by ring
  cases f <;> simp only [faceMap, point, hsub, hadd, Int.natAbs_neg] <;> omega

theorem faceLength_even (d : ℕ) (heven : d % 2 = 0) : 2 ∣ d * d :=
  dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero heven) d

/-- The original complete face word, with its full injective lattice fold. -/
def faceFold (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face) :
    Fold cubicLattice (faceWord (d * d)).length where
  pos i := faceMap d f ((faceLift _ (faceLength_even d heven) (rectangleFold d d hd)
    (fun k => rectanglePos_z d d k)).pos i)
  injective_pos := (faceMap_injective d f).comp
    (faceLift _ (faceLength_even d heven) (rectangleFold d d hd) (fun k => rectanglePos_z d d k)).injective_pos
  consecutive i j hij := faceMap_adj d f _ _
    ((faceLift _ (faceLength_even d heven) (rectangleFold d d hd)
      (fun k => rectanglePos_z d d k)).consecutive i j hij)

def firstP (d : ℕ) : Face → Site
  | .back => point d 1 (d + 2)
  | .left => point (-1) d d
  | .bottom => point 1 (-1) d
  | .right => point (d + 2) 1 d

def lastP (d : ℕ) : Face → Site
  | .back => point 1 1 (d + 2)
  | .left => point (-1) 1 d
  | .bottom => point d (-1) d
  | .right => point (d + 2) d d

theorem faceFold_first (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face) :
    (faceFold d hd heven f).pos
      (faceFirstIndex (d * d) (faceLength_even d heven) (Nat.mul_pos hd hd)) = firstP d f := by
  change faceMap d f (faceLiftPos (d * d) (faceLength_even d heven)
    (rectangleFold d d hd) (faceFirstIndex _ _ _)) = _
  rw [faceLiftPos_first]
  have hfirst := rectanglePos_first d d hd hd
  change rectanglePos d d ⟨0, _⟩ = _ at hfirst
  change faceMap d f (atHeight (rectanglePos d d ⟨0, _⟩) (-1)) = _
  rw [hfirst]
  cases f <;> apply site_ext <;> dsimp [faceMap, point, firstP, atHeight] <;> omega

theorem faceFold_last (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face) :
    (faceFold d hd heven f).pos
      (faceLastIndex (d * d) (faceLength_even d heven) (Nat.mul_pos hd hd)) = lastP d f := by
  change faceMap d f (faceLiftPos (d * d) (faceLength_even d heven)
    (rectangleFold d d hd) (faceLastIndex _ _ _)) = _
  rw [faceLiftPos_last]
  have hlast := rectanglePos_last_even d d hd hd heven
  change rectanglePos d d ⟨d * d - 1, _⟩ = _ at hlast
  change faceMap d f (atHeight (rectanglePos d d ⟨d * d - 1, _⟩) (-1)) = _
  rw [hlast]
  cases f <;> apply site_ext <;> simp [faceMap, point, lastP, atHeight] <;> omega

theorem faceFold_first_of_val (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face)
    (i : Fin (faceWord (d * d)).length) (hi : i.val = 0) :
    (faceFold d hd heven f).pos i = firstP d f := by
  have he : i = faceFirstIndex _ (faceLength_even d heven) (Nat.mul_pos hd hd) := Fin.ext hi
  rw [he]
  exact faceFold_first d hd heven f

theorem faceFold_last_of_end (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face)
    (i : Fin (faceWord (d * d)).length) (hi : i.val + 1 = (faceWord (d * d)).length) :
    (faceFold d hd heven f).pos i = lastP d f := by
  have he : i = faceLastIndex _ (faceLength_even d heven) (Nat.mul_pos hd hd) := by
    apply Fin.ext
    change i.val = (faceWord (d * d)).length - 1
    omega
  rw [he]
  exact faceFold_last d hd heven f

def HSupport (d : ℕ) : Face → Site → Prop
  | .back, p => p 2 = (d : ℤ) + 1 ∧ (1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ))
  | .left, p => p 0 = 0 ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))
  | .bottom, p => p 1 = 0 ∧ (1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))
  | .right, p => p 0 = (d : ℤ) + 1 ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))

def inverseFaceMap (d : ℕ) : Face → Site → Site
  | .back, p => point (p 1 - 1) (d - p 0) (d + 1 - p 2)
  | .left, p => point (d - p 2) (d - p 1) (p 0)
  | .bottom, p => point (d - p 2) (p 0 - 1) (p 1)
  | .right, p => point (d - p 2) (p 1 - 1) (d + 1 - p 0)

theorem faceMap_inverse (d : ℕ) (f : Face) (p : Site) : faceMap d f (inverseFaceMap d f p) = p := by
  cases f <;> apply site_ext <;> dsimp [faceMap, inverseFaceMap, point] <;> omega

theorem HSupport_inverse (d : ℕ) (f : Face) (p : Site) :
    HSupport d f p ↔ (inverseFaceMap d f p) 2 = 0 ∧
      (0 ≤ (inverseFaceMap d f p) 0 ∧ (inverseFaceMap d f p) 0 < (d : ℤ)) ∧
      (0 ≤ (inverseFaceMap d f p) 1 ∧ (inverseFaceMap d f p) 1 < (d : ℤ)) := by
  cases f <;> dsimp [HSupport, inverseFaceMap, point] <;> omega

theorem faceFold_hydrophobicSites_range (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face) (p : Site) :
    p ∈ hydrophobicSites (faceWord (d * d)) (faceFold d hd heven f) ↔
      ∃ k, faceMap d f (rectanglePos d d k) = p := by
  let lift := faceLift (d * d) (faceLength_even d heven) (rectangleFold d d hd) (fun k => rectanglePos_z d d k)
  constructor
  · rintro ⟨i, hi, hp⟩
    obtain ⟨k, hk⟩ := (faceLift_hydrophobicSites _ (faceLength_even d heven)
      (rectangleFold d d hd) (fun k => rectanglePos_z d d k) (lift.pos i)).mp ⟨i, hi, rfl⟩
    exact ⟨k, (congrArg (faceMap d f) hk).trans hp⟩
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi, hp⟩ := (faceLift_hydrophobicSites _ (faceLength_even d heven)
      (rectangleFold d d hd) (fun k => rectanglePos_z d d k) (rectanglePos d d k)).mpr ⟨k, rfl⟩
    exact ⟨i, hi, (congrArg (faceMap d f) hp).trans hk⟩

/-- Each complete face component occupies every interior cell of exactly its
designated cube face, and no other H cells. -/
theorem faceFold_hydrophobicSites (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face) (p : Site) :
    p ∈ hydrophobicSites (faceWord (d * d)) (faceFold d hd heven f) ↔ HSupport d f p := by
  rw [faceFold_hydrophobicSites_range]
  constructor
  · rintro ⟨k, rfl⟩
    have hb := CubicPackingTopFace.rectanglePos_bounds d k
    have hz := rectanglePos_z d d k
    cases f <;> dsimp [HSupport, faceMap, point] <;> omega
  · intro hp
    obtain ⟨hz, hx, hy⟩ := (HSupport_inverse d f p).mp hp
    obtain ⟨k, hk⟩ := CubicPackingTopFace.rectanglePos_exists d (inverseFaceMap d f p) hx hy hz
    exact ⟨k, (congrArg (faceMap d f) hk).trans (faceMap_inverse d f p)⟩

def Region (d : ℕ) : Face → Site → Prop
  | .back, p => (p 2 = (d : ℤ) + 1 ∨ p 2 = (d : ℤ) + 2) ∧
      (1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ))
  | .left, p => (p 0 = 0 ∨ p 0 = -1) ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))
  | .bottom, p => (p 1 = 0 ∨ p 1 = -1) ∧ (1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))
  | .right, p => (p 0 = (d : ℤ) + 1 ∨ p 0 = (d : ℤ) + 2) ∧
      (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ))

theorem faceFold_region (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face)
    (i : Fin (faceWord (d * d)).length) : Region d f ((faceFold d hd heven f).pos i) := by
  let k := faceBaseIndex (d * d) (faceLength_even d heven) i
  have hb := CubicPackingTopFace.rectanglePos_bounds d k
  have hh := faceHeight_cases i.val
  change Region d f (faceMap d f (atHeight (rectanglePos d d k) (faceHeight i.val)))
  cases f <;> dsimp [Region, faceMap, point, atHeight] <;> omega

theorem faceFold_P_outside_cube (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : Face)
    (i : Fin (faceWord (d * d)).length) (hi : (faceWord (d * d)).get i = .P) :
    (faceFold d hd heven f).pos i ∉ cube (fun _ => 0) (d + 2) := by
  have hh := faceLift_P_height (d * d) (faceLength_even d heven) (rectangleFold d d hd) i hi
  change faceHeight i.val = -1 at hh
  intro hc
  cases f with
  | back =>
    have h := hc 2
    change 0 ≤ (d : ℤ) + 1 - faceHeight i.val ∧ (d : ℤ) + 1 - faceHeight i.val < 0 + ((d + 2 : ℕ) : ℤ) at h
    rw [hh] at h
    omega
  | left =>
    have h := hc 0
    change 0 ≤ faceHeight i.val ∧ faceHeight i.val < 0 + ((d + 2 : ℕ) : ℤ) at h
    rw [hh] at h
    omega
  | bottom =>
    have h := hc 1
    change 0 ≤ faceHeight i.val ∧ faceHeight i.val < 0 + ((d + 2 : ℕ) : ℤ) at h
    rw [hh] at h
    omega
  | right =>
    have h := hc 0
    change 0 ≤ (d : ℤ) + 1 - faceHeight i.val ∧ (d : ℤ) + 1 - faceHeight i.val < 0 + ((d + 2 : ℕ) : ℤ) at h
    rw [hh] at h
    omega

theorem faceFolds_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f g : Face) (hfg : f ≠ g)
    (i j : Fin (faceWord (d * d)).length) :
    (faceFold d hd heven f).pos i ≠ (faceFold d hd heven g).pos j := by
  have hf := faceFold_region d hd heven f i
  have hg := faceFold_region d hd heven g j
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  cases f <;> cases g <;> dsimp [Region] at hf hg <;> first | contradiction | omega

theorem faceFold_topFold_disjoint (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) (f : Face)
    (i : Fin (faceWord (d * d)).length) (j : Fin (faceWord (d * d - 2)).length) :
    (faceFold d (by omega) heven f).pos i ≠ (CubicPackingTopFace.topFold d hd heven).pos j := by
  have hf := faceFold_region d (by omega) heven f i
  have ht := CubicPackingTopFace.topFold_bounds d hd heven j
  intro he
  have hy := congrFun he 1
  cases f <;> dsimp [Region] at hf <;> omega

end ProteinFolding.CubicPackingFrameFaces

import ProteinFolding.Cubic.Proofs.PackingGeometryPaths
import ProteinFolding.Cubic.Proofs.PackingSnakeLayers

/-! Lifting any even planar self-avoiding H path to the literal F_t word.
Every H receives exactly one P neighbour at height -1. The pairs alternate
P-H and H-P, so successive blocks join through two adjacent exterior P sites.
Injectivity and all backbone edges are proved for the complete binary word.
This is a constructive completeness lemma, independent of any packing witness. -/

namespace ProteinFolding.CubicPackingLift

open CubicPacking CubicPackingGeometry CubicPackingSnake CubicCertificates

def faceBaseIndex (t : ℕ) (ht : 2 ∣ t) (i : Fin (faceWord t).length) : Fin t :=
  ⟨i.val / 2, by have hi := i.isLt; have hlen := faceWord_length t ht; omega⟩

def faceHeight (i : ℕ) : ℤ := if i % 4 = 0 ∨ i % 4 = 3 then -1 else 0

def faceLiftPos (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (i : Fin (faceWord t).length) : Site :=
  atHeight (base.pos (faceBaseIndex t ht i)) (faceHeight i.val)

theorem faceLiftPos_injective (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) : Function.Injective (faceLiftPos t ht base) := by
  intro i j he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  have hbase : base.pos (faceBaseIndex t ht i) = base.pos (faceBaseIndex t ht j) := by
    apply site_ext
    · exact hx
    · exact hy
    · rw [hplane, hplane]
  have hb : i.val / 2 = j.val / 2 := congrArg (fun k : Fin t => k.val) (base.injective_pos hbase)
  change faceHeight i.val = faceHeight j.val at hz
  apply Fin.ext
  unfold faceHeight at hz
  split_ifs at hz <;> omega

theorem faceLiftPos_adjacent (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) (i j : Fin (faceWord t).length) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (faceLiftPos t ht base i) (faceLiftPos t ht base j) := by
  have hm : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
  rcases hm with hm | hm | hm | hm
  · have hj : j.val % 4 = 1 := by omega
    have hb : faceBaseIndex t ht j = faceBaseIndex t ht i := by
      apply Fin.ext; dsimp [faceBaseIndex]; omega
    unfold faceLiftPos
    rw [hb]
    simpa [faceHeight, hm, hj] using atHeight_vertical (base.pos (faceBaseIndex t ht i)) (-1)
  · have hj : j.val % 4 = 2 := by omega
    have hb : (faceBaseIndex t ht i).val + 1 = (faceBaseIndex t ht j).val := by
      dsimp [faceBaseIndex]; omega
    simpa [faceLiftPos, faceHeight, hm, hj] using
      atHeight_horizontal _ _ 0 (hplane _) (hplane _) (base.consecutive _ _ hb)
  · have hj : j.val % 4 = 3 := by omega
    have hb : faceBaseIndex t ht j = faceBaseIndex t ht i := by
      apply Fin.ext; dsimp [faceBaseIndex]; omega
    unfold faceLiftPos
    rw [hb]
    simpa [faceHeight, hm, hj] using (atHeight_vertical (base.pos (faceBaseIndex t ht i)) (-1)).symm
  · have hj : j.val % 4 = 0 := by omega
    have hb : (faceBaseIndex t ht i).val + 1 = (faceBaseIndex t ht j).val := by
      dsimp [faceBaseIndex]; omega
    simpa [faceLiftPos, faceHeight, hm, hj] using
      atHeight_horizontal _ _ (-1) (hplane _) (hplane _) (base.consecutive _ _ hb)

/-- The full F_t chain, with the original literal word's exact sequence length. -/
def faceLift (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) : Fold cubicLattice (faceWord t).length where
  pos := faceLiftPos t ht base
  injective_pos := faceLiftPos_injective t ht base hplane
  consecutive := fun i j hij => faceLiftPos_adjacent t ht base hplane i j hij

theorem faceWord_residue_height (t : ℕ) (i : Fin (faceWord t).length) :
    (faceWord t).get i = if faceHeight i.val = -1 then .P else .H := by
  have hi := i.isLt
  simp only [faceWord, repeatWord_length] at hi
  change i.val < t / 2 * 4 at hi
  have hblock : i.val / 4 < t / 2 := by omega
  have hrem : i.val % 4 < ([.P, .H, .H, .P] : Sequence).length := by change i.val % 4 < 4; omega
  have he := repeatWord_getElem? [.P, .H, .H, .P] (t / 2) (i.val / 4) (i.val % 4) hblock hrem
  change (faceWord t)[4 * (i.val / 4) + i.val % 4]? = ([.P, .H, .H, .P] : Sequence)[i.val % 4]? at he
  rw [Nat.div_add_mod, List.getElem?_eq_getElem i.isLt] at he
  have hm : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
  rcases hm with hm | hm | hm | hm <;>
    simpa [faceHeight, hm, List.get_eq_getElem] using he

theorem faceHeight_cases (i : ℕ) : faceHeight i = -1 ∨ faceHeight i = 0 := by
  unfold faceHeight
  split_ifs <;> simp

theorem faceWord_H_iff (t : ℕ) (i : Fin (faceWord t).length) :
    (faceWord t).get i = .H ↔ faceHeight i.val = 0 := by
  rw [faceWord_residue_height]
  rcases faceHeight_cases i.val with hm | hm <;> simp [hm]

def faceHIndex (t : ℕ) (ht : 2 ∣ t) (k : Fin t) : Fin (faceWord t).length :=
  ⟨2 * k.val + (if k.val % 2 = 0 then 1 else 0), by
    rw [faceWord_length t ht]
    have hk := k.isLt
    split_ifs <;> omega⟩

theorem faceBaseIndex_HIndex (t : ℕ) (ht : 2 ∣ t) (k : Fin t) :
    faceBaseIndex t ht (faceHIndex t ht k) = k := by
  apply Fin.ext
  dsimp [faceBaseIndex, faceHIndex]
  split_ifs <;> omega

theorem faceHeight_HIndex (t : ℕ) (ht : 2 ∣ t) (k : Fin t) :
    faceHeight (faceHIndex t ht k).val = 0 := by
  by_cases hm : k.val % 2 = 0
  · simp only [faceHIndex, if_pos hm, faceHeight]
    split_ifs <;> omega
  · simp only [faceHIndex, if_neg hm, faceHeight]
    split_ifs <;> omega

theorem atHeight_zero_of_plane (p : Site) (h : p 2 = 0) : atHeight p 0 = p := by
  apply site_ext
  · rfl
  · rfl
  · exact h.symm

/-- H occupation of the lifted word is exactly the chosen planar path. -/
theorem faceLift_hydrophobicSites (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) (p : Site) :
    p ∈ hydrophobicSites (faceWord t) (faceLift t ht base hplane) ↔ ∃ k, base.pos k = p := by
  constructor
  · rintro ⟨i, hi, hpos⟩
    have hz := (faceWord_H_iff t i).mp hi
    refine ⟨faceBaseIndex t ht i, ?_⟩
    have he : faceLiftPos t ht base i = base.pos (faceBaseIndex t ht i) := by
      rw [faceLiftPos, hz]
      exact atHeight_zero_of_plane _ (hplane _)
    exact he.symm.trans hpos
  · rintro ⟨k, hk⟩
    refine ⟨faceHIndex t ht k, (faceWord_H_iff t _).mpr (faceHeight_HIndex t ht k), ?_⟩
    change faceLiftPos t ht base (faceHIndex t ht k) = p
    rw [faceLiftPos, faceBaseIndex_HIndex, faceHeight_HIndex,
      atHeight_zero_of_plane _ (hplane k)]
    exact hk

theorem faceLift_P_height (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (i : Fin (faceWord t).length) (hi : (faceWord t).get i = .P) : faceLiftPos t ht base i 2 = -1 := by
  have h := faceWord_residue_height t i
  have hz : faceHeight i.val = -1 := by
    by_contra hn
    simp only [if_neg hn] at h
    rw [hi] at h
    contradiction
  exact hz

theorem faceLift_hydrophobicSites_eq (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (hplane : ∀ k, base.pos k 2 = 0) :
    hydrophobicSites (faceWord t) (faceLift t ht base hplane) = Set.range base.pos := by
  ext p
  exact faceLift_hydrophobicSites t ht base hplane p

def faceFirstIndex (t : ℕ) (ht : 2 ∣ t) (hpos : 0 < t) : Fin (faceWord t).length :=
  ⟨0, by have hlen := faceWord_length t ht; omega⟩

def faceLastIndex (t : ℕ) (ht : 2 ∣ t) (hpos : 0 < t) : Fin (faceWord t).length :=
  ⟨(faceWord t).length - 1, by have hlen := faceWord_length t ht; omega⟩

/-- The endpoint P sites are the outward neighbours of the endpoint H sites. -/
theorem faceLiftPos_first (t : ℕ) (ht : 2 ∣ t) (hpos : 0 < t) (base : Fold cubicLattice t) :
    faceLiftPos t ht base (faceFirstIndex t ht hpos) = atHeight (base.pos ⟨0, hpos⟩) (-1) := by
  have hb : faceBaseIndex t ht (faceFirstIndex t ht hpos) = ⟨0, hpos⟩ := by
    apply Fin.ext
    simp [faceBaseIndex, faceFirstIndex]
  rw [faceLiftPos, hb]
  simp [faceHeight, faceFirstIndex]

theorem faceLiftPos_last (t : ℕ) (ht : 2 ∣ t) (hpos : 0 < t) (base : Fold cubicLattice t) :
    faceLiftPos t ht base (faceLastIndex t ht hpos) =
      atHeight (base.pos ⟨t - 1, by omega⟩) (-1) := by
  have hlen := faceWord_length t ht
  have heven := Nat.mul_div_cancel' ht
  have hb : faceBaseIndex t ht (faceLastIndex t ht hpos) = ⟨t - 1, by omega⟩ := by
    apply Fin.ext
    change ((faceWord t).length - 1) / 2 = t - 1
    omega
  have hh : faceHeight (faceLastIndex t ht hpos).val = -1 := by
    have hm : ((faceWord t).length - 1) % 4 = 3 := by omega
    simp [faceHeight, faceLastIndex, hm]
  rw [faceLiftPos, hb, hh]

theorem faceLift_P_outside_cube (t : ℕ) (ht : 2 ∣ t) (base : Fold cubicLattice t)
    (i : Fin (faceWord t).length) (hi : (faceWord t).get i = .P) (n : ℕ) :
    faceLiftPos t ht base i ∉ cube (fun _ => 0) n := by
  intro hp
  have hz := (hp 2).1
  change (0 : ℤ) ≤ faceLiftPos t ht base i 2 at hz
  rw [faceLift_P_height t ht base i hi] at hz
  omega

end ProteinFolding.CubicPackingLift

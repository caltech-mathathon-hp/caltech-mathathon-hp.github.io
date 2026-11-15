import ProteinFolding.Cubic.Proofs.PackingGeometryCompression
import ProteinFolding.Cubic.Proofs.PackingGeometryFaces
import ProteinFolding.Cubic.Proofs.PackingWords

/-! Extracting the compressed H paths of the literal edge and face words
from arbitrary perfect folds. The surrounding prefix and suffix are arbitrary;
no preferred embedding or orientation is imposed. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking CubicCertificates

theorem repeatWord_getElem? (w : Sequence) (t i r : ℕ) (hi : i < t) (hr : r < w.length) :
    (repeatWord w t)[w.length * i + r]? = w[r]? := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    cases i with
    | zero => simpa only [Nat.mul_zero, Nat.zero_add, repeatWord] using
        (List.getElem?_append_left (l₂ := repeatWord w t) hr)
    | succ i =>
      rw [repeatWord, List.getElem?_append_right (by rw [Nat.mul_succ]; omega)]
      have he : w.length * (i + 1) + r - w.length = w.length * i + r := by
        rw [Nat.mul_succ]
        omega
      rw [he]
      exact ih i (by omega)

def edgeIndex (pre post : Sequence) (t : ℕ) (i : Fin t) (r : Fin 3) :
    Fin (pre ++ edgeWord t ++ post).length :=
  ⟨pre.length + 3 * i.val + r.val, by
    have hi := i.isLt
    have hr := r.isLt
    simp only [List.length_append, edgeWord_length]
    omega⟩

theorem edgeIndex_residue (pre post : Sequence) (t : ℕ) (i : Fin t) (r : Fin 3) :
    (pre ++ edgeWord t ++ post).get (edgeIndex pre post t i r) =
      if r = 1 then .H else .P := by
  have he : (pre ++ edgeWord t ++ post)[(edgeIndex pre post t i r).val]? =
      ([.P, .H, .P] : Sequence)[r.val]? := by
    simp only [edgeIndex, List.append_assoc]
    rw [List.getElem?_append_right (by omega)]
    have hs : pre.length + 3 * i.val + r.val - pre.length = 3 * i.val + r.val := by omega
    rw [hs, List.getElem?_append_left (by rw [edgeWord_length]; have := i.isLt; have := r.isLt; omega)]
    exact repeatWord_getElem? [.P, .H, .P] t i.val r.val i.isLt r.isLt
  rw [List.getElem?_eq_getElem (edgeIndex pre post t i r).isLt,
    List.getElem?_eq_getElem r.isLt] at he
  have h := Option.some.inj he
  fin_cases r <;> simpa only [List.get_eq_getElem, Fin.reduceFinMk,
    ↓reduceIte, List.getElem_cons_succ, List.getElem_cons_zero] using h

def edgeHPath (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ edgeWord t ++ post).length) : Fin t → Site :=
  fun i => f.pos (edgeIndex pre post t i 1)

theorem edgeHPath_injective (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ edgeWord t ++ post).length) :
    Function.Injective (edgeHPath pre post t f) := by
  intro i j he
  have h := congrArg Fin.val (f.injective_pos he)
  change pre.length + 3 * i.val + 1 = pre.length + 3 * j.val + 1 at h
  apply Fin.ext
  omega

theorem edgeHPath_on_skeleton (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ edgeWord t ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ edgeWord t ++ post) f = cube a n) :
    ∀ i, EdgeSkeleton a n (edgeHPath pre post t f i) := by
  intro i
  apply php_on_edge f a n hpack (edgeIndex pre post t i 0)
    (edgeIndex pre post t i 1) (edgeIndex pre post t i 2)
  · simp only [edgeIndex]; omega
  · simp only [edgeIndex]; omega
  · exact edgeIndex_residue pre post t i 0
  · exact edgeIndex_residue pre post t i 1
  · exact edgeIndex_residue pre post t i 2

theorem edgeHPath_adjacent (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ edgeWord t ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ edgeWord t ++ post) f = cube a n) :
    ∀ i j : Fin t, i.val + 1 = j.val →
      cubicLattice.Adj (edgeHPath pre post t f i) (edgeHPath pre post t f j) := by
  intro i j hij
  apply hpph_adjacent f a n hpack (edgeIndex pre post t i 1)
    (edgeIndex pre post t i 2) (edgeIndex pre post t j 0) (edgeIndex pre post t j 1)
  · simp only [edgeIndex]; omega
  · simp only [edgeIndex]; omega
  · simp only [edgeIndex]; omega
  · exact edgeIndex_residue pre post t i 1
  · exact edgeIndex_residue pre post t i 2
  · exact edgeIndex_residue pre post t j 0
  · exact edgeIndex_residue pre post t j 1

def faceIndex (pre post : Sequence) (t : ℕ) (i : Fin (t / 2)) (r : Fin 4) :
    Fin (pre ++ faceWord t ++ post).length :=
  ⟨pre.length + 4 * i.val + r.val, by
    have hi := i.isLt
    have hr := r.isLt
    simp only [List.length_append, faceWord, repeatWord_length]
    change pre.length + 4 * i.val + r.val < pre.length + t / 2 * 4 + post.length
    omega⟩

theorem faceIndex_residue (pre post : Sequence) (t : ℕ) (i : Fin (t / 2)) (r : Fin 4) :
    (pre ++ faceWord t ++ post).get (faceIndex pre post t i r) =
      if r = 1 ∨ r = 2 then .H else .P := by
  have he : (pre ++ faceWord t ++ post)[(faceIndex pre post t i r).val]? =
      ([.P, .H, .H, .P] : Sequence)[r.val]? := by
    simp only [faceIndex, List.append_assoc]
    rw [List.getElem?_append_right (by omega)]
    have hs : pre.length + 4 * i.val + r.val - pre.length = 4 * i.val + r.val := by omega
    rw [hs, List.getElem?_append_left (by
      simp only [faceWord, repeatWord_length]
      change 4 * i.val + r.val < t / 2 * 4
      have := i.isLt
      have := r.isLt
      omega)]
    exact repeatWord_getElem? [.P, .H, .H, .P] (t / 2) i.val r.val i.isLt r.isLt
  rw [List.getElem?_eq_getElem (faceIndex pre post t i r).isLt,
    List.getElem?_eq_getElem r.isLt] at he
  have h := Option.some.inj he
  fin_cases r <;> simpa only [List.get_eq_getElem, Fin.reduceFinMk,
    ↓reduceIte, List.getElem_cons_succ, List.getElem_cons_zero] using h

def faceBlock {t : ℕ} (i : Fin (2 * (t / 2))) : Fin (t / 2) :=
  ⟨i.val / 2, by have := i.isLt; omega⟩

def faceHOffset {t : ℕ} (i : Fin (2 * (t / 2))) : Fin 4 := ⟨i.val % 2 + 1, by omega⟩

theorem faceHOffset_mem {t : ℕ} (i : Fin (2 * (t / 2))) :
    faceHOffset i = 1 ∨ faceHOffset i = 2 := by
  simp only [faceHOffset, Fin.ext_iff]
  omega

def faceHPath (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ faceWord t ++ post).length) : Fin (2 * (t / 2)) → Site :=
  fun i => f.pos (faceIndex pre post t (faceBlock i) (faceHOffset i))

theorem faceHPath_injective (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ faceWord t ++ post).length) :
    Function.Injective (faceHPath pre post t f) := by
  intro i j he
  have h := congrArg Fin.val (f.injective_pos he)
  change pre.length + 4 * (i.val / 2) + (i.val % 2 + 1) =
    pre.length + 4 * (j.val / 2) + (j.val % 2 + 1) at h
  apply Fin.ext
  omega

theorem faceHPath_on_surface (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ faceWord t ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ faceWord t ++ post) f = cube a n) :
    ∀ i, Surface a n (faceHPath pre post t f i) := by
  intro i
  have hh : (pre ++ faceWord t ++ post).get
      (faceIndex pre post t (faceBlock i) (faceHOffset i)) = .H := by
    rw [faceIndex_residue]
    simp only [faceHOffset_mem, ite_true]
  by_cases hi : i.val % 2 = 0
  · apply hp_on_surface f a n hpack
      (faceIndex pre post t (faceBlock i) (faceHOffset i))
      (faceIndex pre post t (faceBlock i) 0)
    · apply (f.consecutive _ _ ?_).symm
      simp only [faceIndex, faceHOffset, hi]
      omega
    · exact hh
    · exact faceIndex_residue pre post t (faceBlock i) 0
  · apply hp_on_surface f a n hpack
      (faceIndex pre post t (faceBlock i) (faceHOffset i))
      (faceIndex pre post t (faceBlock i) 3)
    · apply f.consecutive
      simp only [faceIndex, faceHOffset]
      omega
    · exact hh
    · exact faceIndex_residue pre post t (faceBlock i) 3

theorem faceHPath_adjacent (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ faceWord t ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ faceWord t ++ post) f = cube a n) :
    ∀ i j : Fin (2 * (t / 2)), i.val + 1 = j.val →
      cubicLattice.Adj (faceHPath pre post t f i) (faceHPath pre post t f j) := by
  intro i j hij
  by_cases hi : i.val % 2 = 0
  · apply f.consecutive
    simp only [faceIndex, faceBlock, faceHOffset]
    omega
  · apply hpph_adjacent f a n hpack
      (faceIndex pre post t (faceBlock i) (faceHOffset i))
      (faceIndex pre post t (faceBlock i) 3)
      (faceIndex pre post t (faceBlock j) 0)
      (faceIndex pre post t (faceBlock j) (faceHOffset j))
    · simp only [faceIndex, faceBlock, faceHOffset]; omega
    · simp only [faceIndex, faceBlock]; omega
    · simp only [faceIndex, faceBlock, faceHOffset]; omega
    · simp only [faceIndex_residue, faceHOffset_mem, ite_true]
    · exact faceIndex_residue pre post t (faceBlock i) 3
    · exact faceIndex_residue pre post t (faceBlock j) 0
    · simp only [faceIndex_residue, faceHOffset_mem, ite_true]

/-- A nonempty F word occupies one face interior once skeleton saturation
has excluded its H sites from every cube edge. No preferred face is assumed. -/
theorem faceHPath_in_one_face (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ faceWord t ++ post).length)
    (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (pre ++ faceWord t ++ post) f = cube a n)
    (ht : 0 < 2 * (t / 2))
    (hedge : ∀ i, ¬ EdgeSkeleton a n (faceHPath pre post t f i)) :
    ∃ axis upper, ∀ i, FaceInterior a n axis upper (faceHPath pre post t f i) :=
  surface_path_in_one_face (faceHPath pre post t f) ht
    (faceHPath_on_surface pre post t f a n hpack) hedge
    (faceHPath_adjacent pre post t f a n hpack)

end ProteinFolding.CubicPackingGeometry

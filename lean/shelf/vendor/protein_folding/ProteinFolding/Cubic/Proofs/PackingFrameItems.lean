import ProteinFolding.Cubic.Proofs.PackingFrameFaceConfinement
import ProteinFolding.Cubic.Proofs.PackingFromLabels
import Mathlib.Data.List.Infix

/-! The actual item F fragments, indexed by occurrences in the original size
list. Their source intervals are disjoint regardless of repeated item sizes. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

def itemBlock (q Q a : ℕ) : Sequence :=
  List.replicate (4 * side q Q) .P ++ faceWord (depth q Q * a)

def itemFaceOccurrence (q Q : ℕ) (items : List ℕ) (i : Fin items.length) :
    FaceOccurrence (frameWord q Q items) (depth q Q * items.get i) where
  pre := prefixWord q Q ++ walls q Q ++ (items.take i.val).flatMap (itemBlock q Q) ++
    List.replicate (4 * side q Q) .P
  post := (items.drop (i.val + 1)).flatMap (itemBlock q Q)
  word_eq := by
    have he : items = items.take i.val ++ items.get i :: items.drop (i.val + 1) := by
      have h := (List.take_append_drop i.val items).symm
      rw [List.drop_eq_getElem_cons i.isLt] at h
      exact h
    have hf := congrArg (fun xs => xs.flatMap (itemBlock q Q)) he
    have hfull := congrArg (fun w => prefixWord q Q ++ walls q Q ++ w) hf
    simpa only [frameWord, itemWords, itemBlock, List.flatMap_append, List.flatMap_cons,
      List.append_assoc] using hfull

theorem itemFaceOccurrence_after_prefix (q Q : ℕ) (items : List ℕ) (i : Fin items.length) :
    (prefixWord q Q).length ≤ (itemFaceOccurrence q Q items i).pre.length := by
  simp only [itemFaceOccurrence, List.length_append, List.length_replicate]
  omega

theorem itemFaceOccurrence_before (q Q : ℕ) (items : List ℕ) (i j : Fin items.length)
    (hij : i < j) :
    (itemFaceOccurrence q Q items i).pre.length + (faceWord (depth q Q * items.get i)).length ≤
      (itemFaceOccurrence q Q items j).pre.length := by
  have htake := ((List.take_prefix_take_left (l := items)
    (show i.val + 1 ≤ j.val by exact hij)).flatMap (itemBlock q Q)).length_le
  rw [List.take_succ_eq_append_getElem i.isLt, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil] at htake
  simp only [List.length_append, itemBlock, List.length_replicate, List.length_nil,
    Nat.add_zero] at htake
  simp only [itemFaceOccurrence, List.length_append, List.length_replicate]
  simp only [List.get_eq_getElem]
  omega

theorem itemFaceOccurrence_sites_disjoint (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (i j : Fin items.length) (hij : i ≠ j) :
    Disjoint ((itemFaceOccurrence q Q items i).sites f) ((itemFaceOccurrence q Q items j).sites f) := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact FaceOccurrence.sites_disjoint_of_before _ _ f (itemFaceOccurrence_before q Q items i j hij)
  · exact (FaceOccurrence.sites_disjoint_of_before _ _ f (itemFaceOccurrence_before q Q items j i hij)).symm

theorem itemFaceOccurrence_sites_card (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (i : Fin items.length) :
    ((itemFaceOccurrence q Q items i).sites f).card = depth q Q * items.get i := by
  rw [FaceOccurrence.sites_card]
  exact Nat.mul_div_cancel' (Nat.dvd_mul_right_of_dvd (depth_even q Q) _)

/-- Every item of a successful actual frame fold lies on the same face.
The conclusion uses arbitrary folded item shapes, with no rectangular-shape
assumption and no bound on the number of items assigned to a bin. -/
theorem frame_item_faces (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (hpositive : ∀ x ∈ items, 0 < x)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ face : CubeFace, ∀ (i : Fin items.length) p,
      p ∈ (itemFaceOccurrence q Q items i).sites f →
        FaceInterior a (side q Q) face.1 face.2 p := by
  have hd : 2 < depth q Q := by
    dsimp [depth, beta]
    nlinarith [Nat.zero_le (q * Q)]
  obtain ⟨face, hface⟩ := frame_remaining_face_confines q Q items (by omega)
    (by nlinarith : 4 < depth q Q ^ 2) f a hpack
  refine ⟨face, ?_⟩
  intro i
  apply hface (depth q Q * items.get i) (itemFaceOccurrence q Q items i)
    (itemFaceOccurrence_after_prefix q Q items i)
  have hp : 0 < items.get i := hpositive _ (List.get_mem items i)
  have he : 2 * (depth q Q * items.get i / 2) = depth q Q * items.get i :=
    Nat.mul_div_cancel' (Nat.dvd_mul_right_of_dvd (depth_even q Q) _)
  rw [he]
  nlinarith

end ProteinFolding.CubicPackingGeometry

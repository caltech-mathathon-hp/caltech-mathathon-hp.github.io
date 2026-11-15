import ProteinFolding.Cubic.Proofs.PackingGeometryBlockOccurrences
import ProteinFolding.Cubic.Proofs.PackingGeometryLargeFaces

/-! Literal F fragments in a larger protein, with their exact sequence indices.
The surrounding fold is arbitrary; injectivity of the complete chain gives
disjointness of fragments whose source intervals do not overlap. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

structure FaceOccurrence (S : Sequence) (t : ℕ) where
  pre : Sequence
  post : Sequence
  word_eq : S = pre ++ faceWord t ++ post

namespace FaceOccurrence

def index {S : Sequence} {t : ℕ} (o : FaceOccurrence S t) (i : Fin (2 * (t / 2))) :
    Fin S.length :=
  Fin.cast (congrArg List.length o.word_eq).symm
    (faceIndex o.pre o.post t (faceBlock i) (faceHOffset i))

theorem index_val {S : Sequence} {t : ℕ} (o : FaceOccurrence S t) (i : Fin (2 * (t / 2))) :
    (o.index i).val = o.pre.length + 4 * (i.val / 2) + (i.val % 2 + 1) := rfl

theorem index_in_fragment {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (i : Fin (2 * (t / 2))) :
    o.pre.length ≤ (o.index i).val ∧ (o.index i).val < o.pre.length + (faceWord t).length := by
  have hi := i.isLt
  rw [index_val]
  simp only [faceWord, repeatWord_length]
  change o.pre.length ≤ o.pre.length + 4 * (i.val / 2) + (i.val % 2 + 1) ∧
    o.pre.length + 4 * (i.val / 2) + (i.val % 2 + 1) < o.pre.length + t / 2 * 4
  omega

def path {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) (i : Fin (2 * (t / 2))) : Site := f.pos (o.index i)

theorem path_eq {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) :
    o.path f = faceHPath o.pre o.post t (foldOnWord o.word_eq f) := by
  funext i
  exact (foldOnWord_pos o.word_eq f (faceIndex o.pre o.post t (faceBlock i) (faceHOffset i))).symm

theorem path_injective {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) : Function.Injective (o.path f) := by
  rw [o.path_eq]
  exact faceHPath_injective o.pre o.post t (foldOnWord o.word_eq f)

def sites {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) : Finset Site := Finset.univ.image (o.path f)

theorem sites_card {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) : (o.sites f).card = 2 * (t / 2) := by
  rw [sites, Finset.card_image_of_injective _ (o.path_injective f)]
  simp

theorem sites_disjoint_of_before {S : Sequence} {t u : ℕ}
    (o : FaceOccurrence S t) (p : FaceOccurrence S u)
    (f : Fold cubicLattice S.length)
    (hbefore : o.pre.length + (faceWord t).length ≤ p.pre.length) :
    Disjoint (o.sites f) (p.sites f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
  have he := congrArg Fin.val (f.injective_pos (hi.trans hj.symm))
  have ho := o.index_in_fragment i
  have hp := p.index_in_fragment j
  omega

/-- A nonempty literal F fragment belongs to one face once edge sites have
been excluded. Both compression and face confinement are already proved. -/
theorem in_one_face {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites S f = cube a n) (ht : 0 < 2 * (t / 2))
    (hnoedge : ∀ i, ¬ EdgeSkeleton a n (o.path f i)) :
    ∃ face : CubeFace, ∀ p ∈ o.sites f, FaceInterior a n face.1 face.2 p := by
  have hno : ∀ i, ¬ EdgeSkeleton a n
      (faceHPath o.pre o.post t (foldOnWord o.word_eq f) i) := by
    simpa only [o.path_eq] using hnoedge
  obtain ⟨axis, upper, hface⟩ := faceHPath_in_one_face o.pre o.post t (foldOnWord o.word_eq f)
    a n (by rw [foldOnWord_hydrophobicSites]; exact hpack) ht hno
  refine ⟨(axis, upper), ?_⟩
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  rw [o.path_eq]
  exact hface i

end FaceOccurrence

end ProteinFolding.CubicPackingGeometry

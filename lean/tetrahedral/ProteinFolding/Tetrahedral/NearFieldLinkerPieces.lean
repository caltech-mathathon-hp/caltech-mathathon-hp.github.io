import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly

/-! A full cap-to-cap far-field route contributes exactly its interior P word;
the already occupied caps are retained once, in the adjacent units. -/

namespace ProteinFolding.Tetrahedral.NearField

def innerLinkerFold {L : ℕ} (f : Fold tetrahedralLattice L) :
    Fold tetrahedralLattice (List.replicate (L - 2) Residue.P).length where
  pos i := f.pos ⟨i.val + 1, by have h := i.isLt; simp only [List.length_replicate] at h; omega⟩
  injective_pos i j hij := by
    apply Fin.ext
    have h := congrArg Fin.val (f.injective_pos hij)
    change i.val + 1 = j.val + 1 at h
    omega
  consecutive i j hij := by
    apply f.consecutive
    change i.val + 1 + 1 = j.val + 1
    omega

def innerLinkerFirst {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L) : Site :=
  f.pos ⟨1, by omega⟩

def innerLinkerLast {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L) : Site :=
  f.pos ⟨L - 2, by omega⟩

def innerLinkerPiece {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L) : PositionedWord where
  word := List.replicate (L - 2) .P
  fold := innerLinkerFold f
  length_pos := by simp only [List.length_replicate]; omega
  first := innerLinkerFirst hL f
  last := innerLinkerLast hL f
  first_eq i hi := by
    apply congrArg f.pos
    exact Fin.ext (by change i.val + 1 = 1; omega)
  last_eq i hi := by
    apply congrArg f.pos
    apply Fin.ext
    change i.val + 1 = L - 2
    simpa only [List.length_replicate] using hi

theorem innerLinkerPiece_hSupport {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L) :
    hSupport (innerLinkerPiece hL f).word (innerLinkerPiece hL f).fold = ∅ :=
  hSupport_allP_empty _ _

theorem innerLinker_first_seam {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L)
    (p : Site) (hp : ∀ i, i.val = 0 → f.pos i = p) :
    tetrahedralLattice.Adj p (innerLinkerPiece hL f).first := by
  rw [← hp ⟨0, by omega⟩ rfl]
  exact f.consecutive ⟨0, by omega⟩ ⟨1, by omega⟩ rfl

theorem innerLinker_last_seam {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L)
    (p : Site) (hp : ∀ i, i.val + 1 = L → f.pos i = p) :
    tetrahedralLattice.Adj (innerLinkerPiece hL f).last p := by
  rw [← hp ⟨L - 1, by omega⟩ (by dsimp; omega)]
  apply f.consecutive
  change L - 2 + 1 = L - 1
  omega

theorem innerLinkerFold_avoids_obstacles {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L)
    (O : Set Site) (p q : Site)
    (hp : ∀ i, i.val = 0 → f.pos i = p)
    (hq : ∀ i, i.val + 1 = L → f.pos i = q)
    (hO : ∀ i, f.pos i ∈ O → f.pos i = p ∨ f.pos i = q)
    (i : Fin (List.replicate (L - 2) Residue.P).length) :
    (innerLinkerFold f).pos i ∉ O := by
  intro hi
  let r : Fin L := ⟨i.val + 1, by have h := i.isLt; simp only [List.length_replicate] at h; omega⟩
  have hr0 : r.val ≠ 0 := by dsimp [r]; omega
  have hrLast : r.val + 1 ≠ L := by
    have h := i.isLt
    simp only [List.length_replicate] at h
    dsimp [r]
    omega
  rcases hO r hi with h | h
  · have heq := f.injective_pos (h.trans (hp ⟨0, by omega⟩ rfl).symm)
    exact hr0 (congrArg Fin.val heq)
  · have heq := f.injective_pos (h.trans (hq ⟨L - 1, by omega⟩ (by dsimp; omega)).symm)
    have hv := congrArg Fin.val heq
    exact hrLast (by dsimp at hv; omega)

end ProteinFolding.Tetrahedral.NearField

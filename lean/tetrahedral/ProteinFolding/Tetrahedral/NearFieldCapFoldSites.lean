import ProteinFolding.Tetrahedral.NearFieldCapFold

/-! Exact sites and terminal positions of a capped literal word. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem foldSites_onePFold (p : Site) : foldSites (onePFold p) = {p} := by
  ext x
  simp [foldSites, onePFold]

theorem cappedWordFold_sites {S : Sequence} (f : Fold tetrahedralLattice S.length) (p q : Site)
    (hS : 0 < S.length) (hp : ∀ i, p ≠ f.pos i) (hq : ∀ i, f.pos i ≠ q) (hpq : p ≠ q)
    (hfirst : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (hlast : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q) :
    foldSites (cappedWordFold f p q hS hp hq hpq hfirst hlast) =
      ({p} ∪ foldSites f) ∪ {q} := by
  change foldSites (Fold.appendWord (Fold.appendWord _ _ _ _) _ _ _) = _
  rw [foldSites_appendWord, foldSites_appendWord, foldSites_onePFold, foldSites_onePFold]

theorem cappedWordFold_first {S : Sequence} (f : Fold tetrahedralLattice S.length) (p q : Site)
    (hS : 0 < S.length) (hp : ∀ i, p ≠ f.pos i) (hq : ∀ i, f.pos i ≠ q) (hpq : p ≠ q)
    (hfirst : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (hlast : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q)
    (i : Fin (capWord S).length) (hi : i.val = 0) :
    (cappedWordFold f p q hS hp hq hpq hfirst hlast).pos i = p := by
  have heq : i = Fold.leftWordIndex ([Residue.P] ++ S) [Residue.P]
      (Fold.leftWordIndex [Residue.P] S ⟨0, by decide⟩) := by
    apply Fin.ext
    exact hi
  rw [heq]
  change (Fold.appendWord (Fold.appendWord _ _ _ _) _ _ _).pos
    (Fold.leftWordIndex ([Residue.P] ++ S) [Residue.P]
      (Fold.leftWordIndex [Residue.P] S ⟨0, by decide⟩)) = p
  rw [Fold.appendWord_pos_left, Fold.appendWord_pos_left]
  rfl

theorem cappedWordFold_last {S : Sequence} (f : Fold tetrahedralLattice S.length) (p q : Site)
    (hS : 0 < S.length) (hp : ∀ i, p ≠ f.pos i) (hq : ∀ i, f.pos i ≠ q) (hpq : p ≠ q)
    (hfirst : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (hlast : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q)
    (i : Fin (capWord S).length) (hi : i.val + 1 = (capWord S).length) :
    (cappedWordFold f p q hS hp hq hpq hfirst hlast).pos i = q := by
  have heq : i = Fold.rightWordIndex ([Residue.P] ++ S) [Residue.P] ⟨0, by decide⟩ := by
    apply Fin.ext
    dsimp [Fold.rightWordIndex]
    simp only [capWord, List.length_cons, List.length_append, List.length_nil] at hi ⊢
    omega
  rw [heq]
  change (Fold.appendWord _ (onePFold q) _ _).pos
    (Fold.rightWordIndex ([Residue.P] ++ S) [Residue.P] ⟨0, by decide⟩) = q
  rw [Fold.appendWord_pos_right]
  rfl

end ProteinFolding.Tetrahedral.NearField


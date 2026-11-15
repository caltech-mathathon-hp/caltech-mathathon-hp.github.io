import ProteinFolding.Tetrahedral.FoldAssembly
import ProteinFolding.Tetrahedral.FrameWordPHP

/-! Adding two actual P sites to a nonempty word preserves its H support. -/

namespace ProteinFolding.Tetrahedral.NearField

def onePFold (p : Site) : Fold tetrahedralLattice ([Residue.P] : Sequence).length where
  pos _ := p
  injective_pos i j _ := by
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega
  consecutive i j hij := by
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega

def prependPFold {S : Sequence} (f : Fold tetrahedralLattice S.length) (p : Site)
    (hdisjoint : ∀ i, p ≠ f.pos i)
    (hseam : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i)) :
    Fold tetrahedralLattice ([Residue.P] ++ S).length :=
  Fold.appendWord (onePFold p) f (fun _ j => hdisjoint j)
    (fun _ j _ hj => hseam j hj)

theorem prependPFold_avoids {S : Sequence} (f : Fold tetrahedralLattice S.length) (p : Site)
    (hdisjoint : ∀ i, p ≠ f.pos i)
    (hseam : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (q : Site) (hpq : p ≠ q) (hq : ∀ i, f.pos i ≠ q)
    (i : Fin ([Residue.P] ++ S).length) : (prependPFold f p hdisjoint hseam).pos i ≠ q := by
  intro heq
  have hmem : q ∈ foldSites (prependPFold f p hdisjoint hseam) := (mem_foldSites _ _).mpr ⟨i, heq⟩
  rw [prependPFold, foldSites_appendWord] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact hpq hj
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact hq j hj

theorem prependPFold_last_seam {S : Sequence} (f : Fold tetrahedralLattice S.length) (p : Site)
    (hS : 0 < S.length) (hdisjoint : ∀ i, p ≠ f.pos i)
    (hseam : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (q : Site) (hq : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q)
    (i : Fin ([Residue.P] ++ S).length) (hi : i.val + 1 = ([Residue.P] ++ S).length) :
    tetrahedralLattice.Adj ((prependPFold f p hdisjoint hseam).pos i) q := by
  have hil := i.isLt
  simp only [List.length_append, List.length_cons, List.length_nil] at hi hil
  let j : Fin S.length := ⟨i.val - 1, by omega⟩
  have hij : i = Fold.rightWordIndex [Residue.P] S j := by
    apply Fin.ext
    dsimp [Fold.rightWordIndex, j]
    omega
  rw [hij]
  change tetrahedralLattice.Adj ((Fold.appendWord _ _ _ _).pos (Fold.rightWordIndex _ _ j)) q
  rw [Fold.appendWord_pos_right]
  apply hq j
  dsimp [j]
  omega

def cappedWordFold {S : Sequence} (f : Fold tetrahedralLattice S.length) (p q : Site)
    (hS : 0 < S.length) (hp : ∀ i, p ≠ f.pos i) (hq : ∀ i, f.pos i ≠ q)
    (hpq : p ≠ q)
    (hfirst : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (hlast : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q) :
    Fold tetrahedralLattice (capWord S).length := by
  let g := prependPFold f p hp hfirst
  have hdis : ∀ i j, g.pos i ≠ (onePFold q).pos j :=
    fun i _ => prependPFold_avoids f p hp hfirst q hpq hq i
  have hseam : ∀ (i : Fin ([Residue.P] ++ S).length) (j : Fin ([Residue.P] : Sequence).length),
      i.val + 1 = ([Residue.P] ++ S).length → j.val = 0 →
      tetrahedralLattice.Adj (g.pos i) ((onePFold q).pos j) :=
    fun i _ hi _ => prependPFold_last_seam f p hS hp hfirst q hlast i hi
  exact Fold.appendWord g (onePFold q) hdis hseam

theorem hSupport_onePFold (p : Site) : hSupport [Residue.P] (onePFold p) = ∅ := by
  simpa only [List.replicate_succ, List.replicate_zero] using hSupport_allP_empty 1 (onePFold p)

theorem cappedWordFold_hSupport {S : Sequence} (f : Fold tetrahedralLattice S.length) (p q : Site)
    (hS : 0 < S.length) (hp : ∀ i, p ≠ f.pos i) (hq : ∀ i, f.pos i ≠ q) (hpq : p ≠ q)
    (hfirst : ∀ i, i.val = 0 → tetrahedralLattice.Adj p (f.pos i))
    (hlast : ∀ i, i.val + 1 = S.length → tetrahedralLattice.Adj (f.pos i) q) :
    hSupport (capWord S) (cappedWordFold f p q hS hp hq hpq hfirst hlast) = hSupport S f := by
  change hSupport (([Residue.P] ++ S) ++ [Residue.P])
    (Fold.appendWord (Fold.appendWord _ _ _ _) _ _ _) = _
  rw [hSupport_appendWord, hSupport_appendWord, hSupport_onePFold, hSupport_onePFold]
  simp

end ProteinFolding.Tetrahedral.NearField

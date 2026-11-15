import ProteinFolding.Tetrahedral.FrameForcingSeparatorLocation
import ProteinFolding.Tetrahedral.FrameForcingCataloguePoints

/-! Exact physical HH occurrences and offsets of one central separator
chain, independently of the enclosing reduction frame. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem catalogue_separator_centre_data {α : Type} {S : Sequence}
    (p : ConstructionParameters) (k : ℕ) (f : Fold tetrahedralLattice S.length)
    (hsupport : hSupport S f = octahedron p.side) (c : DimerCatalogue α S)
    (pre post : Sequence) (hsep : S = pre ++ capWord (p.separatorWord k) ++ post)
    (iC : c.Index) (hC : c.q iC = 2)
    (hpreC : (c.pre iC).length = pre.length + p.entryTether k + 2) :
    let D := foldDimerPairs S f
    let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep
    ∃ i j : DimerOccurrence S, i ≠ j ∧
      D.point (i, false) = P.site (p.entryTether k + 3) ∧
      D.point (i, true) = P.site (p.entryTether k + 4) ∧
      D.point (j, false) = P.site (p.entryTether k + 8) ∧
      D.point (j, true) = P.site (p.entryTether k + 9) ∧
      OctTriangularNeighbours p.side (D.point (i, true)) (D.point (j, false)) ∧
      p.separatorCentreSites k P ⊆ c.chainSites f iC ∧
      ∀ t, c.q t ≠ 2 → Disjoint (c.chainSites f t) (p.separatorCentreSites k P) := by
  let D := foldDimerPairs S f
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep
  let a : Fin (c.q iC) := ⟨0, by omega⟩
  let b : Fin (c.q iC) := ⟨1, by omega⟩
  let i := factorDimerOccurrence S (c.pre iC) (c.post iC) (c.q iC) (c.factor iC) a
  let j := factorDimerOccurrence S (c.pre iC) (c.post iC) (c.q iC) (c.factor iC) b
  have hpoint (t : Fin (c.q iC)) (e : Bool) :
      D.point (factorDimerOccurrence S (c.pre iC) (c.post iC) (c.q iC) (c.factor iC) t, e) =
        P.site (p.entryTether k + (5 * t.val + if e then 4 else 3)) := by
    change (factorDimerPairs S f (c.pre iC) (c.post iC) (c.q iC) (c.factor iC)).point (t, e) = _
    rw [factorDimerPairs_point S f p.side hsupport]
    change foldSiteAt f ((c.pre iC).length + (5 * t.val + if e then 2 else 1)) =
      foldSiteAt f (pre.length + (p.entryTether k + (5 * t.val + if e then 4 else 3)))
    congr 1
    rw [hpreC]
    cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hA : D.point (i, false) = P.site (p.entryTether k + 3) := by simpa [i, a] using hpoint a false
  have hB : D.point (i, true) = P.site (p.entryTether k + 4) := by simpa [i, a] using hpoint a true
  have hC' : D.point (j, false) = P.site (p.entryTether k + 8) := by simpa [j, b] using hpoint b false
  have hD : D.point (j, true) = P.site (p.entryTether k + 9) := by simpa [j, b] using hpoint b true
  have hmem (t : Fin (c.q iC)) (e : Bool) :
      D.point (factorDimerOccurrence S (c.pre iC) (c.post iC) (c.q iC) (c.factor iC) t, e) ∈
        c.chainSites f iC := c.chainPairs_point_mem f iC t e
  have hcentreSub : p.separatorCentreSites k P ⊆ c.chainSites f iC := by
    intro x hx
    simp only [ConstructionParameters.separatorCentreSites, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [← hA]; exact hmem a false
    · rw [← hB]; exact hmem a true
    · rw [← hC']; exact hmem b false
    · rw [← hD]; exact hmem b true
  have hcentreAvoid (t : c.Index) (hne : c.q t ≠ 2) :
      Disjoint (c.chainSites f t) (p.separatorCentreSites k P) := by
    have hti : t ≠ iC := by intro he; subst t; exact hne hC
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (c.chainSites_disjoint f t iC hti) hx (hcentreSub hy)
  have hne : i ≠ j := by
    intro he
    have hn := congrArg Subtype.val he
    change (c.pre iC).length + 5 * 0 = (c.pre iC).length + 5 * 1 at hn
    omega
  have hlink : OctTriangularNeighbours p.side (D.point (i, true)) (D.point (j, false)) := by
    exact factorDimerPairs_link S f p.side hsupport (c.pre iC) (c.post iC) (c.q iC) (c.factor iC) 0 (by omega)
  exact ⟨i, j, hne, hA, hB, hC', hD, hlink, hcentreSub, hcentreAvoid⟩

end ProteinFolding.Tetrahedral

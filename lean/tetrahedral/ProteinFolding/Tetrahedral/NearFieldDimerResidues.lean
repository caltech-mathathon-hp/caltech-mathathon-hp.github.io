import ProteinFolding.Tetrahedral.NearFieldUnitSupport
import ProteinFolding.Tetrahedral.NearFieldLeftFillerSupport
import ProteinFolding.Tetrahedral.NearFieldAssemblySeparation

/-! Polar residues of the actual dimer words remain outside the octahedron. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem edgeDimerFold_P_outside {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) (hP : (dimerChain (q + 1)).get i = .P) :
    (edgeDimerFold hm F base q reverse hroom).pos i ∉ octahedron m := by
  have hi : i.val < 5 * q + 2 := by simpa only [dimerChain_succ_length] using i.isLt
  have hmod : ¬ i.val % 5 < 2 := by
    intro hH
    have hg := dimerChain_get_mod5 q i
    rw [hP, if_pos hH] at hg
    cases hg
  rw [edgeDimerFold_pos]
  exact edgeDimerCurve_P_outside hm F base q reverse hroom i.val hi hmod

theorem edgeDimerFold_oct_site_mem_Hsites {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length)
    (hoct : (edgeDimerFold hm F base q reverse hroom).pos i ∈ octahedron m) :
    (edgeDimerFold hm F base q reverse hroom).pos i ∈ edgeDimerHsites m F base q := by
  have hH := site_mem_hSupport_of_mem_oct (S := dimerChain (q + 1))
    (edgeDimerFold hm F base q reverse hroom) m
    (edgeDimerFold_P_outside hm F base q reverse hroom) _
    ((mem_foldSites _ _).mpr ⟨i, rfl⟩) hoct
  rw [edgeDimerFold_hSupport] at hH
  exact hH

theorem intervalDimerFold_P_outside {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (i : Fin (dimerChain n).length) (hP : (dimerChain n).get i = .P) :
    (intervalDimerFold hm F base n hn reverse hroom).pos i ∉ octahedron m := by
  have he : n - 1 + 1 = n := by omega
  have hi : i.val < 5 * (n - 1) + 2 := by
    have hl := dimerChain_succ_length (n - 1)
    rw [he] at hl
    rw [← hl]
    exact i.isLt
  have hmod : ¬ i.val % 5 < 2 := by
    intro hH
    have hg := dimerChain_get_mod5_positive n hn i
    rw [hP, if_pos hH] at hg
    cases hg
  rw [intervalDimerFold_pos]
  exact edgeDimerCurve_P_outside hm F base (n - 1) reverse (by omega) i.val hi hmod

theorem leftFillerFold_P_outside (p : ConstructionParameters) (i : Fin (dimerChain p.leftFiller).length)
    (hP : (dimerChain p.leftFiller).get i = .P) : (leftFillerFold p).pos i ∉ octahedron p.side := by
  have hl : 0 < p.leftFiller := by have h := p.leftFiller_ge; omega
  have hmod : ¬ i.val % 5 < 2 := by
    intro hH
    have hg := dimerChain_get_mod5_positive p.leftFiller hl i
    rw [hP, if_pos hH] at hg
    cases hg
  have hn : i.val ≠ 0 := by intro he; simp only [he, Nat.zero_mod] at hmod; omega
  have hi : i.val < 5 * (p.leftFiller - 1) + 2 := by
    rw [← leftFiller_word_length p]
    exact i.isLt
  rw [leftFillerFold_pos, leftFillerCurve, if_neg hn]
  exact edgeDimerCurve_P_outside (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p) i.val hi hmod

theorem P_outside_of_sites_hSupport {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) (m : ℕ) (caps : Finset Site)
    (hcap : ∀ x ∈ caps, x ∉ octahedron m)
    (hsites : foldSites g ⊆ caps ∪ foldSites f)
    (hSupport : hSupport T g = hSupport S f)
    (hP : ∀ i, S.get i = .P → f.pos i ∉ octahedron m)
    (i : Fin T.length) (hi : T.get i = .P) : g.pos i ∉ octahedron m := by
  intro hoct
  have hx := hsites ((mem_foldSites g _).mpr ⟨i, rfl⟩)
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hcap _ hx hoct
  · have hH := site_mem_hSupport_of_mem_oct (S := S) f m hP _ hx hoct
    rw [← hSupport] at hH
    have hres := residue_H_of_pos_mem_hSupport (S := T) g i hH
    rw [hi] at hres
    cases hres

end ProteinFolding.Tetrahedral.NearField

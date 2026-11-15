import ProteinFolding.Tetrahedral.NearFieldUnitPieces
import ProteinFolding.Tetrahedral.NearFieldIntervalPieces

/-! All H residues of the actual local word pieces lie in the octahedron. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem dimerChain_get_mod5_positive (n : ℕ) (hn : 0 < n) (i : Fin (dimerChain n).length) :
    (dimerChain n).get i = if i.val % 5 < 2 then .H else .P := by
  have he : n - 1 + 1 = n := by omega
  have h := dimerChain_getElem_mod5 (n - 1) i.val (by rw [he]; exact i.isLt)
  rw [he] at h
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp h
  simpa only [List.get_eq_getElem] using hget

theorem edgeDimerCurve_H_inOctahedron {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ)
    (hi : i < 5 * q + 2) (hH : i % 5 < 2) :
    InOctahedron m (edgeDimerCurve m F base reverse i) := by
  exact (mem_octahedron m (edgeDimerCurve m F base reverse i)).mp
    (edgeDimerCurve_H_mem hm F base q reverse hroom i hi hH)

theorem columnOwner_inOctahedron {m : ℕ} (C : DanglingColumn m) :
    InOctahedron m C.owner := (mem_octahedron m C.owner).mp C.owner_mem

private theorem subset_transport {A B T : Finset Site} (h : A = B) (hB : B ⊆ T) : A ⊆ T := by
  rw [h]
  exact hB

theorem hSupport_subset_oct_of_Hcoordinates {S : Sequence} {m : ℕ}
    (f : Fold tetrahedralLattice S.length)
    (hf : ∀ i, S.get i = .H → InOctahedron m (f.pos i)) : hSupport S f ⊆ octahedron m := by
  intro x hx
  obtain ⟨i, hH, hi⟩ := (mem_hSupport S f x).mp hx
  rw [← hi]
  exact (mem_octahedron m (f.pos i)).mpr (hf i hH)

private theorem site_inOctahedron {m : ℕ} {x : Site} (hx : x ∈ octahedron m) :
    InOctahedron m x := (mem_octahedron m x).mp hx

private theorem columnOwner_singleton_subset_oct {m : ℕ} (C : DanglingColumn m) :
    ({C.owner} : Finset Site) ⊆ octahedron m := Finset.singleton_subset_iff.mpr C.owner_mem

theorem leftFillerFold_H_inOctahedron (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) (hH : (dimerChain p.leftFiller).get i = .H) :
    InOctahedron p.side ((leftFillerFold p).pos i) := by
  intro d
  have hl : 0 < p.leftFiller := by have h := p.leftFiller_ge; omega
  have hmod : i.val % 5 < 2 := by
    have hg := dimerChain_get_mod5_positive p.leftFiller hl i
    rw [hH] at hg
    by_contra hbad
    simp only [if_neg hbad] at hg
    cases hg
  by_cases hi : i.val = 0
  · rw [leftFillerFold_pos, leftFillerCurve, if_pos hi]
    exact site_inOctahedron (leftFillerStart_mem_oct p) d
  · rw [leftFillerFold_pos, leftFillerCurve, if_neg hi]
    have hlen : i.val < 5 * (p.leftFiller - 1) + 2 := by
      have hb := i.isLt
      have hn := leftFiller_word_length p
      omega
    have hm : 1 ≤ p.side := by have h := p.side_ge; omega
    exact edgeDimerCurve_H_inOctahedron hm trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) i.val hlen hmod d

theorem leftFillerFold_hSupport_subset_oct (p : ConstructionParameters) :
    hSupport (dimerChain p.leftFiller) (leftFillerFold p) ⊆ octahedron p.side :=
  hSupport_subset_oct_of_Hcoordinates (S := dimerChain p.leftFiller) (leftFillerFold p)
    (leftFillerFold_H_inOctahedron p)

theorem cappedLeftFillerFold_hSupport_subset_oct (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    hSupport (capWord (dimerChain p.leftFiller)) (cappedLeftFillerFold p C D hC hD) ⊆ octahedron p.side :=
  subset_transport (cappedLeftFillerFold_hSupport p C D hC hD) (leftFillerFold_hSupport_subset_oct p)

theorem cappedIntervalDimerPiece_hSupport_subset_oct {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base n : ℕ) (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1)) :
    hSupport (cappedIntervalDimerPiece hm F base n hn reverse hroom C D hC hD).word
      (cappedIntervalDimerPiece hm F base n hn reverse hroom C D hC hD).fold ⊆ octahedron m :=
  subset_transport (cappedIntervalDimerFold_hSupport hm F base n hn reverse hroom C D hC hD)
    (edgeDimerHsites_subset_oct hm F base (n - 1) (by omega))

theorem singletonWordPiece_hSupport_subset_oct {m : ℕ} (C D : DanglingColumn m)
    (howner : C.owner = D.owner) (hseed : C.seed ≠ D.seed) :
    hSupport (singletonWordPiece C D howner hseed).word (singletonWordPiece C D howner hseed).fold ⊆ octahedron m :=
  subset_transport (cappedSingletonFold_hSupport C D howner hseed) (columnOwner_singleton_subset_oct C)

theorem terminalWordPiece_hSupport_subset_oct (p : ConstructionParameters) :
    hSupport (terminalWordPiece p).word (terminalWordPiece p).fold ⊆ octahedron p.side := by
  apply hSupport_subset_oct_of_Hcoordinates (S := [.H, .P]) (terminalWordFold p)
  intro i hH
  intro d
  have hi0 : i.val = 0 := by
    by_contra hi0
    have hi : i.val < 2 := i.isLt
    have hi1 : i = ⟨1, by decide⟩ := by
      apply Fin.ext
      change i.val = 1
      omega
    have hP : ([Residue.H, .P] : Sequence).get i = .P := by rw [hi1]; rfl
    rw [hP] at hH
    cases hH
  have hsite : (terminalWordPiece p).fold.pos i = (terminalColumn p).owner :=
    (terminalWordPiece p).first_eq i hi0
  change (terminalWordFold p).pos i = (terminalColumn p).owner at hsite
  rw [hsite]
  exact columnOwner_inOctahedron (terminalColumn p) d

end ProteinFolding.Tetrahedral.NearField

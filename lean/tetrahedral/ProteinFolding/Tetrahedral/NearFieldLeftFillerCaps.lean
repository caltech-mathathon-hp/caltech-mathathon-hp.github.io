import ProteinFolding.Tetrahedral.NearFieldLeftFillerFold
import ProteinFolding.Tetrahedral.NearFieldDimerBulkClearance

/-! Both endpoint caps belong to the actual corner-starting left filler. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem leftFillerLast_index (p : ConstructionParameters) :
    dimerHIndex 0 false (p.leftFiller - 1) 1 = 2 * p.leftFiller - 2 := by
  have hl := p.leftFiller_ge
  have heven := p.leftFiller_even
  dsimp [dimerHIndex, dimerFlip]
  omega

theorem leftFillerFold_ne_first_cap (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (i : Fin (dimerChain p.leftFiller).length) : (leftFillerFold p).pos i ≠ C.seed := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · intro heq
    have hmem := leftFillerStart_mem_oct p
    rw [heq] at hmem
    exact C.seed_outside hmem
  · have hm : 1 ≤ p.side := by have h := p.side_ge; omega
    have hnot : C.owner ∉ edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1) := by
      intro hc
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hc
      rw [hC] at hr
      exact leftFillerStart_ne_track p _ hr.symm
    let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hq := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have hbody := edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) C hnot j
    rw [edgeDimerFold_pos] at hbody
    exact hbody

theorem leftFillerFold_ne_last_cap (p : ConstructionParameters) (D : DanglingColumn p.side)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (i : Fin (dimerChain p.leftFiller).length) : (leftFillerFold p).pos i ≠ D.seed := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · intro heq
    have hmem := leftFillerStart_mem_oct p
    rw [heq] at hmem
    exact D.seed_outside hmem
  · let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hq := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have hbody := edgeDimerFold_ne_last_cap (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame 0
      (p.leftFiller - 1) false (leftFiller_room p) D (by rw [leftFillerLast_index]; exact hD) j
    rw [edgeDimerFold_pos] at hbody
    exact hbody

def cappedLeftFillerFold (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    Fold tetrahedralLattice (capWord (dimerChain p.leftFiller)).length :=
  cappedWordFold (leftFillerFold p) C.seed D.seed
    (by rw [leftFiller_word_length]; omega)
    (fun i => (leftFillerFold_ne_first_cap p C hC i).symm)
    (leftFillerFold_ne_last_cap p D hD)
    (by
      apply dangling_caps_ne_of_owner_ne p.side C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
      rw [hC, hD]
      exact leftFillerStart_ne_track p _)
    (by intro i hi; rw [leftFillerFold_first p i hi, ← hC]; exact (step_adj C.owner C.dir).symm)
    (by intro i hi; rw [leftFillerFold_last p i hi, ← hD]; exact step_adj D.owner D.dir)

theorem cappedLeftFillerFold_hSupport (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    hSupport (capWord (dimerChain p.leftFiller)) (cappedLeftFillerFold p C D hC hD) =
      hSupport (dimerChain p.leftFiller) (leftFillerFold p) := cappedWordFold_hSupport _ _ _ _ _ _ _ _ _

theorem cappedLeftFillerFold_sites (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    foldSites (cappedLeftFillerFold p C D hC hD) =
      ({C.seed} ∪ foldSites (leftFillerFold p)) ∪ {D.seed} := cappedWordFold_sites _ _ _ _ _ _ _ _ _

theorem leftFillerFold_ne_bulkEndColumn (p : ConstructionParameters)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (dimerChain p.leftFiller).length) (n : ℕ) :
    (leftFillerFold p).pos i ≠ C.point n := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · intro heq
    have hmem := leftFillerStart_mem_oct p
    rw [heq] at hmem
    exact C.point_outside n hmem
  · let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hq := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have hbody := edgeDimerFold_ne_bulkEndColumn p.side (by have h := p.side_ge; omega) trackEdgeFrame 0
      (p.leftFiller - 1) false (leftFiller_room p) C hC hend j n
    rw [edgeDimerFold_pos] at hbody
    exact hbody

end ProteinFolding.Tetrahedral.NearField

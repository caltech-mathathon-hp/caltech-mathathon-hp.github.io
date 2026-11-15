import ProteinFolding.Tetrahedral.NearFieldLeftFillerFold

/-! Scalar locality bounds for the actual corner-starting left filler. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem edgeDimerFold_inSkinSolid {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) :
    InSkinSolid m 1 ((edgeDimerFold hm F base q reverse hroom).pos i) := by
  exact (mem_skinSolid m 1 ((edgeDimerFold hm F base q reverse hroom).pos i)).mp
    (edgeDimerFold_mem_solid_one hm F base q reverse hroom i)

theorem leftFillerFold_mem_solid_one (p : ConstructionParameters) (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i ∈ skinSolid p.side 1 := by
  apply (mem_skinSolid p.side 1 ((leftFillerFold p).pos i)).mpr
  intro d
  by_cases hi : i.val = 0
  · rw [leftFillerFold_pos, leftFillerCurve, if_pos hi]
    have hd := ((mem_octahedron p.side (octEdgeZigzag p.side entryEdgeFrame 2)).mp
      (leftFillerStart_mem_oct p)) d
    dsimp [octRadius] at hd
    push_cast
    omega
  · rw [leftFillerFold_pos, leftFillerCurve, if_neg hi]
    let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hq := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have hm : 1 ≤ p.side := by have h := p.side_ge; omega
    have hd := edgeDimerFold_inSkinSolid hm trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) j d
    rw [edgeDimerFold_pos] at hd
    exact hd

end ProteinFolding.Tetrahedral.NearField

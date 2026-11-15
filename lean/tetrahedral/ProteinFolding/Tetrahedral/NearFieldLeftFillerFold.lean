import ProteinFolding.Tetrahedral.NearFieldDimerBounds
import ProteinFolding.Tetrahedral.ConstructionParameters
import ProteinFolding.Tetrahedral.OctahedralTrackGeometry
import ProteinFolding.Tetrahedral.FrameForcingTrackPath

/-! The left filler starts with (entry[2], entry[1]), then follows the track
dimers and their actual three-P links. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem leftFiller_room (p : ConstructionParameters) :
    0 + 2 * (p.leftFiller - 1 + 1) ≤ 2 * p.side - 1 := by
  have hm := p.side_ge
  have hs := p.side_eq_track
  have hl := p.leftFiller_ge
  omega

theorem leftFillerStart_ne_track (p : ConstructionParameters) (r : ℕ) :
    octEdgeZigzag p.side entryEdgeFrame 2 ≠ octEdgeZigzag p.side trackEdgeFrame r := by
  intro heq
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hx := congrArg (fun x : Site => x.val 0) heq
  have hy := congrArg (fun x : Site => x.val 1) heq
  change (octEdgeZigzag p.side entryEdgeFrame 2).val 0 =
    (octEdgeZigzag p.side trackEdgeFrame r).val 0 at hx
  change (octEdgeZigzag p.side entryEdgeFrame 2).val 1 =
    (octEdgeZigzag p.side trackEdgeFrame r).val 1 at hy
  rw [entryEdgeZigzag_coordinates hm, trackEdgeZigzag_coordinates hm] at hx hy
  change (0 : ℤ) = r at hx
  change octRadius p.side + 2 = octRadius p.side + (r % 2 : ℕ) at hy
  omega

theorem leftFillerStart_mem_oct (p : ConstructionParameters) :
    octEdgeZigzag p.side entryEdgeFrame 2 ∈ octahedron p.side := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have h := octEdgeZigzag_mem hm entryEdgeFrame (show 2 < 2 * p.side - 1 by have h := p.side_ge; omega)
  exact h.elim (fun h => h.1.1) (fun h => h.1.1)

theorem leftFillerStart_ne_curve (p : ConstructionParameters) (i : ℕ)
    (hi : i < 5 * (p.leftFiller - 1) + 2) :
    octEdgeZigzag p.side entryEdgeFrame 2 ≠ edgeDimerCurve p.side trackEdgeFrame 0 false i := by
  by_cases hH : i % 5 < 2
  · simp only [edgeDimerCurve, dif_pos hH]
    exact leftFillerStart_ne_track p _
  · intro heq
    have hoct := leftFillerStart_mem_oct p
    rw [heq] at hoct
    exact edgeDimerCurve_P_outside (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame 0
      (p.leftFiller - 1) false (leftFiller_room p) i hi hH hoct

def leftFillerCurve (p : ConstructionParameters) (i : ℕ) : Site :=
  if i = 0 then octEdgeZigzag p.side entryEdgeFrame 2
  else edgeDimerCurve p.side trackEdgeFrame 0 false i

def leftFillerRawFold (p : ConstructionParameters) :
    Fold tetrahedralLattice (5 * (p.leftFiller - 1) + 2) where
  pos i := leftFillerCurve p i.val
  injective_pos i j heq := by
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact Fin.ext (hi.trans hj.symm)
      · exfalso
        exact leftFillerStart_ne_curve p j.val j.isLt (by simpa only [leftFillerCurve, hi, hj, if_pos, if_false] using heq)
    · by_cases hj : j.val = 0
      · exfalso
        exact leftFillerStart_ne_curve p i.val i.isLt (by simpa only [leftFillerCurve, hi, hj, if_pos, if_false] using heq.symm)
      · apply edgeDimerCurve_injective (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame 0
          (p.leftFiller - 1) false (leftFiller_room p)
        simpa only [leftFillerCurve, hi, hj, if_false] using heq
  consecutive i j hij := by
    have hj : j.val ≠ 0 := by omega
    by_cases hi : i.val = 0
    · have hj1 : j.val = 1 := by omega
      change tetrahedralLattice.Adj (leftFillerCurve p i.val) (leftFillerCurve p j.val)
      rw [leftFillerCurve, if_pos hi, leftFillerCurve, if_neg hj, hj1]
      change tetrahedralLattice.Adj (octEdgeZigzag p.side entryEdgeFrame 2)
        (edgeDimerCurve p.side trackEdgeFrame 0 false (5 * 0 + (1 : Fin 2).val))
      rw [edgeDimerCurve_H]
      change tetrahedralLattice.Adj (octEdgeZigzag p.side entryEdgeFrame 2)
        (octEdgeZigzag p.side trackEdgeFrame 1)
      have hshared := start_corner_shared p.side (by have h := p.side_ge; omega) entryEdgeFrame
      change octEdgeZigzag p.side entryEdgeFrame 1 = octEdgeZigzag p.side trackEdgeFrame 1 at hshared
      rw [← hshared]
      exact (octEdgeZigzag_adj p.side entryEdgeFrame 1).symm
    · change tetrahedralLattice.Adj (leftFillerCurve p i.val) (leftFillerCurve p j.val)
      simp only [leftFillerCurve, if_neg hi, if_neg hj]
      rw [← hij]
      exact edgeDimerCurve_consecutive p.side trackEdgeFrame 0 false i.val

theorem leftFiller_word_length (p : ConstructionParameters) :
    (dimerChain p.leftFiller).length = 5 * (p.leftFiller - 1) + 2 := by
  have hl := p.leftFiller_ge
  have he : p.leftFiller = p.leftFiller - 1 + 1 := by omega
  conv_lhs => rw [he]
  exact dimerChain_succ_length _

def leftFillerFold (p : ConstructionParameters) : Fold tetrahedralLattice (dimerChain p.leftFiller).length :=
  (leftFillerRawFold p).onLength (leftFiller_word_length p)

theorem leftFillerFold_pos (p : ConstructionParameters) (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i = leftFillerCurve p i.val := rfl

theorem leftFillerFold_first (p : ConstructionParameters) (i : Fin (dimerChain p.leftFiller).length)
    (hi : i.val = 0) : (leftFillerFold p).pos i = octEdgeZigzag p.side entryEdgeFrame 2 := by
  rw [leftFillerFold_pos, leftFillerCurve, if_pos hi]

theorem leftFillerFold_last (p : ConstructionParameters) (i : Fin (dimerChain p.leftFiller).length)
    (hi : i.val + 1 = (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2) := by
  have hl := p.leftFiller_ge
  have heven := p.leftFiller_even
  have hiv : i.val = 5 * (p.leftFiller - 1) + 1 := by
    have hi' := hi.trans (leftFiller_word_length p)
    omega
  rw [leftFillerFold_pos, leftFillerCurve, if_neg (by omega : i.val ≠ 0), hiv]
  change edgeDimerCurve p.side trackEdgeFrame 0 false (5 * (p.leftFiller - 1) + (1 : Fin 2).val) = _
  rw [edgeDimerCurve_H]
  congr 1
  dsimp [dimerHIndex, dimerFlip]
  omega

end ProteinFolding.Tetrahedral.NearField

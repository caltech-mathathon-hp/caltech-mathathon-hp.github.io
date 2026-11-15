import ProteinFolding.Tetrahedral.NearFieldRingPieces
import ProteinFolding.Tetrahedral.NearFieldDimerChainDisjoint

/-! The physical H intervals of the three oriented sides are disjoint,
including their small-face B corners. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem edgePoint_big_coordinate_lower (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hr : r < 2 * m - 1) :
    octRadius m - 1 ≤ tetraCoordinate m (octEdgeZigzag m F r).val F.k := by
  rcases octEdgeZigzag_mem hm F hr with hA | hB
  · rw [hA.1.2.2]
    omega
  · rw [hB.2]
    dsimp only [octRadius]
    omega

theorem ringSide_end_coordinate_upper (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hr : r + 3 ≤ 2 * m - 1) :
    tetraCoordinate m (octEdgeZigzag m F r).val F.a ≤ octRadius m - 4 := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with heven | hodd
  · have heq : r = 2 * (r / 2) := by omega
    have hf := (octEdgeZigzag_even (by omega : 1 ≤ m) F (r / 2)).2.2.2.1
    rw [← heq] at hf
    dsimp only [octRadius] at hf ⊢
    omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    have hf := (octEdgeZigzag_odd (by omega : 1 ≤ m) F (r / 2)).2.2.2.1
    rw [← heq] at hf
    dsimp only [octRadius] at hf ⊢
    omega

theorem ringSide_point_ne_next (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r s : ℕ) (hr : r + 3 ≤ 2 * m - 1) (hs : s < 2 * m - 1) :
    octEdgeZigzag m F r ≠ octEdgeZigzag m (ringNextFrame F) s := by
  intro heq
  have hupper := ringSide_end_coordinate_upper m hm F r hr
  have hlower := edgePoint_big_coordinate_lower m (by omega) (ringNextFrame F) s hs
  change octRadius m - 1 ≤ tetraCoordinate m (octEdgeZigzag m (ringNextFrame F) s).val F.a at hlower
  rw [← heq] at hlower
  omega

theorem ringSideHsites_disjoint_next (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    Disjoint (edgeDimerHsites m F 1 (m - 3))
      (edgeDimerHsites m (ringNextFrame F) 1 (m - 3)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp'
  have hi := i.isLt
  have hjb := j.isLt
  exact ringSide_point_ne_next m hm F (1 + i.val) (1 + j.val)
    (by omega) (by omega) hj.symm

theorem ringSideFolds_disjoint_next (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i j : Fin (dimerChain (m - 2)).length) :
    (ringSideFold m hm F).pos i ≠ (ringSideFold m hm (ringNextFrame F)).pos j := by
  have hlen : (dimerChain (m - 3 + 1)).length = (dimerChain (m - 2)).length := by
    rw [show m - 3 + 1 = m - 2 by omega]
  let i' : Fin (dimerChain (m - 3 + 1)).length := ⟨i.val, by rw [hlen]; exact i.isLt⟩
  let j' : Fin (dimerChain (m - 3 + 1)).length := ⟨j.val, by rw [hlen]; exact j.isLt⟩
  have h := edgeDimerFolds_disjoint (by omega : 1 ≤ m) F (ringNextFrame F)
    1 (m - 3) 1 (m - 3) false false (by omega) (by omega)
    (ringSideHsites_disjoint_next m hm F) i' j'
  simpa only [edgeDimerFold_pos, ringSideFold_pos] using h

def ringSideFrame (F : OctEdgeFrame) (i : Fin 3) : OctEdgeFrame :=
  match i.val with
  | 0 => F
  | 1 => ringNextFrame F
  | _ => ringNextFrame (ringNextFrame F)

theorem ringSideFolds_pairwise (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i j : Fin 3) (hij : i ≠ j)
    (r s : Fin (dimerChain (m - 2)).length) :
    (ringSideFold m hm (ringSideFrame F i)).pos r ≠
      (ringSideFold m hm (ringSideFrame F j)).pos s := by
  have h01 := ringSideFolds_disjoint_next m hm F
  have h12 := ringSideFolds_disjoint_next m hm (ringNextFrame F)
  have h20 := ringSideFolds_disjoint_next m hm (ringNextFrame (ringNextFrame F))
  simp only [ringNextFrame_three] at h20
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01 r s
    | exact (h01 s r).symm
    | exact h12 r s
    | exact (h12 s r).symm
    | exact h20 r s
    | exact (h20 s r).symm

end ProteinFolding.Tetrahedral.NearField

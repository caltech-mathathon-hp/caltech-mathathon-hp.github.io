import ProteinFolding.Tetrahedral.NearFieldDimerChainArithmetic
import ProteinFolding.Tetrahedral.NearFieldPPPEdges

/-! An explicit alternating-dimer walk, before restriction to a finite word. -/

namespace ProteinFolding.Tetrahedral.NearField

def edgeDimerCurve (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool) (i : ℕ) : Site :=
  if h : i % 5 < 2 then
    octEdgeZigzag m F (dimerHIndex base reverse (i / 5) ⟨i % 5, h⟩)
  else
    (edgePPPFold m F (dimerLinkIndex base reverse (i / 5))).pos
      ⟨i % 5 - 2, by have := Nat.mod_lt i (by decide : 0 < 5); omega⟩

theorem edgeDimerCurve_H (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool)
    (j : ℕ) (s : Fin 2) :
    edgeDimerCurve m F base reverse (5 * j + s.val) =
      octEdgeZigzag m F (dimerHIndex base reverse j s) := by
  have hd : (5 * j + s.val) / 5 = j := by omega
  have hr : (5 * j + s.val) % 5 = s.val := by omega
  simp only [edgeDimerCurve, hd, hr, dif_pos s.isLt]

theorem edgeDimerCurve_P (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool)
    (j : ℕ) (s : Fin 3) :
    edgeDimerCurve m F base reverse (5 * j + 2 + s.val) =
      (edgePPPFold m F (dimerLinkIndex base reverse j)).pos s := by
  have hd : (5 * j + 2 + s.val) / 5 = j := by omega
  have hr : (5 * j + 2 + s.val) % 5 = 2 + s.val := by omega
  have hn : ¬2 + s.val < 2 := by omega
  simp only [edgeDimerCurve, hd, hr, dif_neg hn]
  congr 1
  apply Fin.ext
  simp

theorem edgeDimerCurve_HH (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool) (j : ℕ) :
    tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j))
      (edgeDimerCurve m F base reverse (5 * j + 1)) := by
  change tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + (0 : Fin 2).val))
    (edgeDimerCurve m F base reverse (5 * j + (1 : Fin 2).val))
  rw [edgeDimerCurve_H, edgeDimerCurve_H]
  rcases dimerHIndex_adjacent base reverse j with h | h
  · rw [← h]
    exact octEdgeZigzag_adj m F _
  · rw [← h]
    exact (octEdgeZigzag_adj m F _).symm

theorem edgeDimerCurve_HP (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool) (j : ℕ) :
    tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + 1))
      (edgeDimerCurve m F base reverse (5 * j + 2)) := by
  change tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + (1 : Fin 2).val))
    (edgeDimerCurve m F base reverse (5 * j + 2 + (0 : Fin 3).val))
  rw [edgeDimerCurve_H, edgeDimerCurve_P, dimerHIndex_last]
  exact edgePPPFold_first_seam m F _

theorem edgeDimerCurve_PP (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool)
    (j : ℕ) (s t : Fin 3) (hst : s.val + 1 = t.val) :
    tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + 2 + s.val))
      (edgeDimerCurve m F base reverse (5 * j + 2 + t.val)) := by
  rw [edgeDimerCurve_P, edgeDimerCurve_P]
  exact (edgePPPFold m F _).consecutive s t hst

theorem edgeDimerCurve_PH (m : ℕ) (F : OctEdgeFrame) (base : ℕ) (reverse : Bool) (j : ℕ) :
    tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + 4))
      (edgeDimerCurve m F base reverse (5 * (j + 1))) := by
  change tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * j + 2 + (2 : Fin 3).val))
    (edgeDimerCurve m F base reverse (5 * (j + 1) + (0 : Fin 2).val))
  rw [edgeDimerCurve_P, edgeDimerCurve_H, dimerLinkIndex_next]
  exact edgePPPFold_last_seam m F _

theorem edgeDimerCurve_consecutive (m : ℕ) (F : OctEdgeFrame) (base : ℕ)
    (reverse : Bool) (i : ℕ) :
    tetrahedralLattice.Adj (edgeDimerCurve m F base reverse i)
      (edgeDimerCurve m F base reverse (i + 1)) := by
  have hm := Nat.mod_lt i (by decide : 0 < 5)
  have hd := Nat.mod_add_div i 5
  generalize hdiv : i / 5 = j at *
  rcases (show i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 by omega) with
    h | h | h | h | h
  · have hi : i = 5 * j := by omega
    simpa only [hi] using edgeDimerCurve_HH m F base reverse j
  · have hi : i = 5 * j + 1 := by omega
    simpa only [hi] using edgeDimerCurve_HP m F base reverse j
  · have hi : i = 5 * j + 2 := by omega
    simpa only [hi] using edgeDimerCurve_PP m F base reverse j 0 1 rfl
  · have hi : i = 5 * j + 3 := by omega
    simpa only [hi] using edgeDimerCurve_PP m F base reverse j 1 2 rfl
  · have hi : i = 5 * j + 4 := by omega
    have hin : i + 1 = 5 * (j + 1) := by omega
    rw [hin, hi]
    exact edgeDimerCurve_PH m F base reverse _

end ProteinFolding.Tetrahedral.NearField

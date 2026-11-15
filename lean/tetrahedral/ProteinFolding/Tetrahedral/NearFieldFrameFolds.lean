import ProteinFolding.Tetrahedral.NearFieldFrameEndpoints
import ProteinFolding.Tetrahedral.NearFieldFrameSeparation

/-! The literal frame P-lists as actual finite folds, with both H seams. -/

namespace ProteinFolding.Tetrahedral.NearField

def framePFold (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) :
    Fold tetrahedralLattice (nearFrameLength kind - 2) where
  pos i := nearFramePoint m q kind hq ⟨i.val + 1, by have h := i.isLt; omega⟩
  injective_pos := by
    intro i j heq
    have h := nearFramePoint_injective m q kind hq heq
    have hv := congrArg Fin.val h
    change i.val + 1 = j.val + 1 at hv
    exact Fin.ext (by omega)
  consecutive i j hij := by
    have h := nearFramePoint_adj m q kind hq ⟨i.val + 1, by have hi := i.isLt; omega⟩
    have hidx : (⟨i.val + 1 + 1, by have hi := i.isLt; omega⟩ : Fin (nearFrameLength kind)) =
        ⟨j.val + 1, by have hj := j.isLt; omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx] at h
    exact h

theorem framePFold_mem_skin_one (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (i : Fin (nearFrameLength kind - 2)) : (framePFold m q kind hq).pos i ∈ skin m 1 := by
  exact nearFramePoint_mem_skin_one m q kind hq hqlo hqhi _
    (by change 0 < i.val + 1; omega) (by change i.val + 1 + 1 < _; have h := i.isLt; omega)

theorem framePFold_outside (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind - 2)) : (framePFold m q kind hq).pos i ∉ octahedron m := by
  exact nearFramePoint_outside m q kind hq _
    (by change 0 < i.val + 1; omega) (by change i.val + 1 + 1 < _; have h := i.isLt; omega)

theorem framePFold_first_seam (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (i : Fin (nearFrameLength kind - 2)) (hi : i.val = 0) :
    tetrahedralLattice.Adj
      (octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameStartIndex m q kind))
      ((framePFold m q kind hq).pos i) := by
  have h := nearFramePoint_adj m q kind hq ⟨0, by have h := nearFrameLength_ge_five kind; omega⟩
  rw [nearFrame_start_eq m q kind hq hqlo hqhi] at h
  have he : (⟨0 + 1, by have h := nearFrameLength_ge_five kind; omega⟩ : Fin (nearFrameLength kind)) =
      ⟨i.val + 1, by have h := i.isLt; omega⟩ := Fin.ext (by dsimp; omega)
  rw [he] at h
  exact h

theorem framePFold_last_seam (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (i : Fin (nearFrameLength kind - 2)) (hi : i.val + 1 = nearFrameLength kind - 2) :
    tetrahedralLattice.Adj ((framePFold m q kind hq).pos i)
      (octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameEndIndex m q kind)) := by
  have hn := nearFrameLength_ge_five kind
  have h := nearFramePoint_adj m q kind hq ⟨i.val + 1, by omega⟩
  have he : (⟨i.val + 1 + 1, by omega⟩ : Fin (nearFrameLength kind)) =
      ⟨nearFrameLength kind - 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [he, nearFrame_end_eq m q kind hq hqlo hqhi] at h
  exact h

theorem framePFolds_disjoint (m q q' : ℕ) (kind kind' : Fin 6)
    (hq : q % 2 = 1) (hq' : q' % 2 = 1) (hqlo : 5 ≤ q) (hqlo' : 5 ≤ q')
    (hqhi : (q : ℤ) + 10 ≤ octRadius m) (hqhi' : (q' : ℤ) + 10 ≤ octRadius m)
    (hsep : NearFrameRoutesSeparated kind q kind' q')
    (i : Fin (nearFrameLength kind - 2)) (j : Fin (nearFrameLength kind' - 2)) :
    (framePFold m q kind hq).pos i ≠ (framePFold m q' kind' hq').pos j := by
  apply nearFramePoints_ne_of_routes_separated m q q' kind kind' hq hq' hqlo hqlo' hqhi hqhi' hsep
  all_goals first | (change 0 < _ + 1; omega) | (change _ + 1 + 1 < _; have hi := i.isLt; have hj := j.isLt; omega)

end ProteinFolding.Tetrahedral.NearField

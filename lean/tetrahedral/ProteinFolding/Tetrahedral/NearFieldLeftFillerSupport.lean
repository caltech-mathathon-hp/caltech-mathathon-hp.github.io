import ProteinFolding.Tetrahedral.NearFieldRepointSupport
import ProteinFolding.Tetrahedral.NearFieldUnitSupport

/-! Exact H sites of the special left filler: replace track[0] by entry[2]. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem intervalDimerFold_pos {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (i : Fin (dimerChain n).length) :
    (intervalDimerFold hm F base n hn reverse hroom).pos i = edgeDimerCurve m F base reverse i.val := rfl

def leftFillerHsites (p : ConstructionParameters) : Finset Site :=
  insert (octEdgeZigzag p.side entryEdgeFrame 2)
    ((edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1)).erase
      (octEdgeZigzag p.side trackEdgeFrame 0))

theorem leftFillerFold_hSupport (p : ConstructionParameters) :
    hSupport (dimerChain p.leftFiller) (leftFillerFold p) = leftFillerHsites p := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hl : 0 < p.leftFiller := by have h := p.leftFiller_ge; omega
  have hr : 0 + 2 * p.leftFiller ≤ 2 * p.side - 1 := by
    have h := leftFiller_room p
    omega
  let g := intervalDimerFold hm trackEdgeFrame 0 p.leftFiller hl false hr
  let i₀ : Fin (dimerChain p.leftFiller).length := ⟨0, by rw [leftFiller_word_length]; omega⟩
  have hH : (dimerChain p.leftFiller).get i₀ = .H := by
    rw [dimerChain_get_mod5_positive p.leftFiller hl i₀]
    rfl
  have hfirst : (leftFillerFold p).pos i₀ = octEdgeZigzag p.side entryEdgeFrame 2 :=
    leftFillerFold_first p i₀ rfl
  have hgfirst : g.pos i₀ = octEdgeZigzag p.side trackEdgeFrame 0 := by
    rw [intervalDimerFold_pos]
    change edgeDimerCurve p.side trackEdgeFrame 0 false (5 * 0 + (0 : Fin 2).val) = _
    rw [edgeDimerCurve_H]
    rfl
  have hother : ∀ i, i ≠ i₀ → (leftFillerFold p).pos i = g.pos i := by
    intro i hi
    have hn : i.val ≠ 0 := by
      intro he
      exact hi (Fin.ext he)
    rw [leftFillerFold_pos, leftFillerCurve, if_neg hn, intervalDimerFold_pos]
  rw [hSupport_repoint (leftFillerFold p) g i₀ _ hH hfirst hother,
    hgfirst, intervalDimerFold_hSupport]
  rfl

theorem cappedLeftFillerFold_hSupport_exact (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    hSupport (capWord (dimerChain p.leftFiller)) (cappedLeftFillerFold p C D hC hD) = leftFillerHsites p := by
  rw [cappedLeftFillerFold_hSupport, leftFillerFold_hSupport]

end ProteinFolding.Tetrahedral.NearField

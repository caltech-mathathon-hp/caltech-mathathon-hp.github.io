import ProteinFolding.Tetrahedral.NearFieldFramePaths

/-! The single possible dangling-neighbour direction along each long frame link. -/

namespace ProteinFolding.Tetrahedral

def nearFrameStepCoordinates (m q : ℕ) (kind : Fin 6) (r : ℕ) (d : Fin 4) (k : Fin 3) : ℤ :=
  nearFrameCoordinates m q kind r k +
    (if nearFrameIsA kind r then bondComponent d k else -bondComponent d k)

def nearFrameSinglePort (kind : Fin 6) (r : ℕ) : Fin 4 :=
  if kind = 0 then if r % 2 = 1 then 2 else 3
  else if kind = 1 then if r % 2 = 1 then 3 else 2
  else if r % 2 = 1 then 0 else 3

theorem nearFramePoint_step_coordinates (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength kind)) (d : Fin 4) :
    (step (nearFramePoint m q kind hq r) d).val = nearFrameStepCoordinates m q kind r.val d := by
  by_cases hr : nearFrameIsA kind r.val
  · rw [step_val_of_A _ (nearFramePoint_inA m q kind hq r hr)]
    funext k
    change nearFrameCoordinates m q kind r.val k + bondVector d k = _
    rw [bondVector_eq_bondComponent]
    simp only [nearFrameStepCoordinates, if_pos hr]
  · rw [step_val_of_B _ (nearFramePoint_inB m q kind hq r hr)]
    funext k
    change nearFrameCoordinates m q kind r.val k - bondVector d k = _
    rw [bondVector_eq_bondComponent]
    simp only [nearFrameStepCoordinates, if_neg hr, sub_eq_add_neg]

end ProteinFolding.Tetrahedral

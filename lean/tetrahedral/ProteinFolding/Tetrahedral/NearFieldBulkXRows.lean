import ProteinFolding.Tetrahedral.NearFieldPPPEdgeColumns
import ProteinFolding.Tetrahedral.BulkEdgeCoordinates

/-! The finite family of X-plane second rows. Both edge orientations are
retained, so subsequent reference certificates require no orientation
symmetry of the asymmetric frozen vertex patches. -/

namespace ProteinFolding.Tetrahedral.NearField

def xRowOtherA (k : Fin 4) : Fin 4 := if k = 0 ∨ k = 1 then 2 else 0
def xRowOtherB (k : Fin 4) : Fin 4 := if k = 0 ∨ k = 1 then 3 else 1

def xRowFrame (k : Fin 4) (reverse : Bool) : OctEdgeFrame where
  k := k
  j := columnOpposite k
  a := if reverse then xRowOtherB k else xRowOtherA k
  b := if reverse then xRowOtherA k else xRowOtherB k
  kj := by revert k reverse; decide
  ka := by revert k reverse; decide
  kb := by revert k reverse; decide
  ja := by revert k reverse; decide
  jb := by revert k reverse; decide
  ab := by revert k reverse; decide

theorem xRowFrame_opposite (k : Fin 4) (reverse : Bool) :
    columnOpposite (xRowFrame k reverse).k = (xRowFrame k reverse).j := rfl

def xRowSite (m : ℕ) (hm : 1 ≤ m) (k : Fin 4) (reverse small : Bool) (t : ℕ) : Site :=
  let F := xRowFrame k reverse
  let p := bulkClosedEdgeAnchor m F t hm
  if small then step (step (step p F.a) F.k) F.a else step (step p F.j) F.b

theorem xRowSite_eq_owner (m : ℕ) (hm : 1 ≤ m) (k : Fin 4) (reverse small : Bool) (t : ℕ) :
    xRowSite m hm k reverse small t =
      if small then edgeBSecondRowOwner m (xRowFrame k reverse) (2 * t + 1)
      else edgeASecondRowOwner m (xRowFrame k reverse) (2 * t) := by
  simp only [xRowSite, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
  cases small
  · rfl
  · simp only [ite_true, edgeBSecondRowOwner]
    have hA := (octEdgeZigzag_even hm (xRowFrame k reverse) t).1
    change step (step (step (octEdgeZigzag m (xRowFrame k reverse) (2 * t)) _ ) _) _ = _
    rw [show octEdgeZigzag m (xRowFrame k reverse) (2 * t + 1) =
      step (octEdgeZigzag m (xRowFrame k reverse) (2 * t)) (xRowFrame k reverse).a by
        change edgeForwardStep _ _ _ = _
        unfold octEdgeZigzag at hA
        rw [edgeForwardStep, if_pos hA]
        rfl]

theorem xRowSite_coordinates (m : ℕ) (hm : 1 ≤ m) (k : Fin 4) (reverse small : Bool)
    (t : ℕ) (c : Fin 3) :
    (xRowSite m hm k reverse small t).val c =
      (bulkClosedEdgeAnchor m (xRowFrame k reverse) t hm).val c +
        if small then 2 * bondComponent (xRowFrame k reverse).a c - bondComponent (xRowFrame k reverse).k c
        else bondComponent (xRowFrame k reverse).j c - bondComponent (xRowFrame k reverse).b c := by
  have hA : InASublattice (bulkClosedEdgeAnchor m (xRowFrame k reverse) t hm).val := by
    rw [bulkClosedEdgeAnchor_eq]
    exact bulkEdgeAnchor_inA _ _ _
  cases small
  · change (step (step (bulkClosedEdgeAnchor m (xRowFrame k reverse) t hm) _) _).val c = _
    rw [step_val_of_B _ (step_in_B hA _), step_val_of_A _ hA]
    simp only [bondVector_eq_bondComponent, Bool.false_eq_true, ite_false]
    omega
  · change (step (step (step (bulkClosedEdgeAnchor m (xRowFrame k reverse) t hm) _) _) _).val c = _
    rw [step_val_of_A _ (step_in_A (step_in_B hA _) _),
      step_val_of_B _ (step_in_B hA _), step_val_of_A _ hA]
    simp only [bondVector_eq_bondComponent, ite_true]
    omega

end ProteinFolding.Tetrahedral.NearField

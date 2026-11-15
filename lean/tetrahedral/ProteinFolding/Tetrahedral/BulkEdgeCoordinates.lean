import ProteinFolding.Tetrahedral.BulkEdgeSigns

/-! Closed coordinate evaluation of edge anchors, equivalent to the zigzag recursion. -/

namespace ProteinFolding.Tetrahedral

def bulkEdgeFaceValue (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (i : Fin 4) : ℤ :=
  if i = F.k then octRadius m else if i = F.j then -octRadius m
  else if i = F.a then -octRadius m + 4 * (t : ℤ) else octRadius m - 4 * (t : ℤ)

theorem bulkEdgeAnchor_faceValue {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) (i : Fin 4) :
    tetraCoordinate m (bulkEdgeAnchor m F t).val i = bulkEdgeFaceValue m F t i := by
  have h := bulkEdgeAnchor_faces hm F t
  rcases F.index_cases i with rfl | rfl | rfl | rfl
  · simpa only [bulkEdgeFaceValue, if_true] using h.1
  · simpa only [bulkEdgeFaceValue, if_neg (Ne.symm F.kj), if_true] using h.2.1
  · simpa only [bulkEdgeFaceValue, if_neg (Ne.symm F.ka), if_neg (Ne.symm F.ja), if_true] using h.2.2.1
  · simpa only [bulkEdgeFaceValue, if_neg (Ne.symm F.kb), if_neg (Ne.symm F.jb), if_neg (Ne.symm F.ab)] using h.2.2.2

def bulkEdgeClosedCoordinates (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then (bulkEdgeFaceValue m F t 0 + bulkEdgeFaceValue m F t 1) / 2
  else if k = 1 then octRadius m + (bulkEdgeFaceValue m F t 0 + bulkEdgeFaceValue m F t 2) / 2
  else (bulkEdgeFaceValue m F t 0 + bulkEdgeFaceValue m F t 3) / 2

theorem bulkEdgeAnchor_closedCoordinates {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) :
    (bulkEdgeAnchor m F t).val = bulkEdgeClosedCoordinates m F t := by
  have hx := tetraCoordinate_pair_x m (bulkEdgeAnchor m F t).val
  have hy := tetraCoordinate_pair_y m (bulkEdgeAnchor m F t).val
  have hz := tetraCoordinate_pair_z m (bulkEdgeAnchor m F t).val
  simp_rw [bulkEdgeAnchor_faceValue hm F t] at hx hy hz
  funext k
  fin_cases k <;> dsimp [bulkEdgeClosedCoordinates] <;> omega

def bulkClosedEdgeAnchor (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (hm : 1 ≤ m) : Site :=
  ⟨bulkEdgeClosedCoordinates m F t, by
    rw [← bulkEdgeAnchor_closedCoordinates hm F t]
    exact (bulkEdgeAnchor m F t).property⟩

theorem bulkClosedEdgeAnchor_eq {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) :
    bulkClosedEdgeAnchor m F t hm = bulkEdgeAnchor m F t :=
  Subtype.ext (bulkEdgeAnchor_closedCoordinates hm F t).symm

end ProteinFolding.Tetrahedral

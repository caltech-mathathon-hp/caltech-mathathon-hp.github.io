import ProteinFolding.Tetrahedral.NearFieldBulkXRows
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! Uniform transfer of every X-plane second-row site. No symmetry of the
frozen graph is assumed; only the already proved bounded-box translations. -/

namespace ProteinFolding.Tetrahedral.NearField

def xRowStartIndex (k : Fin 4) (reverse : Bool) : Fin 6 := bulkEdgeStartIndex (xRowFrame k reverse)
def xRowEndIndex (k : Fin 4) (reverse : Bool) : Fin 6 :=
  bulkEdgeStartIndex (bulkReverseEdgeFrame (xRowFrame k reverse))

theorem xRowSite_in_edge_box (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ) :
    InBulkEdgeBox m (xRowFrame k reverse) t 3 (xRowSite m hm k reverse small t) := by
  intro c
  rw [xRowSite_coordinates, bulkClosedEdgeAnchor_eq]
  have hoff : |if small then
      2 * bondComponent (xRowFrame k reverse).a c - bondComponent (xRowFrame k reverse).k c
      else bondComponent (xRowFrame k reverse).j c - bondComponent (xRowFrame k reverse).b c| ≤ (3 : ℤ) := by
    revert k reverse small c
    decide
  convert hoff using 1 <;> congr 1 <;> omega

theorem xRowSite_edge_reanchor (m M : ℕ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (k : Fin 4) (reverse small : Bool) (t T : ℕ) :
    bulkEdgeReanchor m M t T (xRowFrame k reverse) (xRowSite m hm k reverse small t) =
      xRowSite M hM k reverse small T := by
  apply Subtype.ext
  funext c
  rw [bulkEdgeReanchor_coordinates, xRowSite_coordinates, xRowSite_coordinates,
    bulkClosedEdgeAnchor_eq, bulkClosedEdgeAnchor_eq]
  omega

theorem xRowSite_in_left_box (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ) (ht : t ≤ 10) :
    InBulkVertexBox m (xRowStartIndex k reverse) 23 (xRowSite m hm k reverse small t) := by
  have hb := bulkEdgeZigzag_in_start_box m (xRowFrame k reverse) (2 * t)
  simp only [xRowSite, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
  cases small
  · exact bulkVertexBox_mono _ _ (by omega)
      (bulk_adjacent_in_vertex_box _ _ _
        (bulk_adjacent_in_vertex_box _ _ _ hb (step_adj _ _)) (step_adj _ _))
  · exact bulkVertexBox_mono _ _ (by omega)
      (bulk_adjacent_in_vertex_box _ _ _
        (bulk_adjacent_in_vertex_box _ _ _
          (bulk_adjacent_in_vertex_box _ _ _ hb (step_adj _ _)) (step_adj _ _)) (step_adj _ _))

theorem xRowSite_left_reanchor (m M : ℕ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (k : Fin 4) (reverse small : Bool) (t : ℕ) :
    bulkReanchorSite m M (xRowStartIndex k reverse) (xRowSite m hm k reverse small t) =
      xRowSite M hM k reverse small t := by
  simp only [xRowSite, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
  cases small <;> simp only [Bool.false_eq_true, ite_false, ite_true, bulkReanchorSite_step]
  all_goals rw [show xRowStartIndex k reverse = bulkEdgeStartIndex (xRowFrame k reverse) from rfl,
    bulkVertexReanchor_edgeZigzag]

theorem xRowAnchor_right_reanchor (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse : Bool) (t : ℕ) (htm : t + 1 ≤ m) (hr : m - 1 - t ≤ 10) :
    bulkReanchorSite m 50 (xRowEndIndex k reverse)
      (bulkClosedEdgeAnchor m (xRowFrame k reverse) t hm) =
      bulkClosedEdgeAnchor 50 (xRowFrame k reverse) (49 - (m - 1 - t)) (by decide) := by
  simp only [bulkClosedEdgeAnchor_eq]
  rw [bulkEdgeAnchor_reverse hm (xRowFrame k reverse) t (by omega)]
  change bulkReanchorSite m 50 (bulkEdgeStartIndex (bulkReverseEdgeFrame (xRowFrame k reverse)))
    (octEdgeZigzag m (bulkReverseEdgeFrame (xRowFrame k reverse)) (2 * (m - 1 - t))) = _
  rw [bulkVertexReanchor_edgeZigzag]
  have h := bulkEdgeAnchor_reverse (by decide : 1 ≤ 50)
    (bulkReverseEdgeFrame (xRowFrame k reverse)) (m - 1 - t) (by omega)
  simpa only [bulkReverseEdgeFrame] using h

theorem xRowSite_right_reanchor (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ) (htm : t + 1 ≤ m) (hr : m - 1 - t ≤ 10) :
    bulkReanchorSite m 50 (xRowEndIndex k reverse) (xRowSite m hm k reverse small t) =
      xRowSite 50 (by decide) k reverse small (49 - (m - 1 - t)) := by
  unfold xRowSite
  cases small <;> simp only [Bool.false_eq_true, ite_false, ite_true, bulkReanchorSite_step]
  all_goals rw [xRowAnchor_right_reanchor m hm k reverse t htm hr]

theorem xRowSite_in_right_box (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ) (htm : t + 1 ≤ m) (hr : m - 1 - t ≤ 10) :
    InBulkVertexBox m (xRowEndIndex k reverse) 23 (xRowSite m hm k reverse small t) := by
  have hb := bulkEdgeZigzag_in_start_box m (bulkReverseEdgeFrame (xRowFrame k reverse)) (2 * (m - 1 - t))
  have heq := bulkEdgeAnchor_reverse hm (xRowFrame k reverse) t (by omega)
  change bulkEdgeAnchor m (xRowFrame k reverse) t =
    octEdgeZigzag m (bulkReverseEdgeFrame (xRowFrame k reverse)) (2 * (m - 1 - t)) at heq
  rw [← heq] at hb
  simp only [xRowSite, bulkClosedEdgeAnchor_eq]
  cases small
  · exact bulkVertexBox_mono _ _ (by omega)
      (bulk_adjacent_in_vertex_box _ _ _
        (bulk_adjacent_in_vertex_box _ _ _ hb (step_adj _ _)) (step_adj _ _))
  · exact bulkVertexBox_mono _ _ (by omega)
      (bulk_adjacent_in_vertex_box _ _ _
        (bulk_adjacent_in_vertex_box _ _ _
          (bulk_adjacent_in_vertex_box _ _ _ hb (step_adj _ _)) (step_adj _ _)) (step_adj _ _))

end ProteinFolding.Tetrahedral.NearField

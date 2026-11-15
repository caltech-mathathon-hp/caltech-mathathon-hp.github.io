import ProteinFolding.Tetrahedral.NearFieldPPPEdgeColumns
import ProteinFolding.Tetrahedral.NearFieldPPPTrackStart

/-! Track PPPs can meet only columns of their own endpoint H-sites. -/

namespace ProteinFolding.Tetrahedral

theorem trackPPPFold_column_owner {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (n : ℕ) (s : Fin 3)
    (heq : C.point n = (edgePPPFold m trackEdgeFrame r).pos s) :
    C.owner = octEdgeZigzag m trackEdgeFrame r ∨ C.owner = octEdgeZigzag m trackEdgeFrame (r + 2) := by
  rcases edgePPPFold_column_owner hm trackEdgeFrame r hr C n s heq with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact ((by decide : columnOpposite trackEdgeFrame.k ≠ trackEdgeFrame.j) h.1).elim
  · exact ((by decide : columnOpposite trackEdgeFrame.j ≠ trackEdgeFrame.k) h.1).elim

theorem DanglingColumn.owner_ne_edgePoint_of_bulk {m : ℕ} (C : DanglingColumn m)
    (hbulk : C.owner ∈ bulkInterior m) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) : C.owner ≠ octEdgeZigzag m F r := by
  intro heq
  have hE := octEdgeZigzag_mem hm F hr
  have hdel : bulkOnDeletedEdge m C.owner := by rw [heq]; exact ⟨F.k, F.j, F.kj, hE⟩
  exact (Finset.mem_sdiff.mp hbulk).2 (Finset.mem_filter.mpr ⟨C.owner_mem, hdel⟩)

theorem trackPPPFold_ne_bulkColumn {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (hbulk : C.owner ∈ bulkInterior m)
    (n : ℕ) (s : Fin 3) : (edgePPPFold m trackEdgeFrame r).pos s ≠ C.point n := by
  intro heq
  rcases trackPPPFold_column_owner hm r hr C n s heq.symm with h | h
  · exact C.owner_ne_edgePoint_of_bulk hbulk hm trackEdgeFrame r (by omega) h
  · exact C.owner_ne_edgePoint_of_bulk hbulk hm trackEdgeFrame (r + 2) hr h

theorem trackPPPFold_ne_column_of_endpoint_owner_ne {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hp : C.owner ≠ octEdgeZigzag m trackEdgeFrame r)
    (hq : C.owner ≠ octEdgeZigzag m trackEdgeFrame (r + 2)) (n : ℕ) (s : Fin 3) :
    (edgePPPFold m trackEdgeFrame r).pos s ≠ C.point n := by
  intro heq
  rcases trackPPPFold_column_owner hm r hr C n s heq.symm with h | h
  · exact hp h
  · exact hq h

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns
import ProteinFolding.Tetrahedral.NearFieldPPPBorrowedFrameColumns
import ProteinFolding.Tetrahedral.NearFieldTetherOwners

/-! All four selected tether-column families have the required PPP clearance. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem positive_faceColumn_owner_bulk (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (faceDanglingColumn m a b c hs).owner ∈ bulkInterior m := by
  let C := faceDanglingColumn m a b c hs
  have hB : InBSublattice C.owner.val := faceSurfaceCoordinates_inB m 0 a b c hs
  have hstrict : ∀ d, tetraCoordinate m C.owner.val d < 2 * (m : ℤ) - 3 := by
    intro d
    change tetraCoordinate m (faceSurfaceSite m 0 a b c hs).val d < _
    rw [tetraCoordinate_faceSurface]
    fin_cases d <;> dsimp <;> omega
  refine Finset.mem_sdiff.mpr ⟨C.owner_mem, ?_⟩
  intro hdel
  obtain ⟨k, _, _, hk, _⟩ := (bulkOnDeletedEdge_B_iff m hB C.owner_mem).mp (Finset.mem_filter.mp hdel).2
  exact (ne_of_lt (hstrict k)) hk

def entryBorrowColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) : DanglingColumn p.side :=
  faceDanglingColumn p.side (entryAnchorA p k - 1) (3 * (k + 1)) 1
    (by have h := entryAnchor_equation p k hk; have ha := entryAnchor_positive p k hk; omega)

theorem entryBorrowColumn_owner_bulk (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (entryBorrowColumn p k hk).owner ∈ bulkInterior p.side := by
  apply positive_faceColumn_owner_bulk
  · have h := p.entry_column_triangle_room k hk
    dsimp [entryAnchorA]
    omega
  · omega
  · omega

theorem edgePPPFold_ne_entryBorrowColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hpair : F.k ≠ 2 ∨ F.j ≠ 3) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠ (entryBorrowColumn p k hk).point n := by
  apply edgePPPFold_ne_B_column_of_pair_ne p.side (by have h := p.side_ge; omega) F r hr
    (entryBorrowColumn p k hk) (entryBorrowColumn_owner_bulk p k hk)
    (faceSurfaceCoordinates_inB p.side 0 (entryAnchorA p k - 1) (3 * (k + 1)) 1
      (by have h := entryAnchor_equation p k hk; have ha := entryAnchor_positive p k hk; omega)) 3 rfl _ s n
  rcases hpair with h | h
  · right
    simpa only [show columnOpposite (3 : Fin 4) = 2 from rfl] using h
  · exact Or.inl h

theorem edgePPPFold_ne_entryUp (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hpair : F.k ≠ 2 ∨ F.j ≠ 3) (s : Fin 3) (i : Fin (2 * p.entrySkin k - 1)) :
    (edgePPPFold p.side F r).pos s ≠ (entryUp p k hk).pos i := by
  cases hn : i.val with
  | zero =>
    change (edgePPPFold p.side F r).pos s ≠ borrowedPoint p.side (entryAnchorA p k)
      (3 * (k + 1)) 0 (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val
    rw [hn]
    apply edgePPPFold_ne_cap_on_inner_entry p.side (by have h := p.side_ge; omega)
      (6 * (k + 1) + 1) (by omega) _ F r hr hpair _ (entrySource_owner p k hk) s
    have h := p.entry_column_triangle_room k hk
    dsimp [octRadius]
    omega
  | succ n =>
    change (edgePPPFold p.side F r).pos s ≠ borrowedPoint p.side (entryAnchorA p k)
      (3 * (k + 1)) 0 (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val
    rw [hn]
    exact edgePPPFold_ne_entryBorrowColumn p k hk F r hr hpair s (n + 1)

theorem edgePPPFold_ne_entryTargetColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hp : (entryTargetColumn p k hk).owner ≠ octEdgeZigzag p.side F r)
    (hq : (entryTargetColumn p k hk).owner ≠ octEdgeZigzag p.side F (r + 2)) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠ (entryTargetColumn p k hk).point n := by
  have hj : 132 ≤ p.separatorIndex k := by have h := p.leftFiller_ge; unfold ConstructionParameters.separatorIndex; omega
  have hroom := p.separator_room k hk
  have hfill := p.rightFiller_ge
  exact edgePPPFold_ne_inner_edge_column p.side (by have h := p.side_ge; omega)
    F trackEdgeFrame r (2 * p.separatorIndex k + 1) hr (by omega) (by omega)
    _ (entryTarget_owner p k hk) hp hq s n

theorem edgePPPFold_ne_exitSourceColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hp : (exitSourceColumn p k hk).owner ≠ octEdgeZigzag p.side F r)
    (hq : (exitSourceColumn p k hk).owner ≠ octEdgeZigzag p.side F (r + 2)) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠ (exitSourceColumn p k hk).point n := by
  have hj : 132 ≤ p.separatorIndex k := by have h := p.leftFiller_ge; unfold ConstructionParameters.separatorIndex; omega
  have hroom := p.separator_room k hk
  have hfill := p.rightFiller_ge
  exact edgePPPFold_ne_inner_edge_column p.side (by have h := p.side_ge; omega)
    F trackEdgeFrame r (2 * p.separatorIndex k + 3) hr (by omega) (by omega)
    _ (exitSource_owner p k hk) hp hq s n

theorem edgePPPFold_ne_exitTargetColumn (p : ConstructionParameters) (k : ℕ)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hp : (exitTargetColumn p k).owner ≠ octEdgeZigzag p.side F r)
    (hq : (exitTargetColumn p k).owner ≠ octEdgeZigzag p.side F (r + 2)) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠ (exitTargetColumn p k).point n := by
  have hroom := p.exit_column_triangle_room k
  exact edgePPPFold_ne_inner_edge_column p.side (by have h := p.side_ge; omega)
    F exitEdgeFrame r (10 * p.exitSlot k + 7) hr (by omega) (by omega)
    _ (exitTarget_owner p k) hp hq s n

end ProteinFolding.Tetrahedral.NearField

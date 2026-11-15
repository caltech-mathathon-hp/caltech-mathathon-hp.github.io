import ProteinFolding.Tetrahedral.NearFieldBorrowedOwnersInterior
import ProteinFolding.Tetrahedral.NearFieldPPPColumnPairs
import ProteinFolding.Tetrahedral.NearFieldPPPPairwiseEdges
import ProteinFolding.Tetrahedral.FrameForcingSlotGeometry

/-! The selected borrowed frame-cap columns avoid every non-frame PPP:
those PPPs lie off the entry edge, while these borrowed owners and their
original caps can meet only the entry-edge normal pair. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem innerEntryPoint_ne_other_edge (m : ℕ) (hm : 3 ≤ m) (i : ℕ)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m)
    (F : OctEdgeFrame) (r : ℕ) (hr : r < 2 * m - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3) :
    octEdgeZigzag m entryEdgeFrame i ≠ octEdgeZigzag m F r := by
  intro heq
  have hm1 : 1 ≤ m := by omega
  have he := octEdgeZigzag_mem hm1 F hr
  rw [← heq] at he
  have hfaces := inner_edge_unique_faces m hm entryEdgeFrame i hilo
    (by dsimp [octRadius] at hihi; omega) he
  rcases hpair with hk | hj
  · exact hk hfaces.1
  · exact hj hfaces.2

theorem edgePPPFold_ne_cap_on_inner_entry (m : ℕ) (hm : 3 ≤ m) (i : ℕ)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * m - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (C : DanglingColumn m) (howner : C.owner = octEdgeZigzag m entryEdgeFrame i) (s : Fin 3) :
    (edgePPPFold m F r).pos s ≠ C.seed := by
  have hm1 : 1 ≤ m := by omega
  have hqp : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm1 F hr with h | h
    · exact h.1.1
    · exact h.1.1
  apply facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne F _)
    (edgePPP_back_ne_normal F _) (edgePPP_normal_face hm1 F r (by omega)) hqp C _ _ s
  · rw [howner]
    exact innerEntryPoint_ne_other_edge m hm i hilo hihi F r (by omega) hpair
  · rw [edgePPP_endpoint, howner]
    exact innerEntryPoint_ne_other_edge m hm i hilo hihi F (r + 2) hr hpair

theorem edgePPPFold_ne_frameBorrowPoint (m : ℕ) (hm : 3 ≤ m) (i : ℕ)
    (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ i) (hfar : mode = false ∨ (i : ℤ) + 4 ≤ octRadius m)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * m - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (s : Fin 3) (n : ℕ) :
    (edgePPPFold m F r).pos s ≠ frameBorrowPoint (by omega : 1 ≤ m) i hi hilo hihi mode n := by
  have hm1 : 1 ≤ m := by omega
  cases n with
  | zero =>
    have hOct : octEdgeZigzag m entryEdgeFrame i ∈ octahedron m := by
      have he := octEdgeZigzag_mem hm1 entryEdgeFrame (by dsimp [octRadius] at hihi; omega : i < 2 * m - 1)
      exact he.elim (fun h => h.1.1) (fun h => h.1.1)
    let C : DanglingColumn m := ⟨octEdgeZigzag m entryEdgeFrame i, 2, hOct,
      (frameLinkerCap_dangling hm1 i hi hilo hihi).1⟩
    exact edgePPPFold_ne_cap_on_inner_entry m hm i hilo hihi F r hr hpair C rfl s
  | succ n =>
    exact edgePPPFold_ne_A_column_of_pair_ne m hm1 F r hr
      (frameBorrowColumn hm1 i hi hilo hihi mode)
      (frameBorrowColumn_owner_in_bulk hm1 i hi hilo hihi mode hnear hfar)
      (frameBorrowOwner_inA hm1 i hi mode) 2 rfl hpair s (n + 1)

end ProteinFolding.Tetrahedral.NearField

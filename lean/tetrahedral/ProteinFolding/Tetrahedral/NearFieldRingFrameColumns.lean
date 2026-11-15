import ProteinFolding.Tetrahedral.NearFieldRingWordPiece
import ProteinFolding.Tetrahedral.NearFieldRingFaceGeometry
import ProteinFolding.Tetrahedral.NearFieldFrameFolds

/-! Ring columns avoid every Appendix C frame P-link. The reserved face
coordinate separates the frame from the first two sites of each ring column;
skin one excludes all later column sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem nearFramePoint_reserved_small_coordinate (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength kind)) :
    tetraCoordinate m (nearFramePoint m q kind hq r).val 3 ≤ -octRadius m := by
  have hb := (nearFrameOffset_bounds kind r 3).2
  have heq := tetraCoordinate_add_linear m (nearFrameReference m q kind)
    (nearFrameOffset kind r.val) 3
  change tetraCoordinate m (nearFramePoint m q kind hq r).val 3 = _ at heq
  rw [heq]
  fin_cases kind
  all_goals dsimp [nearFrameReference, nearFrameOffsetHigh, tetraCoordinate, octRadius] at hb ⊢
  all_goals omega

theorem ringTerminal_reserved_coordinate (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (hj : F.j ≠ 3) (j : Fin 3) (e : Fin 2) :
    -octRadius m < tetraCoordinate m (ringTerminalSite m F j e).val 3 := by
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (ringTerminalSite_mem m hm F j e)
  have hb := r.isLt
  rw [← hr]
  exact ringEdgePoint_other_small_coordinate m hm (ringSideFrame F j) (1 + r.val)
    (by omega) (by omega) 3 (by rw [ringSideFrame_small]; exact hj.symm)

theorem Bcolumn_first_two_reserved_coordinate (m : ℕ) (C : DanglingColumn m)
    (hB : InBSublattice C.owner.val) (hp : -octRadius m < tetraCoordinate m C.owner.val 3)
    (n : ℕ) (hn : n = 0 ∨ n = 1) : -octRadius m < tetraCoordinate m (C.point n).val 3 := by
  have hd : C.dir ≠ 3 := by
    intro hd
    have hface := (step_not_mem_octahedron_B m hB C.owner_mem C.dir).mp C.seed_outside
    rw [hd] at hface
    dsimp [octRadius] at hp
    omega
  have hs := tetraCoordinate_step_B m hB C.dir 3
  simp only [if_neg hd.symm] at hs
  rcases hn with rfl | rfl
  · change -octRadius m < tetraCoordinate m (step C.owner C.dir).val 3
    omega
  · rw [C.point_one_eq]
    have ht := tetraCoordinate_step_A m (step_in_A hB C.dir) (columnOpposite C.dir) 3
    split_ifs at ht <;> omega

theorem Bcolumn_ne_framePFold_of_reserved_coordinate (m q : ℕ) (C : DanglingColumn m)
    (hB : InBSublattice C.owner.val) (hp : -octRadius m < tetraCoordinate m C.owner.val 3)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (n : ℕ) (r : Fin (nearFrameLength kind - 2)) : C.point n ≠ (framePFold m q kind hq).pos r := by
  intro heq
  have hskin := framePFold_mem_skin_one m q kind hq hqlo hqhi r
  rw [← heq] at hskin
  have hn : n = 0 ∨ n = 1 := by
    have h := (C.point_mem_skin_iff_two_indices n 1 (by decide)).mp hskin
    omega
  have hlower := Bcolumn_first_two_reserved_coordinate m C hB hp n hn
  have hupper := nearFramePoint_reserved_small_coordinate m q kind hq
    (⟨r.val + 1, by have h := r.isLt; omega⟩ : Fin (nearFrameLength kind))
  change tetraCoordinate m ((framePFold m q kind hq).pos r).val 3 ≤ -octRadius m at hupper
  rw [heq] at hlower
  omega

theorem ringTerminalColumn_ne_framePFold (m q : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (hj : F.j ≠ 3) (j : Fin 3) (e : Fin 2) (C : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F j e)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (n : ℕ) (r : Fin (nearFrameLength kind - 2)) : C.point n ≠ (framePFold m q kind hq).pos r :=
  Bcolumn_ne_framePFold_of_reserved_coordinate m q C
    (by rw [hC]; exact ringTerminalSite_inB m hm F j e)
    (by rw [hC]; exact ringTerminal_reserved_coordinate m hm F hj j e)
    kind hq hqlo hqhi n r

end ProteinFolding.Tetrahedral.NearField

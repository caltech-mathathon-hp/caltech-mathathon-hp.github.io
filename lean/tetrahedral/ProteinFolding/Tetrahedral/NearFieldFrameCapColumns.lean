import ProteinFolding.Tetrahedral.NearFieldFrameCapSeparation
import ProteinFolding.Tetrahedral.NearFieldFrameVertexCaps
import ProteinFolding.Tetrahedral.FaceRowsColumnOwners

/-! Pairwise separation of the complete borrowed frame-cap columns. -/

namespace ProteinFolding.Tetrahedral

theorem DanglingColumn.seed_ne_of_owner_colours {m : ℕ} (C D : DanglingColumn m)
    (hC : InASublattice C.owner.val) (hD : InBSublattice D.owner.val) : C.seed ≠ D.seed := by
  intro heq
  have hCB : InBSublattice C.seed.val := step_in_B hC C.dir
  have hDA : InASublattice D.seed.val := step_in_A hD D.dir
  rw [heq] at hCB
  exact sublattices_disjoint D.seed.val hDA hCB

theorem DanglingColumn.points_ne_of_owner_colours {m : ℕ} (C D : DanglingColumn m)
    (hC : InASublattice C.owner.val) (hD : InBSublattice D.owner.val) (n r : ℕ) :
    C.point n ≠ D.point r :=
  DanglingColumn.points_ne_of_seed_ne (DanglingColumn.seed_ne_of_owner_colours C D hC hD) n r

theorem frameBorrowColumns_seed_ne {m : ℕ} (hm : 1 ≤ m) (i i' : ℕ)
    (hi : i % 2 = 0) (hi' : i' % 2 = 0) (hilo : 2 ≤ i) (hilo' : 2 ≤ i')
    (hihi : (i : ℤ) + 2 ≤ octRadius m) (hihi' : (i' : ℤ) + 2 ≤ octRadius m)
    (mode mode' : Bool) (hsep : i + 4 ≤ i' ∨ i' + 4 ≤ i) :
    (frameBorrowColumn hm i hi hilo hihi mode).seed ≠
      (frameBorrowColumn hm i' hi' hilo' hihi' mode').seed := by
  intro heq
  have howner := congrArg (fun p => step p 2) heq
  change step (step (frameBorrowOwner hm i hi mode) 2) 2 =
    step (step (frameBorrowOwner hm i' hi' mode') 2) 2 at howner
  rw [step_step, step_step] at howner
  have hy := congrArg (fun p : Site => p.val 1) howner
  change (octEdgeZigzag m entryEdgeFrame i).val 1 + frameBorrowOffset mode 1 =
    (octEdgeZigzag m entryEdgeFrame i').val 1 + frameBorrowOffset mode' 1 at hy
  rw [entryEdgeZigzag_coordinates hm, entryEdgeZigzag_coordinates hm] at hy
  cases mode <;> cases mode' <;> dsimp [entryEdgeCoordinates, frameBorrowOffset] at hy <;> omega

namespace NearField

theorem frameBorrowPoints_ne {m : ℕ} (hm : 1 ≤ m) (i i' : ℕ)
    (hi : i % 2 = 0) (hi' : i' % 2 = 0) (hilo : 2 ≤ i) (hilo' : 2 ≤ i')
    (hihi : (i : ℤ) + 2 ≤ octRadius m) (hihi' : (i' : ℤ) + 2 ≤ octRadius m)
    (mode mode' : Bool) (hsep : i + 4 ≤ i' ∨ i' + 4 ≤ i) (n r : ℕ) :
    frameBorrowPoint hm i hi hilo hihi mode n ≠ frameBorrowPoint hm i' hi' hilo' hihi' mode' r := by
  intro heq
  cases n with
  | zero =>
    cases r with
    | zero =>
      have h := congrArg (fun p => step p 2) heq
      change step (step (octEdgeZigzag m entryEdgeFrame i) 2) 2 =
        step (step (octEdgeZigzag m entryEdgeFrame i') 2) 2 at h
      rw [step_step, step_step] at h
      have hiEq := octEdgeZigzag_injective hm entryEdgeFrame h
      omega
    | succ r =>
      change frameLinkerCap m i = (frameBorrowColumn hm i' hi' hilo' hihi' mode').point (r + 1) at heq
      have hdang : IsDangling m ((frameBorrowColumn hm i' hi' hilo' hihi' mode').point (r + 1)) := by
        rw [← heq]
        exact frameLinkerCap_dangling hm i hi hilo hihi
      have hzero := ((frameBorrowColumn hm i' hi' hilo' hihi' mode').point_dangling_iff_zero (r + 1)).mp hdang
      omega
  | succ n =>
    cases r with
    | zero =>
      change (frameBorrowColumn hm i hi hilo hihi mode).point (n + 1) = frameLinkerCap m i' at heq
      have hdang : IsDangling m ((frameBorrowColumn hm i hi hilo hihi mode).point (n + 1)) := by
        rw [heq]
        exact frameLinkerCap_dangling hm i' hi' hilo' hihi'
      have hzero := ((frameBorrowColumn hm i hi hilo hihi mode).point_dangling_iff_zero (n + 1)).mp hdang
      omega
    | succ r =>
      exact DanglingColumn.points_ne_of_seed_ne
        (frameBorrowColumns_seed_ne hm i i' hi hi' hilo hilo' hihi hihi' mode mode' hsep)
        (n + 1) (r + 1) heq

theorem frameBorrowPoint_ne_faceColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (a b c : ℕ) (hs : a + b + c + 2 = m) (n r : ℕ) :
    frameBorrowPoint hm i hi hilo hihi mode n ≠ (faceDanglingColumn m a b c hs).point r := by
  cases n with
  | zero =>
    intro heq
    have hdang : IsDangling m ((faceDanglingColumn m a b c hs).point r) := by
      rw [← heq]
      exact frameLinkerCap_dangling hm i hi hilo hihi
    have hr := ((faceDanglingColumn m a b c hs).point_dangling_iff_zero r).mp hdang
    subst r
    have hcapB : InBSublattice (frameLinkerCap m i).val := step_in_B (frameEntryAnchor_inA hm i hi) 2
    have hseedA : InASublattice (faceDanglingColumn m a b c hs).seed.val :=
      step_in_A (faceSurfaceCoordinates_inB m 0 a b c hs) 3
    change frameLinkerCap m i = (faceDanglingColumn m a b c hs).seed at heq
    rw [heq] at hcapB
    exact sublattices_disjoint _ hseedA hcapB
  | succ n =>
    exact DanglingColumn.points_ne_of_owner_colours _ _
      (frameBorrowOwner_inA hm i hi mode) (faceSurfaceCoordinates_inB m 0 a b c hs) (n + 1) r

end NearField
end ProteinFolding.Tetrahedral

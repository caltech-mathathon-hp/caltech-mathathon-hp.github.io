import ProteinFolding.Tetrahedral.NearFieldFrameFaceCaps

/-! Frame-link separation from the F' columns and the borrowed entry cap. -/

namespace ProteinFolding.Tetrahedral

theorem faceColumn_ne_frameP (m a b c : ℕ) (hs : a + b + c + 2 = m) (hc : 1 ≤ c)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6)
    (hexit : kind = 4 → faceSurfaceSite m 0 a b c hs ≠ octEdgeZigzag m exitEdgeFrame q)
    (n : ℕ) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (faceDanglingColumn m a b c hs).point n ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hm : 1 ≤ m := by omega
  obtain ⟨_, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 0
  obtain ⟨hzl, _⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 2
  rw [← heq, faceDanglingColumn_point_coordinates] at hxu hzl
  fin_cases kind <;>
    dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh] at hxu hzl
  · omega
  · omega
  · omega
  · omega
  · have hn : n = 0 := by omega
    have ha : a = 0 := by omega
    have hz := congrArg (fun p : Site => p.val 2) heq
    change ((faceDanglingColumn m a b c hs).point n).val 2 =
      nearFrameReference m q 4 2 + nearFrameOffset 4 r.val 2 at hz
    rw [faceDanglingColumn_point_coordinates] at hz
    dsimp [nearFrameReference] at hz
    have hoff : nearFrameOffset 4 r.val 2 = -1 := by omega
    have hr : r = ⟨10, by decide⟩ := Fin.ext (nearFrame_sixSlot_only_minZ r hr0 hrlast hoff)
    have hbad := hexit rfl
    change (faceDanglingColumn m a b c hs).point n = nearFramePoint m q 4 hq r at heq
    rw [hn, hr, nearFrame_sixSlot_faceCap hm q hq] at heq
    change step (faceSurfaceSite m 0 a b c hs) 3 = step (octEdgeZigzag m exitEdgeFrame q) 3 at heq
    exact hbad (by simpa only [step_step] using congrArg (fun p => step p 3) heq)
  · omega

theorem interiorFaceColumn_ne_frameP (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6)
    (n : ℕ) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (faceDanglingColumn m a b c hs).point n ≠ nearFramePoint m q kind hq r := by
  apply faceColumn_ne_frameP m a b c hs hc q hq kind _ n r hr0 hrlast
  intro _ heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  change (faceSurfaceSite m 0 a b c hs).val 2 = (octEdgeZigzag m exitEdgeFrame q).val 2 at hz
  rw [exitEdgeZigzag_coordinates (by omega)] at hz
  dsimp [faceSurfaceSite, faceSurfaceCoordinates, exitEdgeCoordinates] at hz
  omega

theorem faceEntryCap_ne_frameP (m a b c : ℕ) (hs : a + b + c + 2 = m) (ha : 1 ≤ a)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6)
    (hstart : kind = 0 → faceSurfaceSite m 0 a b c hs ≠ octEdgeZigzag m entryEdgeFrame 3)
    (hentry : kind = 1 → faceSurfaceSite m 0 a b c hs ≠ octEdgeZigzag m entryEdgeFrame q)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (faceDanglingColumn m a b c hs).seed ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hm : 1 ≤ m := by omega
  have heq' : (faceDanglingColumn m a b c hs).point 0 = nearFramePoint m q kind hq r := heq
  obtain ⟨_, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 0
  obtain ⟨hzl, _⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 2
  rw [← heq', faceDanglingColumn_point_coordinates] at hxu hzl
  fin_cases kind <;>
    dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh] at hxu hzl
  · have hc : c = 0 := by omega
    have hx := congrArg (fun p : Site => p.val 0) heq'
    change ((faceDanglingColumn m a b c hs).point 0).val 0 =
      nearFrameReference m q 0 0 + nearFrameOffset 0 r.val 0 at hx
    rw [faceDanglingColumn_point_coordinates] at hx
    dsimp [nearFrameReference] at hx
    have hoff : nearFrameOffset 0 r.val 0 = 2 := by omega
    have hr : r = ⟨6, by decide⟩ := Fin.ext (nearFrame_initial_only_maxX r hr0 hrlast hoff)
    have hbad := hstart rfl
    change (faceDanglingColumn m a b c hs).seed = nearFramePoint m q 0 hq r at heq
    rw [hr, nearFrame_initial_faceCap hm q hq] at heq
    change step (faceSurfaceSite m 0 a b c hs) 3 = step (octEdgeZigzag m entryEdgeFrame 3) 3 at heq
    exact hbad (by simpa only [step_step] using congrArg (fun p => step p 3) heq)
  · have hc : c = 0 := by omega
    have hx := congrArg (fun p : Site => p.val 0) heq'
    change ((faceDanglingColumn m a b c hs).point 0).val 0 =
      nearFrameReference m q 1 0 + nearFrameOffset 1 r.val 0 at hx
    rw [faceDanglingColumn_point_coordinates] at hx
    dsimp [nearFrameReference] at hx
    have hoff : nearFrameOffset 1 r.val 0 = 1 := by omega
    have hr : r = ⟨1, by decide⟩ := Fin.ext (nearFrame_twoSlot_only_maxX r hr0 hrlast hoff)
    have hbad := hentry rfl
    change (faceDanglingColumn m a b c hs).seed = nearFramePoint m q 1 hq r at heq
    rw [hr, nearFrame_twoSlot_faceCap hm q hq] at heq
    change step (faceSurfaceSite m 0 a b c hs) 3 = step (octEdgeZigzag m entryEdgeFrame q) 3 at heq
    exact hbad (by simpa only [step_step] using congrArg (fun p => step p 3) heq)
  · omega
  · omega
  · omega
  · omega

end ProteinFolding.Tetrahedral

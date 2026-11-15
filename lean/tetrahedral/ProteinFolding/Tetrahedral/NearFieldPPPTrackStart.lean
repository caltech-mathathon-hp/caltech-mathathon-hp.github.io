import ProteinFolding.Tetrahedral.NearFieldPPPTrack

/-! The first track PPP, next to Va, also avoids the initial frame link. -/

namespace ProteinFolding.Tetrahedral

def firstTrackPPPOffset (s : Fin 3) (k : Fin 3) : ℤ :=
  if k = 0 then 2 + s.val else if k = 1 then 2 + (s.val % 2 : ℕ) else s.val

private theorem firstTrack_offset_ne_initial (s : Fin 3) (t : Fin (nearFrameLength 0)) :
    firstTrackPPPOffset s ≠ nearFrameOffset 0 t.val := by
  revert s t
  decide

theorem firstTrackPPPFold_ne_frameP {m : ℕ} (hm : 1 ≤ m) (hR : 5 ≤ octRadius m)
    (q : ℕ) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (kind : Fin 6) (s : Fin 3)
    (t : Fin (nearFrameLength kind)) (ht0 : 0 < t.val) (htlast : t.val + 1 < nearFrameLength kind) :
    (edgePPPFold m trackEdgeFrame 1).pos s ≠ nearFramePoint m q kind hq t := by
  intro heq
  obtain ⟨_, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq t ht0 htlast 0
  obtain ⟨hyl, _⟩ := nearFramePoint_coordinate_bounds m q kind hq t ht0 htlast 1
  obtain ⟨hzl, _⟩ := nearFramePoint_coordinate_bounds m q kind hq t ht0 htlast 2
  rw [← heq, trackPPPFold_coordinates hm] at hxu hyl hzl
  have hs := s.isLt
  fin_cases kind <;> dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh,
    trackPPPCoordinates] at hxu hyl hzl
  · apply firstTrack_offset_ne_initial s t
    funext k
    have hk := congrArg (fun p : Site => p.val k) heq
    change ((edgePPPFold m trackEdgeFrame 1).pos s).val k =
      nearFrameReference m q 0 k + nearFrameOffset 0 t.val k at hk
    rw [trackPPPFold_coordinates hm] at hk
    fin_cases k <;> dsimp [trackPPPCoordinates, firstTrackPPPOffset, nearFrameReference] at hk ⊢ <;> omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem trackPPPFold_ne_frameP_from_first {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (hrlo : 1 ≤ r) (hrhi : (r : ℤ) + 4 ≤ octRadius m)
    (q : ℕ) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (kind : Fin 6) (s : Fin 3)
    (t : Fin (nearFrameLength kind)) (ht0 : 0 < t.val) (htlast : t.val + 1 < nearFrameLength kind) :
    (edgePPPFold m trackEdgeFrame r).pos s ≠ nearFramePoint m q kind hq t := by
  by_cases hr : 2 ≤ r
  · exact trackPPPFold_ne_frameP hm r hr hrhi q hq kind s t ht0 htlast
  · have he : r = 1 := by omega
    subst r
    exact firstTrackPPPFold_ne_frameP hm (by omega) q hq hqlo kind s t ht0 htlast

end ProteinFolding.Tetrahedral

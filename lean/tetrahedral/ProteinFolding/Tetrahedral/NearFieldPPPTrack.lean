import ProteinFolding.Tetrahedral.NearFieldPPPEdges
import ProteinFolding.Tetrahedral.NearFieldFrameSeparation

/-! Literal coordinates of the track PPPs; their separation from the frame is uniform. -/

namespace ProteinFolding.Tetrahedral

def trackPPPCoordinates (m r : ℕ) (s : Fin 3) (k : Fin 3) : ℤ :=
  if k = 0 then (r : ℤ) + s.val + 1
  else if k = 1 then octRadius m + (if r % 2 = 0 then (-1 : ℤ) - (s.val % 2 : ℕ) else (2 : ℤ) + (s.val % 2 : ℕ))
  else -octRadius m + r + s.val - 1

theorem trackPPPFold_coordinates {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (s : Fin 3) :
    ((edgePPPFold m trackEdgeFrame r).pos s).val = trackPPPCoordinates m r s := by
  by_cases hr : r % 2 = 0
  · have hpA : InASublattice (octEdgeZigzag m trackEdgeFrame r).val := by
      have he : r = 2 * (r / 2) := by omega
      rw [he]
      exact (octEdgeZigzag_even hm trackEdgeFrame (r / 2)).1
    change (facePPPSite (octEdgeZigzag m trackEdgeFrame r)
      (edgePPPNormal trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r))
      (edgePPPBack trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r))
      (edgePPPForward trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r)) s).val = _
    simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_pos hpA]
    fin_cases s
    all_goals dsimp [facePPPSite]
    · change (step (octEdgeZigzag m trackEdgeFrame r) 1).val = trackPPPCoordinates m r 0
      rw [step_val_of_A _ hpA, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega
    · change (step (step (octEdgeZigzag m trackEdgeFrame r) 1) 2).val = trackPPPCoordinates m r 1
      rw [step_val_of_B _ (step_in_B hpA 1), step_val_of_A _ hpA, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega
    · change (step (step (step (octEdgeZigzag m trackEdgeFrame r) 1) 2) 0).val = trackPPPCoordinates m r 2
      rw [step_val_of_A _ (step_in_A (step_in_B hpA 1) 2),
        step_val_of_B _ (step_in_B hpA 1), step_val_of_A _ hpA, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega
  · have hpB : InBSublattice (octEdgeZigzag m trackEdgeFrame r).val := by
      have he : r = 2 * (r / 2) + 1 := by omega
      rw [he]
      exact (octEdgeZigzag_odd hm trackEdgeFrame (r / 2)).1
    have hpnot := (inB_iff_not_inA _).mp hpB
    change (facePPPSite (octEdgeZigzag m trackEdgeFrame r)
      (edgePPPNormal trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r))
      (edgePPPBack trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r))
      (edgePPPForward trackEdgeFrame (octEdgeZigzag m trackEdgeFrame r)) s).val = _
    simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_neg hpnot]
    fin_cases s
    all_goals dsimp [facePPPSite]
    · change (step (octEdgeZigzag m trackEdgeFrame r) 3).val = trackPPPCoordinates m r 0
      rw [step_val_of_B _ hpB, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega
    · change (step (step (octEdgeZigzag m trackEdgeFrame r) 3) 0).val = trackPPPCoordinates m r 1
      rw [step_val_of_A _ (step_in_A hpB 3), step_val_of_B _ hpB, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega
    · change (step (step (step (octEdgeZigzag m trackEdgeFrame r) 3) 0) 2).val = trackPPPCoordinates m r 2
      rw [step_val_of_B _ (step_in_B (step_in_A hpB 3) 0),
        step_val_of_A _ (step_in_A hpB 3), step_val_of_B _ hpB, trackEdgeZigzag_coordinates hm]
      funext k
      simp_rw [bondVector_eq_bondComponent]
      fin_cases k <;> dsimp [trackPPPCoordinates, trackEdgeCoordinates, bondComponent] <;> omega

theorem trackPPPFold_ne_frameP {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (hrlo : 2 ≤ r) (hrhi : (r : ℤ) + 4 ≤ octRadius m)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6) (s : Fin 3)
    (t : Fin (nearFrameLength kind)) (ht0 : 0 < t.val) (htlast : t.val + 1 < nearFrameLength kind) :
    (edgePPPFold m trackEdgeFrame r).pos s ≠ nearFramePoint m q kind hq t := by
  intro heq
  obtain ⟨_, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq t ht0 htlast 0
  obtain ⟨hzl, _⟩ := nearFramePoint_coordinate_bounds m q kind hq t ht0 htlast 2
  rw [← heq, trackPPPFold_coordinates hm] at hxu hzl
  have hs := s.isLt
  fin_cases kind <;> dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh,
    trackPPPCoordinates] at hxu hzl
  all_goals omega

end ProteinFolding.Tetrahedral

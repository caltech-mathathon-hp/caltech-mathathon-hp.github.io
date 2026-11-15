import ProteinFolding.Tetrahedral.NearFieldLeftFillerFrameOwners
import ProteinFolding.Tetrahedral.NearFieldFrameHRunHoles

/-! The special left filler occupies no retained H site of the actual frame. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem frameHRunSite_not_leftFillerHsites (p : ConstructionParameters) (i : FrameHRunIndex p)
    (r : ℕ) (hr : r < (frameHRunData p i).count) :
    octEdgeZigzag p.side (frameHRunData p i).frame ((frameHRunData p i).base + r) ∉ leftFillerHsites p := by
  have hroom := frameHRun_room p i
  have hidx : (frameHRunData p i).base + r < 2 * p.side - 1 := by omega
  rw [frameHRun_frame]
  cases hb : frameHRunOnExit i
  · simp only [hb, Bool.false_eq_true, if_false]
    exact entryPoint_not_leftFillerHsites p _ hidx
      (frameHRun_entry_initial_gap p i r hr hb 1 (by omega) (by omega))
      (frameHRun_entry_initial_gap p i r hr hb 2 (by omega) (by omega))
  · simp only [hb, ite_true]
    exact exitPoint_not_leftFillerHsites p _ hidx

theorem frameHRunFold_disjoint_left_hSupport (p : ConstructionParameters) (i : FrameHRunIndex p) :
    Disjoint (foldSites (frameHRunFold p i)) (hSupport (dimerChain p.leftFiller) (leftFillerFold p)) := by
  rw [frameHRunFold_sites, leftFillerFold_hSupport]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hx
  rw [← heq] at hy
  exact frameHRunSite_not_leftFillerHsites p i r (Finset.mem_range.mp hr) hy

end ProteinFolding.Tetrahedral.NearField

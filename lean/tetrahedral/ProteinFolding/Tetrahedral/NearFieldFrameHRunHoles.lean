import ProteinFolding.Tetrahedral.NearFieldFrameHRunSeparation
import ProteinFolding.Tetrahedral.TetherRouteParameters

/-! Arithmetic metadata for the H sites removed from the literal frame.
No geometric edge walk occurs in the finite case analysis. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem frameHRun_entry_separator_gap (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) (r : ℕ) (hr : r < (frameHRunData p i).count)
    (hentry : frameHRunOnExit i = false) (t : ℕ) (ht : t < 2) :
    (frameHRunData p i).base + r ≠ 6 * (k + 1) + t := by
  have hside := p.side_ge
  have hfamily := p.family_side_bound
  rcases i with c | ⟨b, u⟩
  · fin_cases c <;> dsimp [frameHRunData, frameHRunOnExit] at hr hentry ⊢
    all_goals first | contradiction | omega
  · have hu := u.isLt
    cases b <;> dsimp [frameHRunData, frameHRunOnExit] at hr hentry ⊢
    · split_ifs at hr <;> omega
    · contradiction

theorem frameHRun_exit_separator_gap (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) (r : ℕ) (hr : r < (frameHRunData p i).count)
    (hexit : frameHRunOnExit i = true) (t : ℕ) (ht : t < 6) :
    (frameHRunData p i).base + r ≠ 10 * p.exitSlot k + 6 + t := by
  have hslot := p.exitSlot_add k hk
  rcases i with c | ⟨b, u⟩
  · fin_cases c <;> dsimp [frameHRunData, frameHRunOnExit] at hr hexit ⊢
    all_goals first | contradiction | omega
  · have hu := u.isLt
    cases b <;> dsimp [frameHRunData, frameHRunOnExit] at hr hexit ⊢
    · contradiction
    · omega

theorem frameHRun_entry_initial_gap (p : ConstructionParameters) (i : FrameHRunIndex p)
    (r : ℕ) (hr : r < (frameHRunData p i).count) (hentry : frameHRunOnExit i = false)
    (t : ℕ) (ht0 : 1 ≤ t) (ht2 : t ≤ 2) : (frameHRunData p i).base + r ≠ t := by
  have hside := p.side_ge
  rcases i with c | ⟨b, u⟩
  · fin_cases c <;> dsimp [frameHRunData, frameHRunOnExit] at hr hentry ⊢
    all_goals first | contradiction | omega
  · cases b <;> dsimp [frameHRunData, frameHRunOnExit] at hr hentry ⊢
    · omega
    · contradiction

end ProteinFolding.Tetrahedral.NearField

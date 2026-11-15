import ProteinFolding.Tetrahedral.FrameForcingTrackPath
import ProteinFolding.Tetrahedral.FrameForcingMatchingPairs

/-! The unique alternating path matching is the actual HH pairing on the
complete track, including its first pair across the start B-corner. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

variable {ι : Type*} [Fintype ι]

theorem track_even_pair (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hW : frameTrackSites m F ⊆ P.covered)
    (hclosed : ∀ i, P.point (i, false) ∈ frameTrackSites m F ↔ P.point (i, true) ∈ frameTrackSites m F)
    (hadj : ∀ i, tetrahedralLattice.Adj (P.point (i, false)) (P.point (i, true)))
    (k : ℕ) (hk : 2 * k < 2 * m - 2) :
    ∃ i b, frameTrackPoint m F (2 * k) = P.point (i, b) ∧
      frameTrackPoint m F (2 * k + 1) = P.point (i, !b) := by
  let e := frameTrackEquiv m hm F
  have hpath : ∀ i j, tetrahedralLattice.Adj (e i).val (e j).val →
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    intro i j hbond
    exact frameTrackPoint_adj_indices m hm F i.val j.val hbond
  let M := P.pathMatching (frameTrackSites m F) hW hclosed hadj (2 * m - 2) e hpath
  have hmate := M.mate_even k hk
  obtain ⟨i, b, hfirst, hsecond⟩ := P.pathMatching_mate_pair _ hW hclosed hadj _ e hpath ⟨2 * k, hk⟩
  change frameTrackPoint m F (2 * k) = P.point (i, b) at hfirst
  change frameTrackPoint m F (M.mate ⟨2 * k, hk⟩).val = P.point (i, !b) at hsecond
  rw [hmate] at hsecond
  exact ⟨i, b, hfirst, hsecond⟩

end ProteinFolding.Tetrahedral.FinitePairFamily

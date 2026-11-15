import ProteinFolding.Tetrahedral.FrameForcingTrackPairIndex

/-! Finite-set bookkeeping for two oriented physical HH pairs. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

theorem OnTrackPair.two_pairs_sites {ι : Type*} (P : FinitePairFamily ι Site)
    (m : ℕ) (F : OctEdgeFrame) {i j : ι} {k l : ℕ}
    (hi : P.OnTrackPair m F i k) (hj : P.OnTrackPair m F j l) :
    ({P.point (i, false), P.point (i, true), P.point (j, false), P.point (j, true)} : Finset Site) =
      {frameTrackPoint m F (2 * k), frameTrackPoint m F (2 * k + 1),
        frameTrackPoint m F (2 * l), frameTrackPoint m F (2 * l + 1)} := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  all_goals rw [hi.1, hi.2, hj.1, hj.2]
  all_goals ext x
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton]
  all_goals tauto

end ProteinFolding.Tetrahedral.FinitePairFamily

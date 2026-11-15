import ProteinFolding.Tetrahedral.FrameForcingHeightBounds
import ProteinFolding.Tetrahedral.SeparatorArithmetic
import ProteinFolding.Tetrahedral.FrameForcingTrackPath
import ProteinFolding.Tetrahedral.FrameForcingCapped

/-! The sharp separator window uses the entry H height and exit K height.
The radius is exactly 3 + sigma/2, preserving the scale-eight margin. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem frameTrackPoint_K2 (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (hr : r ≠ 0) :
    frameK2 m F (frameTrackPoint m F r) = -2 * octRadius m + 2 * (r : ℤ) := by
  rw [frameTrackPoint, if_neg hr]
  exact (track_edge_height_data m hm F r).2

namespace ConstructionParameters

theorem separator_tether_height_bounds (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : OctWordPath p.side (capWord (p.separatorWord k))) (F G : OctEdgeFrame)
    (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (r s : ℕ)
    (hentry : P.site 2 = octEdgeZigzag p.side F r)
    (hexit : P.site (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side G s) :
    frameH2 p.side F (P.site (p.entryTether k + 3)) ≤
        4 * (p.separatorIndex k : ℤ) + 10 + 2 * (p.entrySlack k : ℤ) ∧
      -2 * octRadius p.side + 4 * (p.separatorIndex k : ℤ) - 6 - 2 * (p.exitSlack k : ℤ) ≤
        frameK2 p.side F (P.site (p.entryTether k + 9)) := by
  have hm := p.side_ge
  have hlen : (capWord (p.separatorWord k)).length = p.entryTether k + p.exitTether k + 23 := by
    simp [capWord, separatorWord, dimerChain, repeatWord]
    omega
  have heH := path_height_bounds P (frameH2 p.side F) (frameH2_adj_bounds p.side F)
    2 (p.entryTether k + 1) (by rw [hlen]; omega)
  have hxK := path_height_bounds P (frameK2 p.side F) (frameK2_adj_bounds p.side F)
    (p.entryTether k + 9) (p.exitTether k + 1) (by rw [hlen]; omega)
  rw [show 2 + (p.entryTether k + 1) = p.entryTether k + 3 by omega] at heH
  rw [show p.entryTether k + 9 + (p.exitTether k + 1) =
    p.entryTether k + p.exitTether k + 10 by omega] at hxK
  have hentryData := entry_edge_height_data p.side (by omega) F r
  have hexitData := intended_exit_height_data p.side (by omega) F G hGk hGj hGa s
  rw [← hentry] at hentryData
  rw [← hexit] at hexitData
  have hroom := p.separatorIndex_add_two_le k hk
  dsimp only [entryTether, exitTether, octRadius] at heH hxK hentryData hexitData ⊢
  push_cast at heH hxK
  constructor <;> omega

theorem separator_window_from_heights (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (i : ℕ) (a d : Site)
    (hmin : 4 * (i : ℤ) ≤ frameH2 p.side F a)
    (hmax : frameK2 p.side F d ≤ -2 * octRadius p.side + 4 * (i : ℤ) + 6)
    (hentry : frameH2 p.side F a ≤
      4 * (p.separatorIndex k : ℤ) + 10 + 2 * (p.entrySlack k : ℤ))
    (hexit : -2 * octRadius p.side + 4 * (p.separatorIndex k : ℤ) - 6 -
      2 * (p.exitSlack k : ℤ) ≤ frameK2 p.side F d) :
    |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ) := by
  have hslack := p.tether_slack_bounds k hk
  have hradius := p.separatorRadius_twice
  apply abs_le.mpr
  constructor <;> omega

end ConstructionParameters

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FrameForcingLocalDimer
import ProteinFolding.Tetrahedral.FrameForcingHeightBounds
import ProteinFolding.Tetrahedral.FrameForcingTrackRegion
import ProteinFolding.Tetrahedral.FrameForcingChainTwoGeometry

/-! The actual tether lengths put every central separator H strictly
between the two frame edges.  O7 then forces all four onto the track. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem separator_numeric_strict (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (r s : ℕ) (hr : r ≤ 6 * p.bins + 7) (_hs : s ≤ 2 * p.side - 2)
    (hdef : 2 * p.side - 2 - s ≤ 10 * p.bins + 11)
    (H K aK dH : ℤ) (hH : -8 ≤ H - dH) (hK : K - aK ≤ 8)
    (hentry : aK - (-2 * octRadius p.side + 2 * (r : ℤ)) ≤
      2 * ((p.entryTether k + 1 : ℕ) : ℤ))
    (hexit : 2 * (s : ℤ) - dH ≤ 2 * ((p.exitTether k + 1 : ℕ) : ℤ)) :
    6 ≤ H ∧ K ≤ -6 := by
  have hm := p.side_ge
  have hslack := p.tether_slack_bounds k hk
  have hroom := p.separator_room k hk
  have hscale := p.binDimers_ge_scale
  have hscaleEq := p.scale_eq
  have hleft : 2 * p.scale ≤ p.leftFiller := by unfold leftFiller; omega
  have hJleft : p.leftFiller ≤ p.separatorIndex k := by unfold separatorIndex; omega
  have hright : p.rightFiller = p.leftFiller + 1 := rfl
  have hJroom := p.separatorIndex_add_two_le k hk
  dsimp only [entryTether, exitTether, octRadius] at hentry hexit
  push_cast at hentry hexit
  constructor <;> omega

def separatorCentreSites (p : ConstructionParameters) (k : ℕ)
    (P : OctWordPath p.side (capWord (p.separatorWord k))) : Finset Site :=
  {P.site (p.entryTether k + 3), P.site (p.entryTether k + 4),
    P.site (p.entryTether k + 8), P.site (p.entryTether k + 9)}

theorem separator_centre_strict_heights (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : OctWordPath p.side (capWord (p.separatorWord k))) (F G : OctEdgeFrame)
    (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (r s : ℕ) (hr : r ≤ 6 * p.bins + 7) (hs : s ≤ 2 * p.side - 2)
    (hdef : 2 * p.side - 2 - s ≤ 10 * p.bins + 11)
    (hentry : P.site 2 = octEdgeZigzag p.side F r)
    (hexit : P.site (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side G s) :
    ∀ x ∈ p.separatorCentreSites k P,
      bulkOnDeletedEdge p.side x ∧ 6 ≤ frameH2 p.side F x ∧ frameK2 p.side F x ≤ -6 := by
  have hm := p.side_ge
  obtain ⟨pre, post, hfactor, hpre⟩ := p.separator_centre_factor k hk
  let Q := P.factor pre (capWord (dimerChain 2)) post hfactor
  have hqa : Q.site 1 = P.site (p.entryTether k + 3) := by
    change P.site (pre.length + 1) = _
    rw [hpre]
  have hqb : Q.site 2 = P.site (p.entryTether k + 4) := by
    change P.site (pre.length + 2) = _
    rw [hpre]
  have hqc : Q.site 6 = P.site (p.entryTether k + 8) := by
    change P.site (pre.length + 6) = _
    rw [hpre]
  have hqd : Q.site 7 = P.site (p.entryTether k + 9) := by
    change P.site (pre.length + 7) = _
    rw [hpre]
  have hset : p.separatorCentreSites k P = {Q.site 1, Q.site 2, Q.site 6, Q.site 7} := by
    simp only [separatorCentreSites, hqa, hqb, hqc, hqd]
  have hquartH := (Q.chain2_height_bounds F).1
  have hquartK := (Q.chain2_height_bounds F).2
  have hlen : (capWord (p.separatorWord k)).length = p.entryTether k + p.exitTether k + 23 := by
    simp [capWord, separatorWord, dimerChain, repeatWord]
    omega
  have heK := path_height_bounds P (frameK2 p.side F) (frameK2_adj_bounds p.side F)
    2 (p.entryTether k + 1) (by rw [hlen]; omega)
  have hxH := path_height_bounds P (frameH2 p.side F) (frameH2_adj_bounds p.side F)
    (p.entryTether k + 9) (p.exitTether k + 1) (by rw [hlen]; omega)
  have hei : 2 + (p.entryTether k + 1) = p.entryTether k + 3 := by omega
  have hxi : p.entryTether k + 9 + (p.exitTether k + 1) =
      p.entryTether k + p.exitTether k + 10 := by omega
  rw [hei, ← hqa] at heK
  rw [hxi, ← hqd] at hxH
  have hentryData := entry_edge_height_data p.side (by omega) F r
  have hexitData := intended_exit_height_data p.side (by omega) F G hGk hGj hGa s
  rw [← hentry] at hentryData
  rw [← hexit] at hexitData
  have heBound : frameK2 p.side F (Q.site 1) - (-2 * octRadius p.side + 2 * (r : ℤ)) ≤
      2 * ((p.entryTether k + 1 : ℕ) : ℤ) := by
    rw [← hentryData.2.2]
    exact heK.2
  have hxBound : 2 * (s : ℤ) - frameH2 p.side F (Q.site 7) ≤
      2 * ((p.exitTether k + 1 : ℕ) : ℤ) := by
    rw [← hexitData.1]
    exact hxH.2
  intro x hx
  rw [hset] at hx
  have hH := hquartH x hx
  have hK := hquartK x hx
  have hdeleted := Q.chain2_deleted x hx
  exact ⟨hdeleted, p.separator_numeric_strict k hk r s hr hs hdef _ _ _ _
    hH.2.2.1 hK.2.1 heBound hxBound⟩

theorem separator_centre_on_track (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : OctWordPath p.side (capWord (p.separatorWord k))) (F G : OctEdgeFrame)
    (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (r s : ℕ) (hr : r ≤ 6 * p.bins + 7) (hs : s ≤ 2 * p.side - 2)
    (hdef : 2 * p.side - 2 - s ≤ 10 * p.bins + 11)
    (hentry : P.site 2 = octEdgeZigzag p.side F r)
    (hexit : P.site (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side G s) :
    ∀ x ∈ p.separatorCentreSites k P, ∃ t, 3 ≤ t ∧ t ≤ 2 * p.side - 5 ∧
      x = octEdgeZigzag p.side F.smallOtherSide t := by
  intro x hx
  have hm := p.side_ge
  obtain ⟨hdeleted, hH, hK⟩ := p.separator_centre_strict_heights k hk P F G hGk hGj hGa
    r s hr hs hdef hentry hexit x hx
  exact frame_deleted_edge_track_region p.side (by omega) F x hdeleted hH hK

end ProteinFolding.Tetrahedral.ConstructionParameters

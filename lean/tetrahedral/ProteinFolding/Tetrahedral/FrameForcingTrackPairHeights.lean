import ProteinFolding.Tetrahedral.FrameForcingTrackPairIndex
import ProteinFolding.Tetrahedral.FrameForcingSeparatorWindow

/-! Height bounds for the physical two-pair block occupied by a separator. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

variable {ι : Type*}

theorem OnTrackPair.height_bounds (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m)
    (F : OctEdgeFrame) {i : ι} {k : ℕ} (hi : P.OnTrackPair m F i k) (hk : 0 < k) (b : Bool) :
    4 * (k : ℤ) ≤ frameH2 m F (P.point (i, b)) ∧
      frameH2 m F (P.point (i, b)) ≤ 4 * (k : ℤ) + 2 ∧
      -2 * octRadius m + 4 * (k : ℤ) ≤ frameK2 m F (P.point (i, b)) ∧
      frameK2 m F (P.point (i, b)) ≤ -2 * octRadius m + 4 * (k : ℤ) + 2 := by
  have hp : P.point (i, b) = frameTrackPoint m F (2 * k) ∨
      P.point (i, b) = frameTrackPoint m F (2 * k + 1) := by
    rcases hi with hi | hi <;> cases b
    · exact Or.inl hi.1
    · exact Or.inr hi.2
    · exact Or.inr hi.1
    · exact Or.inl hi.2
  rcases hp with hp | hp
  · rw [hp, frameTrackPoint_H2 m hm F, frameTrackPoint_K2 m hm F _ (by omega)]
    push_cast
    omega
  · rw [hp, frameTrackPoint_H2 m hm F, frameTrackPoint_K2 m hm F _ (by omega)]
    push_cast
    omega

theorem OnTrackPair.block_height_bounds (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m)
    (F : OctEdgeFrame) {i j : ι} {k l : ℕ}
    (hi : P.OnTrackPair m F i k) (hj : P.OnTrackPair m F j l)
    (hk : 0 < k) (hl : 0 < l) (hconsecutive : k + 1 = l ∨ l + 1 = k) :
    ∀ x ∈ ({P.point (i, false), P.point (i, true), P.point (j, false), P.point (j, true)} : Finset Site),
      4 * (min k l : ℕ) ≤ frameH2 m F x ∧
        frameK2 m F x ≤ -2 * octRadius m + 4 * (min k l : ℕ) + 6 := by
  have hmink : min k l ≤ k := min_le_left _ _
  have hminl : min k l ≤ l := min_le_right _ _
  have hmaxk : k ≤ min k l + 1 := by omega
  have hmaxl : l ≤ min k l + 1 := by omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h := OnTrackPair.height_bounds P m hm F hi hk false
    constructor <;> omega
  · have h := OnTrackPair.height_bounds P m hm F hi hk true
    constructor <;> omega
  · have h := OnTrackPair.height_bounds P m hm F hj hl false
    constructor <;> omega
  · have h := OnTrackPair.height_bounds P m hm F hj hl true
    constructor <;> omega

end ProteinFolding.Tetrahedral.FinitePairFamily

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem two_pair_separator_window {ι : Type*} [Fintype ι] (p : ConstructionParameters)
    (D : FinitePairFamily ι Site) (F G : OctEdgeFrame)
    (hW : frameTrackSites p.side F ⊆ D.covered)
    (hclosed : ∀ i, D.point (i, false) ∈ frameTrackSites p.side F ↔
      D.point (i, true) ∈ frameTrackSites p.side F)
    (hadj : ∀ i, tetrahedralLattice.Adj (D.point (i, false)) (D.point (i, true)))
    (k : ℕ) (hk : k ≤ p.bins) (P : OctWordPath p.side (capWord (p.separatorWord k)))
    (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (r s : ℕ) (hentry : P.site 2 = octEdgeZigzag p.side F r)
    (hexit : P.site (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side G s)
    (i j : ι) (hne : i ≠ j)
    (hi : D.point (i, false) ∈ frameTrackSites p.side F)
    (hj : D.point (j, false) ∈ frameTrackSites p.side F)
    (hHi : 6 ≤ frameH2 p.side F (D.point (i, false)))
    (hHj : 6 ≤ frameH2 p.side F (D.point (j, false)))
    (hlink : OctTriangularNeighbours p.side (D.point (i, true)) (D.point (j, false)))
    (ha : D.point (i, false) = P.site (p.entryTether k + 3))
    (hd : D.point (j, true) = P.site (p.entryTether k + 9)) :
    ∃ u v, D.OnTrackPair p.side F i u ∧ D.OnTrackPair p.side F j v ∧
      (u + 1 = v ∨ v + 1 = u) ∧
      |(min u v : ℕ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ) := by
  have hm := p.side_ge
  obtain ⟨u, _, hu⟩ := D.track_pair_index p.side (by omega) F hW hclosed hadj i hi
  obtain ⟨v, _, hv⟩ := D.track_pair_index p.side (by omega) F hW hclosed hadj j hj
  have hu0 : 0 < u := by
    rcases hu with hu | hu
    all_goals rw [hu.1, frameTrackPoint_H2 p.side (by omega) F] at hHi
    all_goals push_cast at hHi
    all_goals omega
  have hv0 : 0 < v := by
    rcases hv with hv | hv
    all_goals rw [hv.1, frameTrackPoint_H2 p.side (by omega) F] at hHj
    all_goals push_cast at hHj
    all_goals omega
  have hconsecutive := FinitePairFamily.OnTrackPair.link_consecutive D p.side (by omega) F hu hv hne hlink
  have hb := FinitePairFamily.OnTrackPair.block_height_bounds D p.side (by omega) F hu hv hu0 hv0 hconsecutive
  have haB := hb (D.point (i, false)) (by simp)
  have hdB := hb (D.point (j, true)) (by simp)
  rw [ha] at haB
  rw [hd] at hdB
  have htether := p.separator_tether_height_bounds k hk P F G hGk hGj hGa r s hentry hexit
  refine ⟨u, v, hu, hv, hconsecutive, ?_⟩
  exact p.separator_window_from_heights k hk F (min u v) _ _ haB.1 hdB.2 htether.1 htether.2

end ProteinFolding.Tetrahedral.ConstructionParameters

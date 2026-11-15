import ProteinFolding.Tetrahedral.FrameForcingTrackBands

/-! The separator windows leave interior bands of the required capacity.
All error margins are strictly smaller than the item scale. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem separator_window_track_margin (p : ConstructionParameters) (k i : ℕ) (hk : k ≤ p.bins)
    (hi : |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    5 ≤ 2 * i ∧ 2 * i + 6 ≤ 2 * p.side := by
  have hb := abs_le.mp hi
  have hradius := p.separatorRadius_twice
  have hroom := p.separator_room k hk
  have hscale := p.binDimers_ge_scale
  have hscaleEq := p.scale_eq
  have hleft : 2 * p.scale ≤ p.leftFiller := by unfold leftFiller; omega
  have hJleft : p.leftFiller ≤ p.separatorIndex k := by unfold separatorIndex; omega
  have hright : p.rightFiller = p.leftFiller + 1 := rfl
  have hsigma : p.sigma = 18 * p.bins + 40 := rfl
  constructor <;> omega

theorem separator_bin_band_card (p : ConstructionParameters) (F : OctEdgeFrame)
    (k i j : ℕ)
    (hi : |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |(j : ℤ) - (p.separatorIndex (k + 1) : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    (frameTrackBand p.side F (2 * i + 4) (2 * j)).card = 2 * (j - i - 2) := by
  have hm := p.side_ge
  have horder := p.separator_window_order k (i : ℤ) (j : ℤ) hi hj
  rw [frameTrackBand_card p.side (by omega) F]
  omega

theorem separator_bin_capacity_error (p : ConstructionParameters) (k i j : ℕ)
    (hi : |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |(j : ℤ) - (p.separatorIndex (k + 1) : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    |((j - i - 2 : ℕ) : ℤ) - (p.binDimers : ℤ)| ≤ (p.sigma : ℤ) + 6 := by
  have horder := p.separator_window_order k (i : ℤ) (j : ℤ) hi hj
  have herr := p.separator_bin_error k (i : ℤ) (j : ℤ) hi hj
  have hcast : ((j - i - 2 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) - 2 := by omega
  rwa [hcast]

theorem scaled_items_fit_perturbed_bin (p : ConstructionParameters) (load c : ℕ)
    (hsize : p.scale * load ≤ c) (hc : c ≤ p.binDimers + p.sigma + 6) : load ≤ p.capacity := by
  have hscale : p.scale = p.sigma + 8 := rfl
  by_contra hnot
  have hmul := Nat.mul_le_mul_left p.scale (show p.capacity + 1 ≤ load by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  change p.scale * p.capacity + p.scale ≤ p.scale * load at hmul
  change c ≤ p.scale * p.capacity + p.sigma + 6 at hc
  omega

end ProteinFolding.Tetrahedral.ConstructionParameters

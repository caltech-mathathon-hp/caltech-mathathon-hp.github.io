import ProteinFolding.Tetrahedral.WordPieces

/-! The exact integer margins in Section 7's separator and bin argument. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

def separatorRadius (p : ConstructionParameters) : ℕ := 3 + p.sigma / 2

theorem sigma_even (p : ConstructionParameters) : p.sigma % 2 = 0 := by
  unfold sigma
  omega

theorem separatorRadius_twice (p : ConstructionParameters) :
    2 * p.separatorRadius = p.sigma + 6 := by
  have h := p.sigma_even
  unfold separatorRadius
  omega

theorem separator_windows_separated (p : ConstructionParameters) (k : ℕ) :
    p.separatorIndex k + p.separatorRadius + 4 ≤
      p.separatorIndex (k + 1) - p.separatorRadius := by
  have hspacing := p.separator_spacing k
  have hscale := p.binDimers_ge_scale
  have hr := p.separatorRadius_twice
  have hle := p.separatorIndex_mono (show k ≤ k + 1 by omega)
  unfold scale at hscale
  omega

theorem separator_window_order (p : ConstructionParameters) (k : ℕ) (i j : ℤ)
    (hi : |i - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |j - (p.separatorIndex (k + 1) : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    i + 4 ≤ j := by
  have hs := p.separator_windows_separated k
  have hm := p.separatorIndex_mono (show k ≤ k + 1 by omega)
  have hir := (abs_le.mp hi)
  have hjr := (abs_le.mp hj)
  omega

theorem separator_bin_error (p : ConstructionParameters) (k : ℕ) (i j : ℤ)
    (hi : |i - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |j - (p.separatorIndex (k + 1) : ℤ)| ≤ (p.separatorRadius : ℤ)) :
    |(j - i - 2) - (p.binDimers : ℤ)| ≤ (p.sigma : ℤ) + 6 := by
  have hs := p.separator_spacing k
  have hm := p.separatorIndex_mono (show k ≤ k + 1 by omega)
  have hr := p.separatorRadius_twice
  have hir := (abs_le.mp hi)
  have hjr := (abs_le.mp hj)
  apply abs_le.mpr
  constructor <;> omega

/-- A union of whole scaled item chains in one separator window has exactly
the intended bin capacity. -/
theorem scaled_bin_capacity_unique (p : ConstructionParameters) (q : ℕ)
    (herror : |(p.scale * q : ℕ) - (p.binDimers : ℤ)| ≤ (p.sigma : ℤ) + 6) :
    q = p.capacity := by
  have hscale := p.scale_ge
  have hrel : p.scale = p.sigma + 8 := rfl
  have herr := abs_le.mp herror
  unfold binDimers at herr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_left p.scale (show q + 1 ≤ p.capacity by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    push_cast at herr
    omega
  · have hmul := Nat.mul_le_mul_left p.scale (show p.capacity + 1 ≤ q by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    push_cast at herr
    omega

theorem scaled_bin_sum_unique (p : ConstructionParameters) (items : List ℕ)
    (herror : |((items.map p.itemDimers).sum : ℤ) - (p.binDimers : ℤ)| ≤
      (p.sigma : ℤ) + 6) : items.sum = p.capacity := by
  rw [itemDimers_sum] at herror
  exact p.scaled_bin_capacity_unique items.sum herror

theorem fillers_exceed_bin_window (p : ConstructionParameters) (c : ℕ)
    (hc : c ≤ p.binDimers + p.sigma + 6) :
    c < p.leftFiller ∧ c < p.rightFiller := by
  simp only [leftFiller, rightFiller, scale]
  omega

theorem side_exceeds_opposite_frame_threshold (p : ConstructionParameters) :
    8 * p.bins + 19 + p.sigma < p.side := by
  have hbin := p.binDimers_ge_scale
  have hscale := p.scale_eq
  have hside := p.side_eq_track
  unfold leftFiller sigma at *
  omega

theorem opposite_frame_distance_exceeds_separator_span (p : ConstructionParameters) :
    (2 * p.side + 10 + 2 * p.sigma : ℕ) < 4 * p.side - 16 * p.bins - 28 := by
  have h := p.side_exceeds_opposite_frame_threshold
  omega

theorem opposite_frame_separatorBridge_impossible (p : ConstructionParameters)
    (k : ℕ) (hk : k ≤ p.bins) (bonds : ℕ)
    (hnear : bonds ≤ (p.separatorBridge k).length - 1)
    (hfar : 4 * p.side - 16 * p.bins - 28 ≤ bonds) : False := by
  have hu := p.separatorBridge_span_bound k hk
  have hgap := p.opposite_frame_distance_exceeds_separator_span
  omega

end ProteinFolding.Tetrahedral.ConstructionParameters

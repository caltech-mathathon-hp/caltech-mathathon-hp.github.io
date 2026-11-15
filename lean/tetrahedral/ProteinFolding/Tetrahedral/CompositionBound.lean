import ProteinFolding.Tetrahedral.CompositionBoundSplit
import ProteinFolding.Tetrahedral.CompositionBoundCases

/-! Claim U: the sharp value and canonical equality case for compositions of 2m². -/

namespace ProteinFolding.Tetrahedral

open PositiveComposition

theorem composition_inside_median_lt (m : ℕ) (hm : 0 < m) (c : PositiveComposition)
    (hmass : c.mass = 2 * m ^ 2) (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
    (suf : Option PositiveComposition) (hc : c = medianBuild pre b hb suf)
    (hbefore : medianContextMass pre < m ^ 2)
    (hafter : m ^ 2 < medianContextMass pre + b) : twoSidedValue c < octahedralNumber m := by
  have hC := hmass
  rw [hc, medianBuild_mass] at hC
  have hsuf : medianContextMass suf < m ^ 2 := by omega
  let v := m ^ 2 - medianContextMass suf
  let v' := m ^ 2 - medianContextMass pre
  let L := medianLeft pre b hb
  let R := medianRight suf b hb
  have hv : 1 ≤ v := by dsimp [v]; omega
  have hv' : 1 ≤ v' := by dsimp [v']; omega
  have hvm : v ≤ m ^ 2 := by dsimp [v]; omega
  have hv'm : v' ≤ m ^ 2 := by dsimp [v']; omega
  have hbb : b = v + v' := by dsimp [v, v']; omega
  have hLm : L.mass = m ^ 2 + v := by
    dsimp only [L]
    rw [medianLeft_mass]
    dsimp [v]
    omega
  have hRm : R.mass = m ^ 2 + v' := by
    dsimp only [R]
    rw [medianRight_mass]
    dsimp [v']
    omega
  have hLb : L.lastPart = b := medianLeft_last pre b hb
  have hLG : L.value ≤ rootG (m ^ 2 - v') := by
    have hx : medianContextMass pre = m ^ 2 - v' := by dsimp [v']; omega
    simpa only [hx] using medianLeft_value_le_rootG pre b hb
  have hRG : R.value ≤ rootG (m ^ 2 - v) := by
    have hx : medianContextMass suf = m ^ 2 - v := by dsimp [v]; omega
    simpa only [hx] using medianRight_value_le_rootG suf b hb
  have hnum := median_inside_numeric_lt m b v v' hm hv hv' hvm hv'm hbb L R hLm hRm hLb hLG hRG
  have hV := medianBuild_value_le pre b hb suf
  rw [← hc] at hV
  exact hV.trans_lt hnum

/-- Claim U's universal sharp upper bound. -/
theorem composition_bound (m : ℕ) (hm : 0 < m) (c : PositiveComposition)
    (hmass : c.mass = 2 * m ^ 2) : twoSidedValue c ≤ octahedralNumber m := by
  have hM : 0 < m ^ 2 := by nlinarith
  have hbelow : m ^ 2 < c.mass := by omega
  rcases composition_median_split c (m ^ 2) hM hbelow with
    ⟨L, R, hc, hL⟩ | ⟨pre, b, hb, suf, hc, hbefore, hafter⟩
  · have hR : R.mass = m ^ 2 := by
      have h := hmass
      rw [hc, append_mass] at h
      omega
    have hV := twoSidedValue_append_le L R
    rw [hL, hR, min_self, ← reverse_last R] at hV
    rw [← hc] at hV
    exact hV.trans (median_breakpoint_numeric_bound m L R.reverse hL
      (by simpa only [reverse_mass] using hR))
  · exact (composition_inside_median_lt m hm c hmass pre b hb suf hc hbefore hafter).le

/-- Equality in Claim U forces the canonical octahedral composition. -/
theorem composition_bound_equality (m : ℕ) (hm : 0 < m) (c : PositiveComposition)
    (hmass : c.mass = 2 * m ^ 2) (heq : twoSidedValue c = octahedralNumber m) :
    c.parts = (canonicalSquare (m - 1)).parts ++ (canonicalSquare (m - 1)).parts.reverse := by
  have hM : 0 < m ^ 2 := by nlinarith
  have hbelow : m ^ 2 < c.mass := by omega
  rcases composition_median_split c (m ^ 2) hM hbelow with
    ⟨L, R, hc, hL⟩ | ⟨pre, b, hb, suf, hc, hbefore, hafter⟩
  · have hR : R.mass = m ^ 2 := by
      have h := hmass
      rw [hc, append_mass] at h
      omega
    have hV := twoSidedValue_append_le L R
    rw [hL, hR, min_self, ← reverse_last R] at hV
    rw [hc] at heq
    have hnum := median_breakpoint_numeric_bound m L R.reverse hL
      (by simpa only [reverse_mass] using hR)
    have hnumeric : L.value + min (m ^ 2) (L.lastPart * R.reverse.lastPart) + R.reverse.value =
        octahedralNumber m := by omega
    obtain ⟨hPL, hPR⟩ := median_breakpoint_numeric_equality m hm L R.reverse hL
      (by simpa only [reverse_mass] using hR) hnumeric
    have hRparts : R.parts = (canonicalSquare (m - 1)).parts.reverse := by
      have h := congrArg List.reverse hPR
      simpa only [reverse_parts, List.reverse_reverse] using h
    rw [hc, append_parts, hPL, hRparts]
  · have hstrict := composition_inside_median_lt m hm c hmass pre b hb suf hc hbefore hafter
    omega

/-- The canonical octahedral composition attains the bound, not merely its shape. -/
theorem canonical_twoSidedValue (m : ℕ) (hm : 0 < m) :
    twoSidedValue ((canonicalSquare (m - 1)).append (canonicalSquare (m - 1)).reverse) =
      octahedralNumber m := by
  let p := canonicalSquare (m - 1)
  have hindex : m - 1 + 1 = m := by omega
  have hmass : p.mass = m ^ 2 := by dsimp [p]; rw [canonicalSquare_mass, hindex]
  have hlast : p.lastPart = m := by dsimp [p]; rw [canonicalSquare_last, hindex]
  have hvalue : p.value = rootSum (m ^ 2) := by dsimp [p]; rw [canonicalSquare_value, hindex]
  have hC : (p.append p.reverse).mass = 2 * m ^ 2 := by
    rw [append_mass, reverse_mass, hmass]
    omega
  have hprofile : profileValue (2 * m ^ 2) 0 p = p.value :=
    profileValue_eq_oneSided_of_double_mass_le _ _ (by rw [hmass])
  have htail : profileValue (2 * m ^ 2) (m ^ 2) p.reverse = p.value := by
    have hmirror := profileValue_mirror (2 * m ^ 2) 0 p (by rw [hmass]; omega)
    have hmid : 2 * m ^ 2 - 0 - p.mass = m ^ 2 := by rw [hmass]; omega
    rw [hmid, hprofile] at hmirror
    exact hmirror.symm
  have hrem : 2 * m ^ 2 - m ^ 2 = m ^ 2 := by omega
  have hprod : m * m = m ^ 2 := by ring
  change twoSidedValue (p.append p.reverse) = _
  unfold twoSidedValue
  rw [hC, profileValue_append]
  simp only [Nat.zero_add, reverse_first, hmass, hlast, hrem, hprod, min_self]
  rw [hprofile, htail, hvalue]
  unfold octahedralNumber
  omega

theorem composition_bound_attained (m : ℕ) (hm : 0 < m) :
    ∃ c : PositiveComposition, c.mass = 2 * m ^ 2 ∧ twoSidedValue c = octahedralNumber m ∧
      c.parts = (canonicalSquare (m - 1)).parts ++ (canonicalSquare (m - 1)).parts.reverse := by
  let p := canonicalSquare (m - 1)
  refine ⟨p.append p.reverse, ?_, canonical_twoSidedValue m hm, ?_⟩
  · have hindex : m - 1 + 1 = m := by omega
    have hmass : p.mass = m ^ 2 := by dsimp [p]; rw [canonicalSquare_mass, hindex]
    rw [append_mass, reverse_mass, hmass]
    omega
  · rw [append_parts, reverse_parts]

end ProteinFolding.Tetrahedral

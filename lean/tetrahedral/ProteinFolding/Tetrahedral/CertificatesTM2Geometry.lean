import ProteinFolding.Tetrahedral.Certificates

/-! For valid diamond sites, adjacency is exactly signed-unary displacement
mass three. This lets the concrete counter inspector recognize contacts. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Geometry

def manhattan (p q : Site) : ℕ :=
  (q.val 0 - p.val 0).natAbs + (q.val 1 - p.val 1).natAbs + (q.val 2 - p.val 2).natAbs

theorem manhattan_comm (p q : Site) : manhattan p q = manhattan q p := by
  have hab (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
    rw [← Int.natAbs_neg (a - b), Int.neg_sub]
  simp only [manhattan, hab]

theorem directedBond_of_manhattan_three {p q : Site}
    (hp : InASublattice p.val) (hq : InBSublattice q.val)
    (h : manhattan p q = 3) : DirectedBond p q := by
  have hp0 := hp.1 0
  have hp1 := hp.1 1
  have hp2 := hp.1 2
  have hq0 := hq.1 0
  have hq1 := hq.1 1
  have hq2 := hq.1 2
  have hpsum := hp.2
  have hqsum := hq.2
  unfold manhattan at h
  have h0 : q.val 0 = p.val 0 + 1 ∨ q.val 0 = p.val 0 - 1 := by omega
  have h1 : q.val 1 = p.val 1 + 1 ∨ q.val 1 = p.val 1 - 1 := by omega
  have h2 : q.val 2 = p.val 2 + 1 ∨ q.val 2 = p.val 2 - 1 := by omega
  refine ⟨hp, hq, ?_⟩
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · refine ⟨0, ?_⟩
    intro k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · simp only [coordinateSum] at hpsum hqsum
    omega
  · simp only [coordinateSum] at hpsum hqsum
    omega
  · refine ⟨1, ?_⟩
    intro k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · simp only [coordinateSum] at hpsum hqsum
    omega
  · refine ⟨2, ?_⟩
    intro k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · refine ⟨3, ?_⟩
    intro k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · simp only [coordinateSum] at hpsum hqsum
    omega

theorem manhattan_ne_three_of_same_colour {p q : Site}
    (hcolour : (InASublattice p.val ∧ InASublattice q.val) ∨
      (InBSublattice p.val ∧ InBSublattice q.val)) : manhattan p q ≠ 3 := by
  intro h
  rcases hcolour with ⟨hp, hq⟩ | ⟨hp, hq⟩
  all_goals
    have hp0 := hp.1 0
    have hp1 := hp.1 1
    have hp2 := hp.1 2
    have hq0 := hq.1 0
    have hq1 := hq.1 1
    have hq2 := hq.1 2
    unfold manhattan at h
    omega

theorem adj_iff_manhattan_three (p q : Site) :
    tetrahedralLattice.Adj p q ↔ manhattan p q = 3 := by
  constructor
  · intro h
    have h0 := adj_coordinate h 0
    have h1 := adj_coordinate h 1
    have h2 := adj_coordinate h 2
    unfold manhattan
    omega
  · intro h
    rcases p.property with hp | hp <;> rcases q.property with hq | hq
    · exact False.elim (manhattan_ne_three_of_same_colour (Or.inl ⟨hp, hq⟩) h)
    · exact Or.inl (directedBond_of_manhattan_three hp hq h)
    · apply Or.inr
      exact directedBond_of_manhattan_three hq hp (by rwa [manhattan_comm])
    · exact False.elim (manhattan_ne_three_of_same_colour (Or.inr ⟨hp, hq⟩) h)

theorem manhattan_eq_zero_iff (p q : Site) : manhattan p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold manhattan at h
    have h0 : p.val 0 = q.val 0 := by omega
    have h1 : p.val 1 = q.val 1 := by omega
    have h2 : p.val 2 = q.val 2 := by omega
    apply Subtype.ext
    funext k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
  · rintro rfl
    simp [manhattan]

end ProteinFolding.Tetrahedral.CertificatesTM2Geometry

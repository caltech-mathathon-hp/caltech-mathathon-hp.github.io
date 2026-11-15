import ProteinFolding.Tetrahedral.FarFieldArbitraryAvenues

namespace ProteinFolding.Tetrahedral.FarField

def rungResidue (forward up : Bool) : ℤ :=
  if forward then (if up then 1 else 3) else (if up then 2 else 0)

def previousRungResidue (forward up : Bool) : ℤ :=
  if forward then (if up then 0 else 2) else (if up then 3 else 1)

def orientedAvenue (c : Site) (hc : InASublattice c.val) (up forward : Bool) (n : ℤ) : Site :=
  avenue c hc up (if forward then n else -n)

theorem residue_in_window (r x : ℤ) (hr : 0 ≤ r) (hr' : r < 4) :
    ∃ n : ℤ, x ≤ n ∧ n ≤ x + 3 ∧ n % 4 = r := by
  refine ⟨x + (r - x) % 4, ?_, ?_, ?_⟩ <;> omega

theorem oriented_upper_rung (R : ℤ) (c : Site) (hc : InASublattice c.val)
    (up forward : Bool) (n : ℤ) (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c)
    (hn : n % 4 = rungResidue forward up) :
    rho R (orientedAvenue c hc up forward n) = privateLevel R c up + 2 ∧
      rho R (orientedAvenue c hc up forward (n - 1)) = privateLevel R c up ∧
      alpha R (orientedAvenue c hc up forward n) =
        alpha R (orientedAvenue c hc up forward (n - 1)) := by
  have hcur : (if forward then n else -n) % 4 = rungResidue forward up := by
    cases forward <;> cases up <;> simp [rungResidue] at hn ⊢ <;> omega
  have hprev : (if forward then n - 1 else -(n - 1)) % 4 = previousRungResidue forward up := by
    cases forward <;> cases up <;> simp [rungResidue, previousRungResidue] at hn ⊢ <;> omega
  have hc' := avenue_rho_alpha R c hc up (if forward then n else -n) hy hz
  have hp' := avenue_rho_alpha R c hc up (if forward then n - 1 else -(n - 1)) hy hz
  simp only [orientedAvenue]
  cases forward <;> cases up
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true] at hcur hprev hc' hp' ⊢
    simp only [rungResidue, previousRungResidue, Bool.false_eq_true, ite_false, ite_true] at hcur hprev
    simp [avenueY, avenueZ, hcur, hprev, privateLevel] at hc' hp' ⊢ <;> omega

theorem quadrantAvenue_upper_rung (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c)
    (hn : n % 4 = rungResidue (decide (q.1 = q.2)) up) :
    rho R (quadrantAvenue R hR q c hc up n) = privateLevel R c up + 2 ∧
      rho R (quadrantAvenue R hR q c hc up (n - 1)) = privateLevel R c up ∧
      alpha R (quadrantAvenue R hR q c hc up n) =
        alpha R (quadrantAvenue R hR q c hc up (n - 1)) := by
  have h := oriented_upper_rung R c hc up (decide (q.1 = q.2)) n hy hz hn
  by_cases hq : q.1 = q.2 <;>
    simpa [quadrantAvenue, orientedAvenue, hq] using h

/-- Stage B's slab entry: an actual upper-level site reached by a rung exists
between the slab value xi and xi+3. The preceding site is on the lower level. -/
theorem exists_upper_rung_at_X (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (ξ : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    ∃ n : ℤ,
      ξ ≤ X (quadrantAvenue R hR q c hc up n) ∧
      X (quadrantAvenue R hR q c hc up n) ≤ ξ + 3 ∧
      rho R (quadrantAvenue R hR q c hc up n) = privateLevel R c up + 2 ∧
      rho R (quadrantAvenue R hR q c hc up (n - 1)) = privateLevel R c up ∧
      alpha R (quadrantAvenue R hR q c hc up n) =
        alpha R (quadrantAvenue R hR q c hc up (n - 1)) ∧
      tetrahedralLattice.Adj (quadrantAvenue R hR q c hc up (n - 1))
        (quadrantAvenue R hR q c hc up n) := by
  let r := rungResidue (decide (q.1 = q.2)) up
  have hr : 0 ≤ r ∧ r < 4 := by
    dsimp only [r]
    cases h : decide (q.1 = q.2) <;> cases up <;> decide
  obtain ⟨n, hn0, hn1, hn⟩ := residue_in_window r (ξ - X (quadrantMap R hR q c)) hr.1 hr.2
  have hlevels := quadrantAvenue_upper_rung R hR q c hc up n hy hz hn
  refine ⟨n, ?_, ?_, hlevels.1, hlevels.2.1, hlevels.2.2, ?_⟩
  · rw [quadrantAvenue_x]
    omega
  · rw [quadrantAvenue_x]
    omega
  · have hnext : n - 1 + 1 = n := by omega
    simpa only [hnext] using quadrantAvenue_adj R hR q c hc up (n - 1)

end ProteinFolding.Tetrahedral.FarField

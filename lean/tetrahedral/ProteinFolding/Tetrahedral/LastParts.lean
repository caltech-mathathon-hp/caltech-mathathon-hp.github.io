import ProteinFolding.Tetrahedral.Optimization

/-! Last-part restrictions and canonical equality cases (Lemma 5.4).
All optimality hypotheses refer to the already proved one-sided maximum F. -/

namespace ProteinFolding.Tetrahedral

open PositiveComposition

theorem rootSum_pos_of_two_le (x : ℕ) (hx : 2 ≤ x) : 0 < rootSum x := by
  have h1 : rootSum 1 = 0 := by
    change rootSum (0 + 1) = 0
    rw [rootSum_succ, rootSum_zero, Nat.sqrt_zero]
  have h2 : rootSum 2 = 1 := by
    change rootSum (1 + 1) = 1
    rw [rootSum_succ, h1, Nat.sqrt_one]
  have hm := rootSum_mono hx
  omega

theorem parts_eq_one_of_mass_eq_one (c : PositiveComposition) (hmass : c.mass = 1) :
    c.parts = [1] := by
  cases c with
  | single p hp =>
    change p = 1 at hmass
    subst p
    rfl
  | snoc c p hp =>
    have hc := c.mass_pos
    change c.mass + p = 1 at hmass
    omega

set_option maxHeartbeats 1000000 in
/-- An optimal composition in the first block beyond m² whose last part is
at least m can only be at m² itself, with last part exactly m. -/
theorem optimal_large_last_square_block (c : PositiveComposition) (m v : ℕ)
    (hm : 0 < m) (hv : v < m) (hmass : c.mass = m ^ 2 + v)
    (hlast : m ≤ c.lastPart) (hopt : c.value = rootSum c.mass) :
    v = 0 ∧ c.lastPart = m := by
  by_cases hmone : m = 1
  · subst m
    have hv0 : v = 0 := by omega
    have hle := c.lastPart_le_mass
    have hpos := c.lastPart_pos
    simp only [Nat.one_pow] at hmass
    exact ⟨hv0, by omega⟩
  · cases c with
    | single l hl =>
      change l = m ^ 2 + v at hmass
      change 0 = rootSum l at hopt
      change m ≤ l at hlast
      have hlarge : 2 ≤ l := by omega
      have hp := rootSum_pos_of_two_le l hlarge
      omega
    | snoc p l hl =>
      change p.mass + l = m ^ 2 + v at hmass
      change m ≤ l at hlast
      have ha : p.mass < m ^ 2 := by omega
      have hs : Nat.sqrt p.mass < m := Nat.sqrt_lt'.mpr ha
      rcases optimal_snoc_cases p l hl hopt with
        ⟨hpart, hprod, hend, hprefix⟩ | ⟨hpart, hsize, hlength⟩
      · have hsq : (Nat.sqrt p.mass + 1) ^ 2 ≤ m ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have hv0 : v = 0 := by omega
        have hpow : m ^ 2 = (Nat.sqrt p.mass + 1) ^ 2 := by omega
        have hs1 : Nat.sqrt p.mass + 1 = m := by
          apply le_antisymm (by omega)
          apply Nat.mul_self_le_mul_self_iff.mp
          simpa only [pow_two] using hpow.le
        have hsum : p.mass + l = m ^ 2 := by omega
        have hmul : (Nat.sqrt p.mass + 1) * l ≤ p.mass + l := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_right hprod l
        rw [hs1, hsum, pow_two] at hmul
        have hl_le := Nat.le_of_mul_le_mul_left hmul hm
        exact ⟨hv0, by change l = m; omega⟩
      · omega

/-- Lemma 5.4(F2): a positive offset below m precludes a last part ≥ m. -/
theorem optimal_last_lt_square_offset (c : PositiveComposition) (m v : ℕ)
    (hm : 0 < m) (hv : 1 ≤ v) (hvm : v ≤ m - 1)
    (hmass : c.mass = m ^ 2 + v) (hopt : c.value = rootSum c.mass) : c.lastPart < m := by
  by_contra hnot
  have h := optimal_large_last_square_block c m v hm (by omega) hmass (by omega) hopt
  omega

/-- Lemma 5.4(F3): optimal square mass has last part at most its square root. -/
theorem optimal_square_last_le (c : PositiveComposition) (m : ℕ) (hm : 0 < m)
    (hmass : c.mass = m ^ 2) (hopt : c.value = rootSum c.mass) : c.lastPart ≤ m := by
  by_contra hnot
  have h := optimal_large_last_square_block c m 0 hm (by omega)
    (by simpa using hmass) (by omega) hopt
  omega

set_option maxHeartbeats 2000000 in
/-- Lemma 5.4(F4), indexed so the canonical composition is always nonempty. -/
theorem optimal_square_parts_unique_index (n : ℕ) (c : PositiveComposition)
    (hmass : c.mass = (n + 1) ^ 2) (hlast : c.lastPart = n + 1)
    (hopt : c.value = rootSum c.mass) : c.parts = (canonicalSquare n).parts := by
  induction n generalizing c with
  | zero =>
    have hc : c.mass = 1 := by simpa using hmass
    simpa [canonicalSquare, parts] using parts_eq_one_of_mass_eq_one c hc
  | succ n ih =>
    cases c with
    | single t ht =>
      change t = (n + 1 + 1) ^ 2 at hmass
      change t = n + 1 + 1 at hlast
      nlinarith only [hmass, hlast]
    | snoc p l hl =>
      change l = n + 1 + 1 at hlast
      subst l
      change p.mass + (n + 2) = (n + 2) ^ 2 at hmass
      have hpMass : p.mass = (n + 1) ^ 2 + (n + 1) := by nlinarith only [hmass]
      have hs : Nat.sqrt p.mass = n + 1 := by
        rw [hpMass]
        exact Nat.sqrt_add_eq' (n + 1) (by omega)
      rcases optimal_snoc_cases p (n + 2) hl hopt with
        ⟨hpLast, hprod, hend, hpOpt⟩ | ⟨hpart, hsize, hlength⟩
      · have hpLast' : p.lastPart = n + 1 := by omega
        cases p with
        | single t ht =>
          change t = (n + 1) ^ 2 + (n + 1) at hpMass
          change t = n + 1 at hpLast'
          nlinarith only [hpMass, hpLast']
        | snoc q t ht =>
          change t = n + 1 at hpLast'
          subst t
          change q.mass + (n + 1) = (n + 1) ^ 2 + (n + 1) at hpMass
          have hqMass : q.mass = (n + 1) ^ 2 := by omega
          have hsq : Nat.sqrt q.mass = n + 1 := by rw [hqMass]; exact Nat.sqrt_eq' _
          rcases optimal_snoc_cases q (n + 1) ht hpOpt with
            ⟨hqLast, hprod', hend', hqOpt⟩ | ⟨hpart', hsize', hlength'⟩
          · have hqLast' : q.lastPart = n + 1 := by omega
            have hqParts := ih q hqMass hqLast' hqOpt
            change (q.parts ++ [n + 1]) ++ [n + 2] = _
            rw [hqParts]
            rfl
          · rw [hsq, hqMass] at hsize'
            omega
      · omega

/-- Lemma 5.4(F4): the only optimal composition of m² ending in m is c_m. -/
theorem optimal_square_parts_unique (c : PositiveComposition) (m : ℕ) (hm : 0 < m)
    (hmass : c.mass = m ^ 2) (hlast : c.lastPart = m)
    (hopt : c.value = rootSum c.mass) : c.parts = (canonicalSquare (m - 1)).parts := by
  cases m with
  | zero => omega
  | succ n => simpa using optimal_square_parts_unique_index n c hmass hlast hopt

end ProteinFolding.Tetrahedral

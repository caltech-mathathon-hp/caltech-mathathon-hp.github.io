import ProteinFolding.Tetrahedral.ReductionSize

/-! Uniform polynomial output-size estimates. These bounds do not replace
the separate constructive TM2 runtime proof for the reduction. -/

namespace ProteinFolding.Tetrahedral

theorem octahedralNumber_le_cubic (m : ℕ) : octahedralNumber m ≤ 4 * m ^ 3 := by
  rw [octahedralNumber_formula]
  calc
    m * (4 * m ^ 2 - 1) / 3 ≤ m * (4 * m ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ m * (4 * m ^ 2) := Nat.mul_le_mul_left m (Nat.sub_le _ _)
    _ = 4 * m ^ 3 := by ring

namespace ConstructionParameters

theorem side_le_input_cubic (p : ConstructionParameters) (t : ℕ)
    (hK : p.bins ≤ t) (hB : p.capacity ≤ t) : p.side ≤ 200 * (t + 1) ^ 3 := by
  let X := t + 1
  have h1 : p.bins + 2 ≤ 2 * X := by dsimp [X]; omega
  have h2 : 18 * p.bins + 48 ≤ 48 * X := by dsimp [X]; omega
  have h3 : p.capacity ≤ X := by dsimp [X]; omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have htail : 38 * p.bins + 100 ≤ 100 * X := by dsimp [X]; omega
  have hcube : X ≤ X ^ 3 := le_self_pow (by dsimp [X]; omega) (by decide : 3 ≠ 0)
  rw [p.side_closedForm]
  calc
    (p.bins + 2) * (18 * p.bins + 48) * p.capacity + 38 * p.bins + 100 ≤
        (2 * X) * (48 * X) * X + 100 * X := by omega
    _ = 96 * X ^ 3 + 100 * X := by ring
    _ ≤ 200 * X ^ 3 := by omega

theorem reduction_units_count_cubic (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (hitems : ∀ s ∈ items, 0 < s) (htotal : items.sum = p.bins * p.capacity)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42) :
    (p.reductionUnitBodies items bulkLengths).length ≤ 16 * (p.side + 1) ^ 3 := by
  have hcount := p.reduction_units_count_bound items bulkLengths hitems htotal hbulkRuns
  have hlarge := p.side_ge
  have hmass : bulkLengths.sum ≤ octahedralNumber p.side := by omega
  have hN := octahedralNumber_le_cubic p.side
  have hm3 := Nat.pow_le_pow_left (show p.side ≤ p.side + 1 by omega) 3
  have hcube : p.side + 1 ≤ (p.side + 1) ^ 3 :=
    le_self_pow (by omega) (by decide : 3 ≠ 0)
  omega

/-- The exact word, including the corrected long linker lengths, has a
uniform sixth-degree bound in the octahedral size. -/
theorem prescribedReductionWord_length_polynomial (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (sameSublattice : List Bool)
    (hitems : ∀ s ∈ items, 0 < s) (htotal : items.sum = p.bins * p.capacity)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42) :
    (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤
      600000 * (p.side + 1) ^ 6 := by
  let X := p.side + 1
  let N := (p.reductionUnitBodies items bulkLengths).length
  have hlarge := p.side_ge
  have hmass : bulkLengths.sum ≤ octahedralNumber p.side := by omega
  have hNcube := octahedralNumber_le_cubic p.side
  have hm3 : p.side ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by dsimp [X]; omega) 3
  have hcube : X ≤ X ^ 3 := le_self_pow (by dsimp [X]; omega) (by decide : 3 ≠ 0)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hN : N ≤ 16 * X ^ 3 :=
    p.reduction_units_count_cubic items bulkLengths hitems htotal hbulkRuns hbulkMass
  have hQ : bulkLengths.sum + 200 * (p.side + 1) ≤ 204 * X ^ 3 := by
    change bulkLengths.sum + 200 * X ≤ 204 * X ^ 3
    omega
  have hL : p.baseLinkerLength (p.reductionWireCount items bulkLengths) + 1 ≤ 33007 * X ^ 3 := by
    change 1000 * (p.side + 2 * N + 1) + 6 + 1 ≤ 33007 * X ^ 3
    have hm : p.side ≤ X ^ 3 := by dsimp [X] at hcube; omega
    omega
  have hword := p.prescribedReductionWord_length_bound items bulkLengths sameSublattice htotal
  have hcombined : bulkLengths.sum + 200 * (p.side + 1) +
      p.baseLinkerLength (p.reductionWireCount items bulkLengths) + 1 ≤ 33211 * X ^ 3 := by omega
  have hprod := Nat.mul_le_mul hN hcombined
  dsimp only [N] at hprod
  have hX6 : 0 < X ^ 6 := pow_pos (by omega) _
  calc
    (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤
        2 + (16 * X ^ 3) * (33211 * X ^ 3) := by omega
    _ = 2 + 531376 * X ^ 6 := by ring
    _ ≤ 600000 * X ^ 6 := by omega

end ConstructionParameters

end ProteinFolding.Tetrahedral

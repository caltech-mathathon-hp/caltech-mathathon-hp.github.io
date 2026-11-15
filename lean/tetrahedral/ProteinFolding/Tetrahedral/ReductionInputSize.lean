import ProteinFolding.Tetrahedral.ReductionSizePolynomial
import ProteinFolding.Tetrahedral.PackingSource

/-! Instantiate the scale and word-size estimates at the actual unary
packing encoding. Canonical bulk/parity data and their TM2 computation remain
separate obligations; the estimate applies to every such valid data list. -/

namespace ProteinFolding.Tetrahedral

namespace ConstructionParameters

theorem prescribedReductionWord_length_input_bound (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (sameSublattice : List Bool) (t : ℕ)
    (hK : p.bins ≤ t) (hB : p.capacity ≤ t)
    (hitems : ∀ s ∈ items, 0 < s) (htotal : items.sum = p.bins * p.capacity)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42) :
    (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤
      (600000 * 201 ^ 6) * (t + 1) ^ 18 := by
  have hm := p.side_le_input_cubic t hK hB
  have hcube : 1 ≤ (t + 1) ^ 3 := by
    have h := le_self_pow (show 1 ≤ t + 1 by omega) (by decide : 3 ≠ 0)
    omega
  have hplus : p.side + 1 ≤ 201 * (t + 1) ^ 3 := by omega
  calc
    (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤
        600000 * (p.side + 1) ^ 6 :=
      p.prescribedReductionWord_length_polynomial items bulkLengths sameSublattice
        hitems htotal hbulkRuns hbulkMass
    _ ≤ 600000 * (201 * (t + 1) ^ 3) ^ 6 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hplus 6)
    _ = (600000 * 201 ^ 6) * (t + 1) ^ 18 := by
      rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]

end ConstructionParameters

namespace PackingSource

def parameters (I : Instance) (hw : Packing.WellFormed I) : ConstructionParameters :=
  ⟨I.bins, I.capacity, hw.2.1, hw.1⟩

theorem parameters_side_bound (I : Instance) (hw : Packing.WellFormed I) :
    (parameters I hw).side ≤ 200 * ((instanceEncoding.encode I).length + 1) ^ 3 := by
  have h := instanceEncoding_length I
  apply (parameters I hw).side_le_input_cubic
  · change I.bins ≤ (instanceEncoding.encode I).length
    omega
  · change I.capacity ≤ (instanceEncoding.encode I).length
    omega

theorem prescribed_word_unary_input_bound (I : Instance) (hw : Packing.WellFormed I)
    (htotal : I.sizes.sum = I.bins * I.capacity) (bulkLengths : List ℕ)
    (sameSublattice : List Bool) (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hbulkMass : 24 * (parameters I hw).side + bulkLengths.sum =
      octahedralNumber (parameters I hw).side + 42) :
    ((parameters I hw).prescribedReductionWord I.sizes bulkLengths sameSublattice).length ≤
      (600000 * 201 ^ 6) * ((instanceEncoding.encode I).length + 1) ^ 18 := by
  have h := instanceEncoding_length I
  apply (parameters I hw).prescribedReductionWord_length_input_bound
  · change I.bins ≤ (instanceEncoding.encode I).length
    omega
  · change I.capacity ≤ (instanceEncoding.encode I).length
    omega
  · exact hw.2.2
  · exact htotal
  · exact hbulkRuns
  · exact hbulkMass

end PackingSource

end ProteinFolding.Tetrahedral

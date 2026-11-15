import ProteinFolding.Tetrahedral.FrameForcingBinArithmetic
import ProteinFolding.Tetrahedral.FrameForcingEntryExhaustion

/-! Once a bin is covered by whole scaled item chains, its sharp physical
capacity forces the exact unscaled source load. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

open scoped BigOperators

theorem bin_load_of_item_chain_cover {ι : Type*} (p : ConstructionParameters)
    (I : Finset ι) (value : ι → ℕ) (C : ι → Finset Site)
    (hcard : ∀ i ∈ I, (C i).card = 2 * p.itemDimers (value i))
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j))
    (F : OctEdgeFrame) (k i j : ℕ)
    (hi : |(i : ℤ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hj : |(j : ℤ) - (p.separatorIndex (k + 1) : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hcover : I.biUnion C = frameTrackBand p.side F (2 * i + 4) (2 * j)) :
    (∑ t ∈ I, value t) = p.capacity := by
  classical
  have hsumcard : (I.biUnion C).card = 2 * (p.scale * ∑ t ∈ I, value t) := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      (∑ t ∈ I, (C t).card) = ∑ t ∈ I, 2 * (p.scale * value t) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hcard t ht
      _ = 2 * (p.scale * ∑ t ∈ I, value t) := by rw [Finset.mul_sum, Finset.mul_sum]
  have hcount : p.scale * (∑ t ∈ I, value t) = j - i - 2 := by
    have hc : 2 * (p.scale * ∑ t ∈ I, value t) = 2 * (j - i - 2) := by
      rw [← hsumcard, hcover, p.separator_bin_band_card F k i j hi hj]
    omega
  have herr := p.separator_bin_capacity_error k i j hi hj
  rw [← hcount] at herr
  exact p.scaled_bin_capacity_unique (∑ t ∈ I, value t) herr

end ProteinFolding.Tetrahedral.ConstructionParameters

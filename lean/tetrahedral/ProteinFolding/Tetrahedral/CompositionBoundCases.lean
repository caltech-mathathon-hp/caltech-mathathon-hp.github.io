import ProteinFolding.Tetrahedral.LastParts
import ProteinFolding.Tetrahedral.RootConvexity

/-! The numerical median cases of Claim U, independent of structural splitting. -/

namespace ProteinFolding.Tetrahedral

open PositiveComposition

theorem median_breakpoint_numeric_bound (m : ℕ) (L R : PositiveComposition)
    (hL : L.mass = m ^ 2) (hR : R.mass = m ^ 2) :
    L.value + min (m ^ 2) (L.lastPart * R.lastPart) + R.value ≤ octahedralNumber m := by
  have hLv := oneSided_le_rootSum L
  have hRv := oneSided_le_rootSum R
  rw [hL] at hLv
  rw [hR] at hRv
  have hmid := min_le_left (m ^ 2) (L.lastPart * R.lastPart)
  unfold octahedralNumber
  omega

theorem median_breakpoint_numeric_equality (m : ℕ) (hm : 0 < m) (L R : PositiveComposition)
    (hL : L.mass = m ^ 2) (hR : R.mass = m ^ 2)
    (heq : L.value + min (m ^ 2) (L.lastPart * R.lastPart) + R.value = octahedralNumber m) :
    L.parts = (canonicalSquare (m - 1)).parts ∧ R.parts = (canonicalSquare (m - 1)).parts := by
  have hLv := oneSided_le_rootSum L
  have hRv := oneSided_le_rootSum R
  rw [hL] at hLv
  rw [hR] at hRv
  have hmid := min_le_left (m ^ 2) (L.lastPart * R.lastPart)
  have hmidprod := min_le_right (m ^ 2) (L.lastPart * R.lastPart)
  have hoptL : L.value = rootSum L.mass := by rw [hL]; unfold octahedralNumber at heq; omega
  have hoptR : R.value = rootSum R.mass := by rw [hR]; unfold octahedralNumber at heq; omega
  have hproduct : m ^ 2 ≤ L.lastPart * R.lastPart := by unfold octahedralNumber at heq; omega
  have hlastL := optimal_square_last_le L m hm hL hoptL
  have hlastR := optimal_square_last_le R m hm hR hoptR
  have hlastL' : L.lastPart = m := by
    by_contra hnot
    have hlt : L.lastPart < m := by omega
    have hprodle := Nat.mul_le_mul_left L.lastPart hlastR
    have hprodlt := Nat.mul_lt_mul_of_pos_right hlt hm
    rw [pow_two] at hproduct
    omega
  have hlastR' : R.lastPart = m := by
    rw [hlastL', pow_two] at hproduct
    have h := Nat.le_of_mul_le_mul_left hproduct hm
    omega
  exact ⟨optimal_square_parts_unique L m hm hL hlastL' hoptL,
    optimal_square_parts_unique R m hm hR hlastR' hoptR⟩

/-- The median cannot lie inside any part of an extremal composition. -/
theorem median_inside_numeric_lt (m b v v' : ℕ) (hm : 0 < m)
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hvm : v ≤ m ^ 2) (hv'm : v' ≤ m ^ 2)
    (hb : b = v + v') (L R : PositiveComposition)
    (hL : L.mass = m ^ 2 + v) (hR : R.mass = m ^ 2 + v') (hLb : L.lastPart = b)
    (hLG : L.value ≤ rootG (m ^ 2 - v')) (hRG : R.value ≤ rootG (m ^ 2 - v)) :
    L.value + R.value < octahedralNumber m := by
  have hLv := oneSided_le_rootSum L
  have hRv := oneSided_le_rootSum R
  rw [hL] at hLv
  rw [hR] at hRv
  by_cases hsmall : b < m
  · have h := rootSum_small_central_part_lt m v v' hm (by omega)
    omega
  · by_cases heq : b = m
    · have hstrict : L.value < rootSum (m ^ 2 + v) := by
        by_contra hnot
        have hopt : L.value = rootSum L.mass := by rw [hL]; omega
        have hlast := optimal_last_lt_square_offset L m v hm hv (by omega) hL hopt
        omega
      have h := rootSum_middle_central_part_eq m v v' (by omega)
      omega
    · have h := rootG_large_central_part_lt m v' v hm hv' hv hv'm hvm (by omega)
      omega

end ProteinFolding.Tetrahedral

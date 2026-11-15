import ProteinFolding.Cubic.Proofs.GeometryProjection
import ProteinFolding.Cubic.Proofs.GeometryArithmetic
import ProteinFolding.Cubic.Proofs.GeometryCubeEdges

/-! The edge upper bound in the cubic-cardinality case of Fact 3.1.
This file counts positive coordinate edges. The equality classification and
the bridge to the sequence-index bond count are separate obligations.
-/

namespace ProteinFolding.CubicGeometry

open scoped BigOperators

theorem positiveEdgeCount_le_cube (s : Finset Site) (n : ℕ)
    (hc : s.card = n ^ 3) : positiveEdgeCount s ≤ 3 * n ^ 2 * (n - 1) := by
  have hp := card_sq_le_lineKey_product s
  have hprod : (n ^ 2) ^ 3 ≤ (s.image (lineKey 0)).card *
      (s.image (lineKey 1)).card * (s.image (lineKey 2)).card := by
    simpa [hc, ← pow_mul] using hp
  have hs := Arithmetic.three_mul_le_sum (s.image (lineKey 0)).card
    (s.image (lineKey 1)).card (s.image (lineKey 2)).card (n ^ 2) hprod
  have he := positiveEdgeCount_add_lines_le s
  have hlines : (∑ k : Fin 3, (s.image (lineKey k)).card) =
      (s.image (lineKey 0)).card + (s.image (lineKey 1)).card +
        (s.image (lineKey 2)).card := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [hlines, hc] at he
  by_cases hn : n = 0
  · simp_all
  · have hn' : n - 1 + 1 = n := by omega
    have harith : 3 * n ^ 3 = 3 * n ^ 2 * (n - 1) + 3 * n ^ 2 := by
      nlinarith
    omega

theorem lineKey_cards_of_maximal_edges (s : Finset Site) (n : ℕ)
    (hc : s.card = n ^ 3) (he : positiveEdgeCount s ≥ 3 * n ^ 2 * (n - 1)) :
    (s.image (lineKey 0)).card = n ^ 2 ∧
      (s.image (lineKey 1)).card = n ^ 2 ∧
      (s.image (lineKey 2)).card = n ^ 2 := by
  have hp := card_sq_le_lineKey_product s
  have hprod : (n ^ 2) ^ 3 ≤ (s.image (lineKey 0)).card *
      (s.image (lineKey 1)).card * (s.image (lineKey 2)).card := by
    simpa [hc, ← pow_mul] using hp
  apply Arithmetic.product_rigidity _ _ _ (n ^ 2) hprod
  have hlines := positiveEdgeCount_add_lines_le s
  have hsum : (∑ k : Fin 3, (s.image (lineKey k)).card) =
      (s.image (lineKey 0)).card + (s.image (lineKey 1)).card +
        (s.image (lineKey 2)).card := by simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [hsum, hc] at hlines
  by_cases hn : n = 0
  · simp_all
  · have hn' : n - 1 + 1 = n := by omega
    have harith : 3 * n ^ 3 = 3 * n ^ 2 * (n - 1) + 3 * n ^ 2 := by nlinarith
    omega

end ProteinFolding.CubicGeometry

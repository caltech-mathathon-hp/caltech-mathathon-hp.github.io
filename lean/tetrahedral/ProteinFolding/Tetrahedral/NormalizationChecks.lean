import ProteinFolding.Tetrahedral.Certificates

/-! Boundary cases for normalization and the direction certificate semantics. -/

namespace ProteinFolding.Tetrahedral.NormalizationChecks

open Residue

private def bStart : Site := ⟨![1, 1, 1], by decide⟩
private def aStart : Site := ⟨![2, 2, 0], by decide⟩

example : normalizeSite bStart bStart = origin := normalizeSite_self _
example : normalizeSite aStart aStart = origin := normalizeSite_self _
example : normalizeSite bStart origin = bStart := by decide

private def reverseBond : Fold tetrahedralLattice [H, H].length where
  pos i := if i.val = 0 then bStart else origin
  injective_pos := by decide
  consecutive := by decide

example : (normalizedFold reverseBond).pos ⟨0, by decide⟩ = origin :=
  normalizedFold_normalized reverseBond ⟨0, by decide⟩ rfl
example : bondCount [H, H] (normalizedFold reverseBond) = 1 := by
  rw [normalizedFold_bondCount]
  decide

example : directionVerifier (⟨[H, H], 1⟩, [0, 0]) = true := by decide
example : directionVerifier (⟨[H, H], 2⟩, [0, 0]) = false := by decide
example : directionVerifier (⟨[H, H], 1⟩, [0]) = false := by decide
example : directionVerifier (⟨[H, H, H], 2⟩, [0, 0, 0]) = false := by decide
example : directionVerifier (⟨[], 0⟩, []) = true := by decide
example : directionVerifier (⟨[], 1⟩, []) = false := by decide
example : directionVerifier (⟨[], -1⟩, []) = true := by decide
example : directionVerifier (⟨[H, H, H, H, H, H], 6⟩, [0, 1, 2, 0, 1, 0]) = true := by decide
example : directionVerifier (⟨[H, P, P, P, P, H], 1⟩, [0, 1, 2, 0, 1, 0]) = true := by decide

end ProteinFolding.Tetrahedral.NormalizationChecks

#print axioms ProteinFolding.Tetrahedral.normalizeSite_self
#print axioms ProteinFolding.Tetrahedral.adj_normalizeSite_iff
#print axioms ProteinFolding.Tetrahedral.exists_normalized_bounded_fold
#print axioms ProteinFolding.Tetrahedral.hp_certificate_iff
#print axioms ProteinFolding.Tetrahedral.hp_inNP_of_verifier_polyTime

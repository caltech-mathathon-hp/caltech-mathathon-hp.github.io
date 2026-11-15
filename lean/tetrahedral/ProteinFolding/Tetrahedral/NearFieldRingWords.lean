import ProteinFolding.Tetrahedral.NearFieldDimerChainConcatenation

/-! Concatenating three ring sides and their two corner PPPs gives exactly
the literal dimer-chain word used by the source-only reduction. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem dimerChain_three_sides (n : ℕ) (hn : 0 < n) :
    (((dimerChain n ++ [.P, .P, .P]) ++ dimerChain n) ++ [.P, .P, .P]) ++ dimerChain n =
      dimerChain (3 * n) := by
  have h2 : (dimerChain n ++ [.P, .P, .P]) ++ dimerChain n = dimerChain (n + n) := by
    simpa only [List.append_assoc] using (dimerChain_add n n hn hn).symm
  have h3 : (dimerChain (n + n) ++ [.P, .P, .P]) ++ dimerChain n =
      dimerChain ((n + n) + n) := by
    simpa only [List.append_assoc] using (dimerChain_add (n + n) n (by omega) hn).symm
  rw [h2, h3]
  congr 1
  omega

end ProteinFolding.Tetrahedral.NearField

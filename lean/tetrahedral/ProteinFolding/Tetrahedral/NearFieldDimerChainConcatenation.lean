import ProteinFolding.Tetrahedral.NearFieldDimerChainWords

/-! Joining positive dimer chains by exactly one three-P linker. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem repeatWord_add (w : Sequence) (a b : ℕ) : repeatWord w (a + b) = repeatWord w a ++ repeatWord w b := by
  induction a with
  | zero => simp only [Nat.zero_add, repeatWord, List.nil_append]
  | succ a ih =>
    have he : a + 1 + b = (a + b) + 1 := by omega
    rw [he]
    simp only [repeatWord, ih, List.append_assoc]

theorem dimerChain_add (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    dimerChain (a + b) = dimerChain a ++ List.replicate 3 Residue.P ++ dimerChain b := by
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      have he : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      change dimerChain (a + 1 + (b + 1)) = _
      rw [he]
      simp only [dimerChain]
      have hn : a + b + 1 = a + (b + 1) := by omega
      rw [hn, repeatWord_add]
      simp only [repeatWord, List.append_assoc]
      rfl

end ProteinFolding.Tetrahedral.NearField

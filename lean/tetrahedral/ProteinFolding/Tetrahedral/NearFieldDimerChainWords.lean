import ProteinFolding.Tetrahedral.WordPieces

/-! Exact residue indexing in the literal dimer-chain word. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem dimerChain_succ_recurrence (q : ℕ) :
    dimerChain (q + 2) = [.H, .H, .P, .P, .P] ++ dimerChain (q + 1) := by
  simp only [dimerChain, repeatWord, List.append_assoc]

theorem dimerChain_succ_length (q : ℕ) : (dimerChain (q + 1)).length = 5 * q + 2 := by
  have h := dimerChain_length (q + 1) (by omega)
  omega

theorem dimerChain_getElem_mod5 (q n : ℕ) (hn : n < (dimerChain (q + 1)).length) :
    (dimerChain (q + 1))[n]? = some (if n % 5 < 2 then Residue.H else Residue.P) := by
  induction q generalizing n with
  | zero =>
    have hnb : n < 2 := by simpa only [dimerChain_succ_length, Nat.mul_zero, Nat.zero_add] using hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> rfl
  | succ q ih =>
    have hrec := dimerChain_succ_recurrence q
    change (dimerChain (q + 2))[n]? = _
    rw [hrec]
    by_cases hsmall : n < 5
    · rw [List.getElem?_append_left (by simpa only [List.length_cons, List.length_nil] using hsmall)]
      have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
      simp only [List.length_cons, List.length_nil]
      have htail : n - 5 < (dimerChain (q + 1)).length := by
        rw [dimerChain_succ_length] at hn ⊢
        omega
      have hmod : (n - 5) % 5 = n % 5 := by omega
      simpa only [hmod] using ih (n - 5) htail

theorem dimerChain_get_mod5 (q : ℕ) (i : Fin (dimerChain (q + 1)).length) :
    (dimerChain (q + 1)).get i = if i.val % 5 < 2 then .H else .P := by
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp (dimerChain_getElem_mod5 q i.val i.isLt)
  simpa only [List.get_eq_getElem] using hget

end ProteinFolding.Tetrahedral.NearField

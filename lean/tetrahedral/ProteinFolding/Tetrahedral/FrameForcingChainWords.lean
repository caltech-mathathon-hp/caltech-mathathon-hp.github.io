import ProteinFolding.Tetrahedral.FrameForcingDimerChains

/-! Literal positions of each HH pair and each intervening PPP in a dimer
chain. These are statements about the written word. -/

namespace ProteinFolding.Tetrahedral

theorem IsDimerStart.of_factor (S pre body post : Sequence)
    (heq : S = pre ++ body ++ post) (i : ℕ) (hi : IsDimerStart body i) :
    IsDimerStart S (pre.length + i) := by
  have hbound := (List.getElem?_eq_some_iff.mp hi.2.2.2).choose
  have hget (r : ℕ) (hr : r ≤ 3) : S[pre.length + i + r]? = body[i + r]? := by
    simpa only [Nat.add_assoc] using word_factor_getElem S pre body post heq (i + r) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (hget 0 (by decide)).trans hi.1
  · exact (hget 1 (by decide)).trans hi.2.1
  · exact (hget 2 (by decide)).trans hi.2.2.1
  · exact (hget 3 le_rfl).trans hi.2.2.2

theorem capped_dimer_recurrence (q : ℕ) :
    capWord (dimerChain (q + 2)) = [.P, .H, .H, .P, .P] ++ capWord (dimerChain (q + 1)) := by
  simp only [capWord, dimerChain, repeatWord, List.cons_append, List.nil_append, List.append_assoc]

theorem capped_dimer_start (q i : ℕ) (hi : i < q) :
    IsDimerStart (capWord (dimerChain q)) (5 * i) := by
  induction q generalizing i with
  | zero => omega
  | succ q ih =>
    by_cases hiz : i = 0
    · subst i
      cases q <;> simp [IsDimerStart, capWord, dimerChain, repeatWord]
    · cases q with
      | zero => omega
      | succ q =>
        have hlocal := ih (i - 1) (by omega)
        have hfactor : capWord (dimerChain (q + 1 + 1)) =
            [.P, .H, .H, .P, .P] ++ capWord (dimerChain (q + 1)) ++ [] := by
          simpa only [List.append_nil, Nat.add_assoc] using capped_dimer_recurrence q
        have h := IsDimerStart.of_factor _ _ _ _ hfactor (5 * (i - 1)) hlocal
        have hindex : ([.P, .H, .H, .P, .P] : Sequence).length + 5 * (i - 1) = 5 * i := by
          simp only [List.length_cons, List.length_nil]
          omega
        simpa only [hindex] using h

theorem capped_dimer_middle_P (q i : ℕ) (hi : i + 1 < q) :
    (capWord (dimerChain q))[5 * i + 4]? = some .P := by
  induction q generalizing i with
  | zero => omega
  | succ q ih =>
    cases q with
    | zero => omega
    | succ q =>
      rw [capped_dimer_recurrence q]
      by_cases hiz : i = 0
      · subst i
        simp
      · have hindex : 5 * i + 4 = 5 + (5 * (i - 1) + 4) := by omega
        rw [hindex, List.getElem?_append_right (by simp)]
        simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
        exact ih (i - 1) (by omega)

theorem capped_dimer_P3 (q i : ℕ) (hi : i + 1 < q) :
    (capWord (dimerChain q))[5 * i + 2]? = some .H ∧
      (capWord (dimerChain q))[5 * i + 6]? = some .H ∧
      (∀ r, 0 < r → r < 4 → (capWord (dimerChain q))[5 * i + 2 + r]? = some .P) := by
  have hfirst := capped_dimer_start q i (by omega)
  have hsecond := capped_dimer_start q (i + 1) hi
  have hindex₀ : 5 * (i + 1) = 5 * i + 5 := by omega
  have hindex₁ : 5 * (i + 1) + 1 = 5 * i + 6 := by omega
  refine ⟨hfirst.2.2.1, by simpa only [hindex₁] using hsecond.2.1, ?_⟩
  intro r hr₀ hr₄
  have hr : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr with rfl | rfl | rfl
  · simpa only [Nat.add_assoc] using hfirst.2.2.2
  · simpa only [Nat.add_assoc] using capped_dimer_middle_P q i hi
  · simpa only [Nat.add_assoc, hindex₀] using hsecond.1

end ProteinFolding.Tetrahedral

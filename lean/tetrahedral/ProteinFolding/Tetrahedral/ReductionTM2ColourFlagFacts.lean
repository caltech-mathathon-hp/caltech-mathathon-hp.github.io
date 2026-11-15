import ProteinFolding.Tetrahedral.ReductionTM2PipelineFacts

/-! The computed parity flags refer to consecutive occurrences in the unit
list. Equal endpoint records retain their original positions. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.ColourFlags

theorem flags_first (seed : Bool) (c : Colours) (cs : List Colours) :
    (flags (seed, c :: cs))[0]'(by rw [flags_length]; simp) = (seed == c.1) := by
  simp only [flags_cons, List.getElem_cons_zero]

theorem flags_next (seed : Bool) (cs : List Colours) (i : ℕ) (hi : i + 1 < cs.length) :
    (flags (seed, cs))[i + 1]'(by rw [flags_length]; exact hi) =
      ((cs[i]'(by omega)).2 == (cs[i + 1]'hi).1) := by
  induction cs generalizing seed i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons c cs ih =>
    cases i with
    | zero =>
      cases cs with
      | nil => simp only [List.length_cons, List.length_nil] at hi; omega
      | cons d ds =>
        simp only [flags_cons, List.getElem_cons_succ, List.getElem_cons_zero]
    | succ i =>
      have htail : i + 1 < cs.length := by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hi
      simpa only [flags_cons, List.getElem_cons_succ] using ih c.2 i htail

theorem flags_first_eq_true_iff (seed : Bool) (c : Colours) (cs : List Colours) :
    (flags (seed, c :: cs))[0]'(by rw [flags_length]; simp) = true ↔ seed = c.1 := by
  rw [flags_first, beq_iff_eq]

theorem flags_next_eq_true_iff (seed : Bool) (cs : List Colours) (i : ℕ)
    (hi : i + 1 < cs.length) :
    (flags (seed, cs))[i + 1]'(by rw [flags_length]; exact hi) = true ↔
      (cs[i]'(by omega)).2 = (cs[i + 1]'hi).1 := by
  rw [flags_next, beq_iff_eq]

end ProteinFolding.Tetrahedral.ReductionTM2.ColourFlags

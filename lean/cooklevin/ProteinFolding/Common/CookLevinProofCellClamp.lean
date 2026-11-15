import ProteinFolding.Common.CookLevinProofCells

/-! The selected-cell truth table has only finitely many distinct cases.
Once the position reaches the replacement bound, its relative query offset
is independent of the position. -/

namespace ProteinFolding.SAT.CookLevinCellClamp

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinCells

theorem selectCell_stable (tm : FinTM2) (k : tm.K) (n : ℕ)
    (hn : replacementBound tm ≤ n) (r : Replacement tm) (q : CellWindow tm k) :
    selectCell tm k n r q = selectCell tm k (replacementBound tm) r q := by
  have hr := (r.2.2 k).property
  have hnr : ¬ n < ((r.2.2 k).val).length := by omega
  have hbr : ¬ replacementBound tm < ((r.2.2 k).val).length := by omega
  simp only [selectCell, dif_neg hnr, dif_neg hbr]
  congr 1
  apply Fin.ext
  dsimp only [cellBase]
  omega

theorem selectCell_clamp (tm : FinTM2) (k : tm.K) (n : ℕ)
    (r : Replacement tm) (q : CellWindow tm k) :
    selectCell tm k n r q = selectCell tm k (min n (replacementBound tm)) r q := by
  by_cases hn : n ≤ replacementBound tm
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega)]
    exact selectCell_stable tm k n (by omega) r q

theorem cellAllowed_clamp (tm : FinTM2) (k : tm.K) (n : ℕ) :
    cellAllowed tm k n = cellAllowed tm k (min n (replacementBound tm)) := by
  funext bs
  apply Bool.eq_iff_iff.mpr
  rw [cellAllowed_iff, cellAllowed_iff]
  simp only [selectCell_clamp tm k n]

theorem cellCNF_clamp (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ) :
    cellCNF tm k n vars = cellCNF tm k (min n (replacementBound tm)) vars := by
  unfold cellCNF
  rw [cellAllowed_clamp tm k n]

end ProteinFolding.SAT.CookLevinCellClamp

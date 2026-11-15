import ProteinFolding.Common.CookLevinProofRows
import Mathlib.Logic.Equiv.Fin.Basic

/-! Arithmetic indexing of the unchanged semantic tableau row. All finite
enumerations below depend only on the fixed machine. The growing position
index is explicit: after the fixed control/window/replacement block, each
position contributes one fixed-size cell/query block. -/

namespace ProteinFolding.SAT.CookLevinRowIndex

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinCells CookLevinPaddedWindow CookLevinRows

abbrev CellChoice (tm : FinTM2) := Σ k, Option (Symbol tm k)
abbrev QueryChoice (tm : FinTM2) := Σ k, CellWindow tm k
abbrev FixedBit (tm : FinTM2) := Control tm ⊕ PaddedWindow tm ⊕ Replacement tm
abbrev MovingChoice (tm : FinTM2) := CellChoice tm ⊕ QueryChoice tm

noncomputable def controlCount (tm : FinTM2) : ℕ := Fintype.card (Control tm)
noncomputable def windowCount (tm : FinTM2) : ℕ := Fintype.card (PaddedWindow tm)
noncomputable def replacementCount (tm : FinTM2) : ℕ := Fintype.card (Replacement tm)

noncomputable def cellCount (tm : FinTM2) : ℕ := by
  letI := tm.kFin
  exact Fintype.card (CellChoice tm)

noncomputable def queryCount (tm : FinTM2) : ℕ := by
  letI := tm.kFin
  exact Fintype.card (QueryChoice tm)

noncomputable def base (tm : FinTM2) : ℕ := controlCount tm + windowCount tm + replacementCount tm
noncomputable def slope (tm : FinTM2) : ℕ := cellCount tm + queryCount tm

noncomputable def controlIndex (tm : FinTM2) : Control tm ≃ Fin (controlCount tm) := Fintype.equivFin _
noncomputable def windowIndex (tm : FinTM2) : PaddedWindow tm ≃ Fin (windowCount tm) := Fintype.equivFin _
noncomputable def replacementIndex (tm : FinTM2) : Replacement tm ≃ Fin (replacementCount tm) := Fintype.equivFin _

noncomputable def cellIndex (tm : FinTM2) : CellChoice tm ≃ Fin (cellCount tm) := by
  letI := tm.kFin
  exact Fintype.equivFin _

noncomputable def queryIndex (tm : FinTM2) : QueryChoice tm ≃ Fin (queryCount tm) := by
  letI := tm.kFin
  exact Fintype.equivFin _

def interleave (tm : FinTM2) (M : ℕ) :
    Bit tm M ≃ FixedBit tm ⊕ (Fin M × MovingChoice tm) where
  toFun
    | .inl c => .inl (.inl c)
    | .inr (.inl ⟨k, n, b⟩) => .inr (n, .inl ⟨k, b⟩)
    | .inr (.inr (.inl w)) => .inl (.inr (.inl w))
    | .inr (.inr (.inr (.inl r))) => .inl (.inr (.inr r))
    | .inr (.inr (.inr (.inr ⟨k, n, q⟩))) => .inr (n, .inr ⟨k, q⟩)
  invFun
    | .inl (.inl c) => .inl c
    | .inl (.inr (.inl w)) => .inr (.inr (.inl w))
    | .inl (.inr (.inr r)) => .inr (.inr (.inr (.inl r)))
    | .inr (n, .inl ⟨k, b⟩) => .inr (.inl ⟨k, n, b⟩)
    | .inr (n, .inr ⟨k, q⟩) => .inr (.inr (.inr (.inr ⟨k, n, q⟩)))
  left_inv x := by
    rcases x with c | ⟨k, n, b⟩ | w | r | ⟨k, n, q⟩ <;> rfl
  right_inv x := by
    rcases x with (c | w | r) | ⟨n, (⟨k, b⟩ | ⟨k, q⟩)⟩ <;> rfl

noncomputable def fixedIndex (tm : FinTM2) : FixedBit tm ≃ Fin (base tm) :=
  ((Equiv.sumCongr (controlIndex tm)
    ((Equiv.sumCongr (windowIndex tm) (replacementIndex tm)).trans finSumFinEquiv)).trans
      finSumFinEquiv).trans (finCongr (by unfold base; omega))

noncomputable def movingIndex (tm : FinTM2) : MovingChoice tm ≃ Fin (slope tm) :=
  (Equiv.sumCongr (cellIndex tm) (queryIndex tm)).trans finSumFinEquiv

theorem base_eq (tm : FinTM2) : base tm = widthBase tm := rfl
theorem slope_eq (tm : FinTM2) : slope tm = widthSlope tm := rfl

theorem width_eq (tm : FinTM2) (M : ℕ) : base tm + M * slope tm = width tm M := by
  rw [width_linear]
  rfl

noncomputable def arithmeticBitIndex (tm : FinTM2) (M : ℕ) : Bit tm M ≃ Fin (width tm M) :=
  ((interleave tm M).trans
    ((Equiv.sumCongr (fixedIndex tm)
      ((Equiv.prodCongr (Equiv.refl (Fin M)) (movingIndex tm)).trans finProdFinEquiv)).trans
        finSumFinEquiv)).trans (finCongr (width_eq tm M))

@[simp] theorem arithmeticBitIndex_control (tm : FinTM2) (M : ℕ) (c : Control tm) :
    (arithmeticBitIndex tm M (controlTag tm M c)).val = (controlIndex tm c).val := rfl

@[simp] theorem arithmeticBitIndex_window (tm : FinTM2) (M : ℕ) (w : PaddedWindow tm) :
    (arithmeticBitIndex tm M (windowTag tm M w)).val = controlCount tm + (windowIndex tm w).val := rfl

@[simp] theorem arithmeticBitIndex_replacement (tm : FinTM2) (M : ℕ) (r : Replacement tm) :
    (arithmeticBitIndex tm M (replacementTag tm M r)).val =
      controlCount tm + windowCount tm + (replacementIndex tm r).val := by
  change controlCount tm + (windowCount tm + (replacementIndex tm r).val) = _
  omega

@[simp] theorem arithmeticBitIndex_cell (tm : FinTM2) (M : ℕ)
    (k : tm.K) (n : Fin M) (b : Option (Symbol tm k)) :
    (arithmeticBitIndex tm M (cellTag tm M k n b)).val =
      base tm + n.val * slope tm + (cellIndex tm ⟨k, b⟩).val := by
  change base tm + ((cellIndex tm ⟨k, b⟩).val + slope tm * n.val) = _
  rw [Nat.mul_comm (slope tm)]
  omega

@[simp] theorem arithmeticBitIndex_query (tm : FinTM2) (M : ℕ)
    (k : tm.K) (n : Fin M) (q : CellWindow tm k) :
    (arithmeticBitIndex tm M (queryTag tm M k n q)).val =
      base tm + n.val * slope tm + cellCount tm + (queryIndex tm ⟨k, q⟩).val := by
  change base tm + ((cellCount tm + (queryIndex tm ⟨k, q⟩).val) + slope tm * n.val) = _
  rw [Nat.mul_comm (slope tm)]
  omega

theorem arithmeticBitIndex_lt (tm : FinTM2) (M : ℕ) (b : Bit tm M) :
    (arithmeticBitIndex tm M b).val < base tm + M * slope tm := by
  rw [width_eq]
  exact (arithmeticBitIndex tm M b).isLt

theorem arithmeticBitIndex_injective (tm : FinTM2) (M : ℕ) :
    Function.Injective (arithmeticBitIndex tm M) := (arithmeticBitIndex tm M).injective

theorem arithmeticBitIndex_surjective (tm : FinTM2) (M : ℕ) :
    Function.Surjective (arithmeticBitIndex tm M) := (arithmeticBitIndex tm M).surjective

noncomputable def arithmeticReference (tm : FinTM2) (M t : ℕ) (b : Bit tm M) : ℕ :=
  t * width tm M + (arithmeticBitIndex tm M b).val

@[simp] theorem arithmeticReference_control (tm : FinTM2) (M t : ℕ) (c : Control tm) :
    arithmeticReference tm M t (controlTag tm M c) =
      t * (base tm + M * slope tm) + (controlIndex tm c).val := by
  rw [arithmeticReference, arithmeticBitIndex_control, ← width_eq]

@[simp] theorem arithmeticReference_window (tm : FinTM2) (M t : ℕ) (w : PaddedWindow tm) :
    arithmeticReference tm M t (windowTag tm M w) =
      t * (base tm + M * slope tm) + controlCount tm + (windowIndex tm w).val := by
  rw [arithmeticReference, arithmeticBitIndex_window, ← width_eq]
  omega

@[simp] theorem arithmeticReference_replacement (tm : FinTM2) (M t : ℕ) (r : Replacement tm) :
    arithmeticReference tm M t (replacementTag tm M r) =
      t * (base tm + M * slope tm) + controlCount tm + windowCount tm + (replacementIndex tm r).val := by
  rw [arithmeticReference, arithmeticBitIndex_replacement, ← width_eq]
  omega

@[simp] theorem arithmeticReference_cell (tm : FinTM2) (M t : ℕ)
    (k : tm.K) (n : Fin M) (b : Option (Symbol tm k)) :
    arithmeticReference tm M t (cellTag tm M k n b) =
      t * (base tm + M * slope tm) + base tm + n.val * slope tm + (cellIndex tm ⟨k, b⟩).val := by
  rw [arithmeticReference, arithmeticBitIndex_cell, ← width_eq]
  omega

@[simp] theorem arithmeticReference_query (tm : FinTM2) (M t : ℕ)
    (k : tm.K) (n : Fin M) (q : CellWindow tm k) :
    arithmeticReference tm M t (queryTag tm M k n q) =
      t * (base tm + M * slope tm) + base tm + n.val * slope tm + cellCount tm + (queryIndex tm ⟨k, q⟩).val := by
  rw [arithmeticReference, arithmeticBitIndex_query, ← width_eq]
  omega

theorem arithmeticReference_lt (tm : FinTM2) (M T t : ℕ) (ht : t ≤ T) (b : Bit tm M) :
    arithmeticReference tm M t b < (T + 1) * width tm M := by
  have hm := Nat.mul_le_mul_right (width tm M) ht
  have hb := (arithmeticBitIndex tm M b).isLt
  simp only [arithmeticReference, Nat.add_mul, Nat.one_mul]
  omega

end ProteinFolding.SAT.CookLevinRowIndex

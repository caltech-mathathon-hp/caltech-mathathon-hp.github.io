import ProteinFolding.Tetrahedral.ReductionTM2Instance
import ProteinFolding.Cubic.Proofs.PackingGuardComputable
import ProteinFolding.Common.TM2Conditional

/-! The exact-capacity source guard on every raw typed input.
The item check tests positivity only; evenness is not a restriction of the
tetrahedral source language. Invalid inputs map to an explicitly rejecting
HP instance. Every guard and output branch has an actual finite TM2. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

namespace Guard

structure ItemState where
  valid : Bool
  seen : Bool
  deriving DecidableEq, Fintype

def itemInitial (valid : Bool) : ItemState := ⟨valid, false⟩

def itemStep (st : ItemState) : Bool → ItemState
  | true => ⟨st.valid, true⟩
  | false => ⟨st.valid && st.seen, false⟩

theorem unary_fold (st : ItemState) (n : ℕ) :
    (unaryEncodeNat n).foldl itemStep st =
      ⟨st.valid, st.seen || decide (0 < n)⟩ := by
  induction n generalizing st with
  | zero => simp [unaryEncodeNat]
  | succ n ih => simp [unaryEncodeNat, itemStep, ih]

theorem item_block_fold (valid : Bool) (n : ℕ) :
    (unaryEncodeNat n ++ [false]).foldl itemStep (itemInitial valid) =
      itemInitial (valid && decide (0 < n)) := by
  rw [List.foldl_append, unary_fold]
  simp [itemStep, itemInitial]

theorem items_fold (valid : Bool) (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).foldl itemStep (itemInitial valid) =
      itemInitial (valid && decide (∀ a ∈ xs, 0 < a)) := by
  induction xs generalizing valid with
  | nil => simp [Packing.itemEncoding, SAT.encTerminated, itemInitial]
  | cons a xs ih =>
    simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons] at ih ⊢
    rw [List.foldl_append, item_block_fold, ih]
    simp only [List.forall_mem_cons, Bool.decide_and, Bool.and_assoc]

noncomputable def itemsComputable :
    TM2ComputableInPolyTime Packing.itemEncoding finEncodingBoolBool
      (fun xs => decide (∀ a ∈ xs, 0 < a)) := by
  let h := TM2WordFold.computable Bool ItemState itemStep ItemState.valid (itemInitial true)
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun xs => by
      have hout := h.outputsFun (Packing.itemEncoding.encode xs)
      have hf : (List.foldl itemStep (itemInitial true) (Packing.itemEncoding.encode xs)).valid =
          decide (∀ a ∈ xs, 0 < a) := by
        rw [items_fold]
        simp only [itemInitial, Bool.true_and]
      rw [hf] at hout
      simpa only [wordEncoding, id_eq] using hout }

def sourceGuard (I : PackingSource.Instance) : Bool :=
  decide (0 < I.capacity ∧ 0 < I.bins ∧
    (∀ a ∈ I.sizes, 0 < a) ∧ I.sizes.sum = I.capacity * I.bins)

theorem sourceGuard_eq_true (I : PackingSource.Instance) :
    sourceGuard I = true ↔
      Packing.WellFormed I ∧ I.sizes.sum = I.bins * I.capacity := by
  simp only [sourceGuard, decide_eq_true_eq, Packing.WellFormed, Nat.mul_comm]
  tauto

theorem accepts_guard {I : PackingSource.Instance} (h : PackingSource.Accepts I) :
    sourceGuard I = true :=
  (sourceGuard_eq_true I).2 ⟨h.1, h.2.1⟩

noncomputable def sourceItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (∀ a ∈ I.sizes, 0 < a)) :=
  compose Packing.sizesComputable itemsComputable

noncomputable def sourceGuardComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool sourceGuard := by
  let hp := compose (pairComputable CubicPacking.Guard.capacityPositiveComputable
    CubicPacking.Guard.binsPositiveComputable) TM2Boolean.andComputable
  let ht := compose (pairComputable sourceItemsComputable
    CubicPacking.Guard.totalEqualityComputable) TM2Boolean.andComputable
  have h := compose (pairComputable hp ht) TM2Boolean.andComputable
  change TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool (fun I => sourceGuard I)
  simpa only [Function.comp_def, sourceGuard, Bool.decide_and, Bool.and_assoc] using h

end Guard

def rejectingInstance : HPInstance := ⟨[], 1⟩

theorem rejectingInstance_not_accepts : ¬ rejectingInstance.Accepts := by
  rintro ⟨f, hf⟩
  have hz : bondCount [] f = 0 := by
    simp [bondCount, hhBonds]
  change (1 : ℤ) ≤ (bondCount [] f : ℤ) at hf
  rw [hz] at hf
  norm_num at hf

def guardedPreparedInstance (x : WordInput) : HPInstance :=
  if Guard.sourceGuard x.1.1 then preparedInstance x else rejectingInstance

set_option maxHeartbeats 1200000 in
noncomputable def guardedPreparedInstanceComputable :
    TM2ComputableInPolyTime wordInputEncoding hpEncoding guardedPreparedInstance :=
  TM2Conditional.iteComputable
    (compose wordSourceComputable Guard.sourceGuardComputable)
    preparedInstanceComputable (TM2Constants.constantComputable _ _ rejectingInstance)

theorem guardedPreparedInstance_of_guard (x : WordInput)
    (h : Guard.sourceGuard x.1.1 = true) :
    guardedPreparedInstance x = preparedInstance x := by
  simp [guardedPreparedInstance, h]

theorem guardedPreparedInstance_rejects (x : WordInput)
    (h : Guard.sourceGuard x.1.1 = false) :
    ¬ (guardedPreparedInstance x).Accepts := by
  simpa [guardedPreparedInstance, h] using rejectingInstance_not_accepts

theorem guardedPreparedInstance_correct (x : WordInput)
    (hvalid : Guard.sourceGuard x.1.1 = true →
      ((preparedInstance x).Accepts ↔ PackingSource.Accepts x.1.1)) :
    (guardedPreparedInstance x).Accepts ↔ PackingSource.Accepts x.1.1 := by
  cases hg : Guard.sourceGuard x.1.1 with
  | false =>
    have hs : ¬ PackingSource.Accepts x.1.1 := by
      intro ha
      have ht := Guard.accepts_guard ha
      simp [hg] at ht
    simp only [guardedPreparedInstance, hg, Bool.false_eq_true, ↓reduceIte]
    exact iff_of_false rejectingInstance_not_accepts hs
  | true =>
    rw [guardedPreparedInstance_of_guard x hg]
    exact hvalid hg

end ProteinFolding.Tetrahedral.ReductionTM2

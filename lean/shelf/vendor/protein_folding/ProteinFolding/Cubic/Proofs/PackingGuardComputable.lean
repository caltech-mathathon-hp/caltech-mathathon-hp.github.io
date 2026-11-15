import ProteinFolding.Cubic.Proofs.PackingWordSource
import ProteinFolding.Cubic.Proofs.PackingBalanceComputable
import ProteinFolding.Cubic.Proofs.VerifierPerfectEquality
import ProteinFolding.Common.TM2WordFold
import ProteinFolding.Common.TM2Boolean

/-! Actual finite-machine computation of the modified-packing input guard.
A three-bit finite state checks positive even item fields in the canonical
unary item code. Unary field nonemptiness checks positive capacity/bin count;
the existing unary multiplier and equality machines check the total load. -/

namespace ProteinFolding.CubicPacking.Guard

open Computability Turing TM2CompositionPoly TM2ProductMap

structure ItemState where
  valid : Bool
  odd : Bool
  seen : Bool
  deriving DecidableEq, Fintype

def itemInitial (valid : Bool) : ItemState := ⟨valid, false, false⟩

def itemStep (st : ItemState) : Bool → ItemState
  | true => ⟨st.valid, !st.odd, true⟩
  | false => ⟨st.valid && st.seen && !st.odd, false, false⟩

theorem unary_succ_append (n : ℕ) :
    unaryEncodeNat (n + 1) = unaryEncodeNat n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryEncodeNat] using congrArg (true :: ·) ih

theorem item_unary_fold (valid : Bool) (n : ℕ) :
    (unaryEncodeNat n).foldl itemStep (itemInitial valid) =
      ⟨valid, decide (n % 2 = 1), decide (0 < n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unary_succ_append, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, itemStep]
    have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases ho : n % 2 = 1
    · have he : (n + 1) % 2 ≠ 1 := by omega
      simp [ho, he]
    · have he : (n + 1) % 2 = 1 := by omega
      simp [ho, he]

theorem positive_even_bit (n : ℕ) :
    (decide (0 < n) && !decide (n % 2 = 1)) = decide (0 < n ∧ Even n) := by
  have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hn : n = 0
  · subst n; decide
  · have hp : 0 < n := by omega
    by_cases ho : n % 2 = 1
    · have he : ¬ Even n := by rw [Nat.even_iff]; omega
      simp [hp, ho, he]
    · have he : Even n := by rw [Nat.even_iff]; omega
      simp [hp, ho, he]

theorem item_block_fold (valid : Bool) (n : ℕ) :
    (unaryEncodeNat n ++ [false]).foldl itemStep (itemInitial valid) =
      itemInitial (valid && decide (0 < n ∧ Even n)) := by
  rw [List.foldl_append, item_unary_fold]
  simp only [List.foldl_cons, List.foldl_nil, itemStep, itemInitial]
  rw [Bool.and_assoc, positive_even_bit]

theorem items_fold (valid : Bool) (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).foldl itemStep (itemInitial valid) =
      itemInitial (valid && decide (∀ a ∈ xs, 0 < a ∧ Even a)) := by
  induction xs generalizing valid with
  | nil => simp [Packing.itemEncoding, SAT.encTerminated, itemInitial]
  | cons a xs ih =>
    simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons] at ih ⊢
    rw [List.foldl_append, item_block_fold, ih]
    simp only [List.forall_mem_cons, Bool.decide_and, Bool.and_assoc]

/-- A finite eight-state machine checks every positive/even unary item field. -/
noncomputable def itemsComputable :
    TM2ComputableInPolyTime Packing.itemEncoding finEncodingBoolBool
      (fun xs => decide (∀ a ∈ xs, 0 < a ∧ Even a)) := by
  let h := TM2WordFold.computable Bool ItemState itemStep ItemState.valid (itemInitial true)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun xs => by
        have hout := h.outputsFun (Packing.itemEncoding.encode xs)
        have hf : (List.foldl itemStep (itemInitial true) (Packing.itemEncoding.encode xs)).valid =
            decide (∀ a ∈ xs, 0 < a ∧ Even a) := by
          rw [items_fold]
          simp only [itemInitial, Bool.true_and]
        rw [hf] at hout
        simpa only [wordEncoding, id_eq] using hout }

theorem unary_nonempty_fold (n : ℕ) (seen : Bool) :
    (unaryEncodeNat n).foldl (fun _ _ => true) seen = (seen || decide (0 < n)) := by
  induction n generalizing seen with
  | zero => simp [unaryEncodeNat]
  | succ n ih => simp [unaryEncodeNat, ih]

noncomputable def positiveComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat finEncodingBoolBool
      (fun n => decide (0 < n)) := by
  let h := TM2WordFold.computable Bool Bool (fun _ _ => true) id false
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        have hout := h.outputsFun (unaryEncodeNat n)
        simpa only [wordEncoding, unaryFinEncodingNat, unary_nonempty_fold, Bool.false_or, id_eq] using hout }

noncomputable def capacityPositiveComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (0 < I.capacity)) :=
  compose Packing.capacityComputable positiveComputable

noncomputable def binsPositiveComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (0 < I.bins)) :=
  compose Packing.binsComputable positiveComputable

noncomputable def sourceItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (∀ a ∈ I.sizes, 0 < a ∧ Even a)) :=
  compose Packing.sizesComputable itemsComputable

noncomputable def totalEqualityComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (I.sizes.sum = I.capacity * I.bins)) :=
  compose (pairComputable Packing.totalSizeComputable Packing.totalCapacityComputable)
    PerfectUnaryEquality.unaryEqualityComputable

/-- Every side condition in the exact frozen auxiliary source guard is
computed by actual finite TM2 machines. No guard or arithmetic hypothesis remains. -/
noncomputable def sourceGuardComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool sourceGuard := by
  let hp := compose (pairComputable capacityPositiveComputable binsPositiveComputable)
    TM2Boolean.andComputable
  let ht := compose (pairComputable sourceItemsComputable totalEqualityComputable)
    TM2Boolean.andComputable
  have h := compose (pairComputable hp ht) TM2Boolean.andComputable
  change TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool (fun I => sourceGuard I)
  simpa only [Function.comp_def, sourceGuard, Bool.decide_and, Bool.and_assoc] using h

end ProteinFolding.CubicPacking.Guard

import ProteinFolding.Cubic.Proofs.PackingBalance
import ProteinFolding.Cubic.Proofs.VerifierPerfectUnary
import ProteinFolding.Common.TM2UnarySubtraction
import ProteinFolding.Common.TM2WordSubstitution
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.ComplexityComposition

/-! The ordinary-to-modified packing reduction as an actual polynomial-time
TM2. Unary field projections, multiplication, truncated subtraction, fixed
word substitutions and concatenation construct the exact target encoding.
No numerical value is expanded from a binary source field: every source
number already has the unary encoding specified in `PackingSources`. -/

namespace ProteinFolding.Packing

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections

section CodeTransport

variable {A B : Type} {ea : FinEncoding A} {eb : FinEncoding B} {f : A → B}

noncomputable def toCode (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime ea (wordEncoding eb.Γ) (fun x => eb.encode (f x)) :=
  { toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := h.outputsFun }

noncomputable def ofCode (h : TM2ComputableInPolyTime ea (wordEncoding eb.Γ)
    (fun x => eb.encode (f x))) : TM2ComputableInPolyTime ea eb f :=
  { toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := h.outputsFun }

end CodeTransport

noncomputable def fieldsComputable : TM2ComputableInPolyTime instanceEncoding fieldsEncoding
    (fun I : Instance => (I.sizes, (I.capacity, I.bins))) := by
  let h := idComputableInPolyTime fieldsEncoding
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun (I.sizes, (I.capacity, I.bins)) }

noncomputable def sizesComputable : TM2ComputableInPolyTime instanceEncoding itemEncoding
    Instance.sizes := compose (g := fun p : List ℕ × (ℕ × ℕ) => p.1) fieldsComputable
  (fstComputable itemEncoding (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def numericalFieldsComputable : TM2ComputableInPolyTime instanceEncoding
    (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) (fun I : Instance => (I.capacity, I.bins)) :=
  compose fieldsComputable
    (sndComputable itemEncoding (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def capacityComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    Instance.capacity := compose (g := fun p : ℕ × ℕ => p.1) numericalFieldsComputable
  (fstComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def binsComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    Instance.bins := compose (g := fun p : ℕ × ℕ => p.2) numericalFieldsComputable
  (sndComputable unaryFinEncodingNat unaryFinEncodingNat)

def keepUnit : Bool → Option Bool
  | true => some true
  | false => none

theorem keepUnit_unary (n : ℕ) : (unaryEncodeNat n).filterMap keepUnit = unaryEncodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, keepUnit, ih]

theorem keepUnit_items (xs : List ℕ) :
    (itemEncoding.encode xs).filterMap keepUnit = unaryEncodeNat xs.sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [itemEncoding, SAT.encTerminated, List.flatMap_cons] at *
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      keepUnit, keepUnit_unary, List.sum_cons, ih, List.append_nil]
    exact (PerfectUnaryMultiplication.unary_append a xs.sum).symm

noncomputable def totalSizeComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    (fun I : Instance => I.sizes.sum) := by
  apply ofCode (f := fun I : Instance => I.sizes.sum)
  simpa only [Function.comp_def, keepUnit_items, unaryFinEncodingNat] using
    compose (toCode sizesComputable) (filterMapComputable Bool Bool keepUnit)

noncomputable def totalCapacityComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    (fun I : Instance => I.capacity * I.bins) :=
  compose numericalFieldsComputable PerfectUnaryMultiplication.unaryMulComputable

noncomputable def slackComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    (fun I : Instance => I.capacity * I.bins - I.sizes.sum) :=
  compose (pairComputable totalCapacityComputable totalSizeComputable)
    TM2UnarySubtraction.subtractionComputable

def unitItem : Bool → List Bool
  | true => [true, false]
  | false => []

theorem unitItem_words (n : ℕ) :
    (unaryEncodeNat n).flatMap unitItem = itemEncoding.encode (List.replicate n 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryEncodeNat, List.replicate_succ, unitItem,
      itemEncoding, SAT.encTerminated] using congrArg (fun w => true :: false :: w) ih

noncomputable def slackItemsWordComputable : TM2ComputableInPolyTime instanceEncoding (wordEncoding Bool)
    (fun I : Instance => itemEncoding.encode (List.replicate (I.capacity * I.bins - I.sizes.sum) 1)) := by
  simpa only [Function.comp_def, unaryFinEncodingNat, unitItem_words] using compose (toCode slackComputable)
    (TM2WordSubstitution.flatMapComputable unitItem 2 (by intro b; cases b <;> decide))

theorem itemEncoding_append (xs ys : List ℕ) :
    itemEncoding.encode (xs ++ ys) = itemEncoding.encode xs ++ itemEncoding.encode ys := by
  simp [itemEncoding, SAT.encTerminated, List.flatMap_append]

noncomputable def balancedItemsWordComputable : TM2ComputableInPolyTime instanceEncoding (wordEncoding Bool)
    (fun I : Instance => itemEncoding.encode (balance I).sizes) := by
  simpa only [Function.comp_def, balance, itemEncoding_append] using
    compose (pairComputable (toCode sizesComputable) slackItemsWordComputable) (concatComputable Bool)

def doubleLetter : Bool → List Bool
  | true => [true, true]
  | false => [false]

theorem doubleLetter_unary (n : ℕ) :
    (unaryEncodeNat n).flatMap doubleLetter = unaryEncodeNat (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, doubleLetter, ih, Nat.mul_succ]

theorem doubleLetter_items (xs : List ℕ) :
    (itemEncoding.encode xs).flatMap doubleLetter = itemEncoding.encode (xs.map (2 * ·)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [itemEncoding, SAT.encTerminated, List.flatMap_cons] at *
    simp [List.flatMap_append, doubleLetter_unary, doubleLetter, ih]

noncomputable def modifiedItemsComputable : TM2ComputableInPolyTime instanceEncoding itemEncoding
    (fun I : Instance => (toModified I).sizes) := by
  apply ofCode (f := fun I : Instance => (toModified I).sizes)
  simpa only [Function.comp_def, doubleLetter_items, toModified, scale] using
    compose balancedItemsWordComputable
      (TM2WordSubstitution.flatMapComputable doubleLetter 2 (by intro b; cases b <;> decide))

noncomputable def doubleCapacityComputable : TM2ComputableInPolyTime instanceEncoding unaryFinEncodingNat
    (fun I : Instance => 2 * I.capacity) := by
  apply ofCode (f := fun I : Instance => 2 * I.capacity)
  simpa only [Function.comp_def, unaryFinEncodingNat, doubleLetter_unary] using compose (toCode capacityComputable)
    (TM2WordSubstitution.flatMapComputable doubleLetter 2 (by intro b; cases b <;> decide))

/-- Actual finite-machine implementation of the total double-and-slack map. -/
noncomputable def toModifiedComputable :
    TM2ComputableInPolyTime instanceEncoding instanceEncoding toModified := by
  let h := pairComputable modifiedItemsComputable (pairComputable doubleCapacityComputable binsComputable)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun I }

/-- The full Karp reduction: mathematical equivalence and polynomial-time
machine are both proved, without a hardness or composition hypothesis. -/
theorem binPacking_karpReduces_modified :
    KarpReduces instanceEncoding instanceEncoding BinAccepts ModifiedAccepts :=
  ⟨toModified, ⟨toModifiedComputable⟩, toModified_correct⟩

theorem modified_hard_of_bin_hard (h : BinPackingUnaryNPHard) : ModifiedBinPackingUnaryNPHard :=
  npHard_of_karpReduces h binPacking_karpReduces_modified

end ProteinFolding.Packing

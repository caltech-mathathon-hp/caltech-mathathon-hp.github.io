import ProteinFolding.Common.SAT.MatchingClauseQuery
import ProteinFolding.Common.SAT.MatchingNextVariableCorrect
import ProteinFolding.Cubic.Proofs.VerifierPerfectArithmetic

/-! An arithmetic implementation of the raw occurrence gadget relation.
All variable lookups inspect binary identifiers in the source word; every
enumerated index is bounded by the number of literal occurrences. -/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2CompositionPoly TM2ProductMap TM2PairProjections

def occurrenceSlot (φ : CNF) (z : ℕ) : ℕ :=
  if z < (indexedOccurrences φ).length then z else z - (indexedOccurrences φ).length

def rawRelation (φ : CNF) (x y z : ℕ) : Bool :=
  let q := (indexedOccurrences φ).length
  if y < q then
    (decide (x = y) && decide (z = y)) ||
      (decide (x = nextVariableIndex (φ, y)) && decide (z = q + y))
  else if y < q + φ.length then
    (decide (x = y) && decide (clauseIndexAt (φ, occurrenceSlot φ z) = y - q)) &&
      decide (positiveAt (φ, occurrenceSlot φ z) = decide (q ≤ z))
  else decide (x = y)

abbrev RelationInput := CNF × Triple
def relationEncoding : FinEncoding RelationInput := pairEncoding cnfEncoding tripleFieldsEncoding

section QueryCombinators

variable {A : Type} {ea : FinEncoding A} {f g : A → ℕ} {b c : A → Bool}

noncomputable def addQuery
    (hf : TM2ComputableInPolyTime ea unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ea unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (fun a => f a + g a) :=
  compose (pairComputable hf hg) PerfectVerifierArithmetic.unaryAddComputable

noncomputable def subQuery
    (hf : TM2ComputableInPolyTime ea unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ea unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (fun a => f a - g a) :=
  compose (pairComputable hf hg) TM2UnarySubtraction.subtractionComputable

noncomputable def ltQuery
    (hf : TM2ComputableInPolyTime ea unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ea unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => decide (f a < g a)) :=
  compose (pairComputable hf hg) TM2UnaryComparison.ltComputable

noncomputable def leQuery
    (hf : TM2ComputableInPolyTime ea unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ea unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => decide (f a ≤ g a)) :=
  compose (pairComputable hf hg) TM2UnaryComparison.leComputable

noncomputable def eqQuery
    (hf : TM2ComputableInPolyTime ea unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ea unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => decide (f a = g a)) :=
  compose (pairComputable hf hg) PerfectUnaryEquality.unaryEqualityComputable

noncomputable def andQuery
    (hb : TM2ComputableInPolyTime ea finEncodingBoolBool b)
    (hc : TM2ComputableInPolyTime ea finEncodingBoolBool c) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => b a && c a) :=
  compose (pairComputable hb hc) TM2Boolean.andComputable

noncomputable def orQuery
    (hb : TM2ComputableInPolyTime ea finEncodingBoolBool b)
    (hc : TM2ComputableInPolyTime ea finEncodingBoolBool c) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => b a || c a) :=
  compose (pairComputable hb hc) (TM2Boolean.binaryComputable Bool.or)

noncomputable def boolEqQuery
    (hb : TM2ComputableInPolyTime ea finEncodingBoolBool b)
    (hc : TM2ComputableInPolyTime ea finEncodingBoolBool c) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun a => decide (b a = c a)) :=
  compose (pairComputable hb hc) (TM2Boolean.binaryComputable (fun a b => decide (a = b)))

end QueryCombinators

noncomputable def relationFormulaComputable :
    TM2ComputableInPolyTime relationEncoding cnfEncoding (fun r : RelationInput => r.1) :=
  fstComputable cnfEncoding tripleFieldsEncoding

noncomputable def relationTripleComputable :
    TM2ComputableInPolyTime relationEncoding tripleFieldsEncoding (fun r : RelationInput => r.2) :=
  sndComputable cnfEncoding tripleFieldsEncoding

noncomputable def relationXComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat (fun r : RelationInput => r.2.1) :=
  compose relationTripleComputable
    (fstComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def relationYZComputable :
    TM2ComputableInPolyTime relationEncoding (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      (fun r : RelationInput => r.2.2) :=
  compose relationTripleComputable
    (sndComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def relationYComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat (fun r : RelationInput => r.2.2.1) :=
  compose relationYZComputable (fstComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def relationZComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat (fun r : RelationInput => r.2.2.2) :=
  compose relationYZComputable (sndComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def relationQComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat
      (fun r : RelationInput => (indexedOccurrences r.1).length) :=
  compose relationFormulaComputable literalCountComputable

noncomputable def relationMComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat (fun r : RelationInput => r.1.length) :=
  compose relationFormulaComputable clauseCountComputable

noncomputable def relationSlotComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat
      (fun r : RelationInput => occurrenceSlot r.1 r.2.2.2) := by
  let h := TM2Conditional.iteComputable (ltQuery relationZComputable relationQComputable)
    relationZComputable (subQuery relationZComputable relationQComputable)
  simpa only [occurrenceSlot, decide_eq_true_eq] using h

noncomputable def relationNextComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat
      (fun r : RelationInput => nextVariableIndex (r.1, r.2.2.1)) :=
  compose (f := fun r : RelationInput => (r.1, r.2.2.1)) (g := nextVariableIndex)
    (pairComputable relationFormulaComputable relationYComputable) nextVariableIndexComputable

noncomputable def relationClauseComputable :
    TM2ComputableInPolyTime relationEncoding unaryFinEncodingNat
      (fun r : RelationInput => clauseIndexAt (r.1, occurrenceSlot r.1 r.2.2.2)) :=
  compose (f := fun r : RelationInput => (r.1, occurrenceSlot r.1 r.2.2.2)) (g := clauseIndexAt)
    (pairComputable relationFormulaComputable relationSlotComputable) clauseIndexComputable

noncomputable def relationPositiveComputable :
    TM2ComputableInPolyTime relationEncoding finEncodingBoolBool
      (fun r : RelationInput => positiveAt (r.1, occurrenceSlot r.1 r.2.2.2)) :=
  compose (f := fun r : RelationInput => (r.1, occurrenceSlot r.1 r.2.2.2)) (g := positiveAt)
    (pairComputable relationFormulaComputable relationSlotComputable) positiveComputable

/-- An actual finite TM2 deciding the arithmetic occurrence-gadget relation. -/
noncomputable def rawRelationComputable :
    TM2ComputableInPolyTime relationEncoding finEncodingBoolBool
      (fun r : RelationInput => rawRelation r.1 r.2.1 r.2.2.1 r.2.2.2) := by
  let eqXY := eqQuery relationXComputable relationYComputable
  let hv := orQuery
    (andQuery eqXY (eqQuery relationZComputable relationYComputable))
    (andQuery (eqQuery relationXComputable relationNextComputable)
      (eqQuery relationZComputable (addQuery relationQComputable relationYComputable)))
  let hc := andQuery
    (andQuery eqXY (eqQuery relationClauseComputable (subQuery relationYComputable relationQComputable)))
    (boolEqQuery relationPositiveComputable (leQuery relationQComputable relationZComputable))
  let h := TM2Conditional.iteComputable (ltQuery relationYComputable relationQComputable) hv
    (TM2Conditional.iteComputable
      (ltQuery relationYComputable (addQuery relationQComputable relationMComputable)) hc eqXY)
  simpa only [rawRelation, decide_eq_true_eq] using h

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

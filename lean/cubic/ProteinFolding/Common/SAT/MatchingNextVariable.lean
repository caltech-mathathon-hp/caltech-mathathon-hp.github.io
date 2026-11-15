import ProteinFolding.Common.SAT.MatchingSourceQueries
import ProteinFolding.Common.TM2BoundedSearch
import ProteinFolding.Common.TM2UnaryComparison
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.TM2Boolean

/-! Actual polynomial-time searches for the next occurrence of a variable.
Candidate and reference variable identifiers are compared as binary words.
Two bounded searches select the first later occurrence, wrapping to the first
occurrence if necessary. The bound is the explicit source occurrence count.
-/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2CompositionPoly TM2ProductMap TM2PairProjections TM2BoundedSearch

abbrev CandidateInput := Input × ℕ
def candidateEncoding : FinEncoding CandidateInput := pairEncoding inputEncoding unaryFinEncodingNat

def sameVariableAt (x : CandidateInput) : Bool :=
  decide (variableCodeAt x.1 = variableCodeAt (x.1.1, x.2))

def laterVariableAt (x : CandidateInput) : Bool := sameVariableAt x && decide (x.1.2 < x.2)

def firstMatch (x : Input) : ℕ := boundedSearch sameVariableAt (x, (indexedOccurrences x.1).length)
def laterMatch (x : Input) : ℕ := boundedSearch laterVariableAt (x, (indexedOccurrences x.1).length)

def nextVariableIndex (x : Input) : ℕ :=
  if decide (laterMatch x < (indexedOccurrences x.1).length) then laterMatch x else firstMatch x

theorem indexedOccurrences_literals (φ : CNF) : (indexedOccurrences φ).map Prod.snd = φ.flatten := by
  simp [indexedOccurrences, List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]

theorem indexedOccurrence_literal (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    ((indexedOccurrences φ).get i).2 =
      φ.flatten.get ⟨i.val, by rw [← indexedOccurrences_length]; exact i.isLt⟩ := by
  have h := congrArg (fun xs : List Literal => xs[i.val]?) (indexedOccurrences_literals φ)
  have hi : i.val < φ.flatten.length := by rw [← indexedOccurrences_length]; exact i.isLt
  simp only [List.getElem?_map] at h
  rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem hi] at h
  simpa only [Option.map_some, Option.some.injEq, List.get_eq_getElem] using h

theorem encodeNat_eq_iff (i j : ℕ) : encodeNat i = encodeNat j ↔ i = j := by
  constructor
  · intro h
    simpa only [decode_encodeNat] using congrArg decodeNat h
  · rintro rfl
    rfl

theorem sameVariableAt_correct (φ : CNF) (i j : Fin (indexedOccurrences φ).length) :
    sameVariableAt ((φ, i.val), j.val) =
      decide (occurrenceVariable φ i = occurrenceVariable φ j) := by
  have hi : i.val < φ.flatten.length := by rw [← indexedOccurrences_length]; exact i.isLt
  have hj : j.val < φ.flatten.length := by rw [← indexedOccurrences_length]; exact j.isLt
  simp only [sameVariableAt, variableCodeAt_correct φ i.val hi,
    variableCodeAt_correct φ j.val hj, encodeNat_eq_iff]
  rw [← indexedOccurrence_literal φ i, ← indexedOccurrence_literal φ j]
  rfl

theorem laterVariableAt_correct (φ : CNF) (i j : Fin (indexedOccurrences φ).length) :
    laterVariableAt ((φ, i.val), j.val) =
      (decide (occurrenceVariable φ i = occurrenceVariable φ j) && decide (i.val < j.val)) := by
  simp only [laterVariableAt, sameVariableAt_correct]

noncomputable def referenceComputable :
    TM2ComputableInPolyTime candidateEncoding inputEncoding (fun x : CandidateInput => x.1) :=
  fstComputable inputEncoding unaryFinEncodingNat

noncomputable def candidateFormulaComputable :
    TM2ComputableInPolyTime candidateEncoding cnfEncoding (fun x : CandidateInput => x.1.1) :=
  compose referenceComputable (fstComputable cnfEncoding unaryFinEncodingNat)

noncomputable def candidateIndexComputable :
    TM2ComputableInPolyTime candidateEncoding unaryFinEncodingNat (fun x : CandidateInput => x.2) :=
  sndComputable inputEncoding unaryFinEncodingNat

noncomputable def referenceIndexComputable :
    TM2ComputableInPolyTime candidateEncoding unaryFinEncodingNat (fun x : CandidateInput => x.1.2) :=
  compose referenceComputable (sndComputable cnfEncoding unaryFinEncodingNat)

noncomputable def referenceCodeComputable :
    TM2ComputableInPolyTime candidateEncoding (wordEncoding Bool) (fun x : CandidateInput => variableCodeAt x.1) :=
  compose (f := fun x : CandidateInput => x.1) (g := variableCodeAt)
    referenceComputable variableCodeComputable

noncomputable def candidateCodeComputable :
    TM2ComputableInPolyTime candidateEncoding (wordEncoding Bool)
      (fun x : CandidateInput => variableCodeAt (x.1.1, x.2)) :=
  compose (f := fun x : CandidateInput => (x.1.1, x.2)) (g := variableCodeAt)
    (pairComputable candidateFormulaComputable candidateIndexComputable) variableCodeComputable

noncomputable def sameVariableComputable :
    TM2ComputableInPolyTime candidateEncoding finEncodingBoolBool sameVariableAt :=
  compose (pairComputable referenceCodeComputable candidateCodeComputable)
    (TM2WordEquality.wordEqualityComputable Bool)

noncomputable def laterVariableComputable :
    TM2ComputableInPolyTime candidateEncoding finEncodingBoolBool laterVariableAt :=
  compose
    (pairComputable sameVariableComputable
      (compose (pairComputable referenceIndexComputable candidateIndexComputable) TM2UnaryComparison.ltComputable))
    TM2Boolean.andComputable

noncomputable def boundComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat
      (fun x : Input => (indexedOccurrences x.1).length) :=
  compose (fstComputable cnfEncoding unaryFinEncodingNat) literalCountComputable

noncomputable def searchInputComputable :
    TM2ComputableInPolyTime inputEncoding (pairEncoding inputEncoding unaryFinEncodingNat)
      (fun x : Input => (x, (indexedOccurrences x.1).length)) :=
  pairComputable (idComputableInPolyTime inputEncoding) boundComputable

noncomputable def firstMatchComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat firstMatch :=
  compose searchInputComputable (boundedSearchComputable sameVariableComputable)

noncomputable def laterMatchComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat laterMatch :=
  compose searchInputComputable (boundedSearchComputable laterVariableComputable)

noncomputable def nextVariableIndexComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat nextVariableIndex :=
  TM2Conditional.iteComputable
    (compose (pairComputable laterMatchComputable boundComputable) TM2UnaryComparison.ltComputable)
    laterMatchComputable firstMatchComputable

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

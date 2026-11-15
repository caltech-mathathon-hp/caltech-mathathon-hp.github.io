import ProteinFolding.Common.SAT.MatchingSourceCounts
import ProteinFolding.Common.TM2EncodingWords
import ProteinFolding.Common.TM2WordSegmentsSemantics
import ProteinFolding.Common.TM2WordTakeWhile
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2WordEquality
import ProteinFolding.Common.TM2Constants

/-! Actual polynomial-time source occurrence queries. Variable identifiers
remain binary words throughout; occurrence indices are unary and bounded by
the source's explicit number of literal occurrences. Out-of-range requests
still have total word semantics. -/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2WordSegments TM2CompositionPoly TM2ProductMap TM2PairProjections

local instance : Inhabited Sym := ⟨.bit false⟩

abbrev Input := CNF × ℕ
def inputEncoding : FinEncoding Input := pairEncoding cnfEncoding unaryFinEncodingNat

def eraseClause : Sym → Option Sym
  | .endClause => none
  | s => some s

def isEndLit : Sym → Bool
  | .endLit => true
  | _ => false

def retainBit : Sym → Option Bool
  | .bit b => some b
  | _ => none

def retainNeg : Sym → Option Bool
  | .neg => some true
  | _ => none

def literalStream (φ : CNF) : List Sym := (cnfEncoding.encode φ).filterMap eraseClause

def literalCodeAt (x : Input) : List Sym :=
  ((splitMarkers isEndLit (literalStream x.1) x.2).2).takeWhile (fun s => !isEndLit s)

def variableCodeAt (x : Input) : List Bool := (literalCodeAt x).filterMap retainBit
def positiveAt (x : Input) : Bool := decide ((literalCodeAt x).filterMap retainNeg = [])

theorem eraseClause_literal (l : Literal) : (encodeLit l).filterMap eraseClause = encodeLit l := by
  cases hp : l.pos <;> simp [encodeLit, hp, List.filterMap_map, Function.comp_def, eraseClause]

theorem eraseClause_clause (c : Clause) : (encodeClause c).filterMap eraseClause = encodeClause c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [encodeClause, encTerminated, List.flatMap_cons] at *
    simp only [List.filterMap_append, eraseClause_literal, List.filterMap_cons, eraseClause,
      List.filterMap_nil, ih]

theorem literalStream_eq (φ : CNF) :
    literalStream φ = encTerminated Sym.endLit encodeLit φ.flatten := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change (((encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ).filterMap eraseClause) = _
    change (encTerminated Sym.endClause encodeClause φ).filterMap eraseClause = _ at ih
    rw [List.filterMap_append, List.filterMap_append, eraseClause_clause]
    simp only [List.filterMap_cons, eraseClause, List.filterMap_nil, List.append_nil]
    rw [ih]
    simp [encodeClause, encTerminated, List.flatten_cons, List.flatMap_append]

theorem encodeLit_no_endLit (l : Literal) : ∀ s ∈ encodeLit l, isEndLit s = false := by
  have hn : Sym.endLit ∉ encodeLit l := by
    cases hp : l.pos <;> simp [encodeLit, hp]
  intro s hs
  cases s <;> try rfl
  exact False.elim (hn hs)

theorem literalCodeAt_correct (φ : CNF) (i : ℕ) (hi : i < φ.flatten.length) :
    literalCodeAt (φ, i) = encodeLit (φ.flatten.get ⟨i, hi⟩) := by
  unfold literalCodeAt
  rw [literalStream_eq, splitMarkers_terminated isEndLit Sym.endLit rfl encodeLit encodeLit_no_endLit]
  simp only [List.drop_eq_getElem_cons hi]
  change (((encodeLit φ.flatten[i] ++ [Sym.endLit]) ++
    encTerminated Sym.endLit encodeLit (φ.flatten.drop (i + 1))).takeWhile (fun s => !isEndLit s)) = _
  rw [show (encodeLit φ.flatten[i] ++ [Sym.endLit]) ++
      encTerminated Sym.endLit encodeLit (φ.flatten.drop (i + 1)) =
        encodeLit φ.flatten[i] ++ Sym.endLit ::
          encTerminated Sym.endLit encodeLit (φ.flatten.drop (i + 1)) by simp]
  exact takeWhile_segment (fun s => !isEndLit s) Sym.endLit rfl _ _
    (fun s hs => by simp only [encodeLit_no_endLit _ s hs, Bool.not_false])

theorem variableCodeAt_correct (φ : CNF) (i : ℕ) (hi : i < φ.flatten.length) :
    variableCodeAt (φ, i) = encodeNat (φ.flatten.get ⟨i, hi⟩).var := by
  rw [variableCodeAt, literalCodeAt_correct φ i hi]
  generalize φ.flatten.get ⟨i, hi⟩ = l
  obtain ⟨v, b⟩ := l
  cases b <;> simp [encodeLit, retainBit, List.filterMap_map, Function.comp_def]

theorem positiveAt_correct (φ : CNF) (i : ℕ) (hi : i < φ.flatten.length) :
    positiveAt (φ, i) = (φ.flatten.get ⟨i, hi⟩).pos := by
  rw [positiveAt, literalCodeAt_correct φ i hi]
  generalize φ.flatten.get ⟨i, hi⟩ = l
  obtain ⟨v, b⟩ := l
  cases b <;> simp [encodeLit, retainNeg, List.filterMap_map, Function.comp_def]

noncomputable def encodedFormulaComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Sym) (fun x : Input => cnfEncoding.encode x.1) :=
  compose (fstComputable cnfEncoding unaryFinEncodingNat) (TM2EncodingWords.encodeComputable cnfEncoding)

noncomputable def indexComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.2) :=
  sndComputable cnfEncoding unaryFinEncodingNat

noncomputable def literalStreamComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Sym) (fun x : Input => literalStream x.1) :=
  compose encodedFormulaComputable (filterMapComputable Sym Sym eraseClause)

noncomputable def literalSplitComputable :
    TM2ComputableInPolyTime inputEncoding (pairEncoding (wordEncoding Sym) (wordEncoding Sym))
      (fun x : Input => splitMarkers isEndLit (literalStream x.1) x.2) :=
  compose (pairComputable literalStreamComputable indexComputable)
    (TM2WordSegments.splitComputable Sym isEndLit)

noncomputable def literalCodeComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Sym) literalCodeAt :=
  compose (compose literalSplitComputable (sndComputable (wordEncoding Sym) (wordEncoding Sym)))
    (TM2WordTakeWhile.takeWhileComputable Sym (fun s => !isEndLit s))

noncomputable def variableCodeComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Bool) variableCodeAt :=
  compose literalCodeComputable (filterMapComputable Sym Bool retainBit)

noncomputable def positiveComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool positiveAt :=
  compose
    (pairComputable (compose literalCodeComputable (filterMapComputable Sym Bool retainNeg))
      (TM2Constants.constantComputable inputEncoding (wordEncoding Bool) []))
    (TM2WordEquality.wordEqualityComputable Bool)

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

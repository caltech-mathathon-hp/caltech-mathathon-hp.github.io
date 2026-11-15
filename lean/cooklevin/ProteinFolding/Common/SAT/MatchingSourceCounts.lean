import ProteinFolding.Common.SAT.CNFToMatchingBounds
import ProteinFolding.Common.TM2PairProjections

/-! Actual linear-time counters for the two source sizes used by the matching
reduction. Literal and clause terminators occur exactly once per occurrence
and clause in the frozen encoding, including empty clauses. Binary variable
digits are consumed without expansion into unary values. -/

namespace ProteinFolding.ThreeDimensionalMatching

open Computability Turing SAT

def literalCounter : Sym → Option Bool
  | .endLit => some true
  | _ => none

def clauseCounter : Sym → Option Bool
  | .endClause => some true
  | _ => none

theorem literalCounter_literal (l : Literal) : (encodeLit l).filterMap literalCounter = [] := by
  cases hp : l.pos <;> simp [encodeLit, hp, List.filterMap_map, Function.comp_def, literalCounter]

theorem clauseCounter_literal (l : Literal) : (encodeLit l).filterMap clauseCounter = [] := by
  cases hp : l.pos <;> simp [encodeLit, hp, List.filterMap_map, Function.comp_def, clauseCounter]

theorem literalCounter_clause (c : Clause) :
    (encodeClause c).filterMap literalCounter = unaryEncodeNat c.length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [encodeClause, encTerminated, List.flatMap_cons] at *
    simp only [List.filterMap_append, literalCounter_literal, List.filterMap_cons, literalCounter,
      List.filterMap_nil, List.nil_append, List.singleton_append, ih, List.length_cons, unaryEncodeNat]

theorem clauseCounter_clause (c : Clause) : (encodeClause c).filterMap clauseCounter = [] := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [encodeClause, encTerminated, List.flatMap_cons] at *
    simp only [List.filterMap_append, clauseCounter_literal, List.filterMap_cons, clauseCounter,
      List.filterMap_nil, List.nil_append, ih]

theorem unary_append (a b : ℕ) : unaryEncodeNat (a + b) = unaryEncodeNat a ++ unaryEncodeNat b := by
  induction a with
  | zero => simp [unaryEncodeNat]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, unaryEncodeNat, ih]
    rfl

theorem literalCounter_cnf (φ : CNF) :
    (cnfEncoding.encode φ).filterMap literalCounter = unaryEncodeNat (indexedOccurrences φ).length := by
  rw [indexedOccurrences_length]
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change (((encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ).filterMap literalCounter) = _
    change (encTerminated Sym.endClause encodeClause φ).filterMap literalCounter = _ at ih
    simp [literalCounter_clause, literalCounter, ih, List.flatten_cons, unary_append]

theorem clauseCounter_cnf (φ : CNF) :
    (cnfEncoding.encode φ).filterMap clauseCounter = unaryEncodeNat φ.length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change (((encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ).filterMap clauseCounter) = _
    change (encTerminated Sym.endClause encodeClause φ).filterMap clauseCounter = _ at ih
    simp [clauseCounter_clause, clauseCounter, ih, unaryEncodeNat]

noncomputable def literalCountComputable : TM2ComputableInPolyTime cnfEncoding unaryFinEncodingNat
    (fun φ => (indexedOccurrences φ).length) := by
  let h := TM2PairProjections.filterMapComputable Sym Bool literalCounter
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun φ => by
        have hout := h.outputsFun (cnfEncoding.encode φ)
        change TM2OutputsInTime h.tm ((cnfEncoding.encode φ).map h.inputAlphabet.symm)
          (some (((cnfEncoding.encode φ).filterMap literalCounter).map h.outputAlphabet.symm))
          (h.time.eval (cnfEncoding.encode φ).length) at hout
        rw [literalCounter_cnf] at hout
        exact hout }

noncomputable def clauseCountComputable : TM2ComputableInPolyTime cnfEncoding unaryFinEncodingNat
    List.length := by
  let h := TM2PairProjections.filterMapComputable Sym Bool clauseCounter
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun φ => by
        have hout := h.outputsFun (cnfEncoding.encode φ)
        change TM2OutputsInTime h.tm ((cnfEncoding.encode φ).map h.inputAlphabet.symm)
          (some (((cnfEncoding.encode φ).filterMap clauseCounter).map h.outputAlphabet.symm))
          (h.time.eval (cnfEncoding.encode φ).length) at hout
        rw [clauseCounter_cnf] at hout
        exact hout }

end ProteinFolding.ThreeDimensionalMatching

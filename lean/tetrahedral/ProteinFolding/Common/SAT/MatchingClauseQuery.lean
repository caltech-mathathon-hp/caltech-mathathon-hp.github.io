import ProteinFolding.Common.SAT.MatchingSourceQueries
import ProteinFolding.Common.TM2UnarySuccessor

/-! Actual polynomial-time clause-index lookup for a literal occurrence.
The prefix through the (i+1)-st literal terminator contains exactly the clause
terminators preceding occurrence i. Empty clauses are counted explicitly. -/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2WordSegments TM2CompositionPoly TM2ProductMap TM2PairProjections

local instance : Inhabited Sym := ⟨.bit false⟩

def isEndClause : Sym → Bool
  | .endClause => true
  | _ => false

def clauseIndexAt (x : Input) : ℕ :=
  ((splitMarkers isEndLit (cnfEncoding.encode x.1) (x.2 + 1)).1).countP isEndClause

theorem literalCounter_length (w : List Sym) :
    (w.filterMap literalCounter).length = w.countP isEndLit := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [literalCounter, isEndLit, List.countP_cons, ih]

theorem clauseCounter_word (w : List Sym) :
    w.filterMap clauseCounter = unaryEncodeNat (w.countP isEndClause) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [clauseCounter, isEndClause, List.countP_cons, unaryEncodeNat, ih]

theorem clauseCounter_length (w : List Sym) :
    (w.filterMap clauseCounter).length = w.countP isEndClause := by
  rw [clauseCounter_word, unary_length]

theorem countLit_clause (c : Clause) : (encodeClause c).countP isEndLit = c.length := by
  have h := congrArg List.length (literalCounter_clause c)
  simpa only [literalCounter_length, unary_length] using h

theorem countClause_clause (c : Clause) : (encodeClause c).countP isEndClause = 0 := by
  have h := congrArg List.length (clauseCounter_clause c)
  simpa only [clauseCounter_length, List.length_nil] using h

theorem clauseIndexAt_nil (i : ℕ) : clauseIndexAt ([], i) = 0 := rfl

theorem clauseIndexAt_cons (c : Clause) (φ : CNF) (i : ℕ) :
    clauseIndexAt (c :: φ, i) =
      if i < c.length then 0 else 1 + clauseIndexAt (φ, i - c.length) := by
  by_cases hi : i < c.length
  · rw [if_pos hi]
    change (splitMarkers isEndLit
      ((encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ)
      (i + 1)).1.countP isEndClause = 0
    rw [show (encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ =
      encodeClause c ++ (Sym.endClause :: encTerminated Sym.endClause encodeClause φ) by simp,
      splitMarkers_prefix_before isEndLit (encodeClause c) _ (i + 1) (by rw [countLit_clause]; omega)]
    exact splitMarkers_prefix_count_zero isEndLit isEndClause (encodeClause c) (i + 1) (countClause_clause c)
  · rw [if_neg hi]
    change (splitMarkers isEndLit
      ((encodeClause c ++ [Sym.endClause]) ++ encTerminated Sym.endClause encodeClause φ)
      (i + 1)).1.countP isEndClause = _
    have hlit : (encodeClause c ++ [Sym.endClause]).countP isEndLit = c.length := by
      simp [countLit_clause, isEndLit]
    rw [show i + 1 = (encodeClause c ++ [Sym.endClause]).countP isEndLit + (i - c.length) + 1 by
      rw [hlit]; omega,
      splitMarkers_append_after isEndLit (encodeClause c ++ [Sym.endClause]) _ (i - c.length)]
    simp [List.countP_append, countClause_clause, isEndClause, clauseIndexAt, cnfEncoding, Nat.add_comm]

theorem indexedOccurrenceIndices_cons (c : Clause) (φ : CNF) :
    (indexedOccurrences (c :: φ)).map (fun p => (p.1.val, p.2)) =
      c.map (fun l => ((0 : ℕ), l)) ++
        (indexedOccurrences φ).map (fun p => (p.1.val + 1, p.2)) := by
  simp [indexedOccurrences, List.ofFn_succ, List.map_flatten, List.map_ofFn,
    List.map_map, Function.comp_def]

theorem clauseIndexAt_correct (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    clauseIndexAt (φ, i.val) = ((indexedOccurrences φ).get i).1.val := by
  induction φ with
  | nil => have h := i.isLt; simp [indexedOccurrences] at h
  | cons c φ ih =>
    have hget := congrArg (fun xs : List (ℕ × Literal) => xs[i.val]?)
      (indexedOccurrenceIndices_cons c φ)
    simp only [List.getElem?_map] at hget
    rw [List.getElem?_eq_getElem i.isLt] at hget
    simp only [Option.map_some] at hget
    rw [clauseIndexAt_cons]
    by_cases hi : i.val < c.length
    · rw [if_pos hi]
      simp only [List.getElem?_append, List.length_map, hi, ↓reduceIte,
        List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at hget
      have h := congrArg (fun p : ℕ × Literal => p.1) (Option.some.inj hget)
      simpa only [List.get_eq_getElem] using h.symm
    · rw [if_neg hi]
      have hlen : (indexedOccurrences (c :: φ)).length = c.length + (indexedOccurrences φ).length := by
        have h := congrArg List.length (indexedOccurrenceIndices_cons c φ)
        simpa only [List.length_map, List.length_append] using h
      have hj : i.val - c.length < (indexedOccurrences φ).length := by have := i.isLt; omega
      let j : Fin (indexedOccurrences φ).length := ⟨i.val - c.length, hj⟩
      have he := ih j
      simp only [List.getElem?_append, List.length_map, hi, ↓reduceIte,
        List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at hget
      have h := congrArg (fun p : ℕ × Literal => p.1) (Option.some.inj hget)
      have hh : 1 + ((indexedOccurrences φ).get j).1.val =
          ((indexedOccurrences (c :: φ)).get i).1.val := by
        simpa only [List.get_eq_getElem, j, Nat.add_comm] using h.symm
      exact (congrArg (1 + ·) he).trans hh

noncomputable def wordClauseCountComputable :
    TM2ComputableInPolyTime (wordEncoding Sym) unaryFinEncodingNat (List.countP isEndClause) := by
  let h := filterMapComputable Sym Bool clauseCounter
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun w => by
        have hout := h.outputsFun w
        simpa only [wordEncoding, unaryFinEncodingNat, clauseCounter_word] using hout }

noncomputable def successorIndexComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.2 + 1) :=
  compose indexComputable TM2UnarySuccessor.successorComputable

noncomputable def sourcePrefixComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Sym)
      (fun x : Input => (splitMarkers isEndLit (cnfEncoding.encode x.1) (x.2 + 1)).1) :=
  compose
    (compose (pairComputable encodedFormulaComputable successorIndexComputable)
      (TM2WordSegments.splitComputable Sym isEndLit))
    (fstComputable (wordEncoding Sym) (wordEncoding Sym))

noncomputable def clauseIndexComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat clauseIndexAt :=
  compose sourcePrefixComputable wordClauseCountComputable

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

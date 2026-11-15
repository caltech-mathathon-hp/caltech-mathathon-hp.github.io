import ProteinFolding.Common.CookLevinProofLiteralCompiler

/-! A concrete polynomial-time TM2 serializer for entire CNFs whose bounded
loop indices are supplied in unary. Its output is exactly the existing frozen
binary cnfEncoding, including every literal and clause terminator. This is the
serialization backend of the tableau emitter, not its loop-index generator.
-/

namespace ProteinFolding.SAT.CookLevinCNFCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap TM2ListMap
open CookLevinMapCompiler CookLevinLiteralCompiler

noncomputable def listFlatMapWordCompiler {A B : Type} {ea : FinEncoding A}
    [Fintype B] {f : A → List B} (h : TM2ComputableInPolyTime ea (wordEncoding B) f) :
    TM2ComputableInPolyTime (TM2ListMap.listEncoding ea) (wordEncoding B) (List.flatMap f) := by
  let hc := compose (TM2PairProjections.sndComputable finEncodingBoolBool ea) h
  let hl := TM2ListMap.flatMapComputable hc
  let hp := pairComputable (TM2Constants.constantComputable (TM2ListMap.listEncoding ea) finEncodingBoolBool false)
    (idComputableInPolyTime (TM2ListMap.listEncoding ea))
  exact compose (f := fun xs : List A => (false, xs))
    (g := fun z : Bool × List A => z.2.flatMap f) hp hl

noncomputable def appendConstantCompiler {X : Type} {ex : FinEncoding X}
    {f : X → List Sym} (h : TM2ComputableInPolyTime ex (wordEncoding Sym) f) (suffix : List Sym) :
    TM2ComputableInPolyTime ex (wordEncoding Sym) (fun x => f x ++ suffix) :=
  compose (pairComputable h (TM2Constants.constantComputable ex (wordEncoding Sym) suffix))
    (TM2PairProjections.concatComputable Sym)

noncomputable def terminatedLiteralCompiler :
    TM2ComputableInPolyTime unaryLiteralEncoding (wordEncoding Sym)
      (fun nb => encodeLit ⟨nb.1, nb.2⟩ ++ [Sym.endLit]) :=
  appendConstantCompiler literalCodeComputable [Sym.endLit]

def clauseOfRecords (xs : List (ℕ × Bool)) : Clause := xs.map (fun nb => ⟨nb.1, nb.2⟩)

def unaryClauseEncoding : FinEncoding (List (ℕ × Bool)) := TM2ListMap.listEncoding unaryLiteralEncoding

theorem singletonClause_code (xs : List (ℕ × Bool)) :
    cnfEncoding.encode [clauseOfRecords xs] =
      xs.flatMap (fun nb => encodeLit ⟨nb.1, nb.2⟩ ++ [Sym.endLit]) ++ [Sym.endClause] := by
  simp [cnfEncoding, encodeClause, clauseOfRecords, encTerminated, List.flatMap_map]

noncomputable def singletonClauseWordCompiler :
    TM2ComputableInPolyTime unaryClauseEncoding (wordEncoding Sym)
      (fun xs => cnfEncoding.encode [clauseOfRecords xs]) := by
  let hb := listFlatMapWordCompiler terminatedLiteralCompiler
  let ht := appendConstantCompiler hb [Sym.endClause]
  have he : (fun xs : List (ℕ × Bool) =>
      xs.flatMap (fun nb => encodeLit ⟨nb.1, nb.2⟩ ++ [Sym.endLit]) ++ [Sym.endClause]) =
      fun xs => cnfEncoding.encode [clauseOfRecords xs] := by
    funext xs
    exact (singletonClause_code xs).symm
  rw [← he]
  exact ht

noncomputable def singletonClauseCompiler :
    TM2ComputableInPolyTime unaryClauseEncoding cnfEncoding (fun xs => [clauseOfRecords xs]) where
  toTM2ComputableAux := singletonClauseWordCompiler.toTM2ComputableAux
  time := singletonClauseWordCompiler.time
  outputsFun xs := singletonClauseWordCompiler.outputsFun xs

def unaryCNFEncoding : FinEncoding (List (List (ℕ × Bool))) := TM2ListMap.listEncoding unaryClauseEncoding

def cnfOfRecords (xs : List (List (ℕ × Bool))) : CNF := xs.map clauseOfRecords

theorem cnfOfRecords_code (xs : List (List (ℕ × Bool))) :
    cnfEncoding.encode (cnfOfRecords xs) = xs.flatMap (fun c => cnfEncoding.encode [clauseOfRecords c]) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    change cnfEncoding.encode ([clauseOfRecords c] ++ cnfOfRecords cs) = _
    rw [cnfEncoding_append, ih, List.flatMap_cons]

noncomputable def cnfWordCompiler :
    TM2ComputableInPolyTime unaryCNFEncoding (wordEncoding Sym)
      (fun xs => cnfEncoding.encode (cnfOfRecords xs)) := by
  let hm := listFlatMapWordCompiler singletonClauseWordCompiler
  have he : (fun xs : List (List (ℕ × Bool)) => xs.flatMap (fun c => cnfEncoding.encode [clauseOfRecords c])) =
      fun xs => cnfEncoding.encode (cnfOfRecords xs) := by
    funext xs
    exact (cnfOfRecords_code xs).symm
  rw [← he]
  exact hm

/-- Actual polynomial TM2 conversion from the unary loop-record representation
of a complete CNF to its unchanged frozen binary encoding. -/
noncomputable def cnfCompiler :
    TM2ComputableInPolyTime unaryCNFEncoding cnfEncoding cnfOfRecords where
  toTM2ComputableAux := cnfWordCompiler.toTM2ComputableAux
  time := cnfWordCompiler.time
  outputsFun xs := cnfWordCompiler.outputsFun xs

end ProteinFolding.SAT.CookLevinCNFCompiler

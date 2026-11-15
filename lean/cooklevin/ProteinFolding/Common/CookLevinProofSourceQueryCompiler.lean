import ProteinFolding.Common.SAT.MatchingSourceQueries
import ProteinFolding.Common.CookLevinProofArithmeticCompiler
import ProteinFolding.Common.CookLevinProofRangeCompiler

/-! Actual indexed clause/literal queries for the unchanged binary CNF
encoding. Two marker scans retain binary variable words without expanding
their numeric magnitudes. Empty clauses and repeated literals are retained. -/

namespace ProteinFolding.SAT.CookLevinSourceQueryCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap TM2WordSegments
open CookLevinArithmeticCompiler

local instance sourceSymInhabited : Inhabited Sym := ⟨.bit false⟩

def segmentAt {D : Type} (p : D → Bool) (w : List D) (i : ℕ) : List D :=
  ((splitMarkers p w i).2).takeWhile (fun d => !p d)

theorem segmentAt_terminated {D E : Type} (p : D → Bool) (t : D) (ht : p t = true)
    (enc : E → List D) (henc : ∀ e d, d ∈ enc e → p d = false)
    (xs : List E) (i : ℕ) (hi : i < xs.length) :
    segmentAt p (encTerminated t enc xs) i = enc xs[i] := by
  rw [segmentAt, splitMarkers_terminated p t ht enc henc, List.drop_eq_getElem_cons hi]
  change (((enc xs[i] ++ [t]) ++ encTerminated t enc (xs.drop (i + 1))).takeWhile (fun d => !p d)) = _
  rw [show (enc xs[i] ++ [t]) ++ encTerminated t enc (xs.drop (i + 1)) =
    enc xs[i] ++ t :: encTerminated t enc (xs.drop (i + 1)) by simp]
  exact takeWhile_segment (fun d => !p d) t (by simp [ht]) _ _
    (fun d hd => by simp only [henc _ _ hd, Bool.not_false])

noncomputable def segmentCompiler {X D : Type} [Fintype D] [Inhabited D] {ex : FinEncoding X}
    (p : D → Bool) (w : X → List D) (i : X → ℕ)
    (hw : TM2ComputableInPolyTime ex (wordEncoding D) w)
    (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat i) :
    TM2ComputableInPolyTime ex (wordEncoding D) (fun x => segmentAt p (w x) (i x)) :=
  compose (compose (compose (pairComputable hw hi) (TM2WordSegments.splitComputable D p))
    (TM2PairProjections.sndComputable (wordEncoding D) (wordEncoding D)))
      (TM2WordTakeWhile.takeWhileComputable D (fun d => !p d))

def isEndClause : Sym → Bool
  | .endClause => true
  | _ => false

abbrev ClauseInput := CNF × ℕ
abbrev QueryInput := ClauseInput × ℕ
def clauseInputEncoding : FinEncoding ClauseInput := pairEncoding cnfEncoding unaryFinEncodingNat
def queryEncoding : FinEncoding QueryInput := pairEncoding clauseInputEncoding unaryFinEncodingNat

def clauseCodeAt (p : ClauseInput) : List Sym := segmentAt isEndClause (cnfEncoding.encode p.1) p.2

def literalCodeAt (p : QueryInput) : List Sym :=
  segmentAt ThreeDimensionalMatching.SourceQueries.isEndLit (clauseCodeAt p.1) p.2

def variableCodeAt (p : QueryInput) : List Bool :=
  (literalCodeAt p).filterMap ThreeDimensionalMatching.SourceQueries.retainBit

def positiveAt (p : QueryInput) : Bool :=
  decide ((literalCodeAt p).filterMap ThreeDimensionalMatching.SourceQueries.retainNeg = [])

def clauseLengthAt (p : ClauseInput) : ℕ :=
  ((clauseCodeAt p).filterMap ThreeDimensionalMatching.literalCounter).length

theorem encodeClause_no_endClause (c : Clause) :
    ∀ s ∈ encodeClause c, isEndClause s = false := by
  intro s hs
  cases s <;> try rfl
  have hm : true ∈ (encodeClause c).filterMap ThreeDimensionalMatching.clauseCounter :=
    List.mem_filterMap.mpr ⟨.endClause, hs, rfl⟩
  rw [ThreeDimensionalMatching.clauseCounter_clause] at hm
  exact False.elim (List.not_mem_nil hm)

theorem clauseCodeAt_correct (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    clauseCodeAt (φ, i) = encodeClause φ[i] :=
  segmentAt_terminated isEndClause .endClause rfl encodeClause encodeClause_no_endClause φ i hi

theorem literalCodeAt_correct (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < φ[i].length) :
    literalCodeAt ((φ, i), j) = encodeLit φ[i][j] := by
  rw [literalCodeAt, clauseCodeAt_correct φ i hi]
  exact segmentAt_terminated ThreeDimensionalMatching.SourceQueries.isEndLit .endLit rfl encodeLit
    ThreeDimensionalMatching.SourceQueries.encodeLit_no_endLit φ[i] j hj

theorem variableCodeAt_correct (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < φ[i].length) :
    variableCodeAt ((φ, i), j) = encodeNat φ[i][j].var := by
  rw [variableCodeAt, literalCodeAt_correct φ i j hi hj]
  generalize φ[i][j] = l
  obtain ⟨v, b⟩ := l
  cases b <;> simp [encodeLit, ThreeDimensionalMatching.SourceQueries.retainBit,
    List.filterMap_map, Function.comp_def]

theorem positiveAt_correct (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < φ[i].length) :
    positiveAt ((φ, i), j) = φ[i][j].pos := by
  rw [positiveAt, literalCodeAt_correct φ i j hi hj]
  generalize φ[i][j] = l
  obtain ⟨v, b⟩ := l
  cases b <;> simp [encodeLit, ThreeDimensionalMatching.SourceQueries.retainNeg,
    List.filterMap_map, Function.comp_def]

theorem clauseLengthAt_correct (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    clauseLengthAt (φ, i) = φ[i].length := by
  rw [clauseLengthAt, clauseCodeAt_correct φ i hi, ThreeDimensionalMatching.literalCounter_clause]
  simp [CookLevinRangeCompiler.unary_replicate]

noncomputable def clauseCodeCompiler :
    TM2ComputableInPolyTime clauseInputEncoding (wordEncoding Sym) clauseCodeAt :=
  segmentCompiler (ex := clauseInputEncoding) isEndClause (fun p : ClauseInput => cnfEncoding.encode p.1) Prod.snd
    (compose (TM2PairProjections.fstComputable cnfEncoding unaryFinEncodingNat)
      (TM2EncodingWords.encodeComputable cnfEncoding))
    (TM2PairProjections.sndComputable cnfEncoding unaryFinEncodingNat)

noncomputable def literalCodeCompiler :
    TM2ComputableInPolyTime queryEncoding (wordEncoding Sym) literalCodeAt :=
  segmentCompiler (ex := queryEncoding) ThreeDimensionalMatching.SourceQueries.isEndLit (fun p : QueryInput => clauseCodeAt p.1) Prod.snd
    (compose (f := (Prod.fst : QueryInput → ClauseInput)) (g := clauseCodeAt)
      (TM2PairProjections.fstComputable clauseInputEncoding unaryFinEncodingNat) clauseCodeCompiler)
    (TM2PairProjections.sndComputable clauseInputEncoding unaryFinEncodingNat)

noncomputable def variableCodeCompiler :
    TM2ComputableInPolyTime queryEncoding (wordEncoding Bool) variableCodeAt :=
  compose literalCodeCompiler (TM2PairProjections.filterMapComputable Sym Bool
    ThreeDimensionalMatching.SourceQueries.retainBit)

noncomputable def positiveCompiler :
    TM2ComputableInPolyTime queryEncoding finEncodingBoolBool positiveAt :=
  compose (pairComputable (compose literalCodeCompiler (TM2PairProjections.filterMapComputable Sym Bool
    ThreeDimensionalMatching.SourceQueries.retainNeg)) (TM2Constants.constantComputable queryEncoding (wordEncoding Bool) []))
    (TM2WordEquality.wordEqualityComputable Bool)

noncomputable def clauseLengthCompiler :
    TM2ComputableInPolyTime clauseInputEncoding unaryFinEncodingNat clauseLengthAt :=
  compose (compose clauseCodeCompiler (TM2PairProjections.filterMapComputable Sym Bool
    ThreeDimensionalMatching.literalCounter)) (lengthComputable (wordEncoding Bool))

end ProteinFolding.SAT.CookLevinSourceQueryCompiler

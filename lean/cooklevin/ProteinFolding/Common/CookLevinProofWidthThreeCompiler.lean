import ProteinFolding.Common.CookLevinProofBoundedVariableCompiler
import ProteinFolding.Common.CookLevinProofClampedCompiler
import ProteinFolding.Common.CookLevinProofRangeCNFCompiler
import ProteinFolding.Common.CookLevinProofFactorThree
import ProteinFolding.Common.CookLevinProofAddressCompiler
import ProteinFolding.Common.TM2UnaryComparison

/-! Actual finite-Q width-three chain emission. Binary source indices are
queried through the proved bounded unary decoder. Every clause receives Q+1
private flags; exactly the first min(clause length,Q) guarded triples are
emitted. The source-width and literalVariable promises are needed only for the later
semantic comparison, not for this total machine's runtime. -/

namespace ProteinFolding.SAT.CookLevinWidthThreeCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinCircuit
  CookLevinSourceQueryCompiler CookLevinBoundedVariableCompiler CookLevinAddressCompiler
  CookLevinArithmeticCompiler CookLevinClampedCompiler CookLevinRangeCNFCompiler
  CookLevinTemplateCompiler CookLevinFactorThree CookLevinLiteralCompiler

abbrev Input := CNF × ℕ
abbrev ClauseData := Input × ℕ

def inputEncoding : FinEncoding Input := pairEncoding cnfEncoding unaryFinEncodingNat
def clauseDataEncoding : FinEncoding ClauseData := pairEncoding inputEncoding unaryFinEncodingNat

def sourceClause (p : ClauseData) : CookLevinSourceQueryCompiler.ClauseInput := (p.1.1, p.2)
def clauseLength (p : ClauseData) : ℕ := clauseLengthAt (sourceClause p)
def auxBase (Q : ℕ) (p : ClauseData) : ℕ := p.1.2 + p.2 * (Q + 1)
def literalVariable (j : ℕ) (p : ClauseData) : ℕ := boundedVariable ((sourceClause p, j), p.1.2)
def polarity (j : ℕ) (p : ClauseData) : Bool := positiveAt (sourceClause p, j)

def triple (Q j : ℕ) (p : ClauseData) : Clause :=
  [negative (auxBase Q p + j), ⟨literalVariable j p, polarity j p⟩, positive (auxBase Q p + (j + 1))]

def guardedTriple (Q j : ℕ) (p : ClauseData) : CNF :=
  if j < clauseLength p then [triple Q j p] else []

def clauseFormula (Q : ℕ) (p : ClauseData) : CNF :=
  [[positive (auxBase Q p)]] ++
    (List.finRange Q).flatMap (fun j => guardedTriple Q j.val p) ++
      [[negative (auxBase Q p + min (clauseLength p) Q)]]

def formula (Q : ℕ) (p : Input) : CNF :=
  (List.range p.1.length).flatMap (fun i => clauseFormula Q (p, i))

noncomputable def sourceClauseCompiler :
    TM2ComputableInPolyTime clauseDataEncoding clauseInputEncoding sourceClause := by
  let hp := TM2PairProjections.fstComputable inputEncoding unaryFinEncodingNat
  exact pairComputable
    (compose hp (TM2PairProjections.fstComputable cnfEncoding unaryFinEncodingNat))
    (TM2PairProjections.sndComputable inputEncoding unaryFinEncodingNat)

noncomputable def boundCompiler :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (fun p => p.1.2) :=
  compose (TM2PairProjections.fstComputable inputEncoding unaryFinEncodingNat)
    (TM2PairProjections.sndComputable cnfEncoding unaryFinEncodingNat)

noncomputable def ordinalCompiler :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (fun p => p.2) :=
  TM2PairProjections.sndComputable inputEncoding unaryFinEncodingNat

noncomputable def lengthCompiler :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat clauseLength :=
  compose sourceClauseCompiler clauseLengthCompiler

noncomputable def baseCompiler (Q : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (auxBase Q) :=
  addMaps boundCompiler (multiplyMaps ordinalCompiler
    (TM2Constants.constantComputable clauseDataEncoding unaryFinEncodingNat (Q + 1)))

noncomputable def queryCompiler (j : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding queryEncoding (fun p => (sourceClause p, j)) :=
  pairComputable sourceClauseCompiler
    (TM2Constants.constantComputable clauseDataEncoding unaryFinEncodingNat j)

noncomputable def variableCompiler (j : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (literalVariable j) :=
  compose (pairComputable (queryCompiler j) boundCompiler) boundedVariableCompiler

noncomputable def polarityCompiler (j : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding finEncodingBoolBool (polarity j) :=
  compose (queryCompiler j) positiveCompiler

noncomputable def tripleCompiler (Q j : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding cnfEncoding (fun p => [triple Q j p]) := by
  let indices : Fin 3 → ClauseData → ℕ
    | 0 => fun p => auxBase Q p + j
    | 1 => literalVariable j
    | 2 => fun p => auxBase Q p + (j + 1)
  let signs : Fin 3 → ClauseData → Bool
    | 0 => fun _ => false
    | 1 => polarity j
    | 2 => fun _ => true
  have hi : ∀ i, TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (indices i) := by
    intro i
    match i with
    | 0 => exact addConstantCompiler (baseCompiler Q) j
    | 1 => exact variableCompiler j
    | 2 => exact addConstantCompiler (baseCompiler Q) (j + 1)
  have hs : ∀ i, TM2ComputableInPolyTime clauseDataEncoding finEncodingBoolBool (signs i) := by
    intro i
    match i with
    | 0 => exact TM2Constants.constantComputable clauseDataEncoding finEncodingBoolBool false
    | 1 => exact polarityCompiler j
    | 2 => exact TM2Constants.constantComputable clauseDataEncoding finEncodingBoolBool true
  have he : (fun p => [indexedClause 3 indices signs p]) = (fun p => [triple Q j p]) := by
    funext p
    rfl
  rw [← he]
  exact fixedClauseCompiler 3 indices signs hi hs

noncomputable def guardedTripleCompiler (Q j : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding cnfEncoding (guardedTriple Q j) := by
  let hp := compose (pairComputable
    (TM2Constants.constantComputable clauseDataEncoding unaryFinEncodingNat j) lengthCompiler)
      TM2UnaryComparison.ltComputable
  simpa only [guardedTriple, Function.comp_def, decide_eq_true_eq] using
    TM2Conditional.iteComputable hp (tripleCompiler Q j)
      (TM2Constants.constantComputable clauseDataEncoding cnfEncoding [])

noncomputable def minLengthCompiler (Q : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding unaryFinEncodingNat (fun p => min (clauseLength p) Q) :=
  clampedFamilyComputable clauseDataEncoding unaryFinEncodingNat clauseLength lengthCompiler Q
    (fun j _ => j) (fun j => TM2Constants.constantComputable clauseDataEncoding unaryFinEncodingNat j)

noncomputable def clauseCompiler (Q : ℕ) :
    TM2ComputableInPolyTime clauseDataEncoding cnfEncoding (clauseFormula Q) := by
  let hfirst := compose (pairComputable (baseCompiler Q)
    (TM2Constants.constantComputable clauseDataEncoding finEncodingBoolBool true)) singletonCNFComputable
  let htriples := fixedListCNFCompiler (List.finRange Q)
    (fun j p => guardedTriple Q j.val p) (fun j => guardedTripleCompiler Q j.val)
  let hlast := compose (pairComputable (addMaps (baseCompiler Q) (minLengthCompiler Q))
    (TM2Constants.constantComputable clauseDataEncoding finEncodingBoolBool false)) singletonCNFComputable
  exact appendCompiler (appendCompiler hfirst htriples) hlast

noncomputable def computable (Q : ℕ) :
    TM2ComputableInPolyTime inputEncoding cnfEncoding (formula Q) := by
  let hlen := compose (TM2PairProjections.fstComputable cnfEncoding unaryFinEncodingNat)
    ThreeDimensionalMatching.clauseCountComputable
  exact rangeCNFCompiler (fun p : Input => p.1.length)
    (fun p : ClauseData => clauseFormula Q p) hlen (clauseCompiler Q)

theorem guardedTriple_width (Q j : ℕ) (p : ClauseData) :
    ThreeCNF.WidthAtMostThree (guardedTriple Q j p) := by
  unfold guardedTriple
  split <;> simp [ThreeCNF.WidthAtMostThree, triple]

theorem clauseFormula_width (Q : ℕ) (p : ClauseData) :
    ThreeCNF.WidthAtMostThree (clauseFormula Q p) := by
  intro c hc
  simp only [clauseFormula, List.mem_append, List.mem_singleton] at hc
  rcases hc with (rfl | hc) | rfl
  · simp
  · obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
    exact guardedTriple_width Q j.val p c hc
  · simp

theorem formula_width (Q : ℕ) (p : Input) : ThreeCNF.WidthAtMostThree (formula Q p) := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  exact clauseFormula_width Q (p, i) c hc

end ProteinFolding.SAT.CookLevinWidthThreeCompiler

import ProteinFolding.Common.SAT.MatchingRelation
import ProteinFolding.Common.TM2UnaryRange

/-! Three explicit bounded loops enumerate the raw occurrence gadget.
The generic loop constructor simulates an actual polynomial-time child on
each unary index, retaining the common parameter between child runs. -/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2CompositionPoly TM2ProductMap TM2PairProjections

section RangeLoop
variable {P B : Type} [Fintype B] {ep : FinEncoding P}
  {f : P × ℕ → List B} {n : P → ℕ}

noncomputable def enumerateRangeComputable
    (hf : TM2ComputableInPolyTime (pairEncoding ep unaryFinEncodingNat) (wordEncoding B) f)
    (hn : TM2ComputableInPolyTime ep unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ep (wordEncoding B)
      (fun p => (List.range (n p)).flatMap (fun i => f (p, i))) :=
  compose (f := fun p => (p, List.range (n p))) (g := TM2ListMap.mappedFunction f)
    (pairComputable (idComputableInPolyTime ep) (compose hn TM2UnaryRange.rangeComputable))
    (TM2ListMap.flatMapComputable hf)

end RangeLoop

abbrev XYInput := Input × ℕ
abbrev XYZInput := XYInput × ℕ
def xyEncoding : FinEncoding XYInput := pairEncoding inputEncoding unaryFinEncodingNat
def xyzEncoding : FinEncoding XYZInput := pairEncoding xyEncoding unaryFinEncodingNat
abbrev EdgeLetter := Option tripleFieldsEncoding.Γ

def vertexCount (φ : CNF) : ℕ := (indexedOccurrences φ).length + (indexedOccurrences φ).length

def edgeWord (r : XYZInput) : List EdgeLetter :=
  if rawRelation r.1.1.1 r.1.1.2 r.1.2 r.2 then
    (tripleFieldsEncoding.encode (r.1.1.2, r.1.2, r.2)).map some ++ [none]
  else []

def zWords (r : XYInput) : List EdgeLetter :=
  (List.range (vertexCount r.1.1)).flatMap (fun z => edgeWord (r, z))

def yWords (r : Input) : List EdgeLetter :=
  (List.range (vertexCount r.1)).flatMap (fun y => zWords (r, y))

def graphWords (φ : CNF) : List EdgeLetter :=
  (List.range (vertexCount φ)).flatMap (fun x => yWords (φ, x))

noncomputable def vertexCountComputable :
    TM2ComputableInPolyTime cnfEncoding unaryFinEncodingNat vertexCount :=
  addQuery literalCountComputable literalCountComputable

noncomputable def xyzXYComputable :
    TM2ComputableInPolyTime xyzEncoding xyEncoding (fun r : XYZInput => r.1) :=
  fstComputable xyEncoding unaryFinEncodingNat

noncomputable def xyzXComputable :
    TM2ComputableInPolyTime xyzEncoding inputEncoding (fun r : XYZInput => r.1.1) :=
  compose xyzXYComputable (fstComputable inputEncoding unaryFinEncodingNat)

noncomputable def xyzFormulaComputable :
    TM2ComputableInPolyTime xyzEncoding cnfEncoding (fun r : XYZInput => r.1.1.1) :=
  compose xyzXComputable (fstComputable cnfEncoding unaryFinEncodingNat)

noncomputable def xyzFirstComputable :
    TM2ComputableInPolyTime xyzEncoding unaryFinEncodingNat (fun r : XYZInput => r.1.1.2) :=
  compose xyzXComputable (sndComputable cnfEncoding unaryFinEncodingNat)

noncomputable def xyzSecondComputable :
    TM2ComputableInPolyTime xyzEncoding unaryFinEncodingNat (fun r : XYZInput => r.1.2) :=
  compose xyzXYComputable (sndComputable inputEncoding unaryFinEncodingNat)

noncomputable def xyzThirdComputable :
    TM2ComputableInPolyTime xyzEncoding unaryFinEncodingNat (fun r : XYZInput => r.2) :=
  sndComputable xyEncoding unaryFinEncodingNat

noncomputable def xyzTripleComputable :
    TM2ComputableInPolyTime xyzEncoding tripleFieldsEncoding
      (fun r : XYZInput => (r.1.1.2, r.1.2, r.2)) :=
  pairComputable xyzFirstComputable (pairComputable xyzSecondComputable xyzThirdComputable)

noncomputable def xyzRelationInputComputable :
    TM2ComputableInPolyTime xyzEncoding relationEncoding
      (fun r : XYZInput => (r.1.1.1, (r.1.1.2, r.1.2, r.2))) :=
  pairComputable xyzFormulaComputable xyzTripleComputable

noncomputable def edgeWordComputable :
    TM2ComputableInPolyTime xyzEncoding (wordEncoding EdgeLetter) edgeWord :=
  TM2Conditional.iteComputable
    (compose xyzRelationInputComputable rawRelationComputable)
    (TM2ListMap.encodedBlockComputable tripleFieldsEncoding xyzTripleComputable)
    (TM2Constants.constantComputable xyzEncoding (wordEncoding EdgeLetter) [])

noncomputable def xyFormulaComputable :
    TM2ComputableInPolyTime xyEncoding cnfEncoding (fun r : XYInput => r.1.1) :=
  compose (fstComputable inputEncoding unaryFinEncodingNat)
    (fstComputable cnfEncoding unaryFinEncodingNat)

noncomputable def zWordsComputable :
    TM2ComputableInPolyTime xyEncoding (wordEncoding EdgeLetter) zWords :=
  enumerateRangeComputable edgeWordComputable (compose xyFormulaComputable vertexCountComputable)

noncomputable def yWordsComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding EdgeLetter) yWords :=
  enumerateRangeComputable zWordsComputable
    (compose (fstComputable cnfEncoding unaryFinEncodingNat) vertexCountComputable)

/-- An actual TM2 with a composed polynomial runtime for the three nested
bounded loops and the proved source-relation decider. -/
noncomputable def graphWordsComputable :
    TM2ComputableInPolyTime cnfEncoding (wordEncoding EdgeLetter) graphWords :=
  enumerateRangeComputable yWordsComputable vertexCountComputable

def denseTriples (φ : CNF) : List Triple :=
  (List.range (vertexCount φ)).flatMap fun x =>
    (List.range (vertexCount φ)).flatMap fun y =>
      (List.range (vertexCount φ)).flatMap fun z =>
        if rawRelation φ x y z then [(x, y, z)] else []

theorem encoded_append (a b : List Triple) :
    triplesEncoding.encode (a ++ b) = triplesEncoding.encode a ++ triplesEncoding.encode b := by
  simp [triplesEncoding, encTerminated, List.flatMap_append]

theorem encoded_flatMap {A : Type} (xs : List A) (f : A → List Triple) :
    triplesEncoding.encode (xs.flatMap f) = xs.flatMap (fun a => triplesEncoding.encode (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, encoded_append, ih]

theorem graphWords_encode (φ : CNF) : graphWords φ = triplesEncoding.encode (denseTriples φ) := by
  simp only [graphWords, yWords, zWords, denseTriples, encoded_flatMap]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  unfold edgeWord
  split <;> simp [triplesEncoding, encTerminated, encodeTriple]

noncomputable def denseTriplesComputable :
    TM2ComputableInPolyTime cnfEncoding triplesEncoding denseTriples :=
  { toTM2ComputableAux := graphWordsComputable.toTM2ComputableAux
    time := graphWordsComputable.time
    outputsFun := fun φ => by
      simpa only [wordEncoding, graphWords_encode] using graphWordsComputable.outputsFun φ }

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

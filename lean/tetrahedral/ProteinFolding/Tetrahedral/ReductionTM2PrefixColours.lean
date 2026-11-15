import ProteinFolding.Tetrahedral.ReductionTM2Pipeline

/-! Source-only computation of the nonbulk colour list, with the finite frame
and ring colour constants explicit. Their concrete geometric identification
is not assumed by any complexity theorem in this module. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.PrefixColours

open Computability Turing TM2CompositionPoly TM2ProductMap

noncomputable def replicateComputable {A : Type} (e : FinEncoding A) (a : A) :
    TM2ComputableInPolyTime unaryFinEncodingNat (TM2ListMap.listEncoding e) (fun n => List.replicate n a) := by
  let hc := TM2Constants.constantComputable (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) e a
  let h := compose (pairComputable (idComputableInPolyTime unaryFinEncodingNat) TM2UnaryRange.rangeComputable)
    (TM2ListMap.mapComputable e hc)
  exact changeFunction h (fun n => by simp only [Function.comp_def, List.map_const', List.length_range])

def nonbulk (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours) (I : Packing.Instance) :
    List ColourFlags.Colours :=
  [(true, true), (true, true), (true, true), frame] ++
    List.replicate (I.bins + 1) (true, true) ++ [(true, true)] ++
    List.replicate I.sizes.length (true, true) ++ [(true, false)] ++ rings

noncomputable def itemCountComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat (fun I : Packing.Instance => I.sizes.length) :=
  compose (g := List.length) sourceItemsComputable (listLengthComputable unaryFinEncodingNat)

set_option maxHeartbeats 1200000 in
noncomputable def computable (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours) :
    TM2ComputableInPolyTime Packing.instanceEncoding
      (TM2ListMap.listEncoding ColourFlags.coloursEncoding) (nonbulk frame rings) := by
  let he := ColourFlags.coloursEncoding
  let hs := compose (add Packing.binsComputable (natConstant _ 1))
    (replicateComputable he (true, true))
  let hi := compose itemCountComputable (replicateComputable he (true, true))
  let h := listConcat (listConcat (listConcat (listConcat (listConcat
    (TM2Constants.constantComputable _ (TM2ListMap.listEncoding he)
      [(true, true), (true, true), (true, true), frame]) hs)
    (TM2Constants.constantComputable _ (TM2ListMap.listEncoding he) [(true, true)])) hi)
    (TM2Constants.constantComputable _ (TM2ListMap.listEncoding he) [(true, false)]))
    (TM2Constants.constantComputable _ (TM2ListMap.listEncoding he) rings)
  exact changeFunction h (fun I => rfl)

noncomputable def reduction (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours)
    (I : Packing.Instance) : HPInstance := Pipeline.output (I, nonbulk frame rings I)

set_option maxHeartbeats 1200000 in
/-- A source-only actual reduction machine for each fixed finite choice of
frame/ring colours. Correctness still requires identifying those colours and
proving the canonical bulk scan's geometric specifications. -/
noncomputable def reductionComputable (frame : ColourFlags.Colours) (rings : List ColourFlags.Colours) :
    TM2ComputableInPolyTime Packing.instanceEncoding hpEncoding (reduction frame rings) :=
  compose (g := Pipeline.output) (pairComputable (idComputableInPolyTime Packing.instanceEncoding) (computable frame rings)) Pipeline.computable

end ProteinFolding.Tetrahedral.ReductionTM2.PrefixColours

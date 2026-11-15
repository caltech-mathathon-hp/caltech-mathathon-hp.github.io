import ProteinFolding.Tetrahedral.ReductionTM2ZipComputable
import ProteinFolding.Common.TM2WordFold

/-! Compute incoming-linker parity flags from an initial endpoint colour and
the ordered start/end colours of every unit. The finite zipper shifts the
end colours by one, and a finite word fold compares each resulting pair. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.ColourFlags

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev Colours := Bool × Bool
abbrev Input := Bool × List Colours
def coloursEncoding := pairEncoding finEncodingBoolBool finEncodingBoolBool
def inputEncoding := pairEncoding finEncodingBoolBool (TM2ListMap.listEncoding coloursEncoding)

def colourWord (b : Bool) : Sequence := if b then [.H] else [.P]
def bodyWords (cs : List Colours) : List Sequence := cs.map (fun c => colourWord c.1)
def priorEnds (seed : Bool) (cs : List Colours) : List Bool := seed :: cs.map Prod.snd

def recordStep (st : Bool × Bool) : PairSymbol Bool Residue → Bool × Bool
  | .left b => (b, st.2)
  | .sep => st
  | .right r => (st.1, st.1 == decide (r = .H))

def recordBit (r : FlaggedBody) : Bool :=
  ((flaggedBodyEncoding.encode r).foldl recordStep (false, false)).2

def flags (x : Input) : List Bool :=
  (Zip.zipFields (priorEnds x.1 x.2) (bodyWords x.2)).map recordBit

theorem recordBit_colourWord (a b : Bool) : recordBit (a, colourWord b) = (a == b) := by
  cases a <;> cases b <;> decide

theorem flags_nil (seed : Bool) : flags (seed, []) = [] := rfl

theorem flags_cons (seed : Bool) (c : Colours) (cs : List Colours) :
    flags (seed, c :: cs) = (seed == c.1) :: flags (c.2, cs) := by
  unfold flags priorEnds bodyWords
  simp only [List.map_cons, Zip.zipFields, List.getElem?_cons_zero, Option.getD_some,
    List.drop_succ_cons, List.drop_zero, recordBit_colourWord]

noncomputable def recordBitComputable :
    TM2ComputableInPolyTime flaggedBodyEncoding finEncodingBoolBool recordBit := by
  let h := TM2WordFold.computable (PairSymbol Bool Residue) (Bool × Bool)
    recordStep Prod.snd (false, false)
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun r => by
      simpa only [wordEncoding, recordBit, id_eq] using h.outputsFun (flaggedBodyEncoding.encode r) }

noncomputable def childStartComputable :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool coloursEncoding) finEncodingBoolBool
      (fun x : Bool × Colours => x.2.1) :=
  compose (TM2PairProjections.sndComputable finEncodingBoolBool coloursEncoding)
    (TM2PairProjections.fstComputable finEncodingBoolBool finEncodingBoolBool)

noncomputable def childEndComputable :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool coloursEncoding) finEncodingBoolBool
      (fun x : Bool × Colours => x.2.2) :=
  compose (TM2PairProjections.sndComputable finEncodingBoolBool coloursEncoding)
    (TM2PairProjections.sndComputable finEncodingBoolBool finEncodingBoolBool)

noncomputable def childWordComputable :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool coloursEncoding) sequenceEncoding
      (fun x : Bool × Colours => colourWord x.2.1) :=
  TM2Conditional.iteComputable childStartComputable (wordConstant _ [.H]) (wordConstant _ [.P])

noncomputable def seedComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool (fun x : Input => x.1) :=
  TM2PairProjections.fstComputable finEncodingBoolBool (TM2ListMap.listEncoding coloursEncoding)

noncomputable def bodyWordsComputable :
    TM2ComputableInPolyTime inputEncoding bodyListEncoding (fun x : Input => bodyWords x.2) :=
  TM2ListMap.mapComputable sequenceEncoding childWordComputable

theorem flatMap_singletons {A B : Type} (f : A → B) (xs : List A) :
    xs.flatMap (fun a => [f a]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]

noncomputable def priorEndsComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Bool) (fun x : Input => priorEnds x.1 x.2) := by
  let htail := TM2ListMap.flatMapComputable (TM2Conditional.boolWordComputable childEndComputable)
  let h := compose (pairComputable (TM2Conditional.boolWordComputable seedComputable) htail)
    (TM2PairProjections.concatComputable Bool)
  exact changeFunction h (fun x => by
    simp only [Function.comp_def, TM2ListMap.mappedFunction, flatMap_singletons,
      List.singleton_append, priorEnds])

set_option maxHeartbeats 1200000 in
noncomputable def zippedComputable :
    TM2ComputableInPolyTime inputEncoding (TM2ListMap.listEncoding flaggedBodyEncoding)
      (fun x : Input => Zip.zipFields (priorEnds x.1 x.2) (bodyWords x.2)) :=
  compose (pairComputable bodyWordsComputable priorEndsComputable) Zip.zipFieldsComputable

noncomputable def childBitComputable :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool flaggedBodyEncoding) (wordEncoding Bool)
      (fun x : Bool × FlaggedBody => [recordBit x.2]) :=
  TM2Conditional.boolWordComputable (compose (g := recordBit)
    (TM2PairProjections.sndComputable finEncodingBoolBool flaggedBodyEncoding) recordBitComputable)

set_option maxHeartbeats 1200000 in
noncomputable def computable : TM2ComputableInPolyTime inputEncoding (wordEncoding Bool) flags :=
  changeFunction (compose (pairComputable seedComputable zippedComputable)
    (TM2ListMap.flatMapComputable childBitComputable))
      (fun _ => flatMap_singletons recordBit _)

end ProteinFolding.Tetrahedral.ReductionTM2.ColourFlags

import ProteinFolding.Common.CookLevinProofFunctionCompiler
import ProteinFolding.Common.CookLevinProofSelectedCellCompiler
import ProteinFolding.Common.CookLevinProofRangeCNFCompiler
import ProteinFolding.Common.CookLevinProofFactorThree

namespace ProteinFolding.SAT.CookLevinStepCompiler

open Computability Turing TM2CompositionPoly CookLevinAlphabet CookLevinWindow CookLevinCells
  CookLevinRows CookLevinRowIndex CookLevinPaddedWindow CookLevinReferenceCompiler
  CookLevinFunctionCompiler CookLevinRangeCNFCompiler CookLevinFactorThree CookLevinAddressCompiler

noncomputable def controlFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  functionFormula (windowRef tm M t) (controlRef tm M t) (fun w => w.1)

noncomputable def executionFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  functionFormula (windowRef tm M t) (replacementRef tm M t) (executePaddedWindow tm)

noncomputable def nextControlFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  functionFormula (replacementRef tm M t) (controlRef tm M (t + 1)) (fun r => (r.1, r.2.1))

noncomputable def prefixFormula (tm : FinTM2) (M t : ℕ) (k : tm.K)
    (i : Fin (machineReadBound tm)) : CNF :=
  toCellFormula tm M t (windowRef tm M t) k i.val (fun w => ((w.2 k).val)[i.val]?)

noncomputable def queryFormula (tm : FinTM2) (M t n : ℕ) (k : tm.K)
    (i : Fin (cellWindowWidth tm)) : CNF :=
  toCellFormula tm M t (queryRef tm M t n k) k (cellBase tm n + i.val) (fun q => q i)

noncomputable def formula (tm : FinTM2) (M t : ℕ) : CNF := by
  letI := tm.kFin
  exact controlFormula tm M t ++ executionFormula tm M t ++ nextControlFormula tm M t ++
    Finset.univ.toList.flatMap (fun k =>
      (List.finRange (machineReadBound tm)).flatMap (prefixFormula tm M t k) ++
      (List.range M).flatMap (fun n =>
        (List.finRange (cellWindowWidth tm)).flatMap (queryFormula tm M t n k) ++
          CookLevinSelectedCellCompiler.formula tm k M t n))

noncomputable def computable {X : Type} {ex : FinEncoding X} (tm : FinTM2) (M t : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => formula tm (M x) (t x)) := by
  letI := tm.kFin
  let hc := functionCompiler (fun w x => windowRef tm (M x) (t x) w)
    (fun c x => controlRef tm (M x) (t x) c) (fun w => w.1)
    (fun w => windowRefCompiler tm M t w hM ht) (fun c => controlRefCompiler tm M t c hM ht)
  let he := functionCompiler (fun w x => windowRef tm (M x) (t x) w)
    (fun r x => replacementRef tm (M x) (t x) r) (executePaddedWindow tm)
    (fun w => windowRefCompiler tm M t w hM ht) (fun r => replacementRefCompiler tm M t r hM ht)
  let ht1 := addMaps ht (TM2Constants.constantComputable ex unaryFinEncodingNat 1)
  let hnc := functionCompiler (fun r x => replacementRef tm (M x) (t x) r)
    (fun c x => controlRef tm (M x) (t x + 1) c) (fun r => (r.1, r.2.1))
    (fun r => replacementRefCompiler tm M t r hM ht)
    (fun c => controlRefCompiler tm M (fun x => t x + 1) c hM ht1)
  have hprefix (k : tm.K) : TM2ComputableInPolyTime ex cnfEncoding
      (fun x => (List.finRange (machineReadBound tm)).flatMap (prefixFormula tm (M x) (t x) k)) := by
    apply fixedListCNFCompiler
    intro i
    exact toCellCompiler tm M t (fun _ => i.val) (fun w x => windowRef tm (M x) (t x) w) k
      (fun w => ((w.2 k).val)[i.val]?) hM ht
      (TM2Constants.constantComputable ex unaryFinEncodingNat i.val)
      (fun w => windowRefCompiler tm M t w hM ht)
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let M' : X × ℕ → ℕ := fun p => M p.1
  let t' : X × ℕ → ℕ := fun p => t p.1
  let n' : X × ℕ → ℕ := Prod.snd
  let hM' := compose hfst hM
  let ht' := compose hfst ht
  let hn' := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  have hquery (k : tm.K) : TM2ComputableInPolyTime (pairEncoding ex unaryFinEncodingNat) cnfEncoding
      (fun p => (List.finRange (cellWindowWidth tm)).flatMap (queryFormula tm (M' p) (t' p) (n' p) k)) := by
    apply fixedListCNFCompiler
    intro i
    let hpos := addMaps
      (subtractMaps hn' (TM2Constants.constantComputable _ unaryFinEncodingNat (replacementBound tm)))
      (TM2Constants.constantComputable _ unaryFinEncodingNat i.val)
    exact toCellCompiler tm M' t' (fun p => cellBase tm (n' p) + i.val)
      (fun q p => queryRef tm (M' p) (t' p) (n' p) k q) k
      (fun q => q i) hM' ht' hpos
      (fun q => queryRefCompiler tm M' t' n' k q hM' ht' hn')
  have hpositions (k : tm.K) : TM2ComputableInPolyTime ex cnfEncoding
      (fun x => (List.range (M x)).flatMap (fun n =>
        (List.finRange (cellWindowWidth tm)).flatMap (queryFormula tm (M x) (t x) n k) ++
          CookLevinSelectedCellCompiler.formula tm k (M x) (t x) n)) := by
    exact rangeCNFCompiler M _ hM (appendCompiler (hquery k)
      (CookLevinSelectedCellCompiler.computable tm k M' t' n' hM' ht' hn'))
  let hall := fixedListCNFCompiler Finset.univ.toList
    (fun k x => (List.finRange (machineReadBound tm)).flatMap (prefixFormula tm (M x) (t x) k) ++
      (List.range (M x)).flatMap (fun n =>
        (List.finRange (cellWindowWidth tm)).flatMap (queryFormula tm (M x) (t x) n k) ++
          CookLevinSelectedCellCompiler.formula tm k (M x) (t x) n))
    (fun k => appendCompiler (hprefix k) (hpositions k))
  exact appendCompiler (appendCompiler (appendCompiler hc he) hnc) hall

end ProteinFolding.SAT.CookLevinStepCompiler

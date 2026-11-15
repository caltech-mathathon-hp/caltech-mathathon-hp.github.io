import ProteinFolding.Common.CookLevinProofRangeCNFCompiler
import ProteinFolding.Common.CookLevinProofReferenceCompiler
import ProteinFolding.Common.CookLevinProofRelationCompiler
import ProteinFolding.Common.CookLevinProofFactorThree
import ProteinFolding.Common.CookLevinProofRowRename

namespace ProteinFolding.SAT.CookLevinRowCompiler

open Computability Turing TM2CompositionPoly CookLevinRows CookLevinRowIndex CookLevinAlphabet
  CookLevinWindow CookLevinPaddedWindow CookLevinCells CookLevinReferenceCompiler
  CookLevinRelationCompiler CookLevinRangeCNFCompiler CookLevinFactorThree CookLevinLocal
  CookLevinStepCNF CookLevinGlobalCNF CookLevinRowRename

noncomputable def codeFormula (A : Type) [Fintype A] (refs : A → ℕ) : CNF :=
  relationCNF (Finset.univ.toList.map refs) (codeAllowed A)

noncomputable def codeFormulaCompiler {X A : Type} [Fintype A] {ex : FinEncoding X}
    (refs : A → X → ℕ) (h : ∀ a, TM2ComputableInPolyTime ex unaryFinEncodingNat (refs a)) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => codeFormula A (fun a => refs a x)) :=
  relationCNFListCompiler Finset.univ.toList (codeAllowed A) refs h

noncomputable def controlFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  codeFormula (Control tm) (controlRef tm M t)

noncomputable def windowFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  codeFormula (PaddedWindow tm) (windowRef tm M t)

noncomputable def replacementFormula (tm : FinTM2) (M t : ℕ) : CNF :=
  codeFormula (Replacement tm) (replacementRef tm M t)

noncomputable def cellFormula (tm : FinTM2) (M t n : ℕ) (k : tm.K) : CNF :=
  codeFormula (Option (Symbol tm k)) (cellRef tm M t n k)

noncomputable def queryFormula (tm : FinTM2) (M t n : ℕ) (k : tm.K) : CNF :=
  codeFormula (CellWindow tm k) (queryRef tm M t n k)

noncomputable def formula (tm : FinTM2) (M t : ℕ) : CNF := by
  letI := tm.kFin
  exact controlFormula tm M t ++ windowFormula tm M t ++ replacementFormula tm M t ++
    Finset.univ.toList.flatMap (fun k => (List.range M).flatMap (fun n =>
      cellFormula tm M t n k ++ queryFormula tm M t n k))

noncomputable def computable {X : Type} {ex : FinEncoding X} (tm : FinTM2) (M t : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => formula tm (M x) (t x)) := by
  letI := tm.kFin
  let hc := codeFormulaCompiler (fun c x => controlRef tm (M x) (t x) c)
    (fun c => controlRefCompiler tm M t c hM ht)
  let hw := codeFormulaCompiler (fun w x => windowRef tm (M x) (t x) w)
    (fun w => windowRefCompiler tm M t w hM ht)
  let hr := codeFormulaCompiler (fun r x => replacementRef tm (M x) (t x) r)
    (fun r => replacementRefCompiler tm M t r hM ht)
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let M' : X × ℕ → ℕ := fun p => M p.1
  let t' : X × ℕ → ℕ := fun p => t p.1
  let n' : X × ℕ → ℕ := Prod.snd
  let hM' := compose hfst hM
  let ht' := compose hfst ht
  let hn' := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  have hk (k : tm.K) : TM2ComputableInPolyTime ex cnfEncoding
      (fun x => (List.range (M x)).flatMap (fun n =>
        cellFormula tm (M x) (t x) n k ++ queryFormula tm (M x) (t x) n k)) := by
    let hcell := codeFormulaCompiler (fun b p => cellRef tm (M' p) (t' p) (n' p) k b)
      (fun b => cellRefCompiler tm M' t' n' k b hM' ht' hn')
    let hquery := codeFormulaCompiler (fun q p => queryRef tm (M' p) (t' p) (n' p) k q)
      (fun q => queryRefCompiler tm M' t' n' k q hM' ht' hn')
    exact rangeCNFCompiler M
      (fun p : X × ℕ => cellFormula tm (M p.1) (t p.1) p.2 k ++
        queryFormula tm (M p.1) (t p.1) p.2 k) hM (appendCompiler hcell hquery)
  let hall := fixedListCNFCompiler Finset.univ.toList
    (fun k x => (List.range (M x)).flatMap (fun n =>
      cellFormula tm (M x) (t x) n k ++ queryFormula tm (M x) (t x) n k)) hk
  exact appendCompiler (appendCompiler (appendCompiler hc hw) hr) hall

end ProteinFolding.SAT.CookLevinRowCompiler

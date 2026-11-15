import ProteinFolding.Common.CookLevinProofBoundaryCompiler

namespace ProteinFolding.SAT.CookLevinFinalCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinAlphabet CookLevinRows
  CookLevinStepCNF CookLevinGlobalCNF CookLevinRowRename CookLevinBoundaryCompiler
  CookLevinRangeCNFCompiler CookLevinWordLookup CookLevinReferenceCompiler CookLevinFactorThree
  CookLevinRuns CookLevinLinks CookLevinCircuit

noncomputable def stackCellPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t n : X → ℕ) (k : tm.K) (w : List (Symbol tm k))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => cellPins tm (M x) (t x) (n x) k w[n x]?) := by
  classical
  let hw := TM2Constants.constantComputable ex (wordEncoding (Symbol tm k)) w
  have hp (b : Option (Symbol tm k)) : TM2ComputableInPolyTime ex finEncodingBoolBool
      (fun x => decide (b = w[n x]?)) := by
    let h := compose (pairComputable hw hn) (lookupTestComputable (Symbol tm k) b)
    simpa only [Function.comp_def, lookupTest, eq_comm] using h
  exact finitePinsCompiler (fun b x => cellRef tm (M x) (t x) (n x) k b)
    (fun b x => decide (b = w[n x]?))
    (fun b => cellRefCompiler tm M t n k b hM ht hn) hp

noncomputable def formula (tm : FinTM2) (M t : ℕ) (c : tm.Cfg)
    (hs : StacksIn (machineSymbols tm) c.stk) : CNF := by
  letI := tm.kFin
  exact controlPins tm M t (c.l, c.var) ++ Finset.univ.toList.flatMap (fun k =>
    (List.range M).flatMap (fun n => cellPins tm M t n k ((encodedStack tm c hs k)[n]?)))

noncomputable def computable {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (c : tm.Cfg) (hs : StacksIn (machineSymbols tm) c.stk)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => formula tm (M x) (t x) c hs) := by
  letI := tm.kFin
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let M' : X × ℕ → ℕ := fun p => M p.1
  let t' : X × ℕ → ℕ := fun p => t p.1
  let n' : X × ℕ → ℕ := Prod.snd
  let hM' := compose hfst hM
  let ht' := compose hfst ht
  let hn' := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  have hk (k : tm.K) : TM2ComputableInPolyTime ex cnfEncoding
      (fun x => (List.range (M x)).flatMap (fun n =>
        cellPins tm (M x) (t x) n k ((encodedStack tm c hs k)[n]?))) := by
    exact rangeCNFCompiler M _ hM
      (stackCellPinsCompiler tm M' t' n' k (encodedStack tm c hs k) hM' ht' hn')
  exact appendCompiler (controlPinsCompiler tm M t (c.l, c.var) hM ht)
    (fixedListCNFCompiler Finset.univ.toList _ hk)

theorem formula_eq (tm : FinTM2) (M t : ℕ) (c : tm.Cfg)
    (hs : StacksIn (machineSymbols tm) c.stk) :
    formula tm M t c hs = renameCNF (renameIndex tm M) (pins (boundaryBindings tm M t c hs)) := by
  letI := tm.kFin
  rw [boundaryBindings, pins_append, renameCNF_append]
  unfold formula
  rw [controlPins_eq, pins_flatMap, renameCNF_flatMap]
  congr 1
  apply List.flatMap_congr
  intro k _
  rw [pins_flatMap, renameCNF_flatMap, range_flatMap_finRange]
  exact List.flatMap_congr (fun n _ => cellPins_eq tm M t n k _)

noncomputable def finalBindingsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (c : tm.Cfg) (hs : StacksIn (machineSymbols tm) c.stk)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x =>
      renameCNF (renameIndex tm (M x)) (pins (boundaryBindings tm (M x) (t x) c hs))) := by
  have he : (fun x => formula tm (M x) (t x) c hs) =
      (fun x => renameCNF (renameIndex tm (M x)) (pins (boundaryBindings tm (M x) (t x) c hs))) :=
    funext (fun x => formula_eq tm (M x) (t x) c hs)
  rw [← he]
  exact computable tm M t c hs hM ht

end ProteinFolding.SAT.CookLevinFinalCompiler

import ProteinFolding.Common.CookLevinProofStepCompilerCorrectness

namespace ProteinFolding.SAT.CookLevinGlobalCompiler

open Computability Turing TM2CompositionPoly CookLevinRows CookLevinRowRename CookLevinGlobalCNF
  CookLevinLocal CookLevinRangeCNFCompiler CookLevinFactorThree CookLevinAddressCompiler

noncomputable def formula (tm : FinTM2) (M T : ℕ) : CNF :=
  (List.range (T + 1)).flatMap (CookLevinRowCompiler.formula tm M) ++
    (List.range T).flatMap (CookLevinStepCompiler.formula tm M)

noncomputable def computable {X : Type} {ex : FinEncoding X} (tm : FinTM2) (M T : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hT : TM2ComputableInPolyTime ex unaryFinEncodingNat T) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => formula tm (M x) (T x)) := by
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let M' : X × ℕ → ℕ := fun p => M p.1
  let t' : X × ℕ → ℕ := Prod.snd
  let hM' := compose hfst hM
  let ht' := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  let hT1 := addMaps hT (TM2Constants.constantComputable ex unaryFinEncodingNat 1)
  let hrows := rangeCNFCompiler (fun x => T x + 1)
    (fun p => CookLevinRowCompiler.formula tm (M' p) (t' p)) hT1
    (CookLevinRowCompiler.computable tm M' t' hM' ht')
  let hsteps := rangeCNFCompiler T
    (fun p => CookLevinStepCompiler.formula tm (M' p) (t' p)) hT
    (CookLevinStepCompiler.computable tm M' t' hM' ht')
  exact appendCompiler hrows hsteps

theorem rename_append (f : ℕ → ℕ) (φ ψ : CNF) :
    renameCNF f (φ ++ ψ) = renameCNF f φ ++ renameCNF f ψ := by
  simp only [renameCNF, List.map_append]

theorem compile_append (cs ds : List Constraint) :
    compileConstraints (cs ++ ds) = compileConstraints cs ++ compileConstraints ds := by
  simp only [compileConstraints, List.flatMap_append]

theorem rename_compile_flatMap {A : Type*} (f : ℕ → ℕ) (xs : List A) (cs : A → List Constraint) :
    renameCNF f (compileConstraints (xs.flatMap cs)) =
      xs.flatMap (fun x => renameCNF f (compileConstraints (cs x))) := by
  simp only [compileConstraints, renameCNF, List.map_flatMap, List.flatMap_assoc]

theorem formula_eq_arithmeticGlobalCNF (tm : FinTM2) (M T : ℕ) :
    formula tm M T = arithmeticGlobalCNF tm M T := by
  unfold arithmeticGlobalCNF globalCNF globalConstraints
  rw [compile_append, rename_append, rename_compile_flatMap, rename_compile_flatMap]
  unfold formula
  congr 1
  · apply List.flatMap_congr
    intro t _
    exact CookLevinRowCompilerCorrectness.formula_eq_renamed tm M t
  · apply List.flatMap_congr
    intro t _
    exact CookLevinStepCompilerCorrectness.formula_eq_renamed tm M t

noncomputable def arithmeticGlobalCNFCompiler {X : Type} {ex : FinEncoding X}
    (tm : FinTM2) (M T : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hT : TM2ComputableInPolyTime ex unaryFinEncodingNat T) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => arithmeticGlobalCNF tm (M x) (T x)) := by
  have he : (fun x => formula tm (M x) (T x)) =
      (fun x => arithmeticGlobalCNF tm (M x) (T x)) :=
    funext (fun x => formula_eq_arithmeticGlobalCNF tm (M x) (T x))
  rw [← he]
  exact computable tm M T hM hT

end ProteinFolding.SAT.CookLevinGlobalCompiler

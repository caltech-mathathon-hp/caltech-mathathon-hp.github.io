import ProteinFolding.Common.CookLevinProofStepCompiler
import ProteinFolding.Common.CookLevinProofRowCompilerCorrectness

namespace ProteinFolding.SAT.CookLevinStepCompilerCorrectness

open Computability Turing CookLevinRows CookLevinRowIndex CookLevinReferenceCompiler
  CookLevinFunctionCompiler CookLevinStepCompiler CookLevinLocal CookLevinStepCNF
  CookLevinGlobalCNF CookLevinRowRename CookLevinPaddedWindow CookLevinWindow CookLevinCells

noncomputable def factor (tm : FinTM2) (M : ℕ) (c : Constraint) : CNF :=
  relationCNF (renameConstraint (renameIndex tm M) c).vars
    (renameConstraint (renameIndex tm M) c).allowed

theorem controlFormula_eq (tm : FinTM2) (M t : ℕ) :
    controlFormula tm M t = factor tm M (controlLink tm M t) := by
  simpa only [controlFormula, controlLink, factor, ← controlRef_eq, ← windowRef_eq] using
    functionFormula_eq_renamed tm M t t (windowTag tm M) (controlTag tm M) (fun w => w.1)

theorem executionFormula_eq (tm : FinTM2) (M t : ℕ) :
    executionFormula tm M t = factor tm M (executionLink tm M t) := by
  have he : executionLink tm M t = functionFactor tm M t t
      (windowTag tm M) (replacementTag tm M) (executePaddedWindow tm) := rfl
  rw [he]
  simpa only [executionFormula, factor, ← replacementRef_eq, ← windowRef_eq] using
    functionFormula_eq_renamed tm M t t (windowTag tm M) (replacementTag tm M) (executePaddedWindow tm)

theorem nextControlFormula_eq (tm : FinTM2) (M t : ℕ) :
    nextControlFormula tm M t = factor tm M (nextControlLink tm M t) := by
  simpa only [nextControlFormula, nextControlLink, factor, ← controlRef_eq, ← replacementRef_eq] using
    functionFormula_eq_renamed tm M t (t + 1) (replacementTag tm M) (controlTag tm M)
      (fun r => (r.1, r.2.1))

theorem prefixFormula_eq (tm : FinTM2) (M t : ℕ) (k : tm.K) (i : Fin (machineReadBound tm)) :
    prefixFormula tm M t k i = factor tm M (prefixLink tm M t k i) := by
  simpa only [prefixFormula, prefixLink, factor, ← windowRef_eq] using
    toCellFormula_eq_renamed tm M t (windowTag tm M) k i.val (fun w => ((w.2 k).val)[i.val]?)

theorem queryFormula_eq (tm : FinTM2) (M t : ℕ) (k : tm.K) (n : Fin M)
    (i : Fin (cellWindowWidth tm)) :
    queryFormula tm M t n.val k i = factor tm M (queryLink tm M t k n i) := by
  simpa only [queryFormula, queryLink, factor, ← queryRef_eq] using
    toCellFormula_eq_renamed tm M t (queryTag tm M k n) k (cellBase tm n.val + i.val) (fun q => q i)

theorem selectedFormula_eq (tm : FinTM2) (M t : ℕ) (k : tm.K) (n : Fin M) :
    CookLevinSelectedCellCompiler.formula tm k M t n.val =
      factor tm M (selectedCellLink tm M t k n) := by
  rw [CookLevinSelectedCellCompiler.formula_eq_renamed, rename_relationCNF]
  rfl

theorem formula_eq_renamed (tm : FinTM2) (M t : ℕ) :
    formula tm M t = renameCNF (renameIndex tm M)
      (compileConstraints (stepConstraints tm M t)) := by
  letI := tm.kFin
  rw [rename_compileConstraints]
  simp only [compileConstraints, List.flatMap_map]
  change formula tm M t = (stepConstraints tm M t).flatMap (factor tm M)
  simp only [stepConstraints, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_assoc, List.flatMap_map, ← controlFormula_eq, ← executionFormula_eq,
    ← nextControlFormula_eq, ← prefixFormula_eq, ← queryFormula_eq, ← selectedFormula_eq,
    formula, List.append_nil, List.append_assoc]
  congr 1
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  apply congrArg (fun tail => (List.finRange (machineReadBound tm)).flatMap
    (prefixFormula tm M t k) ++ tail)
  exact (CookLevinRowCompilerCorrectness.flatMap_finRange M (fun n =>
    (List.finRange (cellWindowWidth tm)).flatMap (queryFormula tm M t n k) ++
      CookLevinSelectedCellCompiler.formula tm k M t n)).symm

noncomputable def stepConstraintsCompiler {X : Type} {ex : FinEncoding X}
    (tm : FinTM2) (M t : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => renameCNF (renameIndex tm (M x))
        (compileConstraints (stepConstraints tm (M x) (t x)))) := by
  have he : (fun x => formula tm (M x) (t x)) =
      (fun x => renameCNF (renameIndex tm (M x))
        (compileConstraints (stepConstraints tm (M x) (t x)))) :=
    funext (fun x => formula_eq_renamed tm (M x) (t x))
  rw [← he]
  exact CookLevinStepCompiler.computable tm M t hM ht

end ProteinFolding.SAT.CookLevinStepCompilerCorrectness

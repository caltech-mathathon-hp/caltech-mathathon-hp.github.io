import ProteinFolding.Common.CookLevinProofRowCompiler

namespace ProteinFolding.SAT.CookLevinRowCompilerCorrectness

open Computability Turing CookLevinRows CookLevinRowIndex CookLevinReferenceCompiler
  CookLevinLocal CookLevinStepCNF CookLevinGlobalCNF CookLevinRowRename CookLevinRowCompiler

theorem compiled_component {A : Type} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) :
    relationCNF
      (renameConstraint (renameIndex tm M)
        (shiftConstraint (t * width tm M) (componentConstraint tm M tag))).vars
      (renameConstraint (renameIndex tm M)
        (shiftConstraint (t * width tm M) (componentConstraint tm M tag))).allowed =
      codeFormula A (fun a => arithmeticReference tm M t (tag a)) := by
  rw [rename_shifted_component]
  simp only [codeFormula, codeSlots, List.map_map, Function.comp_def]

theorem flatMap_finRange {A : Type*} (M : ℕ) (f : ℕ → List A) :
    (List.finRange M).flatMap (fun n => f n.val) = (List.range M).flatMap f := by
  rw [← List.map_coe_finRange M, List.flatMap_map]

theorem formula_eq_renamed (tm : FinTM2) (M t : ℕ) :
    formula tm M t = renameCNF (renameIndex tm M)
      (compileConstraints (rowConstraints tm M t)) := by
  letI := tm.kFin
  rw [rename_compileConstraints]
  simp only [rowConstraints, validityConstraints, List.map_append, List.map_cons, List.map_nil,
    List.map_flatMap, List.map_map, compileConstraints, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_map, List.flatMap_assoc, Function.comp_def,
    compiled_component]
  simp only [← controlRef_eq, ← windowRef_eq, ← replacementRef_eq, ← cellRef_eq, ← queryRef_eq,
    formula, controlFormula, windowFormula, replacementFormula, cellFormula, queryFormula,
    flatMap_finRange, List.append_nil, List.append_assoc]
  congr 1
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  exact (flatMap_finRange M (fun n =>
    codeFormula (Option (CookLevinAlphabet.Symbol tm k)) (cellRef tm M t n k) ++
      codeFormula (CookLevinCells.CellWindow tm k) (queryRef tm M t n k))).symm

noncomputable def rowConstraintsCompiler {X : Type} {ex : FinEncoding X}
    (tm : FinTM2) (M t : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex ProteinFolding.SAT.cnfEncoding
      (fun x => renameCNF (renameIndex tm (M x))
        (compileConstraints (rowConstraints tm (M x) (t x)))) := by
  have he : (fun x => formula tm (M x) (t x)) =
      (fun x => renameCNF (renameIndex tm (M x))
        (compileConstraints (rowConstraints tm (M x) (t x)))) :=
    funext (fun x => formula_eq_renamed tm (M x) (t x))
  rw [← he]
  exact CookLevinRowCompiler.computable tm M t hM ht

end ProteinFolding.SAT.CookLevinRowCompilerCorrectness

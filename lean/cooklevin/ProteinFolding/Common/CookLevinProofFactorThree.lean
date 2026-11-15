import ProteinFolding.Common.CookLevinProofWidthThree
import ProteinFolding.Common.CookLevinProofTemplateCompiler
import ProteinFolding.Common.CookLevinProofArithmeticCompiler

/-! Actual polynomial TM2 emission of fixed-arity width-three clause gadgets.
The original literal indices and the auxiliary base are supplied by genuine
unary-index machines. Every emitted clause has one or three literals. -/

namespace ProteinFolding.SAT.CookLevinFactorThree

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinWidthThree
  CookLevinTemplateCompiler CookLevinLiteralCompiler CookLevinMapCompiler

noncomputable def addConstantCompiler {X : Type} {ex : FinEncoding X} {f : X → ℕ}
    (h : TM2ComputableInPolyTime ex unaryFinEncodingNat f) (k : ℕ) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x + k) := by
  let hm := compose (pairComputable h (TM2Constants.constantComputable ex unaryFinEncodingNat k))
    CookLevinArithmeticCompiler.additionComputable
  exact hm

noncomputable def appendCompiler {X : Type} {ex : FinEncoding X} {f g : X → CNF}
    (hf : TM2ComputableInPolyTime ex cnfEncoding f) (hg : TM2ComputableInPolyTime ex cnfEncoding g) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => f x ++ g x) := by
  let h := compose (pairComputable (cnfWordComputable hf) (cnfWordComputable hg))
    (TM2PairProjections.concatComputable Sym)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun x := by
        simpa only [Function.comp_def, cnfEncoding_append, wordEncoding, id_eq] using h.outputsFun x }

theorem indexedClause_succ {X : Type} (q : ℕ) (indices : Fin (q + 1) → X → ℕ)
    (positive : Fin (q + 1) → X → Bool) (x : X) :
    indexedClause (q + 1) indices positive x = ⟨indices 0 x, positive 0 x⟩ ::
      indexedClause q (fun i => indices i.succ) (fun i => positive i.succ) x := by
  simp [indexedClause, List.finRange_succ, List.map_map, Function.comp_def]

noncomputable def chainCompiler {X : Type} {ex : FinEncoding X} (q k : ℕ)
    (base : X → ℕ) (indices : Fin q → X → ℕ) (positive : Fin q → X → Bool)
    (hb : TM2ComputableInPolyTime ex unaryFinEncodingNat base)
    (hi : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices i))
    (hp : ∀ i, TM2ComputableInPolyTime ex finEncodingBoolBool (positive i)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => chain (base x) k (indexedClause q indices positive x)) := by
  induction q generalizing k with
  | zero =>
    let hm := compose
      (pairComputable (addConstantCompiler hb k) (TM2Constants.constantComputable ex finEncodingBoolBool false))
      singletonCNFComputable
    exact hm
  | succ q ih =>
    let headIndices : Fin 3 → X → ℕ
      | 0 => fun x => base x + k
      | 1 => indices 0
      | 2 => fun x => base x + (k + 1)
    let headPositive : Fin 3 → X → Bool
      | 0 => fun _ => false
      | 1 => positive 0
      | 2 => fun _ => true
    let hIndex : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (headIndices i) := by
      intro i
      match i with
      | 0 => exact addConstantCompiler hb k
      | 1 => exact hi 0
      | 2 => exact addConstantCompiler hb (k + 1)
    let hPositive : ∀ i, TM2ComputableInPolyTime ex finEncodingBoolBool (headPositive i) := by
      intro i
      match i with
      | 0 => exact TM2Constants.constantComputable ex finEncodingBoolBool false
      | 1 => exact hp 0
      | 2 => exact TM2Constants.constantComputable ex finEncodingBoolBool true
    let hh := fixedClauseCompiler 3 headIndices headPositive hIndex hPositive
    let ht := ih (k + 1) (fun i => indices i.succ) (fun i => positive i.succ)
      (fun i => hi i.succ) (fun i => hp i.succ)
    have he : (fun x => chain (base x) k (indexedClause (q + 1) indices positive x)) =
        (fun x => [indexedClause 3 headIndices headPositive x] ++
          chain (base x) (k + 1) (indexedClause q (fun i => indices i.succ) (fun i => positive i.succ) x)) := by
      funext x
      rw [indexedClause_succ, chain]
      rfl
    rw [he]
    exact appendCompiler hh ht

noncomputable def gadgetCompiler {X : Type} {ex : FinEncoding X} (q : ℕ)
    (base : X → ℕ) (indices : Fin q → X → ℕ) (positive : Fin q → X → Bool)
    (hb : TM2ComputableInPolyTime ex unaryFinEncodingNat base)
    (hi : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices i))
    (hp : ∀ i, TM2ComputableInPolyTime ex finEncodingBoolBool (positive i)) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => gadget (base x) (indexedClause q indices positive x)) := by
  let hfirst := compose
    (pairComputable hb (TM2Constants.constantComputable ex finEncodingBoolBool true)) singletonCNFComputable
  let htail := chainCompiler q 0 base indices positive hb hi hp
  exact appendCompiler hfirst htail

theorem gadgetCompiler_width {X : Type} (q : ℕ) (base : X → ℕ)
    (indices : Fin q → X → ℕ) (positive : Fin q → X → Bool) (x : X) :
    ThreeCNF.WidthAtMostThree (gadget (base x) (indexedClause q indices positive x)) :=
  gadget_width _ _

end ProteinFolding.SAT.CookLevinFactorThree

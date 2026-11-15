import ProteinFolding.Common.CookLevinProofRelationCompiler
import ProteinFolding.Common.CookLevinProofCellClamp
import ProteinFolding.Common.CookLevinProofClampedCompiler
import ProteinFolding.Common.CookLevinProofReferenceCompiler
import ProteinFolding.Common.CookLevinProofRowRename

namespace ProteinFolding.SAT.CookLevinSelectedCellCompiler

open Computability Turing TM2CompositionPoly CookLevinAlphabet CookLevinWindow CookLevinCells
  CookLevinRows CookLevinRowIndex CookLevinStepCNF CookLevinRowRename CookLevinLocal
  CookLevinRelationCompiler CookLevinClampedCompiler CookLevinCellClamp
  CookLevinReferenceCompiler CookLevinAddressCompiler

abbrev Slot (tm : FinTM2) (k : tm.K) :=
  Replacement tm ⊕ CellWindow tm k ⊕ Option (Symbol tm k)

noncomputable def slots (tm : FinTM2) (k : tm.K) : List (Slot tm k) :=
  Finset.univ.toList.map Sum.inl ++ Finset.univ.toList.map (Sum.inr ∘ Sum.inl) ++
    Finset.univ.toList.map (Sum.inr ∘ Sum.inr)

noncomputable def index (tm : FinTM2) (k : tm.K) (M t n : ℕ) : Slot tm k → ℕ
  | .inl r => replacementRef tm M t r
  | .inr (.inl q) => queryRef tm M t n k q
  | .inr (.inr b) => cellRef tm M (t + 1) n k b

noncomputable def formula (tm : FinTM2) (k : tm.K) (M t n : ℕ) : CNF :=
  relationCNF ((slots tm k).map (index tm k M t n)) (cellAllowed tm k n)

theorem indices_eq (tm : FinTM2) (k : tm.K) (M t : ℕ) (n : Fin M) :
    (slots tm k).map (index tm k M t n.val) =
      ((selectedCellLink tm M t k n).vars).map (renameIndex tm M) := by
  simp only [selectedCellLink, List.map_append, rename_codeRefs, codeSlots, List.map_map,
    slots, Function.comp_def, index, replacementRef_eq, cellRef_eq, queryRef_eq]

theorem formula_eq_renamed (tm : FinTM2) (k : tm.K) (M t : ℕ) (n : Fin M) :
    formula tm k M t n.val = renameCNF (renameIndex tm M)
      (relationCNF (selectedCellLink tm M t k n).vars (selectedCellLink tm M t k n).allowed) := by
  rw [rename_relationCNF]
  simp only [formula, indices_eq, selectedCellLink]

noncomputable def computable {X : Type} {ex : FinEncoding X} (tm : FinTM2) (k : tm.K)
    (M t n : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => formula tm k (M x) (t x) (n x)) := by
  let indices : Slot tm k → X → ℕ := fun d x => index tm k (M x) (t x) (n x) d
  have hi : ∀ d, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices d) := by
    intro d
    rcases d with r | q | b
    · exact replacementRefCompiler tm M t r hM ht
    · exact queryRefCompiler tm M t n k q hM ht hn
    · exact cellRefCompiler tm M (fun x => t x + 1) n k b hM
        (addMaps ht (TM2Constants.constantComputable ex unaryFinEncodingNat 1)) hn
  let f : ℕ → X → CNF := fun j x =>
    relationCNF ((slots tm k).map (fun d => indices d x)) (cellAllowed tm k j)
  have hf : ∀ j, TM2ComputableInPolyTime ex cnfEncoding (f j) := fun j =>
    relationCNFListCompiler (slots tm k) (cellAllowed tm k j) indices hi
  have h := clampedFamilyComputable ex cnfEncoding n hn (replacementBound tm) f hf
  have he : (fun x => formula tm k (M x) (t x) (n x)) =
      (fun x => f (min (n x) (replacementBound tm)) x) := by
    funext x
    dsimp only [f, formula, indices]
    rw [cellAllowed_clamp tm k (n x)]
  rw [he]
  exact h

end ProteinFolding.SAT.CookLevinSelectedCellCompiler

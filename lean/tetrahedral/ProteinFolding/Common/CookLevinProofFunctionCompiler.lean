import ProteinFolding.Common.CookLevinProofRelationCompiler
import ProteinFolding.Common.CookLevinProofReferenceCompiler
import ProteinFolding.Common.CookLevinProofRowRename
import ProteinFolding.Common.TM2UnaryComparison

namespace ProteinFolding.SAT.CookLevinFunctionCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinAlphabet
  CookLevinRows CookLevinStepCNF CookLevinRowRename CookLevinReferenceCompiler CookLevinRelationCompiler
  CookLevinLocal

noncomputable def values (A : Type) [Fintype A] : List A := Finset.univ.toList

noncomputable def functionFormula {A B : Type} [Fintype A] [Fintype B]
    (refsA : A → ℕ) (refsB : B → ℕ) (f : A → B) : CNF :=
  relationCNF ((values A).map refsA ++ (values B).map refsB) (functionAllowed f)

noncomputable def functionCompiler {X A B : Type} [Fintype A] [Fintype B]
    {ex : FinEncoding X} (refsA : A → X → ℕ) (refsB : B → X → ℕ) (f : A → B)
    (ha : ∀ a, TM2ComputableInPolyTime ex unaryFinEncodingNat (refsA a))
    (hb : ∀ b, TM2ComputableInPolyTime ex unaryFinEncodingNat (refsB b)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => functionFormula (fun a => refsA a x) (fun b => refsB b x) f) := by
  let slots : List (A ⊕ B) := (values A).map Sum.inl ++ (values B).map Sum.inr
  let refs : A ⊕ B → X → ℕ
    | .inl a => refsA a
    | .inr b => refsB b
  have hi : ∀ s, TM2ComputableInPolyTime ex unaryFinEncodingNat (refs s) := by
    intro s
    cases s with
    | inl a => exact ha a
    | inr b => exact hb b
  simpa only [slots, List.map_append, List.map_map, Function.comp_def, refs, functionFormula] using
    relationCNFListCompiler slots (functionAllowed f) refs hi

noncomputable def toCellFormula {A : Type} [Fintype A] (tm : FinTM2)
    (M t : ℕ) (refs : A → ℕ) (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k)) : CNF :=
  if n < M then functionFormula refs (cellRef tm M t n k) f
  else relationCNF ((values A).map refs)
    (fun bs => functionAllowed f (bs ++ CookLevinWindowCNF.finiteCode (none : Option (Symbol tm k))))

noncomputable def toCellCompiler {X A : Type} [Fintype A] {ex : FinEncoding X}
    (tm : FinTM2) (M t n : X → ℕ) (refs : A → X → ℕ) (k : tm.K)
    (f : A → Option (Symbol tm k))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n)
    (hrefs : ∀ a, TM2ComputableInPolyTime ex unaryFinEncodingNat (refs a)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => toCellFormula tm (M x) (t x) (fun a => refs a x) k (n x) f) := by
  let hp := compose (pairComputable hn hM) TM2UnaryComparison.ltComputable
  let hy := functionCompiler refs (fun b x => cellRef tm (M x) (t x) (n x) k b) f hrefs
    (fun b => cellRefCompiler tm M t n k b hM ht hn)
  let hn := relationCNFListCompiler (values A)
    (fun bs => functionAllowed f (bs ++ CookLevinWindowCNF.finiteCode (none : Option (Symbol tm k)))) refs hrefs
  have h := TM2Conditional.iteComputable hp hy hn
  simpa only [Function.comp_def, toCellFormula, decide_eq_true_eq] using h

theorem functionFormula_eq_renamed {A B : Type} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u : ℕ) (tagA : A → Bit tm M) (tagB : B → Bit tm M) (f : A → B) :
    functionFormula (fun a => CookLevinRowIndex.arithmeticReference tm M t (tagA a))
      (fun b => CookLevinRowIndex.arithmeticReference tm M u (tagB b)) f =
    relationCNF (renameConstraint (renameIndex tm M)
      (functionFactor tm M t u tagA tagB f)).vars
      (renameConstraint (renameIndex tm M) (functionFactor tm M t u tagA tagB f)).allowed := by
  rw [rename_functionFactor]
  simp only [functionFormula, values, codeSlots, List.map_map, Function.comp_def]

theorem toCellFormula_eq_renamed {A : Type} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k)) :
    toCellFormula tm M t (fun a => CookLevinRowIndex.arithmeticReference tm M t (tag a)) k n f =
      relationCNF (renameConstraint (renameIndex tm M) (toCellFactor tm M t tag k n f)).vars
        (renameConstraint (renameIndex tm M) (toCellFactor tm M t tag k n f)).allowed := by
  unfold toCellFormula toCellFactor
  split_ifs with hn
  · have he : cellRef tm M t n k = (fun b =>
        CookLevinRowIndex.arithmeticReference tm M t (cellTag tm M k ⟨n, hn⟩ b)) := by
      funext b
      exact cellRef_eq tm M t ⟨n, hn⟩ k b
    rw [he]
    exact functionFormula_eq_renamed tm M t t tag _ f
  · simp only [renameConstraint, rename_codeRefs, codeSlots, List.map_map, Function.comp_def, values]

end ProteinFolding.SAT.CookLevinFunctionCompiler

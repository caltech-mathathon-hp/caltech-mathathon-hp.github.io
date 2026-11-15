import ProteinFolding.Common.CookLevinProofTemplateCompiler
import ProteinFolding.Common.CookLevinProofLocal

namespace ProteinFolding.SAT.CookLevinRelationCompiler

open Computability Turing CookLevinCircuit CookLevinLocal CookLevinTemplateCompiler

theorem blockingClause_zipWith (vars : List ℕ) (bs : List Bool) :
    blockingClause vars bs = vars.zipWith (fun i b => (⟨i, !b⟩ : Literal)) bs := by
  induction vars generalizing bs with
  | nil => cases bs <;> rfl
  | cons i vars ih => cases bs <;> simp [blockingClause, List.zipWith, ih]

theorem blockingClause_indexed {X : Type} (q : ℕ) (indices : Fin q → X → ℕ)
    (bs : List Bool) (hbs : bs.length = q) (x : X) :
    blockingClause ((List.finRange q).map (fun i => indices i x)) bs =
      indexedClause q indices (fun i _ => !(bs[i.val]'(by rw [hbs]; exact i.isLt))) x := by
  rw [blockingClause_zipWith]
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_map, List.length_finRange, hbs, Nat.min_self,
      indexedClause_length]
  · intro i hi hj
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_finRange, indexedClause]
    rfl

def forbiddenPatterns (q : ℕ) (allowed : List Bool → Bool) : List (List Bool) :=
  (bitWords q).filter (fun bs => !(allowed bs))

theorem forbiddenPattern_length (q : ℕ) (allowed : List Bool → Bool)
    (j : Fin (forbiddenPatterns q allowed).length) :
    ((forbiddenPatterns q allowed)[j.val]).length = q := by
  apply (bitWords_mem q _).mp
  exact (List.mem_filter.mp (List.getElem_mem j.isLt)).1

def patternPositive (q : ℕ) (allowed : List Bool → Bool)
    (j : Fin (forbiddenPatterns q allowed).length) (i : Fin q) : Bool :=
  !((forbiddenPatterns q allowed)[j.val][i.val]'(by rw [forbiddenPattern_length]; exact i.isLt))

theorem relationCNF_skeleton {X : Type} (q : ℕ) (allowed : List Bool → Bool)
    (indices : Fin q → X → ℕ) (x : X) :
    relationCNF ((List.finRange q).map (fun i => indices i x)) allowed =
      skeletonFormula (forbiddenPatterns q allowed).length (fun _ => q)
        (fun _ => indices) (fun j i _ => patternPositive q allowed j i) x := by
  unfold relationCNF
  simp only [List.length_map, List.length_finRange]
  change (forbiddenPatterns q allowed).map _ = _
  conv_lhs => rw [← List.ofFn_getElem (forbiddenPatterns q allowed), List.ofFn_eq_map]
  simp only [List.map_map, skeletonFormula, ← List.map_eq_flatMap]
  apply List.map_congr_left
  intro j _
  exact blockingClause_indexed q indices _ (forbiddenPattern_length q allowed j) x

noncomputable def relationCNFCompiler {X : Type} {ex : FinEncoding X} (q : ℕ)
    (allowed : List Bool → Bool) (indices : Fin q → X → ℕ)
    (hi : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices i)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => relationCNF ((List.finRange q).map (fun i => indices i x)) allowed) := by
  let hp := fun (j : Fin (forbiddenPatterns q allowed).length) (i : Fin q) =>
    TM2Constants.constantComputable ex finEncodingBoolBool (patternPositive q allowed j i)
  let hm := fixedSkeletonCompiler (forbiddenPatterns q allowed).length (fun _ => q)
    (fun _ => indices) (fun j i _ => patternPositive q allowed j i) (fun _ => hi) hp
  have he : (fun x => relationCNF ((List.finRange q).map (fun i => indices i x)) allowed) =
      skeletonFormula (forbiddenPatterns q allowed).length (fun _ => q)
        (fun _ => indices) (fun j i _ => patternPositive q allowed j i) := by
    funext x
    exact relationCNF_skeleton q allowed indices x
  rw [he]
  exact hm

noncomputable def relationCNFListCompiler {X D : Type} {ex : FinEncoding X}
    (slots : List D) (allowed : List Bool → Bool) (indices : D → X → ℕ)
    (hi : ∀ d, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices d)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => relationCNF (slots.map (fun d => indices d x)) allowed) := by
  let hm := relationCNFCompiler slots.length allowed
    (fun i : Fin slots.length => indices slots[i.val]) (fun i => hi slots[i.val])
  have hslots (x : X) : (List.finRange slots.length).map (fun i => indices slots[i.val] x) =
      slots.map (fun d => indices d x) := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem_eq_map slots (fun d => indices d x)
  have he : (fun x => relationCNF ((List.finRange slots.length).map (fun i => indices slots[i.val] x)) allowed) =
      (fun x => relationCNF (slots.map (fun d => indices d x)) allowed) := by
    funext x
    rw [hslots]
  rw [← he]
  exact hm

end ProteinFolding.SAT.CookLevinRelationCompiler

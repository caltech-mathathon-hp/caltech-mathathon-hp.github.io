import ProteinFolding.Common.TM2Embedding

/-! A counted TM2 loop that drains one stack into another, converting symbols
and reversing their order. All other stacks and the ambient state are preserved.
Two such loops provide the order-preserving handoff in sequential composition.
The nonempty-alphabet case is explicit through `Inhabited`; no such assumption
is imposed on the frozen encoding definitions. -/

namespace ProteinFolding.TM2Transfer

open Turing TM2

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
variable (src dst : K)

def setStacks (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v : List (Γ dst)) :
    ∀ k, List (Γ k) :=
  Function.update (Function.update S src u) dst v

theorem setStacks_src (hne : src ≠ dst) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ dst)) : setStacks src dst S u v src = u := by
  simp [setStacks, hne]

theorem setStacks_dst (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ dst)) : setStacks src dst S u v dst = v := by
  simp [setStacks]

theorem setStacks_update_src (hne : src ≠ dst) (S : ∀ k, List (Γ k))
    (u u' : List (Γ src)) (v : List (Γ dst)) :
    Function.update (setStacks src dst S u v) src u' = setStacks src dst S u' v := by
  funext k
  by_cases hs : k = src
  · subst k; simp [setStacks, hne]
  · by_cases hd : k = dst
    · subst k; simp [setStacks, hne.symm]
    · simp [setStacks, hs, hd]

theorem setStacks_update_dst (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v v' : List (Γ dst)) :
    Function.update (setStacks src dst S u v) dst v' = setStacks src dst S u v' := by
  simp only [setStacks, Function.update_idem]

def transferStmt [Inhabited (Γ src)] (convert : Γ src → Γ dst) (loop finish : Λ) :
    Stmt Γ Λ (σ × Option (Γ src)) :=
  .pop src (fun st x => (st.1, x))
    (.branch (fun st => st.2.isSome)
      (.push dst (fun st => convert (st.2.getD default)) (.goto (fun _ => loop)))
      (.goto (fun _ => finish)))

def transferCfg (label : Λ) (s : σ) (reg : Option (Γ src))
    (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v : List (Γ dst)) :
    Cfg Γ Λ (σ × Option (Γ src)) where
  l := some label
  var := (s, reg)
  stk := setStacks src dst S u v

theorem transfer_step_cons [Inhabited (Γ src)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ src)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (a : Γ src) (u : List (Γ src)) (v : List (Γ dst)) :
    step program (transferCfg src dst loop s reg S (a :: u) v) =
      some (transferCfg src dst loop s (some a) S u (convert a :: v)) := by
  simp only [transferCfg, step, hprogram, transferStmt, stepAux,
    setStacks_src src dst hne, List.head?_cons, List.tail_cons,
    setStacks_update_src src dst hne, setStacks_dst,
    Option.isSome_some, cond_true, Option.getD_some, setStacks_update_dst]

theorem transfer_step_nil [Inhabited (Γ src)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ src)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k)) (v : List (Γ dst)) :
    step program (transferCfg src dst loop s reg S [] v) =
      some (transferCfg src dst finish s none S [] v) := by
  simp only [transferCfg, step, hprogram, transferStmt, stepAux,
    setStacks_src src dst hne, List.head?_nil, List.tail_nil,
    setStacks_update_src src dst hne, Option.isSome_none, cond_false]

/-- Exactly one step per transferred symbol, plus the final empty-stack test.
The register is cleared and the continuation label is entered. -/
theorem transfer_run [Inhabited (Γ src)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ src)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ dst)) :
    (fun x : Option (Cfg Γ Λ (σ × Option (Γ src))) => x.bind (step program))^[u.length + 1]
      (some (transferCfg src dst loop s reg S u v)) =
        some (transferCfg src dst finish s none S [] ((u.map convert).reverse ++ v)) := by
  induction u generalizing reg v with
  | nil =>
    simpa using transfer_step_nil src dst hne convert loop finish program hprogram s reg S v
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1,
      Function.iterate_succ_apply]
    simp only [Option.bind_some, transfer_step_cons src dst hne convert loop finish program
      hprogram s reg S a u v]
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (some a) (convert a :: v)

end ProteinFolding.TM2Transfer

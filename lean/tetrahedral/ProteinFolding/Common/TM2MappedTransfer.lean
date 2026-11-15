import ProteinFolding.Common.TM2Transfer

/-! Transfer with a register in the target alphabet. Only the target alphabet
needs a default symbol; source alphabets may be empty. -/

namespace ProteinFolding.TM2MappedTransfer

open Turing TM2 TM2Transfer

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
variable (src dst : K)

def transferStmt [Inhabited (Γ dst)] (convert : Γ src → Γ dst) (loop finish : Λ) :
    Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun st x => (st.1, x.map convert))
    (.branch (fun st => st.2.isSome)
      (.push dst (fun st => st.2.getD default) (.goto (fun _ => loop)))
      (.goto (fun _ => finish)))

def transferCfg (label : Λ) (s : σ) (reg : Option (Γ dst))
    (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v : List (Γ dst)) :
    Cfg Γ Λ (σ × Option (Γ dst)) where
  l := some label
  var := (s, reg)
  stk := setStacks src dst S u v

theorem transfer_step_cons [Inhabited (Γ dst)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ dst)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ dst)) (S : ∀ k, List (Γ k))
    (a : Γ src) (u : List (Γ src)) (v : List (Γ dst)) :
    step program (transferCfg src dst loop s reg S (a :: u) v) =
      some (transferCfg src dst loop s (some (convert a)) S u (convert a :: v)) := by
  simp only [transferCfg, step, hprogram, transferStmt, stepAux,
    setStacks_src src dst hne, List.head?_cons, List.tail_cons, Option.map_some,
    setStacks_update_src src dst hne, setStacks_dst,
    Option.isSome_some, cond_true, Option.getD_some, setStacks_update_dst]

theorem transfer_step_nil [Inhabited (Γ dst)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ dst)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ dst)) (S : ∀ k, List (Γ k)) (v : List (Γ dst)) :
    step program (transferCfg src dst loop s reg S [] v) =
      some (transferCfg src dst finish s none S [] v) := by
  simp only [transferCfg, step, hprogram, transferStmt, stepAux,
    setStacks_src src dst hne, List.head?_nil, List.tail_nil, Option.map_none,
    setStacks_update_src src dst hne, Option.isSome_none, cond_false]

theorem transfer_run [Inhabited (Γ dst)] (hne : src ≠ dst)
    (convert : Γ src → Γ dst) (loop finish : Λ)
    (program : Λ → Stmt Γ Λ (σ × Option (Γ dst)))
    (hprogram : program loop = transferStmt src dst convert loop finish)
    (s : σ) (reg : Option (Γ dst)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ dst)) :
    (fun x : Option (Cfg Γ Λ (σ × Option (Γ dst))) => x.bind (step program))^[u.length + 1]
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
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (some (convert a)) (convert a :: v)

end ProteinFolding.TM2MappedTransfer

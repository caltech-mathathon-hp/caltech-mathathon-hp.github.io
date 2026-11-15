import ProteinFolding.Common.TM2Transfer

/-! A finite TM2 duplication loop for the all-suffix walk verifier. It consumes
the source, reverses converted letters onto two buffers, and preserves every
other stack and the ambient state. Subsequent transfer loops can restore both
copies. Source nonemptiness is explicit; the verifier source alphabet is an
option type, inhabited by the parser-error marker. -/

namespace ProteinFolding.TM2WalkCopy

open Turing TM2

variable {K L σ : Type} {Γ : K → Type} [DecidableEq K]
variable (src one two : K)

def contents (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v : List (Γ one))
    (w : List (Γ two)) : ∀ k, List (Γ k) :=
  Function.update (Function.update (Function.update S src u) one v) two w

theorem contents_src (h01 : src ≠ one) (h02 : src ≠ two) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) : contents src one two S u v w src = u := by
  simp [contents, h01, h02]

theorem contents_one (h12 : one ≠ two) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) : contents src one two S u v w one = v := by
  simp [contents, h12]

theorem contents_two (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) : contents src one two S u v w two = w := by
  simp [contents]

theorem update_src (h01 : src ≠ one) (h02 : src ≠ two) (h12 : one ≠ two)
    (S : ∀ k, List (Γ k)) (u u' : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) :
    Function.update (contents src one two S u v w) src u' = contents src one two S u' v w := by
  funext k
  by_cases hs : k = src
  · subst k; simp [contents, h01, h02]
  · by_cases h1 : k = one
    · subst k; simp [contents, h01.symm, h12]
    · by_cases h2 : k = two
      · subst k; simp [contents, h02.symm]
      · simp [contents, hs, h1, h2]

theorem update_one (_h01 : src ≠ one) (h12 : one ≠ two)
    (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v v' : List (Γ one)) (w : List (Γ two)) :
    Function.update (contents src one two S u v w) one v' = contents src one two S u v' w := by
  funext k
  by_cases h1 : k = one
  · subst k; simp [contents, h12]
  · by_cases h2 : k = two
    · subst k; simp [contents, h12.symm]
    · simp [contents, h1, h2]

theorem update_two (S : ∀ k, List (Γ k)) (u : List (Γ src)) (v : List (Γ one)) (w w' : List (Γ two)) :
    Function.update (contents src one two S u v w) two w' = contents src one two S u v w' := by
  simp only [contents, Function.update_idem]

def duplicateStmt [Inhabited (Γ src)] (f : Γ src → Γ one) (g : Γ src → Γ two)
    (loop finish : L) : Stmt Γ L (σ × Option (Γ src)) :=
  .pop src (fun st x => (st.1, x))
    (.branch (fun st => st.2.isSome)
      (.push one (fun st => f (st.2.getD default))
        (.push two (fun st => g (st.2.getD default)) (.goto (fun _ => loop))))
      (.goto (fun _ => finish)))

def cfg (label : L) (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) : Cfg Γ L (σ × Option (Γ src)) :=
  ⟨some label, (s, reg), contents src one two S u v w⟩

theorem duplicate_step_cons [Inhabited (Γ src)]
    (h01 : src ≠ one) (h02 : src ≠ two) (h12 : one ≠ two)
    (f : Γ src → Γ one) (g : Γ src → Γ two) (loop finish : L)
    (program : L → Stmt Γ L (σ × Option (Γ src)))
    (hprogram : program loop = duplicateStmt src one two f g loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (a : Γ src) (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) :
    step program (cfg src one two loop s reg S (a :: u) v w) =
      some (cfg src one two loop s (some a) S u (f a :: v) (g a :: w)) := by
  simp only [cfg, step, hprogram, duplicateStmt, stepAux, contents_src src one two h01 h02,
    List.head?_cons, List.tail_cons, update_src src one two h01 h02 h12,
    Option.isSome_some, cond_true, Option.getD_some, contents_one src one two h12,
    update_one src one two h01 h12, contents_two, update_two]

theorem duplicate_step_nil [Inhabited (Γ src)]
    (h01 : src ≠ one) (h02 : src ≠ two) (h12 : one ≠ two)
    (f : Γ src → Γ one) (g : Γ src → Γ two) (loop finish : L)
    (program : L → Stmt Γ L (σ × Option (Γ src)))
    (hprogram : program loop = duplicateStmt src one two f g loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (v : List (Γ one)) (w : List (Γ two)) :
    step program (cfg src one two loop s reg S [] v w) =
      some (cfg src one two finish s none S [] v w) := by
  simp only [cfg, step, hprogram, duplicateStmt, stepAux, contents_src src one two h01 h02,
    List.head?_nil, List.tail_nil, update_src src one two h01 h02 h12, Option.isSome_none, cond_false]

theorem duplicate_run [Inhabited (Γ src)]
    (h01 : src ≠ one) (h02 : src ≠ two) (h12 : one ≠ two)
    (f : Γ src → Γ one) (g : Γ src → Γ two) (loop finish : L)
    (program : L → Stmt Γ L (σ × Option (Γ src)))
    (hprogram : program loop = duplicateStmt src one two f g loop finish)
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) :
    (fun x : Option (Cfg Γ L (σ × Option (Γ src))) => x.bind (step program))^[u.length + 1]
      (some (cfg src one two loop s reg S u v w)) =
        some (cfg src one two finish s none S [] ((u.map f).reverse ++ v) ((u.map g).reverse ++ w)) := by
  induction u generalizing reg v w with
  | nil =>
    simpa using duplicate_step_nil src one two h01 h02 h12 f g loop finish program hprogram s reg S v w
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, duplicate_step_cons src one two h01 h02 h12 f g loop finish program
      hprogram s reg S a u v w]
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (some a) (f a :: v) (g a :: w)

end ProteinFolding.TM2WalkCopy

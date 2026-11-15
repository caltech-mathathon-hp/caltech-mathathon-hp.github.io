import ProteinFolding.Common.TM2ListMapCore

/-! Counted parser and transfer executions for the parameterized record mapper. -/

namespace ProteinFolding.TM2Renaming

open Turing TM2

theorem relabelStmt_inverse {K Λ σ τ : Type} {Γ : K → Type}
    (e : σ ≃ τ) (q : Stmt Γ Λ σ) : relabelStmt e.symm (relabelStmt e q) = q := by
  induction q <;> simp_all [relabelStmt]

theorem relabelStmt_inverse' {K Λ σ τ : Type} {Γ : K → Type}
    (e : σ ≃ τ) (q : Stmt Γ Λ τ) : relabelStmt e (relabelStmt e.symm q) = q :=
  relabelStmt_inverse e.symm q

theorem transfer_run {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (src dst : K) [Inhabited (Γ src)] (hne : src ≠ dst)
    (e : (σ × Option (Γ src)) ≃ τ) (convert : Γ src → Γ dst) (loop finalLabel : Λ)
    (program : Λ → Stmt Γ Λ τ)
    (hprogram : program loop = relabelStmt e (TM2Transfer.transferStmt src dst convert loop finalLabel))
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ dst)) :
    (fun x : Option (Cfg Γ Λ τ) => x.bind (step program))^[u.length + 1]
      (some (mapCfg e (TM2Transfer.transferCfg src dst loop s reg S u v))) =
        some (mapCfg e (TM2Transfer.transferCfg src dst finalLabel s none S []
          ((u.map convert).reverse ++ v))) := by
  let raw := fun l => relabelStmt e.symm (program l)
  have hrule : raw loop = TM2Transfer.transferStmt src dst convert loop finalLabel := by
    dsimp only [raw]
    rw [hprogram, relabelStmt_inverse]
  have hr := TM2Transfer.transfer_run src dst hne convert loop finalLabel raw hrule s reg S u v
  have hm := run_relabelStmt e raw (u.length + 1) _ _ hr
  simpa only [raw, relabelStmt_inverse'] using hm

theorem duplicate_run {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (src one two : K) [Inhabited (Γ src)]
    (h01 : src ≠ one) (h02 : src ≠ two) (h12 : one ≠ two)
    (e : (σ × Option (Γ src)) ≃ τ)
    (f : Γ src → Γ one) (g : Γ src → Γ two) (loop finalLabel : Λ)
    (program : Λ → Stmt Γ Λ τ)
    (hprogram : program loop = relabelStmt e (TM2WalkCopy.duplicateStmt src one two f g loop finalLabel))
    (s : σ) (reg : Option (Γ src)) (S : ∀ k, List (Γ k))
    (u : List (Γ src)) (v : List (Γ one)) (w : List (Γ two)) :
    (fun x : Option (Cfg Γ Λ τ) => x.bind (step program))^[u.length + 1]
      (some (mapCfg e (TM2WalkCopy.cfg src one two loop s reg S u v w))) =
        some (mapCfg e (TM2WalkCopy.cfg src one two finalLabel s none S []
          ((u.map f).reverse ++ v) ((u.map g).reverse ++ w))) := by
  let raw := fun l => relabelStmt e.symm (program l)
  have hrule : raw loop = TM2WalkCopy.duplicateStmt src one two f g loop finalLabel := by
    dsimp only [raw]
    rw [hprogram, relabelStmt_inverse]
  have hr := TM2WalkCopy.duplicate_run src one two h01 h02 h12 f g loop finalLabel raw hrule
    s reg S u v w
  have hm := run_relabelStmt e raw (u.length + 1) _ _ hr
  simpa only [raw, relabelStmt_inverse'] using hm

end ProteinFolding.TM2Renaming

namespace ProteinFolding.TM2ListMap

open Computability Turing TM2

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

theorem update_input (S : ∀ k, List (h.tm.Γ k)) (raw raw' : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .input) raw' =
      contents h S raw' p r b acc out := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_parameter (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p p' r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .parameter) p' =
      contents h S raw p' r b acc out := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_record (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r r' b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .record) r' =
      contents h S raw p r' b acc out := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_parameterBuffer (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b b' : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .parameterBuffer) b' =
      contents h S raw p r b' acc out := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_accumulator (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc acc' : List (OutLetter h)) (out : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .accumulator) acc' =
      contents h S raw p r b acc' out := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_output (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out out' : List B) :
    Function.update (contents h S raw p r b acc out) (.inr .output) out' =
      contents h S raw p r b acc out' := by
  funext k; cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_child (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B)
    (k : h.tm.K) (w : List (h.tm.Γ k)) :
    Function.update (contents h S raw p r b acc out) (.inl k) w =
      contents h (Function.update S k w) raw p r b acc out :=
  TM2Embedding.joinStacks_update S _ k w

def leftCode (w : List ep.Γ) : List (InLetter h) :=
  w.map (fun a => h.inputAlphabet.symm (.left a))

def rightCode (w : List ea.Γ) : List (InLetter h) :=
  w.map (fun a => h.inputAlphabet.symm (.right a))

section Inhabited
variable [Inhabited B]

theorem parameter_step (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (a : ep.Γ) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .parameter (s, reg) S (.left a :: raw) p r b acc out) =
      some (cfg h .parameter (s, (some (h.inputAlphabet.symm (.left a)), reg.2))
        S raw (h.inputAlphabet.symm (.left a) :: p) r b acc out) := by
  simp [cfg, program, step, stepAux, contents, extraContents, TM2Embedding.joinStacks,
    rawToInput, isSeparator]
  change Function.update
    (Function.update (contents h S (.left a :: raw) p r b acc out) (.inr .input) raw)
      (.inr .parameter) (h.inputAlphabet.symm (.left a) :: p) = _
  rw [update_input, update_parameter]
  rfl

theorem parameter_separator_step (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .parameter (s, reg) S (.sep :: raw) p r b acc out) =
      some (cfg h .record (s, (none, reg.2)) S raw p r b acc out) := by
  simp [cfg, program, step, stepAux, contents, extraContents, TM2Embedding.joinStacks,
    rawToInput, isSeparator, separator]
  exact update_input h S (.sep :: raw) raw p r b acc out

theorem parameter_run (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (w : List ep.Γ) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    run h (w.length + 1) (cfg h .parameter (s, reg) S (w.map .left ++ .sep :: raw) p r b acc out) =
      some (cfg h .record (s, (none, reg.2)) S raw ((leftCode h w).reverse ++ p) r b acc out) := by
  induction w generalizing reg p with
  | nil => simpa [run, leftCode] using parameter_separator_step h s reg S raw p r b acc out
  | cons a w ih =>
    rw [List.length_cons]
    simp only [List.map_cons, List.cons_append]
    rw [run_step h (parameter_step h s reg S a _ p r b acc out)]
    simpa [leftCode, List.reverse_cons, List.append_assoc] using
      ih (some (h.inputAlphabet.symm (.left a)), reg.2) (h.inputAlphabet.symm (.left a) :: p)

theorem record_step (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (a : ea.Γ) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .record (s, reg) S (.right (some a) :: raw) p r b acc out) =
      some (cfg h .record (s, (some (h.inputAlphabet.symm (.right a)), reg.2))
        S raw p (h.inputAlphabet.symm (.right a) :: r) b acc out) := by
  simp [cfg, program, step, stepAux, contents, extraContents, TM2Embedding.joinStacks,
    rawToInput, isSeparator]
  change Function.update
    (Function.update (contents h S (.right (some a) :: raw) p r b acc out) (.inr .input) raw)
      (.inr .record) (h.inputAlphabet.symm (.right a) :: r) = _
  rw [update_input, update_record]
  rfl

theorem record_separator_step (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .record (s, reg) S (.right none :: raw) p r b acc out) =
      some (cfg h .restoreRecord (s, (none, reg.2)) S raw p r b acc out) := by
  simp [cfg, program, step, stepAux, contents, extraContents, TM2Embedding.joinStacks,
    rawToInput, isSeparator, separator]
  exact update_input h S (.right none :: raw) raw p r b acc out

theorem record_run (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (w : List ea.Γ) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    run h (w.length + 1) (cfg h .record (s, reg) S
      (w.map (fun a => .right (some a)) ++ .right none :: raw) p r b acc out) =
      some (cfg h .restoreRecord (s, (none, reg.2)) S raw p ((rightCode h w).reverse ++ r) b acc out) := by
  induction w generalizing reg r with
  | nil => simpa [run, rightCode] using record_separator_step h s reg S raw p r b acc out
  | cons a w ih =>
    rw [List.length_cons]
    simp only [List.map_cons, List.cons_append]
    rw [run_step h (record_step h s reg S a _ p r b acc out)]
    simpa [rightCode, List.reverse_cons, List.append_assoc] using
      ih (some (h.inputAlphabet.symm (.right a)), reg.2) (h.inputAlphabet.symm (.right a) :: r)

theorem record_nil_step (s : h.tm.σ) (reg : Caches h) (S : ∀ k, List (h.tm.Γ k))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .record (s, reg) S [] p r b acc out) =
      some (cfg h .clearParameter (s, (none, reg.2)) S [] p r b acc out) := by
  simp [cfg, program, step, stepAux, contents, extraContents, TM2Embedding.joinStacks]

end Inhabited
end ProteinFolding.TM2ListMap

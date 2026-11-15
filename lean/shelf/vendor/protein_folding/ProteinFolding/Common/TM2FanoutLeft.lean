import ProteinFolding.Common.TM2Fanout
import ProteinFolding.Common.TM2MappedTransfer
import ProteinFolding.Common.TM2Renaming

/-! Applying a polynomial-time machine to one component of an encoded pair.
The second component is kept in a disjoint tagged buffer while the active
machine runs. Loading and output collection restore the canonical word order. -/

namespace ProteinFolding.TM2FanoutLeft

open Computability Turing TM2

inductive AuxSlot where
  | input
  | load
  | right
  | left
  | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan
  | load
  | right
  | separator
  | collect
  | left
  | finish
  deriving DecidableEq, Fintype

variable {X Y Z : Type} {ea : FinEncoding X} {ey : FinEncoding Y} {f : X → Y}
variable (h : TM2ComputableInPolyTime ea ey f) (eb : FinEncoding Z)

abbrev InTag (_h : TM2ComputableInPolyTime ea ey f) (eb : FinEncoding Z) := PairSymbol ea.Γ eb.Γ
abbrev OutTag (_h : TM2ComputableInPolyTime ea ey f) (eb : FinEncoding Z) := PairSymbol ey.Γ eb.Γ
abbrev Labels (h : TM2ComputableInPolyTime ea ey f) (_eb : FinEncoding Z) := h.tm.Λ ⊕ Phase
abbrev State := (h.tm.σ × Option (InTag h eb)) × Option (OutTag h eb)

def AuxAlphabet : AuxSlot → Type
  | .input => InTag h eb
  | .load => InTag h eb
  | _ => OutTag h eb

abbrev Alphabet := Sum.elim h.tm.Γ (AuxAlphabet h eb)

structure Data where
  input : List (InTag h eb)
  load : List (InTag h eb)
  right : List (OutTag h eb)
  left : List (OutTag h eb)
  output : List (OutTag h eb)

def auxContents (d : Data h eb) : ∀ k, List (AuxAlphabet h eb k)
  | .input => d.input
  | .load => d.load
  | .right => d.right
  | .left => d.left
  | .output => d.output

def contents (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) : ∀ k, List (Alphabet h eb k) :=
  TM2Embedding.joinStacks S (auxContents h eb d)

theorem update_active (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb)
    (k : h.tm.K) (w : List (h.tm.Γ k)) :
    Function.update (contents h eb S d) (.inl k) w =
      contents h eb (Function.update S k w) d :=
  TM2Embedding.joinStacks_update S (auxContents h eb d) k w

theorem update_input (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (w : List (InTag h eb)) :
    Function.update (contents h eb S d) (.inr .input) w = contents h eb S {d with input := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, Function.update_of_ne]

theorem update_load (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (w : List (InTag h eb)) :
    Function.update (contents h eb S d) (.inr .load) w = contents h eb S {d with load := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, Function.update_of_ne]

theorem update_right (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (w : List (OutTag h eb)) :
    Function.update (contents h eb S d) (.inr .right) w = contents h eb S {d with right := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, Function.update_of_ne]

theorem update_left (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (w : List (OutTag h eb)) :
    Function.update (contents h eb S d) (.inr .left) w = contents h eb S {d with left := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, Function.update_of_ne]

theorem update_output (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (w : List (OutTag h eb)) :
    Function.update (contents h eb S d) (.inr .output) w = contents h eb S {d with output := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, Function.update_of_ne]

def activeCfg (reg : Option (InTag h eb) × Option (OutTag h eb)) (d : Data h eb) (c : h.tm.Cfg) :
    Cfg (Alphabet h eb) (Labels h eb) (State h eb) where
  l := c.l.elim (some (.inr .right)) (fun l => some (.inl l))
  var := ((c.var, reg.1), reg.2)
  stk := contents h eb c.stk d

def activeStmt : Stmt h.tm.Γ h.tm.Λ h.tm.σ → Stmt (Alphabet h eb) (Labels h eb) (State h eb)
  | .push k f q => .push (.inl k) (fun st => f st.1.1) (activeStmt q)
  | .peek k f q => .peek (.inl k) (fun st o => ((f st.1.1 o, st.1.2), st.2)) (activeStmt q)
  | .pop k f q => .pop (.inl k) (fun st o => ((f st.1.1 o, st.1.2), st.2)) (activeStmt q)
  | .load f q => .load (fun st => ((f st.1.1, st.1.2), st.2)) (activeStmt q)
  | .branch f q r => .branch (fun st => f st.1.1) (activeStmt q) (activeStmt r)
  | .goto f => .goto (fun st => .inl (f st.1.1))
  | .halt => .goto (fun _ => .inr .right)

theorem activeStmt_stepAux (q : Stmt h.tm.Γ h.tm.Λ h.tm.σ) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    stepAux (activeStmt h eb q) ((s, reg.1), reg.2) (contents h eb S d) =
      activeCfg h eb reg d (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
    simpa only [activeStmt, stepAux, contents, TM2Embedding.joinStacks, TM2Embedding.joinStacks_update] using
      ih s (Function.update S k (f s :: S k))
  | peek k f q ih => exact ih (f s (S k).head?) S
  | pop k f q ih =>
    simpa only [activeStmt, stepAux, contents, TM2Embedding.joinStacks, TM2Embedding.joinStacks_update] using
      ih (f s (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f s) S
  | branch f q r ihq ihr =>
    cases hf : f s
    · simpa [activeStmt, stepAux, hf, activeCfg] using ihr s S
    · simpa [activeStmt, stepAux, hf, activeCfg] using ihq s S
  | goto f => rfl
  | halt => rfl

def inputLeft : Option (InTag h eb) → Bool
  | some (.left _) => true
  | _ => false

def inputRight : Option (InTag h eb) → Bool
  | some (.right _) => true
  | _ => false

def rightTag : Option (InTag h eb) → OutTag h eb
  | some (.right b) => .right b
  | _ => .sep

def loadValue (seed : h.tm.Γ h.tm.k₀) : Option (InTag h eb) → h.tm.Γ h.tm.k₀
  | some (.left a) => h.inputAlphabet.symm a
  | _ => seed

def program (seed : Option (h.tm.Γ h.tm.k₀)) :
    Labels h eb → Stmt (Alphabet h eb) (Labels h eb) (State h eb)
  | .inl l => activeStmt h eb (h.tm.m l)
  | .inr .scan => .pop (.inr .input) (fun st x => ((st.1.1, x), st.2))
      (.branch (fun st => st.1.2.isSome)
        (.branch (fun st => inputLeft h eb st.1.2)
          (.push (.inr .load) (fun st => st.1.2.getD PairSymbol.sep) (.goto (fun _ => .inr .scan)))
          (.branch (fun st => inputRight h eb st.1.2)
            (.push (.inr .right) (fun st => rightTag h eb st.1.2) (.goto (fun _ => .inr .scan)))
            (.goto (fun _ => .inr .scan))))
        (.goto (fun _ => .inr .load)))
  | .inr .load => match seed with
    | none => .goto (fun _ => .inl h.tm.main)
    | some x => .pop (.inr .load) (fun st o => ((st.1.1, o), st.2))
        (.branch (fun st => st.1.2.isSome)
          (.push (.inl h.tm.k₀) (fun st => loadValue h eb x st.1.2) (.goto (fun _ => .inr .load)))
          (.goto (fun _ => .inl h.tm.main)))
  | .inr .right =>
    letI : Inhabited (Alphabet h eb (.inr .right)) := ⟨.sep⟩
    TM2Transfer.transferStmt (Γ := Alphabet h eb) (Λ := Labels h eb)
      (σ := h.tm.σ × Option (InTag h eb)) (.inr .right) (.inr .output) id (.inr .right) (.inr .separator)
  | .inr .separator => .push (.inr .output) (fun _ => .sep) (.goto (fun _ => .inr .collect))
  | .inr .collect =>
    letI : Inhabited (Alphabet h eb (.inr .left)) := ⟨.sep⟩
    TM2MappedTransfer.transferStmt (Γ := Alphabet h eb) (Λ := Labels h eb)
      (σ := h.tm.σ × Option (InTag h eb)) (.inl h.tm.k₁) (.inr .left)
      (fun a => .left (h.outputAlphabet a)) (.inr .collect) (.inr .left)
  | .inr .left =>
    letI : Inhabited (Alphabet h eb (.inr .left)) := ⟨.sep⟩
    TM2Transfer.transferStmt (Γ := Alphabet h eb) (Λ := Labels h eb)
      (σ := h.tm.σ × Option (InTag h eb)) (.inr .left) (.inr .output) id (.inr .left) (.inr .finish)
  | .inr .finish => .halt

def phaseCfg (p : Phase) (s : h.tm.σ) (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) : Cfg (Alphabet h eb) (Labels h eb) (State h eb) :=
  ⟨some (.inr p), ((s, reg.1), reg.2), contents h eb S d⟩

@[simp] theorem contents_inl (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (k : h.tm.K) :
    contents h eb S d (.inl k) = S k := rfl

@[simp] theorem contents_inr (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (k : AuxSlot) :
    contents h eb S d (.inr k) = auxContents h eb d k := rfl

def pushTag (a : InTag h eb) (d : Data h eb) : Data h eb := match a with
  | .left a => { d with load := .left a :: d.load }
  | .right b => { d with right := .right b :: d.right }
  | .sep => d

theorem scan_step_cons (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (a : InTag h eb) (u : List (InTag h eb)) :
    step (program h eb seed) (phaseCfg h eb .scan s reg S {d with input := a :: u}) =
      some (phaseCfg h eb .scan s (some a, reg.2) S (pushTag h eb a {d with input := u})) := by
  cases a <;> simp [phaseCfg, program, step, stepAux, auxContents, pushTag,
    inputLeft, inputRight, rightTag, update_input, update_load, update_right]

theorem scan_step_nil (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    step (program h eb seed) (phaseCfg h eb .scan s reg S {d with input := []}) =
      some (phaseCfg h eb .load s (none, reg.2) S {d with input := []}) := by
  simp [phaseCfg, program, step, stepAux, auxContents, update_input]

def keepLeft : InTag h eb → Option (InTag h eb)
  | .left a => some (.left a)
  | _ => none

def keepRight : InTag h eb → Option (OutTag h eb)
  | .right b => some (.right b)
  | _ => none

theorem scan_run (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (u : List (InTag h eb)) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb seed)))^[u.length + 1]
      (some (phaseCfg h eb .scan s reg S {d with input := u})) =
      some (phaseCfg h eb .load s (none, reg.2) S
        {d with input := [], load := (u.filterMap (keepLeft h eb)).reverse ++ d.load, right := (u.filterMap (keepRight h eb)).reverse ++ d.right}) := by
  induction u generalizing reg d with
  | nil => simpa using scan_step_nil h eb seed s reg S d
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, scan_step_cons]
    have hn := ih (some a, reg.2) (pushTag h eb a d)
    cases a <;> simpa [keepLeft, keepRight, pushTag, List.filterMap_cons,
      List.reverse_cons, List.append_assoc] using hn

theorem load_step_cons (seed : h.tm.Γ h.tm.k₀) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb)
    (a : ea.Γ) (u : List ea.Γ) (w : List (h.tm.Γ h.tm.k₀)) :
    step (program h eb (some seed))
      (phaseCfg h eb .load s reg (Function.update S h.tm.k₀ w)
        {d with load := PairSymbol.left a :: u.map PairSymbol.left}) =
      some (phaseCfg h eb .load s (some (.left a), reg.2)
        (Function.update S h.tm.k₀ (h.inputAlphabet.symm a :: w))
        {d with load := u.map PairSymbol.left}) := by
  simp [phaseCfg, program, step, stepAux, auxContents, loadValue,
    update_load, update_active, Function.update_idem]

theorem load_step_nil (seed : h.tm.Γ h.tm.k₀) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    step (program h eb (some seed)) (phaseCfg h eb .load s reg S {d with load := []}) =
      some (activeCfg h eb (none, reg.2) {d with load := []}
        (Cfg.mk (some h.tm.main) s S)) := by
  simp [phaseCfg, activeCfg, program, step, stepAux, auxContents, update_load]

theorem load_run_some (seed : h.tm.Γ h.tm.k₀) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (u : List ea.Γ) (w : List (h.tm.Γ h.tm.k₀)) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb (some seed))))^[u.length + 1]
      (some (phaseCfg h eb .load s reg (Function.update S h.tm.k₀ w)
        {d with load := u.map PairSymbol.left})) =
      some (activeCfg h eb (none, reg.2) {d with load := []}
        (Cfg.mk (some h.tm.main) s
          (Function.update S h.tm.k₀ ((u.map h.inputAlphabet.symm).reverse ++ w)))) := by
  induction u generalizing reg w with
  | nil => simpa using load_step_nil h eb seed s reg (Function.update S h.tm.k₀ w) d
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [List.map_cons, Option.bind_some, load_step_cons]
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using
      ih (some (.left a), reg.2) (h.inputAlphabet.symm a :: w)

theorem active_step (seed : Option (h.tm.Γ h.tm.k₀))
    (reg : Option (InTag h eb) × Option (OutTag h eb)) (d : Data h eb)
    (c c' : h.tm.Cfg) (hc : h.tm.step c = some c') :
    step (program h eb seed) (activeCfg h eb reg d c) = some (activeCfg h eb reg d c') := by
  obtain ⟨l, s, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, step] at hc
  | some l =>
    have hc' : stepAux (h.tm.m l) s S = c' := by simpa [FinTM2.step, step] using hc
    rw [← hc']
    simpa only [activeCfg, Option.elim, program, step] using
      congrArg some (activeStmt_stepAux h eb (h.tm.m l) s reg S d)

theorem active_run (seed : Option (h.tm.Γ h.tm.k₀))
    (reg : Option (InTag h eb) × Option (OutTag h eb)) (d : Data h eb)
    (c c' : h.tm.Cfg) (n : ℕ)
    (hc : (fun x : Option h.tm.Cfg => x.bind h.tm.step)^[n] (some c) = some c') :
    (fun x : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      x.bind (step (program h eb seed)))^[n] (some (activeCfg h eb reg d c)) =
        some (activeCfg h eb reg d c') :=
  TM2Embedding.simulate_run h.tm.step (step (program h eb seed)) (activeCfg h eb reg d)
    (active_step h eb seed reg d) n c c' hc

theorem rightTransferCfg_eq (p : Phase) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    TM2Transfer.transferCfg (Γ := Alphabet h eb) (Λ := Labels h eb) (.inr .right) (.inr .output)
      (.inr p) (s, reg.1) reg.2 (contents h eb S {d with right := [], output := []}) d.right d.output =
      phaseCfg h eb p s reg S d := by
  simp only [TM2Transfer.transferCfg, phaseCfg, TM2Transfer.setStacks, update_right, update_output]

theorem right_run (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    (fun x : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      x.bind (step (program h eb seed)))^[d.right.length + 1] (some (phaseCfg h eb .right s reg S d)) =
        some (phaseCfg h eb .separator s (reg.1, none) S {d with right := [], output := d.right.reverse ++ d.output}) := by
  letI : Inhabited (Alphabet h eb (.inr .right)) := ⟨.sep⟩
  have hr := TM2Transfer.transfer_run (Γ := Alphabet h eb) (Λ := Labels h eb)
    (σ := h.tm.σ × Option (InTag h eb)) (.inr .right) (.inr .output) (by intro hne; cases hne) id
    (.inr .right) (.inr .separator) (program h eb seed) rfl
    (s, reg.1) reg.2 (contents h eb S {d with right := [], output := []}) d.right d.output
  simp only [List.map_id, rightTransferCfg_eq] at hr
  exact hr.trans (congrArg some (rightTransferCfg_eq h eb .separator s (reg.1, none) S
    {d with right := [], output := d.right.reverse ++ d.output}))

theorem separator_step (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    step (program h eb seed) (phaseCfg h eb .separator s reg S d) =
      some (phaseCfg h eb .collect s reg S {d with output := .sep :: d.output}) := by
  simp [phaseCfg, program, step, stepAux, auxContents, update_output]

theorem collectTransferCfg_eq (p : Phase) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (u : List (h.tm.Γ h.tm.k₁)) :
    TM2MappedTransfer.transferCfg (Γ := Alphabet h eb) (Λ := Labels h eb) (.inl h.tm.k₁) (.inr .left)
      (.inr p) (s, reg.1) reg.2 (contents h eb (Function.update S h.tm.k₁ []) {d with left := []}) u d.left =
      phaseCfg h eb p s reg (Function.update S h.tm.k₁ u) d := by
  simp only [TM2MappedTransfer.transferCfg, phaseCfg, TM2Transfer.setStacks, update_active,
    Function.update_idem, update_left]

theorem collect_run (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) (u : List (h.tm.Γ h.tm.k₁)) :
    (fun x : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      x.bind (step (program h eb seed)))^[u.length + 1]
      (some (phaseCfg h eb .collect s reg (Function.update S h.tm.k₁ u) d)) =
      some (phaseCfg h eb .left s (reg.1, none) (Function.update S h.tm.k₁ [])
        {d with left := (u.map (fun a => PairSymbol.left (h.outputAlphabet a))).reverse ++ d.left}) := by
  letI : Inhabited (Alphabet h eb (.inr .left)) := ⟨.sep⟩
  have hr := TM2MappedTransfer.transfer_run (Γ := Alphabet h eb) (Λ := Labels h eb)
    (σ := h.tm.σ × Option (InTag h eb)) (.inl h.tm.k₁) (.inr .left) (by intro hne; cases hne)
    (fun a => PairSymbol.left (h.outputAlphabet a)) (.inr .collect) (.inr .left) (program h eb seed) rfl
    (s, reg.1) reg.2 (contents h eb (Function.update S h.tm.k₁ []) {d with left := []}) u d.left
  simp only [collectTransferCfg_eq] at hr
  exact hr.trans (congrArg some (collectTransferCfg_eq h eb .left s (reg.1, none) S
    {d with left := (u.map (fun a => PairSymbol.left (h.outputAlphabet a))).reverse ++ d.left} []))

theorem leftTransferCfg_eq (p : Phase) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    TM2Transfer.transferCfg (Γ := Alphabet h eb) (Λ := Labels h eb) (.inr .left) (.inr .output)
      (.inr p) (s, reg.1) reg.2 (contents h eb S {d with left := [], output := []}) d.left d.output =
      phaseCfg h eb p s reg S d := by
  simp only [TM2Transfer.transferCfg, phaseCfg, TM2Transfer.setStacks, update_left, update_output]

theorem left_run (seed : Option (h.tm.Γ h.tm.k₀)) (s : h.tm.σ)
    (reg : Option (InTag h eb) × Option (OutTag h eb))
    (S : ∀ k, List (h.tm.Γ k)) (d : Data h eb) :
    (fun x : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      x.bind (step (program h eb seed)))^[d.left.length + 1] (some (phaseCfg h eb .left s reg S d)) =
        some (phaseCfg h eb .finish s (reg.1, none) S {d with left := [], output := d.left.reverse ++ d.output}) := by
  letI : Inhabited (Alphabet h eb (.inr .left)) := ⟨.sep⟩
  have hr := TM2Transfer.transfer_run (Γ := Alphabet h eb) (Λ := Labels h eb)
    (σ := h.tm.σ × Option (InTag h eb)) (.inr .left) (.inr .output) (by intro hne; cases hne) id
    (.inr .left) (.inr .finish) (program h eb seed) rfl
    (s, reg.1) reg.2 (contents h eb S {d with left := [], output := []}) d.left d.output
  simp only [List.map_id, leftTransferCfg_eq] at hr
  exact hr.trans (congrArg some (leftTransferCfg_eq h eb .finish s (reg.1, none) S
    {d with left := [], output := d.left.reverse ++ d.output}))

def emptyData : Data h eb := ⟨[], [], [], [], []⟩

def pairWord (u : List ea.Γ) (v : List eb.Γ) : List (InTag h eb) :=
  u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right

theorem split_run (seed : Option (h.tm.Γ h.tm.k₀)) (u : List ea.Γ) (v : List eb.Γ) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb seed)))^[(pairWord h eb u v).length + 1]
      (some (phaseCfg h eb .scan h.tm.initialState (none, none) (fun _ => [])
        {emptyData h eb with input := pairWord h eb u v})) =
      some (phaseCfg h eb .load h.tm.initialState (none, none) (fun _ => [])
        {emptyData h eb with load := (u.map PairSymbol.left).reverse, right := (v.map PairSymbol.right).reverse}) := by
  have hl : (pairWord h eb u v).filterMap (keepLeft h eb) = u.map PairSymbol.left := by
    simp [pairWord, List.filterMap_append, List.filterMap_map, Function.comp_def, keepLeft,
      TM2PairProjections.discard_all]
  have hr : (pairWord h eb u v).filterMap (keepRight h eb) = v.map PairSymbol.right := by
    simp [pairWord, List.filterMap_append, List.filterMap_map, Function.comp_def, keepRight,
      TM2PairProjections.discard_all]
  simpa [hl, hr, emptyData] using scan_run h eb seed h.tm.initialState (none, none)
    (fun _ => []) (emptyData h eb) (pairWord h eb u v)

theorem init_stk_eq (u : List (h.tm.Γ h.tm.k₀)) :
    (initList h.tm u).stk = Function.update (fun _ => []) h.tm.k₀ u := by
  funext k
  by_cases hk : k = h.tm.k₀
  · subst k; simp [initList]
  · simp [initList, Function.update_of_ne, hk]

theorem halt_stk_eq (u : List (h.tm.Γ h.tm.k₁)) :
    (haltList h.tm u).stk = Function.update (fun _ => []) h.tm.k₁ u := by
  funext k
  by_cases hk : k = h.tm.k₁
  · subst k; simp [haltList]
  · simp [haltList, Function.update_of_ne, hk]

theorem init_cfg_eq (u : List (h.tm.Γ h.tm.k₀)) :
    initList h.tm u = Cfg.mk (some h.tm.main) h.tm.initialState
      (Function.update (fun _ => []) h.tm.k₀ u) :=
  congrArg (Cfg.mk (some h.tm.main) h.tm.initialState) (init_stk_eq h u)

theorem load_run (seed : Option (h.tm.Γ h.tm.k₀)) (hseed : seed = none → IsEmpty (h.tm.Γ h.tm.k₀))
    (u : List ea.Γ) (d : Data h eb) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb seed)))^[u.length + 1]
      (some (phaseCfg h eb .load h.tm.initialState (none, none) (fun _ => [])
        {d with load := (u.map PairSymbol.left).reverse})) =
      some (activeCfg h eb (none, none) {d with load := []}
        (initList h.tm (u.map h.inputAlphabet.symm))) := by
  cases seed with
  | some x =>
    have hr := load_run_some h eb x h.tm.initialState (none, none) (fun _ => []) d u.reverse []
    rw [init_cfg_eq]
    simpa only [List.map_reverse, List.length_reverse, List.append_nil, List.reverse_reverse,
      Function.update_eq_self] using hr
  | none =>
    have hu : u = [] := by
      cases u with
      | nil => rfl
      | cons x xs => exact False.elim ((hseed rfl).false (h.inputAlphabet.symm x))
    subst u
    simp only [List.map_nil, List.reverse_nil, List.length_nil, Nat.zero_add, Function.iterate_one,
      Option.bind_some]
    rw [init_cfg_eq]
    simp [program, phaseCfg, activeCfg, step, stepAux, Function.update_eq_self]

noncomputable def machine (seed : Option (h.tm.Γ h.tm.k₀)) : FinTM2 := by
  letI := h.tm.kFin
  letI := h.tm.ΛFin
  letI := h.tm.σFin
  letI := ea.ΓFin
  letI := ey.ΓFin
  letI := eb.ΓFin
  letI : Fintype (InTag h eb) := inferInstanceAs (Fintype (PairSymbol ea.Γ eb.Γ))
  letI : Fintype (OutTag h eb) := inferInstanceAs (Fintype (PairSymbol ey.Γ eb.Γ))
  exact
    { K := h.tm.K ⊕ AuxSlot
      k₀ := .inr .input
      k₁ := .inr .output
      Γ := Alphabet h eb
      Λ := Labels h eb
      main := .inr .scan
      σ := State h eb
      initialState := ((h.tm.initialState, none), none)
      Γk₀Fin := inferInstanceAs (Fintype (InTag h eb))
      m := program h eb seed }

theorem initial_eq (seed : Option (h.tm.Γ h.tm.k₀)) (u : List (InTag h eb)) :
    initList (machine h eb seed) u = phaseCfg h eb .scan h.tm.initialState (none, none)
      (fun _ => []) {emptyData h eb with input := u} := by
  unfold machine initList phaseCfg
  congr 1
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, emptyData]

theorem final_eq (seed : Option (h.tm.Γ h.tm.k₀)) (u : List (OutTag h eb)) :
    (Cfg.mk (Γ := Alphabet h eb) (Λ := Labels h eb) (σ := State h eb) none
      ((h.tm.initialState, none), none) (contents h eb (fun _ => []) {emptyData h eb with output := u})) =
      haltList (machine h eb seed) u := by
  unfold haltList machine
  congr 1
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents, emptyData]

def restData (v : List eb.Γ) : Data h eb :=
  {emptyData h eb with right := (v.map PairSymbol.right).reverse}

theorem prepare_run (seed : Option (h.tm.Γ h.tm.k₀))
    (hseed : seed = none → IsEmpty (h.tm.Γ h.tm.k₀)) (u : List ea.Γ) (v : List eb.Γ) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb seed)))^[(pairWord h eb u v).length + u.length + 2]
      (some (phaseCfg h eb .scan h.tm.initialState (none, none) (fun _ => [])
        {emptyData h eb with input := pairWord h eb u v})) =
      some (activeCfg h eb (none, none) (restData h eb v) (initList h.tm (u.map h.inputAlphabet.symm))) := by
  rw [show (pairWord h eb u v).length + u.length + 2 =
      (u.length + 1) + ((pairWord h eb u v).length + 1) by omega,
    Function.iterate_add_apply, split_run]
  simpa only [restData, emptyData] using load_run h eb seed hseed u (restData h eb v)

theorem active_halt_eq (u : List (h.tm.Γ h.tm.k₁)) (d : Data h eb) :
    activeCfg h eb (none, none) d (haltList h.tm u) =
      phaseCfg h eb .right h.tm.initialState (none, none) (Function.update (fun _ => []) h.tm.k₁ u) d := by
  change Cfg.mk (Γ := Alphabet h eb) (Λ := Labels h eb) (σ := State h eb)
      (some (.inr .right)) ((h.tm.initialState, none), none)
      (contents h eb (haltList h.tm u).stk d) = _
  rw [halt_stk_eq]
  rfl

theorem finish_run (seed : Option (h.tm.Γ h.tm.k₀))
    (u : List (h.tm.Γ h.tm.k₁)) (v : List eb.Γ) :
    (fun c : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      c.bind (step (program h eb seed)))^[v.length + 2 * u.length + 5]
      (some (activeCfg h eb (none, none) (restData h eb v) (haltList h.tm u))) =
      some (Cfg.mk none ((h.tm.initialState, none), none) (contents h eb (fun _ => [])
        {emptyData h eb with output := u.map (fun a => PairSymbol.left (h.outputAlphabet a)) ++ PairSymbol.sep :: v.map PairSymbol.right})) := by
  have hr := right_run h eb seed h.tm.initialState (none, none)
    (Function.update (fun _ => []) h.tm.k₁ u) (restData h eb v)
  simp only [restData, emptyData, List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at hr
  let d : Data h eb := {emptyData h eb with output := PairSymbol.sep :: v.map PairSymbol.right}
  have hc := collect_run h eb seed h.tm.initialState (none, none) (fun _ => []) d u
  simp only [d, emptyData, List.append_nil, Function.update_eq_self] at hc
  have hl := left_run h eb seed h.tm.initialState (none, none) (fun _ => [])
    {d with left := (u.map (fun a => PairSymbol.left (h.outputAlphabet a))).reverse}
  simp only [d, emptyData, List.length_reverse, List.length_map, List.reverse_reverse] at hl
  rw [show v.length + 2 * u.length + 5 =
      (((u.length + 1) + 1) + (u.length + 1) + 1) + (v.length + 1) by omega,
    Function.iterate_add_apply, active_halt_eq]
  simp only [restData, emptyData]
  rw [hr, Function.iterate_succ_apply]
  simp only [Option.bind_some, separator_step]
  rw [Function.iterate_add_apply, hc, Function.iterate_succ_apply', hl]
  rfl

noncomputable def machine_outputsInTime (seed : Option (h.tm.Γ h.tm.k₀))
    (hseed : seed = none → IsEmpty (h.tm.Γ h.tm.k₀)) (x : X) (v : List eb.Γ) :
    TM2OutputsInTime (machine h eb seed) (pairWord h eb (ea.encode x) v)
      (some ((ey.encode (f x)).map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right))
      (h.time.eval (ea.encode x).length + 2 * (pairWord h eb (ea.encode x) v).length +
        2 * (ey.encode (f x)).length + 6) := by
  let c := machine h eb seed
  have ha := h.outputsFun x
  let middle := (ey.encode (f x)).map h.outputAlphabet.symm
  let before := (pairWord h eb (ea.encode x) v).length + (ea.encode x).length + 2
  let after := v.length + 2 * middle.length + 5
  refine
    { steps := after + ha.steps + before
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (fun st : Option (Cfg (Alphabet h eb) (Labels h eb) (State h eb)) =>
      st.bind (step (program h eb seed)))^[after + ha.steps + before]
      (some (initList c (pairWord h eb (ea.encode x) v))) = some (haltList c _)
    dsimp only [after, before]
    have harun : (fun st : Option h.tm.Cfg => st.bind h.tm.step)^[ha.steps]
        (some (initList h.tm ((ea.encode x).map h.inputAlphabet.symm))) =
          some (haltList h.tm middle) := ha.evals_in_steps
    rw [initial_eq, Function.iterate_add_apply, prepare_run h eb seed hseed,
      Function.iterate_add_apply, active_run h eb seed (none, none) (restData h eb v)
        (initList h.tm ((ea.encode x).map h.inputAlphabet.symm)) (haltList h.tm middle) ha.steps harun,
      finish_run]
    simp only [middle, List.map_map, Function.comp_def, Equiv.apply_symm_apply]
    exact congrArg some (final_eq h eb seed _)
  · have hs := ha.steps_le_m
    simp only [after, before, middle, List.length_map, pairWord, List.length_append,
      List.length_cons] at *
    omega

end ProteinFolding.TM2FanoutLeft

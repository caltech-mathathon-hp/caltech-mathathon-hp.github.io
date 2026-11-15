import ProteinFolding.Cubic.Proofs.VerifierRecords
import ProteinFolding.Common.TM2StateExtension
import ProteinFolding.Common.TM2Renaming

/-! A concrete suffix-row machine for geometric verification. Each incoming
record takes three TM2 steps: signed counter update, a fixed finite inspection,
and score/validity update. A `none` record is an explicit parser error, not an
ignored letter. This is a stage for the outer all-pairs loop. -/

namespace ProteinFolding.CubicVerifier.Row

open Turing TM2





abbrev Letter := Option Record
abbrev Stack := TM2WalkCounters.Stack ⊕ Unit
abbrev Alphabet : Stack → Type := Sum.elim (TM2WalkCounters.Alphabet Letter) (fun _ => Unit)

inductive Phase where
  | scan | inspect | score | finish
  deriving DecidableEq, Fintype

structure Context where
  currentH : Bool
  startH : Bool
  valid : Bool
  seen : Fin 3
  deriving DecidableEq, Fintype

structure Passive where
  cache : Option Letter
  currentH : Bool
  startH : Bool
  valid : Bool
  deriving DecidableEq, Fintype

abbrev State := (Option Letter × Bool) × Context

def inspectorEquiv : ((Bool × Fin 3) × Passive) ≃ State where
  toFun st := ((st.2.cache, st.1.1), ⟨st.2.currentH, st.2.startH, st.2.valid, st.1.2⟩)
  invFun st := ((st.1.2, st.2.seen), ⟨st.1.1, st.2.currentH, st.2.startH, st.2.valid⟩)
  left_inv st := by obtain ⟨⟨b, n⟩, p⟩ := st; cases p; rfl
  right_inv st := by obtain ⟨⟨r, b⟩, c⟩ := st; cases c; rfl

def rowStacks (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) : ∀ k, List (Alphabet k) :=
  TM2Embedding.joinStacks (TM2WalkCounters.stackContents input c) (fun _ : Unit => List.replicate bonds ())

def cfg (phase : Phase) (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Cfg Alphabet Phase State := ⟨some phase, ((none, false), ctx), rowStacks input c bonds⟩

def direction (letter : Letter) : Fin 6 := (letter.map Prod.snd).getD 0

def peekContext (ctx : Context) : Option Letter → Context
  | none => { ctx with currentH := false }
  | some none => { ctx with currentH := false, valid := false }
  | some (some r) => { ctx with currentH := labelBit r.1 }

def counterLabels : TM2WalkCounters.Phase → Phase
  | .scan => .inspect
  | .finish => .finish

def scanBody : Stmt Alphabet Phase State :=
  TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Context) counterLabels none
    (TM2WalkCounters.program direction .scan)

def scanStmt : Stmt Alphabet Phase State :=
  .peek (.inl .input) (fun st head => (st.1, peekContext st.2 head)) scanBody

def inspectBody : Stmt Alphabet Phase State :=
  let q : Stmt (TM2WalkCounters.Alphabet Letter) Phase (Bool × Fin 3) :=
    TM2WalkInspector.inspect (.goto (fun _ => .score))
  TM2Renaming.relabelStmt inspectorEquiv
    (TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Passive) id none q)

def hit (ctx : Context) : Bool := decide (ctx.seen = 1) && ctx.startH && ctx.currentH

def nextContext (ctx : Context) : Context :=
  ⟨false, ctx.startH, ctx.valid && decide (ctx.seen ≠ 0), 0⟩

def resetStmt : Stmt Alphabet Phase State :=
  .load (fun st => ((none, false), nextContext st.2)) (.goto (fun _ => .scan))

def scoreStmt : Stmt Alphabet Phase State :=
  .branch (fun st => hit st.2)
    (.push (.inr ()) (fun _ => ()) resetStmt) resetStmt

def program : Phase → Stmt Alphabet Phase State
  | .scan => scanStmt
  | .inspect => inspectBody
  | .score => scoreStmt
  | .finish => .halt

theorem scan_step_cons (ctx : Context) (a : Letter) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    step program (cfg .scan ctx (a :: input) c bonds) =
      some (cfg .inspect (peekContext ctx (some a)) input (TM2WalkCounters.updateCounts c (direction a)) bonds) := by
  have hsource : stepAux (TM2WalkCounters.program direction .scan) (none, false)
      (TM2WalkCounters.stackContents (a :: input) c) =
        TM2WalkCounters.cfg .scan (none, false) input (TM2WalkCounters.updateCounts c (direction a)) :=
    Option.some.inj (TM2WalkCounters.scan_step_cons direction a (none, false) input c)
  have hlift := TM2Embedding.stepAux_liftStmt counterLabels none (TM2WalkCounters.program direction .scan)
    (none, false) (peekContext ctx (some a)) (TM2WalkCounters.stackContents (a :: input) c)
    (fun _ : Unit => List.replicate bonds ())
  rw [hsource] at hlift
  simpa [cfg, program, scanStmt, scanBody, step, stepAux, rowStacks, TM2Embedding.joinStacks,
    TM2WalkCounters.stackContents, TM2Embedding.embedCfg, TM2WalkCounters.cfg, counterLabels] using congrArg some hlift

theorem scan_step_nil (ctx : Context) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    step program (cfg .scan ctx [] c bonds) =
      some (cfg .finish (peekContext ctx none) [] c bonds) := by
  have hsource : stepAux (TM2WalkCounters.program direction .scan) (none, false) (TM2WalkCounters.stackContents [] c) =
      TM2WalkCounters.cfg .finish (none, false) [] c :=
    Option.some.inj (TM2WalkCounters.scan_step_nil direction (none, false) c)
  have hlift := TM2Embedding.stepAux_liftStmt counterLabels none (TM2WalkCounters.program direction .scan)
    (none, false) (peekContext ctx none) (TM2WalkCounters.stackContents [] c)
    (fun _ : Unit => List.replicate bonds ())
  rw [hsource] at hlift
  simpa [cfg, program, scanStmt, scanBody, step, stepAux, rowStacks, TM2Embedding.joinStacks,
    TM2WalkCounters.stackContents, TM2Embedding.embedCfg, TM2WalkCounters.cfg, counterLabels] using congrArg some hlift

theorem inspect_step (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    step program (cfg .inspect ctx input c bonds) =
      some (cfg .score { ctx with seen := TM2WalkInspector.cap (ctx.seen.val + TM2WalkCounters.totalCounts c) } input c bonds) := by
  let p : Passive := ⟨none, ctx.currentH, ctx.startH, ctx.valid⟩
  let q : Stmt (TM2WalkCounters.Alphabet Letter) Phase (Bool × Fin 3) := TM2WalkInspector.inspect (.goto (fun _ => .score))
  let lifted := TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Passive) id none q
  have hsource := TM2WalkInspector.inspect_stepAux (.goto (fun _ => Phase.score)) false ctx.seen input c
  have hlift := TM2Embedding.stepAux_liftStmt (id : Phase → Phase) none q
    (false, ctx.seen) p (TM2WalkCounters.stackContents input c) (fun _ : Unit => List.replicate bonds ())
  rw [hsource] at hlift
  have hrename := TM2Renaming.stepAux_relabelStmt inspectorEquiv lifted ((false, ctx.seen), p)
    (rowStacks input c bonds)
  dsimp only [lifted, rowStacks] at hrename
  rw [hlift] at hrename
  simpa [cfg, program, inspectBody, step, q, lifted, p, rowStacks, TM2Embedding.embedCfg,
    TM2Renaming.mapCfg, inspectorEquiv, stepAux] using congrArg some hrename

theorem update_bonds (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Function.update (rowStacks input c bonds) (.inr ()) (() :: List.replicate bonds ()) =
      rowStacks input c (bonds + 1) := by
  funext k
  cases k with
  | inl k => simp [rowStacks, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k; simp [rowStacks, TM2Embedding.joinStacks, List.replicate_succ]

theorem score_step (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    step program (cfg .score ctx input c bonds) =
      some (cfg .scan (nextContext ctx) input c (bonds + (hit ctx).toNat)) := by
  cases hhit : hit ctx <;>
    simp [cfg, program, scoreStmt, resetStmt, step, stepAux, hhit]
  change Function.update (rowStacks input c bonds) (.inr ()) (() :: List.replicate bonds ()) = _
  exact update_bonds input c bonds

def afterLetter (ctx : Context) (c : TM2WalkCounters.Counts) (a : Letter) : Context :=
  let pre := peekContext ctx (some a)
  { pre with seen := TM2WalkInspector.cap (pre.seen.val +
      TM2WalkCounters.totalCounts (TM2WalkCounters.updateCounts c (direction a))) }

theorem process_record (ctx : Context) (a : Letter) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[3]
      (some (cfg .scan ctx (a :: input) c bonds)) =
        some (cfg .scan (nextContext (afterLetter ctx c a)) input
          (TM2WalkCounters.updateCounts c (direction a)) (bonds + (hit (afterLetter ctx c a)).toNat)) := by
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some, scan_step_cons]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some, inspect_step]
  rw [Function.iterate_one]
  simp only [Option.bind_some, score_step]
  rfl

structure Result where
  context : Context
  bonds : ℕ
  counts : TM2WalkCounters.Counts

def rowRun : Context → ℕ → TM2WalkCounters.Counts → List Letter → Result
  | ctx, bonds, c, [] => ⟨peekContext ctx none, bonds, c⟩
  | ctx, bonds, c, a :: input =>
    rowRun (nextContext (afterLetter ctx c a)) (bonds + (hit (afterLetter ctx c a)).toNat)
      (TM2WalkCounters.updateCounts c (direction a)) input

/-- One suffix row takes exactly three steps per endpoint plus one final
empty-input test. The theorem describes the actual counter, Boolean-state,
and unary-bond-stack contents, not just the labels reached. -/
theorem row_run (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[3 * input.length + 1]
      (some (cfg .scan ctx input c bonds)) =
        some (cfg .finish (rowRun ctx bonds c input).context []
          (rowRun ctx bonds c input).counts (rowRun ctx bonds c input).bonds) := by
  induction input generalizing ctx c bonds with
  | nil => simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, rowRun]
      using scan_step_nil ctx c bonds
  | cons a input ih =>
    rw [List.length_cons, show 3 * (input.length + 1) + 1 = (3 * input.length + 1) + 3 by omega,
      Function.iterate_add_apply, process_record]
    exact ih (nextContext (afterLetter ctx c a)) (TM2WalkCounters.updateCounts c (direction a))
      (bonds + (hit (afterLetter ctx c a)).toNat)

theorem rowRun_counts (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c input).counts = TM2WalkCounters.runCounts c (input.map direction) := by
  induction input generalizing ctx c bonds with
  | nil => rfl
  | cons a input ih =>
    exact ih (nextContext (afterLetter ctx c a)) (TM2WalkCounters.updateCounts c (direction a))
      (bonds + (hit (afterLetter ctx c a)).toNat)

theorem rowRun_bonds_le (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c input).bonds ≤ bonds + input.length := by
  induction input generalizing ctx c bonds with
  | nil => simp [rowRun]
  | cons a input ih =>
    have h := ih (nextContext (afterLetter ctx c a)) (TM2WalkCounters.updateCounts c (direction a))
      (bonds + (hit (afterLetter ctx c a)).toNat)
    have hhit : (hit (afterLetter ctx c a)).toNat ≤ 1 := by
      cases hit (afterLetter ctx c a) <;> decide
    simp only [rowRun, List.length_cons]
    omega

theorem rowRun_counter_space (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    TM2WalkCounters.totalCounts (rowRun ctx bonds c input).counts ≤
      TM2WalkCounters.totalCounts c + input.length := by
  rw [rowRun_counts]
  simpa only [List.length_map] using TM2WalkCounters.runCounts_total_le c (input.map direction)

theorem rowRun_invalid (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ)
    (hbad : ctx.valid = false) : (rowRun ctx bonds c input).context.valid = false := by
  induction input generalizing ctx c bonds with
  | nil => simpa [rowRun, peekContext] using hbad
  | cons a input ih =>
    apply ih
    cases a <;> simp [nextContext, afterLetter, peekContext, hbad]

theorem rowRun_none_head_invalid (ctx : Context) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c (none :: input)).context.valid = false := by
  rw [rowRun]
  apply rowRun_invalid
  simp [nextContext, afterLetter, peekContext]

end ProteinFolding.CubicVerifier.Row



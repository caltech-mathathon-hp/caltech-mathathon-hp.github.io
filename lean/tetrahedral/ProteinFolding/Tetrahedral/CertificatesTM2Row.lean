import ProteinFolding.Tetrahedral.CertificatesTM2Updates
import ProteinFolding.Tetrahedral.CertificatesTM2Inspector
import ProteinFolding.Common.TM2StateExtension
import ProteinFolding.Common.TM2Renaming

/-! A concrete suffix-row machine for geometric verification. Each incoming
record takes three TM2 steps: signed counter update, a fixed finite inspection,
and score/validity update. A `none` record is an explicit parser error, not an
ignored letter. This is a stage for the outer all-pairs loop. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Row

open Turing TM2





abbrev Record := Residue × Fin 4
abbrev Letter := Option Record

def labelBit (r : Residue) : Bool := decide (r = Residue.H)
abbrev Stack := TM2WalkCounters.Stack ⊕ Unit
abbrev Alphabet : Stack → Type := Sum.elim (TM2WalkCounters.Alphabet Letter) (fun _ => Unit)

inductive Phase where
  | scan | inspect | score | finish
  deriving DecidableEq, Fintype

structure Context where
  currentH : Bool
  startH : Bool
  valid : Bool
  seen : Fin 5
  phaseA : Bool
  startA : Bool
  deriving DecidableEq, Fintype

structure Passive where
  cache : Option Letter
  currentH : Bool
  startH : Bool
  valid : Bool
  phaseA : Bool
  startA : Bool
  deriving DecidableEq, Fintype

abbrev State := (Option Letter × Bool) × Context

def inspectorEquiv : ((Bool × Fin 5) × Passive) ≃ State where
  toFun st := ((st.2.cache, st.1.1), ⟨st.2.currentH, st.2.startH, st.2.valid, st.1.2, st.2.phaseA, st.2.startA⟩)
  invFun st := ((st.1.2, st.2.seen), ⟨st.1.1, st.2.currentH, st.2.startH, st.2.valid, st.2.phaseA, st.2.startA⟩)
  left_inv st := by obtain ⟨⟨b, n⟩, p⟩ := st; cases p; rfl
  right_inv st := by obtain ⟨⟨r, b⟩, c⟩ := st; cases c; rfl

def rowStacks (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) : ∀ k, List (Alphabet k) :=
  TM2Embedding.joinStacks (TM2WalkCounters.stackContents input c) (fun _ : Unit => List.replicate bonds ())

def cfg (phase : Phase) (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Cfg Alphabet Phase State := ⟨some phase, ((none, false), ctx), rowStacks input c bonds⟩

def direction (letter : Letter) : Fin 4 := (letter.map Prod.snd).getD 0

def peekContext (ctx : Context) : Option Letter → Context
  | none => { ctx with currentH := false }
  | some none => { ctx with currentH := false, valid := false }
  | some (some r) => { ctx with currentH := labelBit r.1 }

def scanEquiv : ((Bool × (Option Letter × Context)) × Unit) ≃ State where
  toFun st := ((st.1.2.1, st.1.1), st.1.2.2)
  invFun st := ((st.1.2, (st.1.1, st.2)), ())
  left_inv st := by obtain ⟨⟨b, r, c⟩, u⟩ := st; cases u; rfl
  right_inv st := by obtain ⟨⟨r, b⟩, c⟩ := st; rfl

def advance (ctx : Context) : Context := { ctx with phaseA := !ctx.phaseA }

def sourceScan : Stmt (TM2WalkCounters.Alphabet Letter) Phase (Bool × (Option Letter × Context)) :=
  .pop .input (fun st head => (false, (head, peekContext st.2.2 head)))
    (.branch (fun st => st.2.1.isSome)
      (CertificatesTM2Updates.dispatchAll
        (fun st => (st.2.phaseA, direction (st.1.getD none)))
        (.load (fun st => (false, (none, advance st.2.2))) (.goto (fun _ => .inspect))))
      (.load (fun st => (false, (none, st.2.2))) (.goto (fun _ => .finish))))

def scanStmt : Stmt Alphabet Phase State :=
  TM2Renaming.relabelStmt scanEquiv
    (TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Unit) id none sourceScan)

def inspectBody : Stmt Alphabet Phase State :=
  let q : Stmt (TM2WalkCounters.Alphabet Letter) Phase (Bool × Fin 5) :=
    CertificatesTM2Inspector.inspect (.goto (fun _ => .score))
  TM2Renaming.relabelStmt inspectorEquiv
    (TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Passive) id none q)

def hit (ctx : Context) : Bool := decide (ctx.seen = 3) && ctx.startH && ctx.currentH

def nextContext (ctx : Context) : Context :=
  ⟨false, ctx.startH, ctx.valid && decide (ctx.seen ≠ 0), 0, ctx.phaseA, ctx.startA⟩

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

theorem sourceScan_step_cons (ctx : Context) (a : Letter) (input : List Letter)
    (c : TM2WalkCounters.Counts) :
    stepAux sourceScan (false, (none, ctx)) (TM2WalkCounters.stackContents (a :: input) c) =
      ⟨some .inspect, (false, (none, advance (peekContext ctx (some a)))),
        TM2WalkCounters.stackContents input
          (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a)))⟩ := by
  simp only [sourceScan, stepAux, TM2WalkCounters.stackContents, List.head?_cons,
    List.tail_cons, TM2WalkCounters.update_input, Option.isSome_some, cond_true]
  rw [CertificatesTM2Updates.dispatchAll_stepAux]
  cases a <;> rfl

theorem sourceScan_step_nil (ctx : Context) (c : TM2WalkCounters.Counts) :
    stepAux sourceScan (false, (none, ctx)) (TM2WalkCounters.stackContents [] c) =
      ⟨some .finish, (false, (none, peekContext ctx none)), TM2WalkCounters.stackContents [] c⟩ := by
  simp [sourceScan, stepAux, TM2WalkCounters.stackContents, TM2WalkCounters.update_input]

theorem scan_step_cons (ctx : Context) (a : Letter) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Turing.TM2.step program (cfg .scan ctx (a :: input) c bonds) =
      some (cfg .inspect (advance (peekContext ctx (some a))) input
        (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a))) bonds) := by
  have hlift := TM2Embedding.stepAux_liftStmt (id : Phase → Phase) none sourceScan
    (false, (none, ctx)) () (TM2WalkCounters.stackContents (a :: input) c)
    (fun _ : Unit => List.replicate bonds ())
  rw [sourceScan_step_cons] at hlift
  have hrename := TM2Renaming.stepAux_relabelStmt scanEquiv
    (TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Unit) id none sourceScan)
    ((false, (none, ctx)), ()) (rowStacks (a :: input) c bonds)
  dsimp only [rowStacks] at hrename
  rw [hlift] at hrename
  simpa [cfg, program, scanStmt, Turing.TM2.step, rowStacks, TM2Embedding.embedCfg,
    TM2Renaming.mapCfg, scanEquiv] using congrArg some hrename

theorem scan_step_nil (ctx : Context) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Turing.TM2.step program (cfg .scan ctx [] c bonds) =
      some (cfg .finish (peekContext ctx none) [] c bonds) := by
  have hlift := TM2Embedding.stepAux_liftStmt (id : Phase → Phase) none sourceScan
    (false, (none, ctx)) () (TM2WalkCounters.stackContents [] c)
    (fun _ : Unit => List.replicate bonds ())
  rw [sourceScan_step_nil] at hlift
  have hrename := TM2Renaming.stepAux_relabelStmt scanEquiv
    (TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Unit) id none sourceScan)
    ((false, (none, ctx)), ()) (rowStacks [] c bonds)
  dsimp only [rowStacks] at hrename
  rw [hlift] at hrename
  simpa [cfg, program, scanStmt, Turing.TM2.step, rowStacks, TM2Embedding.embedCfg,
    TM2Renaming.mapCfg, scanEquiv] using congrArg some hrename

theorem inspect_step (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Turing.TM2.step program (cfg .inspect ctx input c bonds) =
      some (cfg .score { ctx with seen := CertificatesTM2Inspector.cap (ctx.seen.val + TM2WalkCounters.totalCounts c) } input c bonds) := by
  let p : Passive := ⟨none, ctx.currentH, ctx.startH, ctx.valid, ctx.phaseA, ctx.startA⟩
  let q : Stmt (TM2WalkCounters.Alphabet Letter) Phase (Bool × Fin 5) := CertificatesTM2Inspector.inspect (.goto (fun _ => .score))
  let lifted := TM2Embedding.liftStmt (J := Unit) (Δ := fun _ => Unit) (τ := Passive) id none q
  have hsource := CertificatesTM2Inspector.inspect_stepAux (.goto (fun _ => Phase.score)) false ctx.seen input c
  have hlift := TM2Embedding.stepAux_liftStmt (id : Phase → Phase) none q
    (false, ctx.seen) p (TM2WalkCounters.stackContents input c) (fun _ : Unit => List.replicate bonds ())
  rw [hsource] at hlift
  have hrename := TM2Renaming.stepAux_relabelStmt inspectorEquiv lifted ((false, ctx.seen), p)
    (rowStacks input c bonds)
  dsimp only [lifted, rowStacks] at hrename
  rw [hlift] at hrename
  simpa [cfg, program, inspectBody, Turing.TM2.step, q, lifted, p, rowStacks, TM2Embedding.embedCfg,
    TM2Renaming.mapCfg, inspectorEquiv, stepAux] using congrArg some hrename

theorem update_bonds (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Function.update (rowStacks input c bonds) (.inr ()) (() :: List.replicate bonds ()) =
      rowStacks input c (bonds + 1) := by
  funext k
  cases k with
  | inl k => simp [rowStacks, TM2Embedding.joinStacks, Function.update_of_ne]
  | inr k => cases k; simp [rowStacks, TM2Embedding.joinStacks, List.replicate_succ]

theorem score_step (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    Turing.TM2.step program (cfg .score ctx input c bonds) =
      some (cfg .scan (nextContext ctx) input c (bonds + (hit ctx).toNat)) := by
  cases hhit : hit ctx <;>
    simp [cfg, program, scoreStmt, resetStmt, Turing.TM2.step, stepAux, hhit]
  change Function.update (rowStacks input c bonds) (.inr ()) (() :: List.replicate bonds ()) = _
  exact update_bonds input c bonds

def afterLetter (ctx : Context) (c : TM2WalkCounters.Counts) (a : Letter) : Context :=
  let pre := advance (peekContext ctx (some a))
  { pre with seen := CertificatesTM2Inspector.cap (pre.seen.val +
      TM2WalkCounters.totalCounts (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a)))) }

theorem process_record (ctx : Context) (a : Letter) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (Turing.TM2.step program))^[3]
      (some (cfg .scan ctx (a :: input) c bonds)) =
        some (cfg .scan (nextContext (afterLetter ctx c a)) input
          (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a))) (bonds + (hit (afterLetter ctx c a)).toNat)) := by
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
      (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a))) input

/-- One suffix row takes exactly three steps per endpoint plus one final
empty-input test. The theorem describes the actual counter, Boolean-state,
and unary-bond-stack contents, not just the labels reached. -/
theorem row_run (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (Turing.TM2.step program))^[3 * input.length + 1]
      (some (cfg .scan ctx input c bonds)) =
        some (cfg .finish (rowRun ctx bonds c input).context []
          (rowRun ctx bonds c input).counts (rowRun ctx bonds c input).bonds) := by
  induction input generalizing ctx c bonds with
  | nil => simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, rowRun]
      using scan_step_nil ctx c bonds
  | cons a input ih =>
    rw [List.length_cons, show 3 * (input.length + 1) + 1 = (3 * input.length + 1) + 3 by omega,
      Function.iterate_add_apply, process_record]
    exact ih (nextContext (afterLetter ctx c a)) (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a)))
      (bonds + (hit (afterLetter ctx c a)).toNat)

def rowDirections : Bool → List Letter → List (Fin 6)
  | _, [] => []
  | isA, a :: input => CertificatesTM2Directions.unitDirections isA (direction a) ++ rowDirections (!isA) input

theorem runCounts_append (c : TM2WalkCounters.Counts) (ds es : List (Fin 6)) :
    TM2WalkCounters.runCounts c (ds ++ es) =
      TM2WalkCounters.runCounts (TM2WalkCounters.runCounts c ds) es := by
  induction ds generalizing c with
  | nil => rfl
  | cons d ds ih => exact ih (TM2WalkCounters.updateCounts c d)

theorem rowDirections_length (isA : Bool) (input : List Letter) :
    (rowDirections isA input).length = 3 * input.length := by
  induction input generalizing isA with
  | nil => simp [rowDirections]
  | cons a input ih => simp [rowDirections, ih, CertificatesTM2Directions.unitDirections_length]; omega

theorem rowRun_counts (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c input).counts = TM2WalkCounters.runCounts c (rowDirections ctx.phaseA input) := by
  induction input generalizing ctx c bonds with
  | nil => rfl
  | cons a input ih =>
    rw [rowRun, ih, rowDirections, runCounts_append]
    cases a <;> rfl

theorem rowRun_bonds_le (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c input).bonds ≤ bonds + input.length := by
  induction input generalizing ctx c bonds with
  | nil => simp [rowRun]
  | cons a input ih =>
    have h := ih (nextContext (afterLetter ctx c a)) (TM2WalkCounters.runCounts c (CertificatesTM2Directions.unitDirections ctx.phaseA (direction a)))
      (bonds + (hit (afterLetter ctx c a)).toNat)
    have hhit : (hit (afterLetter ctx c a)).toNat ≤ 1 := by
      cases hit (afterLetter ctx c a) <;> decide
    simp only [rowRun, List.length_cons]
    omega

theorem rowRun_counter_space (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    TM2WalkCounters.totalCounts (rowRun ctx bonds c input).counts ≤
      TM2WalkCounters.totalCounts c + 3 * input.length := by
  rw [rowRun_counts]
  simpa only [rowDirections_length] using TM2WalkCounters.runCounts_total_le c (rowDirections ctx.phaseA input)

theorem rowRun_invalid (ctx : Context) (input : List Letter) (c : TM2WalkCounters.Counts) (bonds : ℕ)
    (hbad : ctx.valid = false) : (rowRun ctx bonds c input).context.valid = false := by
  induction input generalizing ctx c bonds with
  | nil => simpa [rowRun, peekContext] using hbad
  | cons a input ih =>
    apply ih
    cases a <;> simp [nextContext, afterLetter, peekContext, advance, hbad]

theorem rowRun_none_head_invalid (ctx : Context) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c (none :: input)).context.valid = false := by
  rw [rowRun]
  apply rowRun_invalid
  simp [nextContext, afterLetter, peekContext, advance]

theorem rowRun_startA (ctx : Context) (input : List Letter)
    (c : TM2WalkCounters.Counts) (bonds : ℕ) :
    (rowRun ctx bonds c input).context.startA = ctx.startA := by
  induction input generalizing ctx c bonds with
  | nil => rfl
  | cons a input ih =>
    rw [rowRun, ih]
    cases a <;> rfl

end ProteinFolding.Tetrahedral.CertificatesTM2Row



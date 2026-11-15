import ProteinFolding.Common.Complexity
import Mathlib.Data.Finset.Lattice.Fold

/-! A syntactic stack-growth bound for mathlib's TM2 statements.
One machine step executes a whole finite statement, so its push count must
enter a runtime-to-output-length estimate. -/

namespace ProteinFolding.TM2Bounds

open Turing TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def pushBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stack_length [DecidableEq K] (q : Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((stepAux q v S).stk k).length ≤ (S k).length + pushBound q := by
  induction q generalizing v S with
  | push j f q ih =>
    have h := ih v (Function.update S j (f v :: S j))
    have hu : ((Function.update S j (f v :: S j)) k).length ≤ (S k).length + 1 := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update, hj]
    change ((stepAux q v (Function.update S j (f v :: S j))).stk k).length ≤ _
    simp only [pushBound]
    omega
  | peek j f q ih => exact ih (f v (S j).head?) S
  | pop j f q ih =>
    have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
    have hu : ((Function.update S j (S j).tail) k).length ≤ (S k).length := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update, hj]
    change ((stepAux q (f v (S j).head?) (Function.update S j (S j).tail)).stk k).length ≤ _
    simp only [pushBound]
    omega
  | load f q ih => exact ih (f v) S
  | branch f q r ihq ihr =>
    change ((cond (f v) (stepAux q v S) (stepAux r v S)).stk k).length ≤ _
    cases hf : f v
    · have h := ihr v S; simp only [cond_false, pushBound]; omega
    · have h := ihq v S; simp only [cond_true, pushBound]; omega
  | goto f => simp [stepAux, pushBound]
  | halt => simp [stepAux, pushBound]

/-- Iterating a partial transition with bounded growth gives linear growth.
This also handles the possibility that an intermediate configuration halts. -/
theorem iterate_length_bound {Config : Type*} (step : Config → Option Config)
    (size : Config → ℕ) (P : ℕ)
    (hs : ∀ a b, step a = some b → size b ≤ size a + P)
    (n : ℕ) (a b : Config)
    (h : (fun x : Option Config => x.bind step)^[n] (some a) = some b) :
    size b ≤ size a + n * P := by
  induction n generalizing b with
  | zero =>
    have hab : a = b := by simpa using h
    subst b
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hc : (fun x : Option Config => x.bind step)^[n] (some a) with
    | none => simp [hc] at h
    | some c =>
      have hprev := ih c hc
      have hstep : step c = some b := by simpa [hc] using h
      have hnext := hs c b hstep
      rw [Nat.succ_mul]
      omega

/-- A finite machine has a uniform per-step push bound. -/
def machinePushBound (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup (fun l => pushBound (tm.m l))

theorem step_stack_length (tm : FinTM2) (a b : tm.Cfg) (k : tm.K)
    (h : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + machinePushBound tm := by
  obtain ⟨label, v, S⟩ := a
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have hb : stepAux (tm.m l) v S = b := by simpa [FinTM2.step, TM2.step] using h
    rw [← hb]
    have hlocal := stepAux_stack_length (tm.m l) v S k
    have hbound : pushBound (tm.m l) ≤ machinePushBound tm := by
      letI := tm.ΛFin
      exact (Finset.le_sup (f := fun l => pushBound (tm.m l)) (Finset.mem_univ l))
    exact hlocal.trans (Nat.add_le_add_left hbound _)

/-- Every actual output is bounded by input length plus a machine constant
times the allowed steps. The initial/final conventions include all stacks. -/
theorem outputsInTime_length (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ)
    (h : TM2OutputsInTime tm input (some output) time) :
    output.length ≤ input.length + time * machinePushBound tm := by
  have hrun := iterate_length_bound tm.step (fun c => (c.stk tm.k₁).length)
    (machinePushBound tm) (fun a b hab => step_stack_length tm a b tm.k₁ hab)
    h.steps (initList tm input) (haltList tm output) h.evals_in_steps
  have hin : ((initList tm input).stk tm.k₁).length ≤ input.length := by
    by_cases hk : tm.k₁ = tm.k₀
    · have hcast : ∀ (U V : Type) (he : U = V) (xs : List U),
          (cast (congrArg List he) xs).length = xs.length := by
        intro U V he xs
        cases he
        rfl
      simpa [initList, hk] using le_of_eq (hcast _ _ (congrArg tm.Γ hk.symm) input)
    · simp [initList, hk]
  have hout : ((haltList tm output).stk tm.k₁).length = output.length := by
    simp [haltList]
  have ht := Nat.mul_le_mul_right (machinePushBound tm) h.steps_le_m
  dsimp only at hrun
  omega

theorem polytime_encoded_output_length {A B : Type}
    {ea : Computability.FinEncoding A} {eb : Computability.FinEncoding B}
    {f : A → B} (h : TM2ComputableInPolyTime ea eb f) (a : A) :
    (eb.encode (f a)).length ≤ (ea.encode a).length +
      h.time.eval (ea.encode a).length * machinePushBound h.tm := by
  have hb := outputsInTime_length h.tm _ _ _ (h.outputsFun a)
  simpa only [List.length_map] using hb

theorem polytime_output_polynomial {A B : Type}
    {ea : Computability.FinEncoding A} {eb : Computability.FinEncoding B}
    {f : A → B} (h : TM2ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, ∀ a, (eb.encode (f a)).length ≤ p.eval (ea.encode a).length := by
  refine ⟨Polynomial.X + h.time * Polynomial.C (machinePushBound h.tm), fun a => ?_⟩
  simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C] using polytime_encoded_output_length h a

end ProteinFolding.TM2Bounds

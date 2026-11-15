import ProteinFolding.Cubic.Proofs.VerifierGeometryMachine

/-! Counted cleanup of the six unary displacement counters in the actual
geometric verifier machine. Context, score, and all other stacks are preserved. -/

namespace ProteinFolding.CubicVerifier.GeometryMachine

open Turing TM2 Computability

theorem update_counter (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (d : Fin 6) (n : ℕ) :
    Function.update (contents w c b r u v o) (counter d) (List.replicate n ()) =
      contents w (Function.update c d n) b r u v o := by
  rw [contents, TM2Embedding.joinStacks_update]
  rw [Row.rowStacks, TM2Embedding.joinStacks_update]
  rw [TM2WalkCounters.update_counter]
  rfl

theorem contents_counter (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (d : Fin 6) :
    contents w c b r u v o (counter d) = List.replicate (c d) () := rfl

theorem drain_step_zero (d : Fin 6) (ctx : Row.Context) (w : List Letter)
    (c : TM2WalkCounters.Counts) (b : ℕ) (r u v : List Letter)
    (o : List (PairSymbol Bool Bool)) (reg : Option Letter) (hc : c d = 0) :
    step program (cfg (.drain d) ctx w c b r u v o reg) =
      some (cfg (nextDrain d) ctx w (Function.update c d 0) b r u v o reg) := by
  simp [cfg, program, drainStmt, step, stepAux, contents_counter, hc]
  exact update_counter w c b r u v o d 0

theorem drain_step_succ (d : Fin 6) (ctx : Row.Context) (w : List Letter)
    (c : TM2WalkCounters.Counts) (n b : ℕ) (r u v : List Letter)
    (o : List (PairSymbol Bool Bool)) (reg : Option Letter) (hc : c d = n + 1) :
    step program (cfg (.drain d) ctx w c b r u v o reg) =
      some (cfg (.drain d) ctx w (Function.update c d n) b r u v o reg) := by
  simp [cfg, program, drainStmt, step, stepAux, contents_counter, hc, List.replicate_succ]
  exact update_counter w c b r u v o d n

theorem drain_axis_aux (d : Fin 6) (ctx : Row.Context) (w : List Letter)
    (n : ℕ) (c : TM2WalkCounters.Counts) (b : ℕ) (r u v : List Letter)
    (o : List (PairSymbol Bool Bool)) (reg : Option Letter) (hc : c d = n) :
    run (n + 1) (cfg (.drain d) ctx w c b r u v o reg) =
      some (cfg (nextDrain d) ctx w (Function.update c d 0) b r u v o reg) := by
  induction n generalizing c with
  | zero =>
    rw [run_step (drain_step_zero d ctx w c b r u v o reg hc) 0]
    rfl
  | succ n ih =>
    rw [run_step (drain_step_succ d ctx w c n b r u v o reg hc) (n + 1)]
    simpa only [Function.update_idem] using
      ih (Function.update c d n) (by simp)

theorem drain_axis (d : Fin 6) (ctx : Row.Context) (w : List Letter)
    (c : TM2WalkCounters.Counts) (b : ℕ) (r u v : List Letter)
    (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (c d + 1) (cfg (.drain d) ctx w c b r u v o reg) =
      some (cfg (nextDrain d) ctx w (Function.update c d 0) b r u v o reg) :=
  drain_axis_aux d ctx w (c d) c b r u v o reg rfl

theorem drain_six (ctx : Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts)
    (b : ℕ) (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (TM2WalkCounters.totalCounts c + 6)
      (cfg (.drain 0) ctx w c b r u v o reg) =
        some (cfg .outer ctx w (fun _ => 0) b r u v o reg) := by
  let c₁ := Function.update c 0 0
  let c₂ := Function.update c₁ 1 0
  let c₃ := Function.update c₂ 2 0
  let c₄ := Function.update c₃ 3 0
  let c₅ := Function.update c₄ 4 0
  let c₆ := Function.update c₅ 5 0
  have h₀ := drain_axis 0 ctx w c b r u v o reg
  have h₁ := drain_axis 1 ctx w c₁ b r u v o reg
  have h₂ := drain_axis 2 ctx w c₂ b r u v o reg
  have h₃ := drain_axis 3 ctx w c₃ b r u v o reg
  have h₄ := drain_axis 4 ctx w c₄ b r u v o reg
  have h₅ := drain_axis 5 ctx w c₅ b r u v o reg
  have h₀₁ := (run_add h₀ (c₁ 1 + 1)).trans h₁
  have h₀₂ := (run_add h₀₁ (c₂ 2 + 1)).trans h₂
  have h₀₃ := (run_add h₀₂ (c₃ 3 + 1)).trans h₃
  have h₀₄ := (run_add h₀₃ (c₄ 4 + 1)).trans h₄
  have h₀₅ := (run_add h₀₄ (c₅ 5 + 1)).trans h₅
  have hz : c₆ = (fun _ : Fin 6 => 0) := by
    funext d
    match d with
    | 0 | 1 | 2 | 3 | 4 | 5 => simp [c₆, c₅, c₄, c₃, c₂, c₁]
  change run _ _ = some (cfg .outer ctx w _ b r u v o reg) at h₀₅
  change run _ _ = some (cfg .outer ctx w c₆ b r u v o reg) at h₀₅
  rw [hz] at h₀₅
  have ht : TM2WalkCounters.totalCounts c + 6 =
      (c 0 + 1) + (c₁ 1 + 1) + (c₂ 2 + 1) + (c₃ 3 + 1) + (c₄ 4 + 1) + (c₅ 5 + 1) := by
    simp [c₅, c₄, c₃, c₂, c₁, TM2WalkCounters.totalCounts]
    omega
  rw [ht]
  exact h₀₅

end ProteinFolding.CubicVerifier.GeometryMachine

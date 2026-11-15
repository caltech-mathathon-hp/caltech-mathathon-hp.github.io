import ProteinFolding.Tetrahedral.CertificatesTM2PairMachine

/-! Serializing the geometric verifier's Boolean flag and unary bond count.
The final step clears the temporary registers and restores the machine's
initial state, as required by mathlib's `haltList` convention. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

open Turing TM2

def halted (o : List (PairSymbol Bool Bool)) : Cfg Alphabet Phase State :=
  ⟨none, initialState, contents [] (fun _ => 0) 0 [] [] [] o⟩

theorem update_bondTokens (w : List Letter) (c : TM2WalkCounters.Counts) (b b' : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) bonds (List.replicate b' ()) =
      contents w c b' r u v o := by
  funext k
  rcases k with ((k | k) | k)
  · simp [bonds, contents, TM2Embedding.joinStacks, CertificatesTM2Row.rowStacks]
  · cases k
    simp [bonds, contents, TM2Embedding.joinStacks, CertificatesTM2Row.rowStacks]
  · simp [bonds, contents, TM2Embedding.joinStacks]

theorem update_output (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o o' : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) output o' = contents w c b r u v o' := by
  funext k
  rcases k with (k | k)
  · simp [output, contents, TM2Embedding.joinStacks]
  · cases k <;> simp [output, contents, TM2Embedding.joinStacks, extraContents]

theorem emit_step_succ (ctx : CertificatesTM2Row.Context) (b : ℕ) (o : List (PairSymbol Bool Bool)) :
    Turing.TM2.step program (cfg .emit ctx [] (fun _ => 0) (b + 1) [] [] [] o) =
      some (cfg .emit ctx [] (fun _ => 0) b [] [] [] (.right true :: o)) := by
  simp [cfg, program, emitStmt, Turing.TM2.step, stepAux, contents, TM2Embedding.joinStacks,
    CertificatesTM2Row.rowStacks, bonds, output, extraContents, List.replicate_succ]
  change Function.update
    (Function.update (contents [] (fun _ => 0) (b + 1) [] [] [] o) bonds
      (List.replicate b ())) output (.right true :: o) =
    contents [] (fun _ => 0) b [] [] [] (.right true :: o)
  rw [update_bondTokens, update_output]

theorem emit_step_zero (ctx : CertificatesTM2Row.Context) (o : List (PairSymbol Bool Bool)) :
    Turing.TM2.step program (cfg .emit ctx [] (fun _ => 0) 0 [] [] [] o) =
      some (halted (.left ctx.valid :: .sep :: o)) := by
  simp [cfg, program, emitStmt, Turing.TM2.step, stepAux, halted, contents, TM2Embedding.joinStacks,
    CertificatesTM2Row.rowStacks, bonds, output, extraContents]
  change Function.update
    (Function.update (contents [] (fun _ => 0) 0 [] [] [] o) bonds
      (List.replicate 0 ())) output (.left ctx.valid :: .sep :: o) =
    contents [] (fun _ => 0) 0 [] [] [] (.left ctx.valid :: .sep :: o)
  rw [update_bondTokens, update_output]

theorem emit_run (ctx : CertificatesTM2Row.Context) (b : ℕ) (o : List (PairSymbol Bool Bool)) :
    run (b + 1) (cfg .emit ctx [] (fun _ => 0) b [] [] [] o) =
      some (halted (.left ctx.valid :: .sep ::
        (List.replicate b (.right true) ++ o))) := by
  induction b generalizing o with
  | zero => simpa only [Nat.zero_add, List.replicate_zero, List.nil_append,
      run, Function.iterate_one, Option.bind_some] using emit_step_zero ctx o
  | succ b ih =>
    rw [run_step (emit_step_succ ctx b o)]
    rw [ih]
    have he : List.replicate b (PairSymbol.right (A := Bool) true) ++ .right true :: o =
        List.replicate (b + 1) (.right true) ++ o := by
      rw [← List.replicate_append_replicate (n := b) (m := 1)]
      simp only [List.replicate_one, List.append_assoc, List.singleton_append]
    rw [he]

end ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

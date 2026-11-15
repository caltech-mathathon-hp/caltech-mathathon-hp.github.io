import ProteinFolding.Tetrahedral.CertificatesTM2PairMachine

namespace ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

open Turing TM2

theorem copy_contents (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    TM2WalkCopy.contents remaining first second (contents w c b [] [] [] o) r u v =
      contents w c b r u v o := by
  unfold TM2WalkCopy.contents
  rw [update_remaining, update_first, update_second]

theorem copy_run (ctx : CertificatesTM2Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (r.length + 1) (cfg .copy ctx w c b r u v o reg) =
      some (cfg .restoreFirst ctx w c b [] (r.reverse ++ u) (r.reverse ++ v) o) := by
  have h := TM2WalkCopy.duplicate_run remaining first second (by decide) (by decide) (by decide)
    (id : Letter → Letter) (id : Letter → Letter) .copy .restoreFirst program rfl
    (((none, false), ctx) : CertificatesTM2Row.State) reg (contents w c b [] [] [] o) r u v
  simpa only [run, cfg, TM2WalkCopy.cfg, copy_contents, List.map_id] using h

theorem first_contents (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    TM2Transfer.setStacks first remaining (contents w c b [] [] v o) u r =
      contents w c b r u v o := by
  unfold TM2Transfer.setStacks
  rw [update_first, update_remaining]

theorem restore_first_run (ctx : CertificatesTM2Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (u.length + 1) (cfg .restoreFirst ctx w c b r u v o reg) =
      some (cfg .restoreSecond ctx w c b (u.reverse ++ r) [] v o) := by
  have h := TM2Transfer.transfer_run first remaining (by decide) (id : Letter → Letter)
    .restoreFirst .restoreSecond program rfl (((none, false), ctx) : CertificatesTM2Row.State) reg
    (contents w c b [] [] v o) u r
  simpa only [run, cfg, TM2Transfer.transferCfg, first_contents, List.map_id] using h

theorem second_contents (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    TM2Transfer.setStacks second input (contents [] c b r u [] o) v w =
      contents w c b r u v o := by
  unfold TM2Transfer.setStacks
  rw [update_second, update_input]

theorem restore_second_run (ctx : CertificatesTM2Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (v.length + 1) (cfg .restoreSecond ctx w c b r u v o reg) =
      some (cfg (.row .scan) ctx (v.reverse ++ w) c b r u [] o) := by
  have h := TM2Transfer.transfer_run second input (by decide) (id : Letter → Letter)
    .restoreSecond (.row .scan) program rfl (((none, false), ctx) : CertificatesTM2Row.State) reg
    (contents [] c b r u [] o) v w
  simpa only [run, cfg, TM2Transfer.transferCfg, second_contents, List.map_id] using h

/-- The suffix is retained for the next outer iteration and an identical copy
is supplied to the row checker. All buffers and the copy register are cleared. -/
theorem prepare_row_run (ctx : CertificatesTM2Row.Context) (r : List Letter) (b : ℕ) (reg : Option Letter) :
    run (3 * r.length + 3) (cfg .copy ctx [] (fun _ => 0) b r [] [] [] reg) =
      some (cfg (.row .scan) ctx r (fun _ => 0) b r [] [] []) := by
  rw [show 3 * r.length + 3 = (r.length + 1) +
    ((r.reverse.length + 1) + (r.reverse.length + 1)) by simp; omega]
  rw [run_add (copy_run ctx [] (fun _ => 0) b r [] [] [] reg)]
  simp only [List.append_nil]
  rw [run_add (restore_first_run ctx [] (fun _ => 0) b [] r.reverse r.reverse [] none)]
  simp only [List.reverse_reverse, List.append_nil]
  simpa only [List.reverse_reverse, List.append_nil] using
    restore_second_run ctx [] (fun _ => 0) b r [] r.reverse [] none

theorem lifted_row_run (ctx : CertificatesTM2Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    run (3 * w.length + 1) (cfg (.row .scan) ctx w c b r u v o reg) =
      some (cfg (.row .finish) (CertificatesTM2Row.rowRun ctx b c w).context []
        (CertificatesTM2Row.rowRun ctx b c w).counts (CertificatesTM2Row.rowRun ctx b c w).bonds r u v o reg) := by
  have h := TM2Embedding.simulate_run (Turing.TM2.step CertificatesTM2Row.program) (Turing.TM2.step program)
    (TM2Embedding.embedCfg Phase.row (some (.drain 0)) reg (extraContents r u v o))
    (fun a b hstep => TM2Embedding.step_liftStmt Phase.row (some (.drain 0))
      CertificatesTM2Row.program program (fun _ => rfl) reg (extraContents r u v o) a b hstep)
    (3 * w.length + 1) (CertificatesTM2Row.cfg .scan ctx w c b)
    (CertificatesTM2Row.cfg .finish (CertificatesTM2Row.rowRun ctx b c w).context []
      (CertificatesTM2Row.rowRun ctx b c w).counts (CertificatesTM2Row.rowRun ctx b c w).bonds)
    (CertificatesTM2Row.row_run ctx w c b)
  simpa only [run, cfg, CertificatesTM2Row.cfg, TM2Embedding.embedCfg, contents, Option.elim_some] using h

theorem row_finish_step (ctx : CertificatesTM2Row.Context) (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) (reg : Option Letter) :
    Turing.TM2.step program (cfg (.row .finish) ctx w c b r u v o reg) =
      some (cfg (.drain 0) ctx w c b r u v o reg) := by
  rfl

theorem row_to_drain_run (ctx : CertificatesTM2Row.Context) (r : List Letter) (b : ℕ) :
    run (3 * r.length + 2) (cfg (.row .scan) ctx r (fun _ => 0) b r [] [] []) =
      some (cfg (.drain 0) (CertificatesTM2Row.rowRun ctx b (fun _ => 0) r).context []
        (CertificatesTM2Row.rowRun ctx b (fun _ => 0) r).counts
        (CertificatesTM2Row.rowRun ctx b (fun _ => 0) r).bonds r [] [] []) := by
  rw [show 3 * r.length + 2 = (3 * r.length + 1) + 1 by omega,
    run_add (lifted_row_run ctx r (fun _ => 0) b r [] [] [] none)]
  exact row_finish_step _ _ _ _ _ _ _ _ _

end ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

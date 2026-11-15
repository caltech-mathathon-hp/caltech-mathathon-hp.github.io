import ProteinFolding.Tetrahedral.CertificatesTM2PairRun
import ProteinFolding.Tetrahedral.CertificatesTM2PairDrain
import Mathlib.Tactic.Linarith

namespace ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

open Turing TM2

def suffixCounts (startA : Bool) (r : List Letter) : TM2WalkCounters.Counts :=
  TM2WalkCounters.runCounts (fun _ => 0) (CertificatesTM2Row.rowDirections startA r)

def coreTime : Bool → List Letter → ℕ
  | _, [] => 0
  | previousA, _ :: r => 6 * r.length + 12 + TM2WalkCounters.totalCounts (suffixCounts (!previousA) r) + coreTime (!previousA) r

def coreResult : CertificatesTM2Row.Context → ℕ → List Letter → CertificatesTM2Row.Context × ℕ
  | ctx, b, [] => (ctx, b)
  | ctx, b, a :: r =>
    let row := CertificatesTM2Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)) b (fun _ => 0) r
    coreResult row.context row.bonds r

theorem coreResult_spec (rs : List Letter) (ctx : CertificatesTM2Row.Context) (b : ℕ) :
    ((coreResult ctx b rs).1.valid, (coreResult ctx b rs).2) = geometryRun ctx.startA ctx.valid b rs := by
  induction rs generalizing ctx b with
  | nil => rfl
  | cons a r ih =>
    exact ih (CertificatesTM2Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)) b (fun _ => 0) r).context
      (CertificatesTM2Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)) b (fun _ => 0) r).bonds

theorem suffixCounts_mass_le (startA : Bool) (r : List Letter) :
    TM2WalkCounters.totalCounts (suffixCounts startA r) ≤ 3 * r.length := by
  simpa only [suffixCounts, TM2WalkCounters.totalCounts, CertificatesTM2Row.rowDirections_length, Nat.zero_add] using
    TM2WalkCounters.runCounts_total_le (fun _ => 0) (CertificatesTM2Row.rowDirections startA r)

/-- One actual outer iteration: pop the starting residue, duplicate and restore
the suffix, scan every endpoint, then reset all six displacement counters. -/
theorem outer_iteration (ctx : CertificatesTM2Row.Context) (a : Letter) (r : List Letter) (b : ℕ) :
    let row := CertificatesTM2Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)) b (fun _ => 0) r
    run (6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
      some (cfg .outer row.context [] (fun _ => 0) row.bonds r [] [] []) := by
  dsimp only
  let pre := rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)
  let row := CertificatesTM2Row.rowRun pre b (fun _ => 0) r
  change run (6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts)
    (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
      some (cfg .outer row.context [] (fun _ => 0) row.bonds r [] [] [])
  rw [show 6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts =
    ((3 * r.length + 3) + ((3 * r.length + 2) +
      (TM2WalkCounters.totalCounts row.counts + 6))) + 1 by omega]
  rw [run_step (outer_step_cons ctx a r b)]
  rw [run_add (prepare_row_run pre r b (some a))]
  rw [run_add (row_to_drain_run pre r b)]
  exact drain_six row.context [] row.counts row.bonds r [] [] [] none

/-- The full nested scan has a concrete successful execution and returns to
the outer label with every temporary stack and counter cleared. -/
theorem outer_run (rs : List Letter) (ctx : CertificatesTM2Row.Context) (b : ℕ) :
    run (coreTime ctx.startA rs) (cfg .outer ctx [] (fun _ => 0) b rs [] [] []) =
      some (cfg .outer (coreResult ctx b rs).1 [] (fun _ => 0)
        (coreResult ctx b rs).2 [] [] [] []) := by
  induction rs generalizing ctx b with
  | nil => rfl
  | cons a r ih =>
    let pre := rowContext (startLabel a) (ctx.valid && a.isSome) (!ctx.startA)
    let row := CertificatesTM2Row.rowRun pre b (fun _ => 0) r
    have hcounts : row.counts = suffixCounts (!ctx.startA) r := CertificatesTM2Row.rowRun_counts pre r (fun _ => 0) b
    have hiter := outer_iteration ctx a r b
    change run (6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
        some (cfg .outer row.context [] (fun _ => 0) row.bonds r [] [] []) at hiter
    rw [hcounts] at hiter
    change run ((6 * r.length + 12 + TM2WalkCounters.totalCounts (suffixCounts (!ctx.startA) r)) + coreTime (!ctx.startA) r)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
        some (cfg .outer (coreResult row.context row.bonds r).1 [] (fun _ => 0)
          (coreResult row.context row.bonds r).2 [] [] [] [])
    rw [run_add hiter]
    have hstart : row.context.startA = !ctx.startA :=
      CertificatesTM2Row.rowRun_startA pre r (fun _ => 0) b
    simpa only [hstart] using ih row.context row.bonds

/-- The actual nested-loop execution uses a quadratic number of TM2 steps. -/
theorem coreTime_bound (previousA : Bool) (rs : List Letter) :
    coreTime previousA rs ≤ 5 * rs.length ^ 2 + 16 * rs.length := by
  induction rs generalizing previousA with
  | nil => simp [coreTime]
  | cons a r ih =>
    have hm := suffixCounts_mass_le (!previousA) r
    have hi := ih (!previousA)
    simp only [coreTime, List.length_cons]
    nlinarith

end ProteinFolding.Tetrahedral.CertificatesTM2Pairs.GeometryMachine

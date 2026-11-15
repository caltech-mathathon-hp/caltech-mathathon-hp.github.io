import ProteinFolding.Cubic.Proofs.VerifierGeometryRun
import ProteinFolding.Cubic.Proofs.VerifierGeometryDrain
import Mathlib.Tactic.Linarith

namespace ProteinFolding.CubicVerifier.GeometryMachine

open Turing TM2

def suffixCounts (r : List Letter) : TM2WalkCounters.Counts :=
  TM2WalkCounters.runCounts (fun _ => 0) (r.map Row.direction)

def coreTime : List Letter → ℕ
  | [] => 0
  | _ :: r => 6 * r.length + 12 + TM2WalkCounters.totalCounts (suffixCounts r) + coreTime r

def coreResult : Row.Context → ℕ → List Letter → Row.Context × ℕ
  | ctx, b, [] => (ctx, b)
  | ctx, b, a :: r =>
    let row := Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome)) b (fun _ => 0) r
    coreResult row.context row.bonds r

theorem coreResult_spec (rs : List Letter) (ctx : Row.Context) (b : ℕ) :
    ((coreResult ctx b rs).1.valid, (coreResult ctx b rs).2) = geometryRun ctx.valid b rs := by
  induction rs generalizing ctx b with
  | nil => rfl
  | cons a r ih =>
    exact ih (Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome)) b (fun _ => 0) r).context
      (Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome)) b (fun _ => 0) r).bonds

theorem suffixCounts_mass_le (r : List Letter) :
    TM2WalkCounters.totalCounts (suffixCounts r) ≤ r.length := by
  simpa only [suffixCounts, TM2WalkCounters.totalCounts, List.length_map, Nat.zero_add] using
    TM2WalkCounters.runCounts_total_le (fun _ => 0) (r.map Row.direction)

/-- One actual outer iteration: pop the starting residue, duplicate and restore
the suffix, scan every endpoint, then reset all six displacement counters. -/
theorem outer_iteration (ctx : Row.Context) (a : Letter) (r : List Letter) (b : ℕ) :
    let row := Row.rowRun (rowContext (startLabel a) (ctx.valid && a.isSome)) b (fun _ => 0) r
    run (6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
      some (cfg .outer row.context [] (fun _ => 0) row.bonds r [] [] []) := by
  dsimp only
  let pre := rowContext (startLabel a) (ctx.valid && a.isSome)
  let row := Row.rowRun pre b (fun _ => 0) r
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
theorem outer_run (rs : List Letter) (ctx : Row.Context) (b : ℕ) :
    run (coreTime rs) (cfg .outer ctx [] (fun _ => 0) b rs [] [] []) =
      some (cfg .outer (coreResult ctx b rs).1 [] (fun _ => 0)
        (coreResult ctx b rs).2 [] [] [] []) := by
  induction rs generalizing ctx b with
  | nil => rfl
  | cons a r ih =>
    let pre := rowContext (startLabel a) (ctx.valid && a.isSome)
    let row := Row.rowRun pre b (fun _ => 0) r
    have hcounts : row.counts = suffixCounts r := Row.rowRun_counts pre r (fun _ => 0) b
    have hiter := outer_iteration ctx a r b
    change run (6 * r.length + 12 + TM2WalkCounters.totalCounts row.counts)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
        some (cfg .outer row.context [] (fun _ => 0) row.bonds r [] [] []) at hiter
    rw [hcounts] at hiter
    change run ((6 * r.length + 12 + TM2WalkCounters.totalCounts (suffixCounts r)) + coreTime r)
      (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
        some (cfg .outer (coreResult row.context row.bonds r).1 [] (fun _ => 0)
          (coreResult row.context row.bonds r).2 [] [] [] [])
    rw [run_add hiter]
    exact ih row.context row.bonds

/-- The actual nested-loop execution uses a quadratic number of TM2 steps. -/
theorem coreTime_bound (rs : List Letter) :
    coreTime rs ≤ 4 * rs.length ^ 2 + 16 * rs.length := by
  induction rs with
  | nil => simp [coreTime]
  | cons a r ih =>
    have hm := suffixCounts_mass_le r
    simp only [coreTime, List.length_cons]
    nlinarith

end ProteinFolding.CubicVerifier.GeometryMachine

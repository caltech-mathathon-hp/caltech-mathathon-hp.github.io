import ProteinFolding.Tetrahedral.Certificates
import ProteinFolding.Common.TM2WalkCounters

/-!
# Translating diamond directions to signed unit-counter updates

Every diamond step is three signed unit-coordinate moves. Its signs depend
only on the direction and the one-bit A/B parity. The shared concrete TM2
counter scanner therefore computes a diamond walk prefix in exactly 3n+1
steps after this finite-state expansion.
-/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Directions

open Turing TM2
open ProteinFolding.TM2WalkCounters

def unitDirections (isA : Bool) (d : Fin 4) : List (Fin 6) :=
  let positive := ![[0, 2, 4], [0, 3, 5], [1, 2, 5], [1, 3, 4]] d
  if isA then positive else positive.map opposite

theorem unitDirections_length (isA : Bool) (d : Fin 4) :
    (unitDirections isA d).length = 3 := by revert isA d; decide

theorem unitDirections_displacement (isA : Bool) (d : Fin 4) (k : Fin 3) :
    displacement (unitDirections isA d) k =
      if isA then bondVector d k else -bondVector d k := by
  revert isA d k
  decide

theorem walkPosition_colour (ds : DirectionWord) (n : ℕ) :
    InASublattice (walkPosition ds n).val ↔ n % 2 = 0 := by
  induction n with
  | zero =>
    change InASublattice origin.val ↔ _
    have h : InASublattice origin.val := by decide
    simp [h]
  | succ n ih =>
    have hcolour := adj_not_same_sublattice
      (step_adj (walkPosition ds n) (ds[n]?.getD 0)).symm
    change InASublattice (step (walkPosition ds n) (ds[n]?.getD 0)).val ↔ _
    rw [hcolour, ih]
    omega

def expandedPrefix (ds : DirectionWord) : ℕ → List (Fin 6)
  | 0 => []
  | n + 1 => expandedPrefix ds n ++ unitDirections (decide (n % 2 = 0)) (ds[n]?.getD 0)

theorem expandedPrefix_length (ds : DirectionWord) (n : ℕ) :
    (expandedPrefix ds n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expandedPrefix, List.length_append, unitDirections_length, ih, Nat.mul_succ]

theorem expandedPrefix_displacement (ds : DirectionWord) (n : ℕ) (k : Fin 3) :
    displacement (expandedPrefix ds n) k = (walkPosition ds n).val k := by
  induction n with
  | zero => simp [expandedPrefix, displacement, walkPosition]
  | succ n ih =>
    rw [expandedPrefix, displacement_append, ih, unitDirections_displacement]
    by_cases hn : n % 2 = 0
    · have hA := (walkPosition_colour ds n).mpr hn
      simp only [hn, decide_true, Bool.true_eq_false, if_true, walkPosition, step_val_of_A _ hA]
    · have hA : ¬ InASublattice (walkPosition ds n).val :=
        fun h => hn ((walkPosition_colour ds n).mp h)
      have hB := (inB_iff_not_inA _).mpr hA
      simp only [hn, decide_false, Bool.false_eq_true, if_false, walkPosition, step_val_of_B _ hB]
      omega

theorem counters_coordinate (ds : DirectionWord) (n : ℕ) (k : Fin 3) :
    coordinate (runCounts (fun _ => 0) (expandedPrefix ds n)) k = (walkPosition ds n).val k := by
  rw [runCounts_zero_coordinate, expandedPrefix_displacement]

theorem counters_mass_bound (ds : DirectionWord) (n : ℕ) :
    totalCounts (runCounts (fun _ => 0) (expandedPrefix ds n)) ≤ 3 * n := by
  have h := runCounts_zero_total_le (expandedPrefix ds n)
  rw [expandedPrefix_length] at h
  exact h

/-- A counted execution of the existing actual finite TM2 counter scanner. -/
theorem expandedPrefix_scanner_run (ds : DirectionWord) (n : ℕ) :
    (fun x : Option (Cfg (Alphabet (Fin 6)) Phase (Option (Fin 6) × Bool)) =>
      x.bind (Turing.TM2.step (program id)))^[3 * n + 1]
      (some (cfg .scan (none, false) (expandedPrefix ds n) (fun _ => 0))) =
        some (cfg .finish (none, false) [] (runCounts (fun _ => 0) (expandedPrefix ds n))) := by
  have h := scan_run (I := Fin 6) id (expandedPrefix ds n) (none, false) (fun _ => 0)
  simpa only [expandedPrefix_length, List.map_id] using h

end ProteinFolding.Tetrahedral.CertificatesTM2Directions

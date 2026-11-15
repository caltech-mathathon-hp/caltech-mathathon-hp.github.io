import ProteinFolding.Cubic.Proofs.VerifierRow

/-! Pure specification of the all-suffix geometric machine. The machine
construction is separate: this file fixes the exact output functions against
which its simulation is proved. Parser errors remain explicit `none` letters.
The incoming direction on the discarded start record is not scanned. -/

namespace ProteinFolding.CubicVerifier

def rowContext (startH valid : Bool) : Row.Context := ⟨false, startH, valid, 0⟩

def startLabel (a : Option Record) : Bool := (a.map (fun r => labelBit r.1)).getD false

def geometryRun : Bool → ℕ → List (Option Record) → Bool × ℕ
  | valid, bonds, [] => (valid, bonds)
  | valid, bonds, a :: input =>
    let row := Row.rowRun (rowContext (startLabel a) (valid && a.isSome)) bonds (fun _ => 0) input
    geometryRun row.context.valid row.bonds input

def geometryValid (input : List (Option Record)) : Bool := (geometryRun true 0 input).1

def bondCountRecords (input : List (Option Record)) : ℕ := (geometryRun true 0 input).2

theorem geometryRun_bonds_le (input : List (Option Record)) (valid : Bool) (bonds : ℕ) :
    (geometryRun valid bonds input).2 ≤ bonds + input.length ^ 2 := by
  induction input generalizing valid bonds with
  | nil => simp [geometryRun]
  | cons a input ih =>
    let row := Row.rowRun (rowContext (startLabel a) (valid && a.isSome)) bonds (fun _ => 0) input
    have hrow : row.bonds ≤ bonds + input.length := Row.rowRun_bonds_le _ _ _ _
    have hrec := ih row.context.valid row.bonds
    change (geometryRun row.context.valid row.bonds input).2 ≤ bonds + (a :: input).length ^ 2
    simp only [List.length_cons, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega

theorem bondCountRecords_le (input : List (Option Record)) :
    bondCountRecords input ≤ input.length ^ 2 := by
  simpa only [bondCountRecords, Nat.zero_add] using geometryRun_bonds_le input true 0

theorem geometryRun_invalid (input : List (Option Record)) (valid : Bool) (bonds : ℕ)
    (hbad : valid = false) : (geometryRun valid bonds input).1 = false := by
  induction input generalizing valid bonds with
  | nil => exact hbad
  | cons a input ih =>
    let row := Row.rowRun (rowContext (startLabel a) (valid && a.isSome)) bonds (fun _ => 0) input
    have hrow : row.context.valid = false := by
      apply Row.rowRun_invalid
      simp [rowContext, hbad]
    change (geometryRun row.context.valid row.bonds input).1 = false
    exact ih row.context.valid row.bonds hrow

theorem geometryRun_none_head_invalid (input : List (Option Record)) (valid : Bool) (bonds : ℕ) :
    (geometryRun valid bonds (none :: input)).1 = false := by
  rw [geometryRun]
  apply geometryRun_invalid
  apply Row.rowRun_invalid
  simp [rowContext]

end ProteinFolding.CubicVerifier

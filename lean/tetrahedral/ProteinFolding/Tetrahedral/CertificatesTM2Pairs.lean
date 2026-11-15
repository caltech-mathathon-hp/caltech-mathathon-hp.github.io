import ProteinFolding.Tetrahedral.CertificatesTM2Row
import Mathlib.Tactic.Linarith

/-! The specification of the all-suffix checkpoint verifier. The colour of
the row's first residue is kept separately from the running endpoint colour.
Only actual residue checkpoints contribute collision tests and H-H bonds. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Pairs


abbrev Record := CertificatesTM2Row.Record

def rowContext (startH valid startA : Bool) : CertificatesTM2Row.Context :=
  ⟨false, startH, valid, 0, startA, startA⟩

def startLabel (a : Option Record) : Bool := (a.map (fun r => CertificatesTM2Row.labelBit r.1)).getD false

def geometryRun : Bool → Bool → ℕ → List (Option Record) → Bool × ℕ
  | _, valid, bonds, [] => (valid, bonds)
  | previousA, valid, bonds, a :: input =>
    let row := CertificatesTM2Row.rowRun (rowContext (startLabel a) (valid && a.isSome) (!previousA))
      bonds (fun _ => 0) input
    geometryRun row.context.startA row.context.valid row.bonds input

def geometryValid (input : List (Option Record)) : Bool := (geometryRun false true 0 input).1

def bondCountRecords (input : List (Option Record)) : ℕ := (geometryRun false true 0 input).2

theorem geometryRun_bonds_le (input : List (Option Record)) (previousA valid : Bool) (bonds : ℕ) :
    (geometryRun previousA valid bonds input).2 ≤ bonds + input.length ^ 2 := by
  induction input generalizing previousA valid bonds with
  | nil => simp [geometryRun]
  | cons a input ih =>
    let row := CertificatesTM2Row.rowRun (rowContext (startLabel a) (valid && a.isSome) (!previousA))
      bonds (fun _ => 0) input
    have hrow : row.bonds ≤ bonds + input.length := CertificatesTM2Row.rowRun_bonds_le _ _ _ _
    have hrec := ih row.context.startA row.context.valid row.bonds
    change (geometryRun row.context.startA row.context.valid row.bonds input).2 ≤
      bonds + (a :: input).length ^ 2
    simp only [List.length_cons, Nat.pow_two, Nat.mul_add, Nat.add_mul,
      Nat.mul_one, Nat.one_mul] at *
    omega

theorem bondCountRecords_le (input : List (Option Record)) :
    bondCountRecords input ≤ input.length ^ 2 := by
  simpa only [bondCountRecords, Nat.zero_add] using geometryRun_bonds_le input false true 0

theorem geometryRun_invalid (input : List (Option Record)) (previousA valid : Bool) (bonds : ℕ)
    (hbad : valid = false) : (geometryRun previousA valid bonds input).1 = false := by
  induction input generalizing previousA valid bonds with
  | nil => exact hbad
  | cons a input ih =>
    let row := CertificatesTM2Row.rowRun (rowContext (startLabel a) (valid && a.isSome) (!previousA))
      bonds (fun _ => 0) input
    have hrow : row.context.valid = false := by
      apply CertificatesTM2Row.rowRun_invalid
      simp [rowContext, hbad]
    change (geometryRun row.context.startA row.context.valid row.bonds input).1 = false
    exact ih row.context.startA row.context.valid row.bonds hrow

theorem geometryRun_none_head_invalid (input : List (Option Record))
    (previousA valid : Bool) (bonds : ℕ) :
    (geometryRun previousA valid bonds (none :: input)).1 = false := by
  rw [geometryRun]
  apply geometryRun_invalid
  apply CertificatesTM2Row.rowRun_invalid
  simp [rowContext]

end ProteinFolding.Tetrahedral.CertificatesTM2Pairs

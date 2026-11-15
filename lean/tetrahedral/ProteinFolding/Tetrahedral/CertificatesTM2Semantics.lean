import ProteinFolding.Tetrahedral.CertificatesTM2Pairs
import ProteinFolding.Tetrahedral.CertificatesTM2Records

/-! Correctness of the checkpoint collision flag. Every later original
residue is inspected; intermediate unit updates are not residue positions. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Semantics

open ProteinFolding.TM2WalkCounters
open CertificatesTM2Expansion CertificatesTM2Records CertificatesTM2Pairs

abbrev Record := CertificatesTM2Records.Record
abbrev Row := CertificatesTM2Row.Context

def rowColour (previousA : Bool) (i : ℕ) : Bool :=
  if i % 2 = 0 then !previousA else previousA

theorem rowColour_zero (previousA : Bool) : rowColour previousA 0 = !previousA := by
  simp [rowColour]

theorem rowColour_succ (previousA : Bool) (i : ℕ) :
    rowColour previousA (i + 1) = rowColour (!previousA) i := by
  unfold rowColour
  by_cases hi : i % 2 = 0
  · have hi' : (i + 1) % 2 ≠ 0 := by omega
    simp [hi, hi']
  · have hi' : (i + 1) % 2 = 0 := by omega
    simp [hi, hi']

theorem rowColour_false (i : ℕ) : rowColour false i = decide (i % 2 = 0) := by
  unfold rowColour
  split_ifs <;> simp_all

def RowClear (isA : Bool) (c : Counts) (rs : List Record) : Prop :=
  ∀ k : Fin rs.length,
    CertificatesTM2Inspector.cap (totalCounts
      (runCounts c (expandFrom isA ((rs.take (k.val + 1)).map Prod.snd)))) ≠ 0

theorem rowClear_cons (isA : Bool) (c : Counts) (r : Record) (rs : List Record) :
    RowClear isA c (r :: rs) ↔
      CertificatesTM2Inspector.cap (totalCounts
        (runCounts c (CertificatesTM2Directions.unitDirections isA r.2))) ≠ 0 ∧
      RowClear (!isA) (runCounts c (CertificatesTM2Directions.unitDirections isA r.2)) rs := by
  simp [RowClear, Fin.forall_fin_succ, expandFrom, CertificatesTM2Row.runCounts_append,
    runCounts]

theorem rowRun_valid_records (ctx : Row) (bonds : ℕ) (c : Counts)
    (rs : List Record) (hseen : ctx.seen = 0) :
    (CertificatesTM2Row.rowRun ctx bonds c (rs.map some)).context.valid = true ↔
      ctx.valid = true ∧ RowClear ctx.phaseA c rs := by
  induction rs generalizing ctx bonds c with
  | nil => simp [CertificatesTM2Row.rowRun, CertificatesTM2Row.peekContext, RowClear]
  | cons r rs ih =>
    rw [List.map_cons, CertificatesTM2Row.rowRun, ih _ _ _ (by rfl), rowClear_cons]
    simp [CertificatesTM2Row.nextContext, CertificatesTM2Row.afterLetter,
      CertificatesTM2Row.peekContext, CertificatesTM2Row.advance,
      CertificatesTM2Row.direction, hseen, Bool.and_eq_true, and_assoc]

def ClearRows (previousA : Bool) (rs : List Record) : Prop :=
  ∀ i : Fin rs.length, RowClear (rowColour previousA i.val) (fun _ => 0) (rs.drop (i.val + 1))

theorem clearRows_cons (previousA : Bool) (r : Record) (rs : List Record) :
    ClearRows previousA (r :: rs) ↔
      RowClear (!previousA) (fun _ => 0) rs ∧ ClearRows (!previousA) rs := by
  simp [ClearRows, Fin.forall_fin_succ, rowColour_zero, rowColour_succ]

theorem geometryRun_valid_records (previousA valid : Bool) (bonds : ℕ) (rs : List Record) :
    (geometryRun previousA valid bonds (rs.map some)).1 = true ↔
      valid = true ∧ ClearRows previousA rs := by
  induction rs generalizing previousA valid bonds with
  | nil => simp [geometryRun, ClearRows]
  | cons r rs ih =>
    simp only [List.map_cons, geometryRun]
    rw [CertificatesTM2Row.rowRun_startA, ih,
      rowRun_valid_records _ _ _ _ (by rfl), clearRows_cons]
    simp [rowContext, and_assoc]

theorem rowClear_suffix_iff (rs : List Record) (i : Fin rs.length) :
    RowClear (decide (i.val % 2 = 0)) (fun _ => 0) (rs.drop (i.val + 1)) ↔
      ∀ j : Fin rs.length, i < j → recordPosition rs i.val ≠ recordPosition rs j.val := by
  constructor
  · intro h j hij heq
    let k : Fin (rs.drop (i.val + 1)).length :=
      ⟨j.val - (i.val + 1), by
        have := j.isLt
        simp only [List.length_drop]
        omega⟩
    have hk := h k
    have hlen : j.val - i.val = k.val + 1 := by dsimp [k]; omega
    have hz := (inspected_suffix_zero_iff rs i.val j.val (by omega) j.isLt).2 heq
    exact hk (by simpa only [suffixExpanded, suffixDirections, hlen] using hz)
  · intro h k hz
    let j : Fin rs.length := ⟨i.val + 1 + k.val, by
      have hk := k.isLt
      simp only [List.length_drop] at hk
      omega⟩
    have hlen : j.val - i.val = k.val + 1 := by dsimp [j]; omega
    apply h j (by dsimp [j]; omega)
    apply (inspected_suffix_zero_iff rs i.val j.val (by dsimp [j]; omega) j.isLt).1
    simpa only [suffixExpanded, suffixDirections, hlen] using hz

theorem clearRows_iff_injective (rs : List Record) :
    ClearRows false rs ↔
      Function.Injective (fun i : Fin rs.length => recordPosition rs i.val) := by
  simp only [ClearRows, rowColour_false, rowClear_suffix_iff]
  constructor
  · intro h i j heq
    by_cases hij : i.val < j.val
    · exact False.elim (h i j hij heq)
    · by_cases hji : j.val < i.val
      · exact False.elim (h j i hji heq.symm)
      · apply Fin.ext
        omega
  · intro h i j hij heq
    have he := congrArg Fin.val (h heq)
    omega

theorem geometryValid_records_iff (rs : List Record) :
    geometryValid (rs.map some) = true ↔
      Function.Injective (fun i : Fin rs.length => recordPosition rs i.val) := by
  simp [geometryValid, geometryRun_valid_records, clearRows_iff_injective]

theorem rowRun_valid_initial (ctx : Row) (bonds : ℕ) (c : Counts)
    (input : List (Option Record))
    (h : (CertificatesTM2Row.rowRun ctx bonds c input).context.valid = true) :
    ctx.valid = true := by
  cases hv : ctx.valid
  · have hf := CertificatesTM2Row.rowRun_invalid ctx input c bonds hv
    rw [h] at hf
    contradiction
  · rfl

theorem geometryRun_valid_initial (previousA valid : Bool) (bonds : ℕ)
    (input : List (Option Record)) (h : (geometryRun previousA valid bonds input).1 = true) :
    valid = true := by
  cases hv : valid
  · have hf := geometryRun_invalid input previousA valid bonds hv
    rw [h] at hf
    contradiction
  · rfl

theorem geometryRun_some (previousA valid : Bool) (bonds : ℕ)
    (input : List (Option Record))
    (h : (geometryRun previousA valid bonds input).1 = true) :
    ∃ rs : List Record, input = rs.map some := by
  induction input generalizing previousA valid bonds with
  | nil => exact ⟨[], rfl⟩
  | cons a input ih =>
    let row := CertificatesTM2Row.rowRun
      (rowContext (startLabel a) (valid && a.isSome) (!previousA)) bonds (fun _ => 0) input
    change (geometryRun row.context.startA row.context.valid row.bonds input).1 = true at h
    obtain ⟨rs, hrs⟩ := ih row.context.startA row.context.valid row.bonds h
    have hrow := geometryRun_valid_initial row.context.startA row.context.valid row.bonds input h
    have ha := rowRun_valid_initial _ _ _ _ hrow
    change (valid && a.isSome) = true at ha
    cases a with
    | none => simp at ha
    | some r => exact ⟨r :: rs, by simp only [List.map_cons, hrs]⟩

theorem geometryValid_some (input : List (Option Record))
    (h : geometryValid input = true) : ∃ rs : List Record, input = rs.map some :=
  geometryRun_some false true 0 input h

end ProteinFolding.Tetrahedral.CertificatesTM2Semantics

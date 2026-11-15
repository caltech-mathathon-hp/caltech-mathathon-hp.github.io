import ProteinFolding.Cubic.Proofs.VerifierGeometry

/-! Correctness of the geometric validity flag. Every suffix is inspected at
every later endpoint, so acceptance is exactly self-avoidance. Malformed
decoded records are rejected, including a malformed first record. -/

namespace ProteinFolding.CubicVerifier

open TM2WalkCounters

def RowClear (c : Counts) (rs : List Record) : Prop :=
  ∀ k : Fin rs.length,
    TM2WalkInspector.cap (totalCounts (runCounts c ((rs.take (k.val + 1)).map Prod.snd))) ≠ 0

theorem rowClear_nil (c : Counts) : RowClear c [] := by
  intro k
  exact Fin.elim0 k

theorem rowClear_cons (c : Counts) (r : Record) (rs : List Record) :
    RowClear c (r :: rs) ↔
      TM2WalkInspector.cap (totalCounts (updateCounts c r.2)) ≠ 0 ∧
        RowClear (updateCounts c r.2) rs := by
  simp [RowClear, Fin.forall_fin_succ, runCounts]

theorem rowRun_valid_records (ctx : Row.Context) (bonds : ℕ) (c : Counts)
    (rs : List Record) (hseen : ctx.seen = 0) :
    (Row.rowRun ctx bonds c (rs.map some)).context.valid = true ↔
      ctx.valid = true ∧ RowClear c rs := by
  induction rs generalizing ctx bonds c with
  | nil => simp [Row.rowRun, Row.peekContext, RowClear]
  | cons r rs ih =>
    rw [List.map_cons, Row.rowRun, ih _ _ _ (by rfl), rowClear_cons]
    simp [Row.nextContext, Row.afterLetter, Row.peekContext, Row.direction, hseen,
      Bool.and_eq_true, and_assoc]

def ClearRows (rs : List Record) : Prop :=
  ∀ i : Fin rs.length, RowClear (fun _ => 0) (rs.drop (i.val + 1))

theorem clearRows_cons (r : Record) (rs : List Record) :
    ClearRows (r :: rs) ↔ RowClear (fun _ => 0) rs ∧ ClearRows rs := by
  simp [ClearRows, Fin.forall_fin_succ]

theorem geometryRun_valid_records (valid : Bool) (bonds : ℕ) (rs : List Record) :
    (geometryRun valid bonds (rs.map some)).1 = true ↔ valid = true ∧ ClearRows rs := by
  induction rs generalizing valid bonds with
  | nil => simp [geometryRun, ClearRows]
  | cons r rs ih =>
    simp only [List.map_cons, geometryRun]
    rw [ih, rowRun_valid_records _ _ _ _ (by rfl), clearRows_cons]
    simp [rowContext, and_assoc]

theorem rowClear_suffix_iff (rs : List Record) (i : Fin rs.length) :
    RowClear (fun _ => 0) (rs.drop (i.val + 1)) ↔
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
    rw [hlen] at hz
    exact hk hz
  · intro h k hz
    let j : Fin rs.length := ⟨i.val + 1 + k.val, by
      have hk := k.isLt
      simp only [List.length_drop] at hk
      omega⟩
    have hlen : j.val - i.val = k.val + 1 := by dsimp [j]; omega
    apply h j (by dsimp [j]; omega)
    apply (inspected_suffix_zero_iff rs i.val j.val (by dsimp [j]; omega) j.isLt).1
    simpa only [hlen] using hz

theorem clearRows_iff_injective (rs : List Record) :
    ClearRows rs ↔ Function.Injective (fun i : Fin rs.length => recordPosition rs i.val) := by
  simp only [ClearRows, rowClear_suffix_iff]
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

theorem rowRun_valid_initial (ctx : Row.Context) (bonds : ℕ) (c : Counts)
    (input : List (Option Record))
    (h : (Row.rowRun ctx bonds c input).context.valid = true) : ctx.valid = true := by
  cases hv : ctx.valid
  · have hf := Row.rowRun_invalid ctx input c bonds hv
    rw [h] at hf
    contradiction
  · rfl

theorem geometryRun_valid_initial (valid : Bool) (bonds : ℕ)
    (input : List (Option Record)) (h : (geometryRun valid bonds input).1 = true) :
    valid = true := by
  cases hv : valid
  · have hf := geometryRun_invalid input valid bonds hv
    rw [h] at hf
    contradiction
  · rfl

theorem geometryRun_some (valid : Bool) (bonds : ℕ) (input : List (Option Record))
    (h : (geometryRun valid bonds input).1 = true) :
    ∃ rs : List Record, input = rs.map some := by
  induction input generalizing valid bonds with
  | nil => exact ⟨[], rfl⟩
  | cons a input ih =>
    let row := Row.rowRun (rowContext (startLabel a) (valid && a.isSome)) bonds (fun _ => 0) input
    change (geometryRun row.context.valid row.bonds input).1 = true at h
    obtain ⟨rs, hrs⟩ := ih row.context.valid row.bonds h
    have hrow := geometryRun_valid_initial row.context.valid row.bonds input h
    have ha := rowRun_valid_initial _ _ _ _ hrow
    change (valid && a.isSome) = true at ha
    cases a with
    | none => simp at ha
    | some r => exact ⟨r :: rs, by simp only [List.map_cons, hrs]⟩

theorem geometryValid_some (input : List (Option Record))
    (h : geometryValid input = true) : ∃ rs : List Record, input = rs.map some :=
  geometryRun_some true 0 input h

end ProteinFolding.CubicVerifier

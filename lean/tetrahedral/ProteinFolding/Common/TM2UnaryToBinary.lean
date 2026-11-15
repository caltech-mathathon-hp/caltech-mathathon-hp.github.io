import ProteinFolding.Common.TM2Transfer
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.Linarith

/-! Canonical unary-to-binary conversion by repeated increment. Binary digits
are little-endian, exactly as in mathlib's `encodeNat`. A carry scans trailing
ones into a unary temporary stack; restoration writes their replacement zeros.
The output stack itself holds the current binary number. All temporary stacks
are empty and the finite register is restored when the machine halts. -/

namespace ProteinFolding.TM2UnaryToBinary

open Computability Turing TM2

def increment : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs

def trailingOnes : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: bs => trailingOnes bs + 1

def stopWord : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => stopWord bs

theorem trailingOnes_le (bs : List Bool) : trailingOnes bs ≤ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [trailingOnes]

theorem increment_eq (bs : List Bool) :
    increment bs = List.replicate (trailingOnes bs) false ++ stopWord bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [increment, trailingOnes, stopWord, List.replicate_succ, ih]

theorem increment_length_le (bs : List Bool) : (increment bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [increment]

theorem increment_encodePosNum (p : PosNum) :
    increment (encodePosNum p) = encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit0 p ih => rfl
  | bit1 p ih => simpa only [encodePosNum, PosNum.succ, increment] using congrArg (false :: ·) ih

theorem increment_encodeNum (n : Num) : increment (encodeNum n) = encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos p => exact increment_encodePosNum p

theorem increment_encodeNat (n : ℕ) : increment (encodeNat n) = encodeNat (n + 1) := by
  change increment (encodeNum (n : Num)) = encodeNum ((n + 1 : ℕ) : Num)
  rw [Nat.cast_succ, Num.add_one]
  exact increment_encodeNum _

theorem iterate_increment_encodeNat (n m : ℕ) :
    increment^[n] (encodeNat m) = encodeNat (m + n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, increment_encodeNat, ih]
    congr 1
    omega

inductive Slot where
  | input | bits | carry
  deriving DecidableEq, Fintype

inductive Phase where
  | outer | increment | restore
  deriving DecidableEq, Fintype

def Alphabet : Slot → Type
  | .input | .bits => Bool
  | .carry => Unit

def contents (u bs : List Bool) (c : ℕ) : ∀ k, List (Alphabet k)
  | .input => u
  | .bits => bs
  | .carry => List.replicate c ()

def cfg (p : Phase) (u bs : List Bool) (c : ℕ) : Cfg Alphabet Phase (Option Bool) :=
  ⟨some p, none, contents u bs c⟩

def halted (bs : List Bool) : Cfg Alphabet Phase (Option Bool) :=
  ⟨none, none, contents [] bs 0⟩

def program : Phase → Stmt Alphabet Phase (Option Bool)
  | .outer => .pop .input (fun _ a => a)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => .increment)))
        (.load (fun _ => none) .halt))
  | .increment => .pop .bits (fun _ b => b)
      (.branch (fun b => decide (b = some true))
        (.push .carry (fun _ => ()) (.load (fun _ => none) (.goto (fun _ => .increment))))
        (.push .bits (fun _ => true) (.load (fun _ => none) (.goto (fun _ => .restore)))))
  | .restore => .pop .carry (fun _ a => a.map (fun _ => true))
      (.branch Option.isSome
        (.push .bits (fun _ => false) (.load (fun _ => none) (.goto (fun _ => .restore))))
        (.load (fun _ => none) (.goto (fun _ => .outer))))

theorem update_input (u u' bs : List Bool) (c : ℕ) :
    Function.update (contents u bs c) .input u' = contents u' bs c := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_bits (u bs bs' : List Bool) (c : ℕ) :
    Function.update (contents u bs c) .bits bs' = contents u bs' c := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_carry (u bs : List Bool) (c c' : ℕ) :
    Function.update (contents u bs c) .carry (List.replicate c' ()) = contents u bs c' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem outer_cons_step (a : Bool) (u bs : List Bool) :
    step program (cfg .outer (a :: u) bs 0) = some (cfg .increment u bs 0) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem outer_nil_step (bs : List Bool) :
    step program (cfg .outer [] bs 0) = some (halted bs) := by
  simp [cfg, program, step, stepAux, contents, halted]

theorem increment_true_step (u bs : List Bool) (c : ℕ) :
    step program (cfg .increment u (true :: bs) c) = some (cfg .increment u bs (c + 1)) := by
  simp [cfg, program, step, stepAux, contents, update_bits, ← List.replicate_succ, update_carry]

theorem increment_false_step (u bs : List Bool) (c : ℕ) :
    step program (cfg .increment u (false :: bs) c) = some (cfg .restore u (true :: bs) c) := by
  simp [cfg, program, step, stepAux, contents, update_bits]

theorem increment_nil_step (u : List Bool) (c : ℕ) :
    step program (cfg .increment u [] c) = some (cfg .restore u [true] c) := by
  simp [cfg, program, step, stepAux, contents, update_bits]

theorem restore_succ_step (u bs : List Bool) (c : ℕ) :
    step program (cfg .restore u bs (c + 1)) = some (cfg .restore u (false :: bs) c) := by
  simp [cfg, program, step, stepAux, contents, List.replicate_succ]
  change Function.update (Function.update (contents u bs (c + 1)) .carry
    (List.replicate c ())) .bits (false :: bs) = contents u (false :: bs) c
  rw [update_carry, update_bits]

theorem restore_zero_step (u bs : List Bool) :
    step program (cfg .restore u bs 0) = some (cfg .outer u bs 0) := by
  simp [cfg, program, step, stepAux, contents]

def run (n : ℕ) (q : Cfg Alphabet Phase (Option Bool)) : Option (Cfg Alphabet Phase (Option Bool)) :=
  (fun x : Option (Cfg Alphabet Phase (Option Bool)) => x.bind (step program))^[n] (some q)

theorem run_step {q q' : Cfg Alphabet Phase (Option Bool)}
    (h : step program q = some q') (n : ℕ) : run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg Alphabet Phase (Option Bool)} {n : ℕ}
    (h : run n q = some q') (m : ℕ) : run (n + m) q = run m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg Alphabet Phase (Option Bool)) => x.bind (step program))^[n]
      (some q) = some q' from h]

theorem increment_scan_run (u bs : List Bool) (c : ℕ) :
    run (trailingOnes bs + 1) (cfg .increment u bs c) =
      some (cfg .restore u (stopWord bs) (c + trailingOnes bs)) := by
  induction bs generalizing c with
  | nil => simpa [run, trailingOnes, stopWord] using increment_nil_step u c
  | cons b bs ih =>
    cases b with
    | false => simpa [run, trailingOnes, stopWord] using increment_false_step u bs c
    | true =>
      simp only [trailingOnes, stopWord]
      rw [run_step (increment_true_step u bs c)]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (c + 1)

theorem restore_run (u bs : List Bool) (c : ℕ) :
    run (c + 1) (cfg .restore u bs c) =
      some (cfg .outer u (List.replicate c false ++ bs) 0) := by
  induction c generalizing bs with
  | zero => simpa [run] using restore_zero_step u bs
  | succ c ih =>
    rw [run_step (restore_succ_step u bs c), ih]
    simp [List.replicate_succ', List.append_assoc]

theorem increment_run (u bs : List Bool) :
    run (2 * trailingOnes bs + 2) (cfg .increment u bs 0) =
      some (cfg .outer u (increment bs) 0) := by
  rw [show 2 * trailingOnes bs + 2 = (trailingOnes bs + 1) + (trailingOnes bs + 1) by omega,
    run_add (increment_scan_run u bs 0)]
  simpa [increment_eq] using restore_run u (stopWord bs) (trailingOnes bs)

def loopTime : ℕ → List Bool → ℕ
  | 0, _ => 1
  | n + 1, bs => 2 * trailingOnes bs + 3 + loopTime n (increment bs)

theorem loopTime_bound (n : ℕ) (bs : List Bool) :
    loopTime n bs ≤ n * (2 * (bs.length + n) + 3) + 1 := by
  induction n generalizing bs with
  | zero => simp [loopTime]
  | succ n ih =>
    have ht := ih (increment bs)
    have hl := increment_length_le bs
    have hc := trailingOnes_le bs
    have hm := Nat.mul_le_mul_left n (by omega :
      2 * ((increment bs).length + n) + 3 ≤ 2 * (bs.length + (n + 1)) + 3)
    simp only [loopTime]
    nlinarith

theorem outer_run (u bs : List Bool) :
    run (loopTime u.length bs) (cfg .outer u bs 0) =
      some (halted (increment^[u.length] bs)) := by
  induction u generalizing bs with
  | nil => simpa [loopTime, run] using outer_nil_step bs
  | cons a u ih =>
    simp only [List.length_cons, loopTime]
    rw [show 2 * trailingOnes bs + 3 + loopTime u.length (increment bs) =
      ((2 * trailingOnes bs + 2) + loopTime u.length (increment bs)) + 1 by omega,
      run_step (outer_cons_step a u bs), run_add (increment_run u bs), ih]
    rw [Function.iterate_succ_apply]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .bits
  Γ := Alphabet
  Λ := Phase
  main := .outer
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryEncodeNat] using congrArg Nat.succ ih

def machine_outputs (n : ℕ) : TM2OutputsInTime machine (unaryEncodeNat n) (some (encodeNat n))
    (2 * (unaryEncodeNat n).length ^ 2 + 3 * (unaryEncodeNat n).length + 1) := by
  have hi : initList machine (unaryEncodeNat n) = cfg .outer (unaryEncodeNat n) [] 0 := by
    apply congrArg (fun S => (⟨some .outer, none, S⟩ : Cfg Alphabet Phase (Option Bool)))
    funext k; cases k <;> rfl
  have ho : haltList machine (encodeNat n) = halted (encodeNat n) := by
    apply congrArg (fun S => (⟨none, none, S⟩ : Cfg Alphabet Phase (Option Bool)))
    funext k; cases k <;> rfl
  refine
    { steps := loopTime n []
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run _ (initList machine _) = some (haltList machine _)
    rw [hi, ho]
    have h := outer_run (unaryEncodeNat n) []
    rw [unary_length] at h
    have hcode : increment^[n] [] = encodeNat n := by
      have he : encodeNat 0 = [] := by
        change encodeNum ((0 : ℕ) : Num) = []
        rw [show ((0 : ℕ) : Num) = Num.zero from Num.of_to_nat Num.zero]
        rfl
      simpa only [he, Nat.zero_add] using iterate_increment_encodeNat n 0
    simpa only [hcode] using h
  · have ht := loopTime_bound n []
    simp only [List.length_nil, Nat.zero_add, unary_length] at *
    nlinarith

/-- The identity from unary natural words to canonical little-endian binary
natural words, implemented in at most `2*X²+3*X+1` TM2 steps. -/
noncomputable def unaryToBinaryComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat finEncodingNatBool (id : ℕ → ℕ) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1
  outputsFun n := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id (unaryEncodeNat n))
      (some (List.map id (encodeNat n)))
      (2 * (unaryEncodeNat n).length ^ 2 + 3 * (unaryEncodeNat n).length + 1)
    simpa only [List.map_id] using machine_outputs n

end ProteinFolding.TM2UnaryToBinary

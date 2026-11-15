import ProteinFolding.Common.TM2ArithmeticComparison

/-! Counted parsing of the frozen sign/binary/unary pair format. -/

namespace ProteinFolding.TM2Arithmetic.Comparator

open Computability Turing TM2

def inputWord (negative : Bool) (w : List Bool) (c : ℕ) : List Sym :=
  .left negative :: (w.map PairSymbol.left ++ .sep :: (unaryEncodeNat c).map PairSymbol.right)

theorem unaryEncodeNat_length (c : ℕ) : (unaryEncodeNat c).length = c := by
  induction c <;> simp_all [unaryEncodeNat]

theorem inputWord_length (negative : Bool) (w : List Bool) (c : ℕ) :
    (inputWord negative w c).length = w.length + c + 2 := by
  simp [inputWord, unaryEncodeNat_length]; omega

theorem sign_step (negative : Bool) (i : List Sym) :
    tick (some (cfg .sign initial (.left negative :: i) [] [] [] [])) =
      some (cfg .scan (regs true negative false) i [] [] [] []) := by
  simp [tick, cfg, initial, regs, program, step, stepAux, contents, update_input, leftBit]

theorem scan_left_step (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.left a :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i (a :: b) w u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_input, update_buffer, leftBit]

theorem scan_right_step (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.right a :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i b w (true :: u) o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_input, update_unary,
    leftBit, rightToken]

theorem scan_sep_step (borrow neg res : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.sep :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i b w u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_input, leftBit, rightToken]

def afterScan (negative : Bool) (b u : List Bool) : Cfg Alphabet Phase Reg :=
  if negative then cfg .clearBits (regs true true true) [] b [] u []
  else cfg .restore (regs true false false) [] b [] u []

theorem scan_nil_step (negative : Bool) (b u : List Bool) :
    tick (some (cfg .scan (regs true negative false) [] b [] u [])) =
      some (afterScan negative b u) := by
  cases negative <;>
    simp [tick, cfg, regs, program, step, stepAux, contents, update_input, afterScan]

theorem scan_left_run (bs : List Bool) (borrow neg res : Bool) (i : List Sym)
    (b w u o : List Bool) :
    tick^[bs.length] (some (cfg .scan (regs borrow neg res)
      (bs.map PairSymbol.left ++ i) b w u o)) =
        some (cfg .scan (regs borrow neg res) i (bs.reverse ++ b) w u o) := by
  induction bs generalizing b with
  | nil => rfl
  | cons a bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append, scan_left_step]
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: b)

theorem scan_unary_run (c : ℕ) (borrow neg res : Bool) (i : List Sym)
    (b w u o : List Bool) :
    tick^[c] (some (cfg .scan (regs borrow neg res)
      ((unaryEncodeNat c).map PairSymbol.right ++ i) b w u o)) =
        some (cfg .scan (regs borrow neg res) i b w (List.replicate c true ++ u) o) := by
  induction c generalizing u with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply]
    simp only [unaryEncodeNat, List.map_cons, List.cons_append, scan_right_step]
    have hrep (c : ℕ) : List.replicate c true ++ true :: u =
        true :: (List.replicate c true ++ u) := by
      induction c with
      | zero => rfl
      | succ c hc =>
        have he := congrArg (List.cons true) hc
        simpa only [List.replicate_succ, List.cons_append] using he
    simpa only [List.replicate_succ, List.cons_append, hrep] using ih (true :: u)

theorem run_one {a b : Option (Cfg Alphabet Phase Reg)} (h : tick a = b) : tick^[1] a = b := by
  simpa only [Function.iterate_one] using h

theorem parse_run (negative : Bool) (w : List Bool) (c : ℕ) :
    tick^[w.length + c + 3]
      (some (cfg .sign initial (inputWord negative w c) [] [] [] [])) =
        some (afterScan negative w.reverse (List.replicate c true)) := by
  have h1 := sign_step negative
    (w.map PairSymbol.left ++ .sep :: (unaryEncodeNat c).map PairSymbol.right)
  have h2 := scan_left_run w true negative false
    (.sep :: (unaryEncodeNat c).map PairSymbol.right) [] [] [] []
  simp only [List.append_nil] at h2
  have h3 := scan_sep_step true negative false
    ((unaryEncodeNat c).map PairSymbol.right) w.reverse [] [] []
  have h4 := scan_unary_run c true negative false [] w.reverse [] [] []
  simp only [List.append_nil] at h4
  have h5 := scan_nil_step negative w.reverse (List.replicate c true)
  have ht := run_join _ 1 (run_join _ _ (run_join _ 1
    (run_join 1 _ (run_one h1) h2) (run_one h3)) h4) (run_one h5)
  have he : 1 + w.length + 1 + c + 1 = w.length + c + 3 := by omega
  simpa only [he, inputWord] using ht

theorem program_run (negative : Bool) (w : List Bool) (c : ℕ) :
    ∃ steps, steps ≤ 10 * (w.length + c + 3) ^ 2 + 10 ∧
      tick^[steps] (some (cfg .sign initial (inputWord negative w c) [] [] [] [])) =
        some (doneCfg (if negative then true else decide (bitValue w ≤ c))) := by
  have hp := parse_run negative w c
  cases negative with
  | true =>
    have hcl := cleanup_run [] w.reverse (List.replicate c true) true true true []
    have ht := run_join _ _ hp hcl
    refine ⟨(w.length + c + 3) + (w.reverse.length + (List.replicate c true).length + 4), ?_, ?_⟩
    · simp only [List.length_reverse, List.length_replicate]
      nlinarith [Nat.zero_le (w.length * c), Nat.zero_le (w.length ^ 2), Nat.zero_le (c ^ 2)]
    · simpa [afterScan, doneCfg] using ht
  | false =>
    have hrestore := restore_run w.reverse true false false [] [] (List.replicate c true) []
    simp only [List.reverse_reverse, List.append_nil] at hrestore
    obtain ⟨t, hbound, hrun⟩ := comparison_run (List.replicate c true) w
    simp only [List.length_replicate] at hbound hrun
    have ht := run_join _ _ (run_join _ _ hp hrestore) hrun
    refine ⟨(w.length + c + 3) + (w.reverse.length + 1) + t, ?_, ?_⟩
    · simp only [List.length_reverse]
      nlinarith [Nat.zero_le (w.length * c), Nat.zero_le (w.length ^ 2), Nat.zero_le (c ^ 2)]
    · simpa [afterScan] using ht

end ProteinFolding.TM2Arithmetic.Comparator

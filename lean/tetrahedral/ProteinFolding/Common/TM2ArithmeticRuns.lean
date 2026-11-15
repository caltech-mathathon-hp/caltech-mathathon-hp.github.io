import ProteinFolding.Common.TM2ArithmeticComparator

/-! Counted execution lemmas for the binary/unary comparator. -/

namespace ProteinFolding.TM2Arithmetic.Comparator

open Computability Turing TM2

theorem dec_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .dec (regs borrow neg res) i b (a :: w) u o)) =
      some (cfg .dec (regs (borrow && !a) neg res) i
        ((if borrow then !a else a) :: b) w u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_bits, update_buffer]

def afterDec (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    Cfg Alphabet Phase Reg :=
  if borrow then cfg .clearBits (regs true neg true) i b [] u o
  else cfg .consume (regs false neg res) i b [] u o

theorem dec_step_nil (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick (some (cfg .dec (regs borrow neg res) i b [] u o)) =
      some (afterDec borrow neg res i b u o) := by
  cases borrow <;> simp [tick, cfg, regs, program, step, stepAux, contents,
    update_bits, afterDec]

theorem dec_run (w : List Bool) (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick^[w.length + 1] (some (cfg .dec (regs borrow neg res) i b w u o)) =
      some (afterDec (decrement borrow w).2 neg res i
        ((decrement borrow w).1.reverse ++ b) u o) := by
  induction w generalizing borrow b with
  | nil => simpa [decrement] using dec_step_nil borrow neg res i b u o
  | cons a w ih =>
    rw [List.length_cons, Nat.add_right_comm w.length 1 1, Function.iterate_succ_apply,
      dec_step_cons]
    simpa [decrement, List.reverse_cons, List.append_assoc] using
      ih (borrow && !a) ((if borrow then !a else a) :: b)

theorem restore_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .restore (regs borrow neg res) i (a :: b) w u o)) =
      some (cfg .restore (regs borrow neg res) i b (a :: w) u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_bits, update_buffer]

theorem restore_step_nil (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick (some (cfg .restore (regs borrow neg res) i [] w u o)) =
      some (cfg .dec (regs true neg res) i [] w u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_buffer]

theorem restore_run (b : List Bool) (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick^[b.length + 1] (some (cfg .restore (regs borrow neg res) i b w u o)) =
      some (cfg .dec (regs true neg res) i [] (b.reverse ++ w) u o) := by
  induction b generalizing w with
  | nil => simpa using restore_step_nil borrow neg res i w u o
  | cons a b ih =>
    rw [List.length_cons, Nat.add_right_comm b.length 1 1, Function.iterate_succ_apply,
      restore_step_cons]
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: w)

theorem consume_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .consume (regs borrow neg res) i b w (a :: u) o)) =
      some (cfg .restore (regs borrow neg res) i b w u o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_unary]

theorem consume_step_nil (borrow neg res : Bool) (i : List Sym) (b w o : List Bool) :
    tick (some (cfg .consume (regs borrow neg res) i b w [] o)) =
      some (cfg .clearBits (regs borrow neg false) i b w [] o) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_unary]

theorem clearBits_run (w : List Bool) (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick^[w.length + 1] (some (cfg .clearBits (regs borrow neg res) i b w u o)) =
      some (cfg .clearBuffer (regs borrow neg res) i b [] u o) := by
  induction w with
  | nil => simp [tick, cfg, regs, program, step, stepAux, contents, update_bits]
  | cons a w ih =>
    rw [List.length_cons, Nat.add_right_comm w.length 1 1, Function.iterate_succ_apply]
    simpa only [tick, Option.bind_some, cfg, regs, program, step, stepAux, contents, update_bits, List.head?_cons,
      List.tail_cons, Option.isSome_some, cond_true] using ih

theorem clearBuffer_run (b : List Bool) (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick^[b.length + 1] (some (cfg .clearBuffer (regs borrow neg res) i b w u o)) =
      some (cfg .clearUnary (regs borrow neg res) i [] w u o) := by
  induction b with
  | nil => simp [tick, cfg, regs, program, step, stepAux, contents, update_buffer]
  | cons a b ih =>
    rw [List.length_cons, Nat.add_right_comm b.length 1 1, Function.iterate_succ_apply]
    simpa only [tick, Option.bind_some, cfg, regs, program, step, stepAux, contents, update_buffer, List.head?_cons,
      List.tail_cons, Option.isSome_some, cond_true] using ih

theorem clearUnary_run (u : List Bool) (borrow neg res : Bool) (i : List Sym) (b w o : List Bool) :
    tick^[u.length + 1] (some (cfg .clearUnary (regs borrow neg res) i b w u o)) =
      some (cfg .finish (regs borrow neg res) i b w [] o) := by
  induction u with
  | nil => simp [tick, cfg, regs, program, step, stepAux, contents, update_unary]
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simpa only [tick, Option.bind_some, cfg, regs, program, step, stepAux, contents, update_unary, List.head?_cons,
      List.tail_cons, Option.isSome_some, cond_true] using ih

theorem finish_step (borrow neg res : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .finish (regs borrow neg res) i b w u o)) =
      some (⟨none, initial, contents i b w u (res :: o)⟩ : Cfg Alphabet Phase Reg) := by
  simp [tick, cfg, regs, program, step, stepAux, contents, update_output]

theorem run_join {a b c : Option (Cfg Alphabet Phase Reg)} (m n : ℕ)
    (hm : tick^[m] a = b) (hn : tick^[n] b = c) : tick^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, hm, hn]

theorem cleanup_run (w b u : List Bool) (borrow neg res : Bool) (o : List Bool) :
    tick^[w.length + b.length + u.length + 4]
      (some (cfg .clearBits (regs borrow neg res) [] b w u o)) =
        some (⟨none, initial, contents [] [] [] [] (res :: o)⟩ : Cfg Alphabet Phase Reg) := by
  have h1 := clearBits_run w borrow neg res [] b u o
  have h2 := clearBuffer_run b borrow neg res [] [] u o
  have h3 := clearUnary_run u borrow neg res [] [] [] o
  have h4 : tick^[1] (some (cfg .finish (regs borrow neg res) [] [] [] [] o)) =
      some (⟨none, initial, contents [] [] [] [] (res :: o)⟩ : Cfg Alphabet Phase Reg) :=
    finish_step borrow neg res [] [] [] [] o
  have h := run_join _ _ (run_join _ _ (run_join _ _ h1 h2) h3) h4
  have hexp : w.length + 1 + (b.length + 1) + (u.length + 1) + 1 =
      w.length + b.length + u.length + 4 := by omega
  simpa only [hexp] using h

end ProteinFolding.TM2Arithmetic.Comparator
